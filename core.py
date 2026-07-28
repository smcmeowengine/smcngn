#!/usr/bin/env python3
"""
AXIS ENGINE v3.3.3
==================
Multi-timeframe SMC/ICT crypto perpetual signal engine for Hyperliquid.

Key components:
  - Three-Pathway Confluence Router (Liquidity Reversal / Trend Continuation
    / Momentum Breakout) scored through one unified logistic model.
  - Adaptive Frequency Governor that nudges the acceptance threshold toward
    a 5-10 signal/day band.
  - Composite Regime Vector (BTC macro bias, volatility percentile, ADX,
    session liquidity weight, noise index, market breadth) driving both
    threshold selection and per-pathway eligibility.
  - Dynamic correlation-cluster deduplication from realized returns.
  - Self-tuning per-pathway/per-symbol/per-combo confidence weighting from
    history.
  - Structure-aware, liquidity-target TP/SL clipped to real liquidity
    pools, order blocks, and volume-profile value-area edges.
  - Session Volume Profile (POC / Value Area / VWAP) feeding TP clipping
    and scoring.

Single file, immediately runnable. Scan-per-run model: an external
scheduler (cron, GitHub Actions, systemd timer, etc.) invokes this script
every 15 minutes. All persistence lives in state.json next to the script.

Configure via environment variables (see CONFIGURATION below) and run:

    python3 axis_engine_v3_3_3.py
"""

from __future__ import annotations

import collections
import fcntl
import json
import math
import os
import re
import signal
import statistics
import threading
import time
import logging
import urllib.error
import urllib.request
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field
from datetime import datetime, timezone
from typing import Optional

# --- CONFIGURATION ---

HL_API_URL = "https://api.hyperliquid.xyz/info"
TG_BOT_TOKEN = os.environ.get("TG_BOT_TOKEN", "")
TG_CHAT_ID = os.environ.get("TG_CHAT_ID", "")

STATE_PATH = os.environ.get("AXIS_STATE_PATH", "state.json")
LOCK_PATH = os.environ.get("AXIS_LOCK_PATH", "axis_engine.lock")
LOG_PATH = os.environ.get("AXIS_LOG_PATH", "axis_engine.log")
CANDLE_CACHE_PATH = os.environ.get("AXIS_CANDLE_CACHE_PATH", "candle_cache.json")
CANDLE_DELTA_OVERLAP_BARS = 3  # extra closed bars re-fetched past the cached watermark

WATCHLIST = [
    "BTC", "ETH", "HYPE", "ZEC", "NEAR", "ONDO", "SUI", "PENGU", "BNB", "SOL",
    "TRX", "BCH", "DOGE", "ADA", "DOT", "TAO", "AVAX", "LINK", "AAVE", "XRP",
    "XLM", "UNI", "LTC", "APT", "PENDLE",
]

# Timeframe combos: (bias, structure, execution). Picked per symbol per
# scan by the Regime Router based on the symbol's volatility/ADX profile.
COMBOS = {
    "scalp":    {"bias": "1h", "struct": "15m", "exec": "5m",  "hold_hint": "0.5-4h"},
    "intraday": {"bias": "4h", "struct": "1h",  "exec": "15m", "hold_hint": "4-24h"},
    "swing":    {"bias": "1d", "struct": "4h",  "exec": "1h",  "hold_hint": "1-5d"},
}

TF_MS = {
    "5m": 5 * 60_000, "15m": 15 * 60_000, "1h": 60 * 60_000,
    "4h": 4 * 60 * 60_000, "1d": 24 * 60 * 60_000,
}
CANDLE_COUNT = {"5m": 300, "15m": 300, "1h": 300, "4h": 240, "1d": 180}

# SL/TP monitoring tests each closed 15m candle's high/low against active
# levels (rather than just live mark price), so a wick that touches and
# reverses between scans is still caught. 15m matches the scan cadence.
MONITOR_TF = "15m"

# Resting/POI entries (e.g. liquidity_reversal's breaker-block entry) sit
# away from market price and may never actually trade. If price hasn't
# reached the entry within this many closed MONITOR_TF candles, the signal
# is cancelled as "expired" instead of sitting open forever. 8 * 15m = 2h.
PENDING_ENTRY_EXPIRY_BARS = 8

ATR_LEN = 14
RSI_LEN = 14
ADX_LEN = 14
EMA_FAST, EMA_SLOW, EMA_TREND = 20, 50, 200
BB_LEN, BB_MULT = 20, 2.0

# Volume-at-price model (POC / Value Area / VWAP) from recent 1h candles.
VOL_PROFILE_BINS = 24
VOL_PROFILE_LOOKBACK_BARS = 96   # ~4 days of 1h bars as the "session" profile

# --- Adaptive Frequency Governor -------------------------------------------
TARGET_SIGNALS_MIN = 5
TARGET_SIGNALS_MAX = 10
GOVERNOR_STEP = 2.0
GOVERNOR_FLOOR = 54.0
GOVERNOR_CEIL = 88.0
GOVERNOR_MIN_INTERVAL_S = 3600  # rate-limit threshold nudges to once/hour

# Each pathway's multiplier drifts slowly toward a win-rate-implied target,
# shrunk toward a neutral prior of 1.0 and bounded.
PATHWAY_WEIGHT_LEARNING_RATE = 0.04
PATHWAY_WEIGHT_MIN, PATHWAY_WEIGHT_MAX = 0.75, 1.30

# Same shrink-toward-neutral drift, but keyed on `combo` (scalp/intraday/
# swing) instead of pathway. Segmenting win rate by combo surfaces edges
# that pathway-level weighting alone can't see -- e.g. intraday setups
# under-perform scalp setups even within the same pathway.
COMBO_WEIGHT_LEARNING_RATE = 0.04
COMBO_WEIGHT_MIN, COMBO_WEIGHT_MAX = 0.75, 1.30

# --- Setup Grade -> risk sizing hint (percent of equity), informational ---
GRADE_SIZE_TABLE = {
    ("A+", "scalp"): 1.00, ("A+", "intraday"): 1.25, ("A+", "swing"): 1.50,
    ("A",  "scalp"): 0.75, ("A",  "intraday"): 1.00, ("A",  "swing"): 1.25,
    ("B",  "scalp"): 0.50, ("B",  "intraday"): 0.65, ("B",  "swing"): 0.85,
    ("C",  "scalp"): 0.25, ("C",  "intraday"): 0.35, ("C",  "swing"): 0.45,
}

MAX_CONCURRENT_PER_SYMBOL = 1
MAX_CONCURRENT_SAME_DIRECTION = 6
COOLDOWN_BARS = 6
DEDUP_PRICE_TOL_PCT = 0.0025
DEDUP_TIME_WINDOW_HOURS = 48

POI_ATR_MULT = {"scalp": 0.5, "intraday": 0.65, "swing": 0.85}
POI_MAX_PCT_OF_PRICE = 0.008

# A shared weight-aware pacer caps aggregate request weight per Hyperliquid's
# per-IP limit (1200/min); most `info` endpoints cost 20, a few cost 2, and
# candleSnapshot scales as 20 * ceil(bars / 60).
HL_WEIGHT_BUDGET_PER_MINUTE = 1100.0  # headroom under the real 1200/min cap
HL_ENDPOINT_BASE_WEIGHT = {
    "l2Book": 2, "allMids": 2, "clearinghouseState": 2, "orderStatus": 2,
    "spotClearinghouseState": 2, "exchangeStatus": 2,
    "userRole": 60,
}
HL_DEFAULT_INFO_WEIGHT = 20
FETCH_THREAD_WORKERS = 6

# Trend-continuation pathway tuning
TREND_ADX_MIN = 20.0
# RSI must dip into a pullback zone, then turn back out past a stricter level.
RSI_DIP_LONG, RSI_TURN_LONG = 40.0, 45.0
RSI_DIP_SHORT, RSI_TURN_SHORT = 60.0, 55.0
RSI_RESET_LOOKBACK = 8

# Momentum breakout pathway tuning
BREAKOUT_BB_SQUEEZE_PCTILE = 0.35   # bandwidth must be in the tightest X pctile of recent history
BREAKOUT_VOL_MULT = 1.6             # breakout bar volume vs 20-bar average
BREAKOUT_LOOKBACK_HIGH_LOW = 20

# Correlation clustering (computed fresh each run from bias-tf returns)
CORR_LOOKBACK_BARS = 60
CORR_CLUSTER_THRESHOLD = 0.72

# Hard filters
MIN_OI_USD = 3_000_000
MIN_ATR_PCT = 0.0012
MAX_ATR_PCT = 0.12
# Raised to a hard 2:1 floor on TP2. This is a floor only -- rr() is never
# clipped down to it, so trades still land wherever the real entry/sl/tp2
# math and liquidity clipping put them (typically above 2.0, since every
# pathway's raw TP2 multiplier is already 2.4-2.8x risk before clipping).
# TP1's 1.4-1.5x multipliers are untouched: TP1 is a deliberate partial-exit
# level, not the trade's reward target, and forcing it to 2:1 too would fight
# that two-stage design rather than just tighten it.
MIN_RR = 2.0

# Per (combo, pathway) RR floor overrides, applied on top of MIN_RR.
# `intraday` + `liquidity_reversal` is both the largest segment (n=62, half
# the dataset) and the weakest (37.1% WR, vs 61.0% for scalp+liquidity_
# reversal), so it's held to a stricter RR bar than everything else so
# weaker setups get filtered pre-signal rather than showing up post-hoc as
# losses. Empty by default; populate/adjust per-pair as trailing data warrants.
# Bumped 1.9 -> 2.5 to preserve the original +0.5-over-base gap now that
# MIN_RR itself moved to 2.0 -- otherwise this override would have collapsed
# to equal the new base floor and silently stopped being "stricter" for the
# segment it was specifically added to guard. This number was tuned to a
# specific observed win rate, though, so it's worth re-checking against
# current segment_stats rather than trusting this preserved-gap guess long-term.
MIN_RR_OVERRIDES: dict[tuple[str, str], float] = {
    ("intraday", "liquidity_reversal"): 2.5,
}


def min_rr_for(combo_name: str, pathway: str) -> float:
    return MIN_RR_OVERRIDES.get((combo_name, pathway), MIN_RR)

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s | %(levelname)s | %(message)s",
    handlers=[logging.FileHandler(LOG_PATH), logging.StreamHandler()],
)
log = logging.getLogger("axis")


def _handle_shutdown(sig_num, frame):
    log.warning("Received shutdown signal %s, exiting cleanly.", sig_num)
    raise SystemExit(0)


signal.signal(signal.SIGTERM, _handle_shutdown)
signal.signal(signal.SIGINT, _handle_shutdown)


# --- HYPERLIQUID API ---

def hl_coin(symbol: str) -> str:
    return symbol.upper()


class _WeightRateLimiter:
    """Sliding-60s-window pacer shared across all threads, tracking request
    weight (not count) so heavy calls are paced accordingly."""

    def __init__(self, budget_per_minute: float):
        self.budget = budget_per_minute
        self.window_s = 60.0
        self.lock = threading.Lock()
        self.events: collections.deque[tuple[float, float]] = collections.deque()

    def wait(self, weight: float):
        while True:
            with self.lock:
                now = time.monotonic()
                cutoff = now - self.window_s
                while self.events and self.events[0][0] < cutoff:
                    self.events.popleft()
                used = sum(w for _, w in self.events)
                if used + weight <= self.budget:
                    self.events.append((now, weight))
                    return
                # not enough budget yet; wait for the oldest event to age out
                sleep_for = max(0.05, self.events[0][0] + self.window_s - now)
            time.sleep(min(sleep_for, 2.0))


_rate_limiter = _WeightRateLimiter(HL_WEIGHT_BUDGET_PER_MINUTE)


def _request_weight(payload: dict) -> float:
    """Estimate the Hyperliquid weight cost of a request."""
    req_type = payload.get("type", "")
    if req_type == "candleSnapshot":
        req = payload.get("req", {})
        interval = req.get("interval")
        start_ms, end_ms = req.get("startTime"), req.get("endTime")
        n_bars = 60  # conservative default if we can't compute the span
        if interval in TF_MS and start_ms is not None and end_ms is not None:
            step = TF_MS[interval]
            n_bars = max(1, math.ceil((end_ms - start_ms) / step))
        return HL_DEFAULT_INFO_WEIGHT * math.ceil(n_bars / 60)
    return HL_ENDPOINT_BASE_WEIGHT.get(req_type, HL_DEFAULT_INFO_WEIGHT)


def hl_post(payload: dict, retries: int = 4, timeout: int = 12) -> dict | list | None:
    body = json.dumps(payload).encode()
    req = urllib.request.Request(
        HL_API_URL, data=body, headers={"Content-Type": "application/json"}
    )
    weight = _request_weight(payload)
    for attempt in range(retries):
        _rate_limiter.wait(weight)
        try:
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                return json.loads(resp.read().decode())
        except urllib.error.HTTPError as e:
            if e.code == 429:
                retry_after = e.headers.get("Retry-After")
                wait_s = float(retry_after) if retry_after else 10.0  # HL allows 1 req/10s once limited
                log.warning("hl_post 429 (attempt %d, type=%s), backing off %.1fs",
                            attempt + 1, payload.get("type"), wait_s)
                time.sleep(wait_s)
            else:
                log.warning("hl_post HTTP error attempt %d (%s): %s", attempt + 1, payload.get("type"), e)
                time.sleep(0.8 * (attempt + 1))
        except (urllib.error.URLError, TimeoutError, ValueError) as e:
            log.warning("hl_post attempt %d failed (%s): %s", attempt + 1, payload.get("type"), e)
            time.sleep(0.8 * (attempt + 1))
    log.error("hl_post exhausted retries for type=%s", payload.get("type"))
    return None


def current_bar_open_ms(reference_ms: int, interval: str) -> int:
    step = TF_MS[interval]
    return (reference_ms // step) * step


def filter_closed_candles(candles: list[dict], interval: str, reference_ms: int) -> list[dict]:
    cutoff = current_bar_open_ms(reference_ms, interval)
    return [c for c in candles if c["t"] < cutoff]


def _request_candles(symbol: str, interval: str, start_ms: int, end_ms: int) -> list[dict]:
    payload = {
        "type": "candleSnapshot",
        "req": {
            "coin": hl_coin(symbol),
            "interval": interval,
            "startTime": start_ms,
            "endTime": end_ms,
        },
    }
    raw = hl_post(payload)
    if not raw:
        return []
    return [
        {"t": c["t"], "o": float(c["o"]), "h": float(c["h"]),
         "l": float(c["l"]), "c": float(c["c"]), "v": float(c["v"])}
        for c in raw
    ]


def get_candles(symbol: str, interval: str, n: int, reference_ms: int | None = None,
                 cache_entry: list[dict] | None = None) -> list[dict]:
    """Return the last `n` closed candles for symbol/interval. Uses
    `cache_entry` to fetch only new bars past the cached watermark when
    possible, and skips the network call entirely if no new bar could
    have closed yet."""
    reference_ms = reference_ms or int(time.time() * 1000)

    if cache_entry:
        step = TF_MS[interval]
        last_cached_t = cache_entry[-1]["t"]
        if current_bar_open_ms(reference_ms, interval) <= last_cached_t + step:
            return filter_closed_candles(cache_entry, interval, reference_ms)[-n:]
        start_ms = last_cached_t - step * CANDLE_DELTA_OVERLAP_BARS
        new_raw = _request_candles(symbol, interval, start_ms, reference_ms)
        if new_raw:
            merged = {c["t"]: c for c in cache_entry}
            for c in new_raw:
                merged[c["t"]] = c
            candles = [merged[t] for t in sorted(merged.keys())]
        else:
            candles = cache_entry  # delta fetch failed; fall back to cache
        candles = filter_closed_candles(candles, interval, reference_ms)
        return candles[-n:]

    # no cache: full pull
    lookback_ms = n * TF_MS[interval] * 2 + TF_MS[interval] * 5
    raw = _request_candles(symbol, interval, reference_ms - lookback_ms, reference_ms)
    candles = filter_closed_candles(raw, interval, reference_ms)
    return candles[-n:]


def fetch_all_candles(symbol: str, candle_cache: dict[str, dict] | None = None,
                       reference_ms: int | None = None) -> dict[str, list[dict]] | None:
    bundle = {}
    sym_cache = (candle_cache or {}).get(symbol, {})
    for tf in ("5m", "15m", "1h", "4h", "1d"):
        cache_entry = sym_cache.get(tf)
        candles = get_candles(symbol, tf, CANDLE_COUNT[tf], reference_ms, cache_entry)
        if len(candles) < 60:
            log.info("Insufficient %s candles for %s (%d)", tf, symbol, len(candles))
            return None
        bundle[tf] = candles
        if candle_cache is not None:
            candle_cache.setdefault(symbol, {})[tf] = candles
    return bundle


def get_meta_and_ctx() -> tuple[list[str], list[dict]] | None:
    raw = hl_post({"type": "metaAndAssetCtxs"})
    if not raw or len(raw) < 2:
        return None
    universe = [a["name"] for a in raw[0]["universe"]]
    return universe, raw[1]


def get_market_snapshot() -> dict[str, dict]:
    """symbol -> {mid, funding, oi_usd, mark}"""
    out = {}
    got = get_meta_and_ctx()
    if not got:
        return out
    universe, ctxs = got
    for i, name in enumerate(universe):
        if name not in WATCHLIST and name != "BTC":
            continue
        try:
            ctx = ctxs[i]
            mark = float(ctx.get("markPx", 0) or 0)
            funding = float(ctx.get("funding", 0) or 0)
            oi_coins = float(ctx.get("openInterest", 0) or 0)
            out[name] = {"mark": mark, "funding": funding, "oi_usd": oi_coins * mark}
        except (KeyError, ValueError, TypeError, IndexError):
            continue
    return out


def get_l2_book(coin: str) -> dict | None:
    return hl_post({"type": "l2Book", "coin": hl_coin(coin)})


def analyze_orderbook(coin: str) -> dict:
    """Lightweight microstructure read: bid/ask imbalance near touch."""
    book = get_l2_book(coin)
    if not book or "levels" not in book:
        return {"imbalance": 0.0, "spread_bps": None}
    try:
        bids, asks = book["levels"][0], book["levels"][1]
        depth = 15
        bid_sz = sum(float(x["sz"]) for x in bids[:depth])
        ask_sz = sum(float(x["sz"]) for x in asks[:depth])
        total = bid_sz + ask_sz
        imbalance = (bid_sz - ask_sz) / total if total > 0 else 0.0
        best_bid, best_ask = float(bids[0]["px"]), float(asks[0]["px"])
        mid = (best_bid + best_ask) / 2
        spread_bps = ((best_ask - best_bid) / mid) * 10_000 if mid else None
        return {"imbalance": imbalance, "spread_bps": spread_bps}
    except (KeyError, IndexError, ValueError, TypeError):
        return {"imbalance": 0.0, "spread_bps": None}


# --- INDICATORS ---

def safe(v, fb=0.0):
    try:
        if v is None or math.isnan(v) or math.isinf(v):
            return fb
        return v
    except TypeError:
        return fb


def ema(vals: list[float], period: int) -> list[float]:
    if not vals:
        return []
    k = 2 / (period + 1)
    out = [vals[0]]
    for v in vals[1:]:
        out.append(v * k + out[-1] * (1 - k))
    return out


def sma(vals: list[float], period: int) -> list[float]:
    out = []
    for i in range(len(vals)):
        lo = max(0, i - period + 1)
        window = vals[lo:i + 1]
        out.append(sum(window) / len(window))
    return out


def stdev(vals: list[float], period: int) -> list[float]:
    out = []
    for i in range(len(vals)):
        lo = max(0, i - period + 1)
        window = vals[lo:i + 1]
        out.append(statistics.pstdev(window) if len(window) > 1 else 0.0)
    return out


def rsi(closes: list[float], period: int = RSI_LEN) -> list[float]:
    if len(closes) < period + 1:
        return [50.0] * len(closes)
    out = [50.0] * len(closes)
    gains, losses = [0.0], [0.0]
    for i in range(1, len(closes)):
        d = closes[i] - closes[i - 1]
        gains.append(max(d, 0.0))
        losses.append(max(-d, 0.0))
    avg_gain = sum(gains[1:period + 1]) / period
    avg_loss = sum(losses[1:period + 1]) / period
    for i in range(period + 1, len(closes)):
        avg_gain = (avg_gain * (period - 1) + gains[i]) / period
        avg_loss = (avg_loss * (period - 1) + losses[i]) / period
        rs = avg_gain / avg_loss if avg_loss > 1e-12 else 999.0
        out[i] = 100 - (100 / (1 + rs))
    return out


def atr(highs, lows, closes, period: int = ATR_LEN) -> list[float]:
    trs = [highs[0] - lows[0]]
    for i in range(1, len(closes)):
        trs.append(max(
            highs[i] - lows[i],
            abs(highs[i] - closes[i - 1]),
            abs(lows[i] - closes[i - 1]),
        ))
    out, a = [], trs[0]
    for i, tr in enumerate(trs):
        a = tr if i == 0 else (a * (period - 1) + tr) / period
        out.append(a)
    return out


def adx_dmi(highs, lows, closes, period: int = ADX_LEN) -> tuple[list[float], list[float], list[float]]:
    n = len(closes)
    plus_dm, minus_dm, trs = [0.0], [0.0], [highs[0] - lows[0]]
    for i in range(1, n):
        up, down = highs[i] - highs[i - 1], lows[i - 1] - lows[i]
        plus_dm.append(up if (up > down and up > 0) else 0.0)
        minus_dm.append(down if (down > up and down > 0) else 0.0)
        trs.append(max(highs[i] - lows[i], abs(highs[i] - closes[i - 1]), abs(lows[i] - closes[i - 1])))

    def wilder(series):
        out, s = [], series[0]
        for i, v in enumerate(series):
            s = v if i == 0 else s - (s / period) + v
            out.append(s)
        return out

    atr_w = wilder(trs)
    pdm_w = wilder(plus_dm)
    mdm_w = wilder(minus_dm)
    plus_di = [100 * safe(pdm_w[i] / atr_w[i], 0) if atr_w[i] else 0.0 for i in range(n)]
    minus_di = [100 * safe(mdm_w[i] / atr_w[i], 0) if atr_w[i] else 0.0 for i in range(n)]
    dx = [100 * safe(abs(plus_di[i] - minus_di[i]) / (plus_di[i] + minus_di[i]), 0)
          if (plus_di[i] + minus_di[i]) else 0.0 for i in range(n)]
    adx = ema(dx, period)
    return adx, plus_di, minus_di


def bollinger_width_pct(closes: list[float], period: int = BB_LEN, mult: float = BB_MULT) -> list[float]:
    mids = sma(closes, period)
    sds = stdev(closes, period)
    return [safe((2 * mult * sds[i]) / mids[i], 0) if mids[i] else 0.0 for i in range(len(closes))]


def detect_rsi_divergence(closes: list[float], rsi_values: list[float],
                           highs: list[float], lows: list[float],
                           lookback: int = 20) -> dict:
    """Price/RSI divergence over the last `lookback` bars: bearish is a
    higher price high with a lower RSI high; bullish is the mirror on
    swing lows. Used as a confluence bonus, never a hard filter."""
    min_len = lookback + 2
    if min(len(closes), len(rsi_values), len(highs), len(lows)) < min_len:
        return {"type": None, "strength": 0}

    recent_highs = highs[-min_len:]
    recent_lows = lows[-min_len:]
    recent_rsi = rsi_values[-min_len:]

    price_highs, price_lows, rsi_highs, rsi_lows = [], [], [], []
    for i in range(1, len(recent_highs) - 1):
        if recent_highs[i] > recent_highs[i - 1] and recent_highs[i] > recent_highs[i + 1]:
            price_highs.append(recent_highs[i])
            rsi_highs.append(recent_rsi[i])
        if recent_lows[i] < recent_lows[i - 1] and recent_lows[i] < recent_lows[i + 1]:
            price_lows.append(recent_lows[i])
            rsi_lows.append(recent_rsi[i])

    if len(price_highs) >= 2 and price_highs[-1] > price_highs[-2] and rsi_highs[-1] < rsi_highs[-2]:
        return {"type": "bearish", "strength": 1}
    if len(price_lows) >= 2 and price_lows[-1] < price_lows[-2] and rsi_lows[-1] > rsi_lows[-2]:
        return {"type": "bullish", "strength": 1}
    return {"type": None, "strength": 0}


def compute_indicators(candles: list[dict]) -> dict:
    closes = [c["c"] for c in candles]
    highs = [c["h"] for c in candles]
    lows = [c["l"] for c in candles]
    vols = [c["v"] for c in candles]
    adx_v, plus_di, minus_di = adx_dmi(highs, lows, closes)
    rsi_vals = rsi(closes)
    return {
        "closes": closes, "highs": highs, "lows": lows, "vols": vols,
        "ema_fast": ema(closes, EMA_FAST), "ema_slow": ema(closes, EMA_SLOW),
        "ema_trend": ema(closes, EMA_TREND),
        "rsi": rsi_vals, "atr": atr(highs, lows, closes),
        "adx": adx_v, "plus_di": plus_di, "minus_di": minus_di,
        "bb_width": bollinger_width_pct(closes),
        "vol_sma20": sma(vols, 20),
        "rsi_divergence": detect_rsi_divergence(closes, rsi_vals, highs, lows),
    }


# --- STATE MANAGEMENT ---

def _default_state() -> dict:
    return {
        "active_signals": [],
        "signal_history": [],
        "cooldowns": {},
        "atr_pct_memory": {},
        "governor": {"threshold": 66.0, "last_adjust_ts": 0, "daily_count_ema": 6.0},
        "pathway_weights": {
            "liquidity_reversal": 1.0, "trend_continuation": 1.0, "momentum_breakout": 1.0,
        },
        "combo_weights": {
            "scalp": 1.0, "intraday": 1.0, "swing": 1.0,
        },
        "symbol_weights": {},
        "corr_returns": {},
        "last_summary_ts": 0,
        "meta": {"version": "3.3.3", "created": int(time.time())},
        "baseline": {"win_rate": None, "profit_factor": None, "avg_rr": None, "n": 0},
        "circuit_breaker": {"active": False, "since": None, "reason": None},
    }


def load_state() -> dict:
    if not os.path.exists(STATE_PATH):
        return _default_state()
    try:
        with open(STATE_PATH, "r") as f:
            state = json.load(f)
        base = _default_state()
        for k, v in base.items():
            state.setdefault(k, v)
        return state
    except (json.JSONDecodeError, OSError) as e:
        log.error("Failed to load state (%s), starting fresh.", e)
        return _default_state()


def save_state(state: dict):
    tmp = STATE_PATH + ".tmp"
    try:
        with open(tmp, "w") as f:
            json.dump(state, f, indent=2)
        os.replace(tmp, STATE_PATH)
    except OSError as e:
        log.error("Failed to save state: %s", e)


def load_candle_cache() -> dict[str, dict]:
    if not os.path.exists(CANDLE_CACHE_PATH):
        return {}
    try:
        with open(CANDLE_CACHE_PATH, "r") as f:
            return json.load(f)
    except (json.JSONDecodeError, OSError) as e:
        log.error("Failed to load candle cache (%s), starting fresh (full re-fetch this run).", e)
        return {}


def save_candle_cache(candle_cache: dict[str, dict]):
    tmp = CANDLE_CACHE_PATH + ".tmp"
    try:
        with open(tmp, "w") as f:
            json.dump(candle_cache, f)
        os.replace(tmp, CANDLE_CACHE_PATH)
    except OSError as e:
        log.error("Failed to save candle cache: %s", e)


def prune_state(state: dict, max_signals: int = 800, max_days: int = 21):
    cutoff = int(time.time()) - max_days * 86400
    state["signal_history"] = [
        s for s in state["signal_history"] if s.get("ts", 0) >= cutoff
    ][-max_signals:]
    for sym in list(state["atr_pct_memory"].keys()):
        state["atr_pct_memory"][sym] = state["atr_pct_memory"][sym][-200:]


# --- REGIME VECTOR ---

@dataclass
class RegimeVector:
    btc_bias: str
    btc_strength: float
    vol_pctile: float
    adx_bias: float
    session_weight: float
    noise_index: float
    breadth: float   # 0..1, % of watchlist whose own 1h trend agrees with btc_bias

    def composite_favorability(self) -> float:
        # higher = more favorable: clean trend, low noise, good breadth
        trend_component = min(self.adx_bias / 35.0, 1.0)
        noise_penalty = max(0.0, 1.0 - self.noise_index)
        return round(
            0.38 * trend_component + 0.26 * noise_penalty +
            0.21 * self.session_weight + 0.15 * self.breadth,
            4,
        )


def session_weight_now() -> float:
    """Weights scans up during high-liquidity hours (13:00-21:00 UTC) and
    down during the quiet 00:00-05:00 UTC stretch."""
    hour = time.gmtime().tm_hour
    if 13 <= hour <= 21:
        return 1.0
    if 0 <= hour <= 5:
        return 0.75
    return 0.9


def update_atr_pct_memory(state: dict, symbol: str, atr_pct: float) -> float:
    mem = state["atr_pct_memory"].setdefault(symbol, [])
    mem.append(atr_pct)
    state["atr_pct_memory"][symbol] = mem[-200:]
    if len(mem) < 10:
        return 0.5
    sorted_mem = sorted(mem)
    rank = sum(1 for x in sorted_mem if x <= atr_pct)
    return rank / len(sorted_mem)


def compute_btc_regime(btc_bundle: dict) -> tuple[str, float]:
    ind = compute_indicators(btc_bundle["4h"])
    price = ind["closes"][-1]
    ef, es, et = ind["ema_fast"][-1], ind["ema_slow"][-1], ind["ema_trend"][-1]
    adx_v = ind["adx"][-1]
    if price > ef > es > et:
        bias = "bullish"
    elif price < ef < es < et:
        bias = "bearish"
    else:
        bias = "neutral"
    return bias, safe(adx_v, 0.0)


def compute_noise_index(candles: list[dict], lookback: int = 30) -> float:
    """1 - (net displacement / path length) over the lookback: low means
    clean directional travel, high means choppy/overlapping candles."""
    window = candles[-lookback:]
    if len(window) < 5:
        return 0.5
    net = abs(window[-1]["c"] - window[0]["c"])
    path = sum(abs(window[i]["c"] - window[i - 1]["c"]) for i in range(1, len(window)))
    efficiency = safe(net / path, 0.5) if path else 0.5
    return round(1.0 - min(efficiency, 1.0), 4)


def symbol_bias_from_bundle(bundle: dict) -> str | None:
    """1h EMA20/EMA50 bias read for the market-breadth gate, reusing the
    already-fetched bundle."""
    candles = bundle.get("1h")
    if not candles or len(candles) < EMA_SLOW + 5:
        return None
    closes = [c["c"] for c in candles]
    fast, slow = ema(closes, EMA_FAST)[-1], ema(closes, EMA_SLOW)[-1]
    return "bullish" if fast > slow else "bearish"


def compute_breadth(bundles: dict[str, dict], btc_bias: str) -> float:
    """Fraction of the watchlist whose 1h trend agrees with BTC's bias.
    Falls back to a neutral 0.5 when BTC bias itself is neutral."""
    if btc_bias not in ("bullish", "bearish") or not bundles:
        return 0.5
    biases = [b for b in (symbol_bias_from_bundle(bundle) for bundle in bundles.values()) if b is not None]
    if not biases:
        return 0.5
    aligned = sum(1 for b in biases if b == btc_bias)
    return aligned / len(biases)


def build_regime_vector(state: dict, symbol: str, bundle: dict, btc_bias: str,
                         btc_strength: float, breadth: float, combo: dict) -> RegimeVector:
    ind_bias = compute_indicators(bundle[combo["bias"]])
    atr_pct = safe(ind_bias["atr"][-1] / ind_bias["closes"][-1], 0.01)
    vol_pctile = update_atr_pct_memory(state, symbol, atr_pct)
    noise = compute_noise_index(bundle[combo["struct"]])
    return RegimeVector(
        btc_bias=btc_bias, btc_strength=btc_strength, vol_pctile=vol_pctile,
        adx_bias=safe(ind_bias["adx"][-1], 0.0), session_weight=session_weight_now(),
        noise_index=noise, breadth=breadth,
    )


def select_combo(regime: RegimeVector) -> str:
    """High vol/high ADX -> scalp; low vol/low ADX -> swing; else intraday."""
    if regime.vol_pctile > 0.7 and regime.adx_bias > 25:
        return "scalp"
    if regime.vol_pctile < 0.3 and regime.adx_bias < 18:
        return "swing"
    return "intraday"


def adaptive_thresholds(regime: RegimeVector, base_threshold: float, combo_name: str | None = None) -> float:
    """Nudges the governor's base threshold up in choppy conditions and
    down in clean ones, bounded within the governor's floor/ceiling."""
    fav = regime.composite_favorability()
    adj = (0.5 - fav) * 10.0  # favorable (fav>0.5) lowers bar, unfavorable raises it
    # "intraday" is the ambiguous-regime catch-all and has weaker historical
    # edge than scalp/swing, so hold it to a higher bar.
    if combo_name == "intraday":
        adj += 4.0
    return max(GOVERNOR_FLOOR, min(GOVERNOR_CEIL, base_threshold + adj))


# --- MARKET STRUCTURE: SWINGS, BOS/CHoCH, ORDER BLOCKS, FVGs, LIQUIDITY ---

@dataclass
class Swing:
    index: int
    price: float
    kind: str  # "high" | "low"


def find_swings(candles: list[dict], left: int = 2, right: int = 2) -> list[Swing]:
    out = []
    for i in range(left, len(candles) - right):
        window_h = [candles[j]["h"] for j in range(i - left, i + right + 1)]
        window_l = [candles[j]["l"] for j in range(i - left, i + right + 1)]
        if candles[i]["h"] == max(window_h):
            out.append(Swing(i, candles[i]["h"], "high"))
        if candles[i]["l"] == min(window_l):
            out.append(Swing(i, candles[i]["l"], "low"))
    return out


@dataclass
class StructureState:
    bias: str            # "bullish" | "bearish" | "neutral"
    last_bos_index: int
    last_choch_index: int
    swings: list[Swing]


def analyze_structure(candles: list[dict], swings: list[Swing]) -> StructureState:
    highs = [s for s in swings if s.kind == "high"]
    lows = [s for s in swings if s.kind == "low"]
    bias, last_bos, last_choch = "neutral", -1, -1
    if len(highs) >= 2 and len(lows) >= 2:
        hh = highs[-1].price > highs[-2].price
        hl = lows[-1].price > lows[-2].price
        lh = highs[-1].price < highs[-2].price
        ll = lows[-1].price < lows[-2].price
        if hh and hl:
            bias, last_bos = "bullish", highs[-1].index
        elif lh and ll:
            bias, last_bos = "bearish", lows[-1].index
        elif hh and ll:
            bias, last_choch = "bullish", lows[-1].index  # failed lower low -> shift
        elif lh and hl:
            bias, last_choch = "bearish", highs[-1].index
    return StructureState(bias, last_bos, last_choch, swings)


@dataclass
class Zone:
    low: float
    high: float
    kind: str        # "bullish_ob" | "bearish_ob" | "bullish_fvg" | "bearish_fvg"
    index: int
    untested: bool = True

    def mid(self) -> float:
        return (self.low + self.high) / 2

    def contains(self, price: float, buf: float = 0.0) -> bool:
        return (self.low - buf) <= price <= (self.high + buf)


def find_order_blocks(candles: list[dict], atr_vals: list[float], lookback: int = 60) -> list[Zone]:
    zones = []
    start = max(1, len(candles) - lookback)
    for i in range(start, len(candles) - 1):
        c, nxt = candles[i], candles[i + 1]
        body = abs(c["c"] - c["o"])
        move = abs(nxt["c"] - nxt["o"])
        if move < 1.2 * atr_vals[i]:
            continue
        if c["c"] < c["o"] and nxt["c"] > nxt["o"] and nxt["c"] > c["h"]:
            zones.append(Zone(c["l"], c["h"], "bullish_ob", i))
        elif c["c"] > c["o"] and nxt["c"] < nxt["o"] and nxt["c"] < c["l"]:
            zones.append(Zone(c["l"], c["h"], "bearish_ob", i))
    return zones[-8:]


def find_fvgs(candles: list[dict], lookback: int = 60) -> list[Zone]:
    zones = []
    start = max(2, len(candles) - lookback)
    for i in range(start, len(candles)):
        a, b, c = candles[i - 2], candles[i - 1], candles[i]
        if a["h"] < c["l"]:
            zones.append(Zone(a["h"], c["l"], "bullish_fvg", i))
        elif a["l"] > c["h"]:
            zones.append(Zone(c["h"], a["l"], "bearish_fvg", i))
    return zones[-10:]


def mark_untested(zones: list[Zone], candles: list[dict]) -> list[Zone]:
    for z in zones:
        for c in candles[z.index + 1:]:
            if z.contains(c["c"]) or (c["l"] <= z.high and c["h"] >= z.low):
                z.untested = False
                break
    return zones


def cluster_levels(levels: list[float], tol_pct: float = 0.0015) -> list[tuple[float, int]]:
    if not levels:
        return []
    levels = sorted(levels)
    clusters, current = [], [levels[0]]
    for lv in levels[1:]:
        if abs(lv - current[-1]) / current[-1] <= tol_pct:
            current.append(lv)
        else:
            clusters.append((sum(current) / len(current), len(current)))
            current = [lv]
    clusters.append((sum(current) / len(current), len(current)))
    return clusters


def build_liquidity_pools(swings: list[Swing]) -> dict:
    highs = [s.price for s in swings if s.kind == "high"]
    lows = [s.price for s in swings if s.kind == "low"]
    return {"resistance": cluster_levels(highs), "support": cluster_levels(lows)}


def detect_sweep(candles: list[dict], pools: dict, direction: str, lookback: int = 10) -> Optional[dict]:
    """direction 'long' looks for a sweep of a support pool (wick below,
    close back above); 'short' looks for a sweep of resistance."""
    window = candles[-lookback:]
    targets = pools["support"] if direction == "long" else pools["resistance"]
    for level, touches in targets:
        for c in window:
            if direction == "long" and c["l"] < level and c["c"] > level:
                return {"level": level, "touches": touches, "candle": c}
            if direction == "short" and c["h"] > level and c["c"] < level:
                return {"level": level, "touches": touches, "candle": c}
    return None


def premium_discount_zone(candles: list[dict], lookback: int = 50) -> dict:
    window = candles[-lookback:]
    hi = max(c["h"] for c in window)
    lo = min(c["l"] for c in window)
    eq = (hi + lo) / 2
    price = candles[-1]["c"]
    zone = "premium" if price > eq else "discount"
    return {"high": hi, "low": lo, "eq": eq, "zone": zone}


def detect_mss(candles_exec: list[dict], direction: str, lookback: int = 30) -> Optional[dict]:
    """Market structure shift on the execution timeframe: a close beyond
    the most recent opposing swing point, confirming reversal intent after
    a sweep."""
    swings = find_swings(candles_exec[-lookback:], left=2, right=2)
    if not swings:
        return None
    last_close = candles_exec[-1]["c"]
    if direction == "long":
        recent_highs = [s for s in swings if s.kind == "high"]
        if not recent_highs:
            return None
        ref = recent_highs[-1]
        if last_close > ref.price:
            return {"confirm_price": ref.price, "index": ref.index}
    else:
        recent_lows = [s for s in swings if s.kind == "low"]
        if not recent_lows:
            return None
        ref = recent_lows[-1]
        if last_close < ref.price:
            return {"confirm_price": ref.price, "index": ref.index}
    return None


# --- CANDIDATE SETUPS ---

@dataclass
class Candidate:
    symbol: str
    direction: str          # "long" | "short"
    pathway: str            # "liquidity_reversal" | "trend_continuation" | "momentum_breakout"
    combo_name: str
    entry: float
    sl: float
    tp1: float
    tp2: float
    confluences: list[str] = field(default_factory=list)
    atr_val: float = 0.0
    # True when `entry` is a resting POI/zone price that price may not yet
    # have reached (e.g. a breaker-block mid), as opposed to a market-price
    # entry (last close) that's filled the instant the signal fires.
    resting_entry: bool = False

    def rr(self) -> float:
        risk = abs(self.entry - self.sl)
        reward = abs(self.tp2 - self.entry)
        return safe(reward / risk, 0.0) if risk else 0.0


def adaptive_sl_buffer(candles: list[dict], atr_val: float, vol_pctile: float,
                        lookback: int = 20) -> float:
    """Sizes the stop buffer from observed recent wick overshoot rather
    than a flat ATR fraction, widened in high-volatility regimes and
    capped so one abnormal spike can't blow out the risk budget."""
    window = candles[-lookback:]
    if len(window) < 5:
        base = atr_val * 0.35
    else:
        wicks = []
        for c in window:
            body_top, body_bot = max(c["o"], c["c"]), min(c["o"], c["c"])
            wicks.append(max(c["h"] - body_top, body_bot - c["l"]))
        avg_wick = sum(wicks) / len(wicks)
        base = max(atr_val * 0.3, avg_wick * 1.3)
    vol_scale = 1.0 + 0.5 * max(0.0, vol_pctile - 0.5)  # up to 1.25x when vol_pctile -> 1.0
    return min(base * vol_scale, atr_val * 1.1)


def clamp_candidate_to_market(cand: "Candidate", market_price: float) -> "Candidate":
    """Keeps entry from drifting too far from live price by parallel-
    shifting entry/SL/TP1/TP2, preserving R:R and structure exactly."""
    if market_price <= 0:
        return cand
    max_dist = min(cand.atr_val * POI_ATR_MULT.get(cand.combo_name, 0.65),
                    market_price * POI_MAX_PCT_OF_PRICE)
    dist = cand.entry - market_price
    if abs(dist) <= max_dist:
        return cand
    target_dist = max_dist if dist > 0 else -max_dist
    shift = target_dist - dist
    cand.entry += shift
    cand.sl += shift
    cand.tp1 += shift
    cand.tp2 += shift
    return cand


def volume_profile(candles: list[dict], bins: int = VOL_PROFILE_BINS) -> dict:
    """Session volume profile -> POC, value-area high/low, and VWAP.
    Buckets typical price by volume, takes the highest-volume bucket as
    POC, then expands outward until 70% of volume is enclosed."""
    hi = max(c["h"] for c in candles)
    lo = min(c["l"] for c in candles)
    if hi <= lo:
        return {"poc": hi, "vah": hi, "val": lo, "vwap": hi}
    step = (hi - lo) / bins
    buckets = [0.0] * bins
    for c in candles:
        idx = min(bins - 1, max(0, int((((c["h"] + c["l"] + c["c"]) / 3) - lo) / step)))
        buckets[idx] += c["v"]
    poc_idx = max(range(bins), key=lambda i: buckets[i])
    poc = lo + (poc_idx + 0.5) * step
    total = sum(buckets) or 1.0
    target = total * 0.70
    lo_i = hi_i = poc_idx
    acc = buckets[poc_idx]
    while acc < target and (lo_i > 0 or hi_i < bins - 1):
        expand_lo = buckets[lo_i - 1] if lo_i > 0 else -1
        expand_hi = buckets[hi_i + 1] if hi_i < bins - 1 else -1
        if expand_hi >= expand_lo:
            hi_i += 1
            acc += buckets[hi_i]
        else:
            lo_i -= 1
            acc += buckets[lo_i]
    vah, val = lo + (hi_i + 1) * step, lo + lo_i * step
    vwap_num = sum(((c["h"] + c["l"] + c["c"]) / 3) * c["v"] for c in candles)
    vwap_den = sum(c["v"] for c in candles) or 1.0
    return {"poc": poc, "vah": vah, "val": val, "vwap": vwap_num / vwap_den}


def _clip_tp_to_liquidity(entry: float, tp: float, direction: str, pools: dict,
                           vp: dict | None = None) -> float:
    targets = pools["resistance"] if direction == "long" else pools["support"]
    candidates = [lv for lv, _ in targets if (lv > entry if direction == "long" else lv < entry)]
    if vp:  # volume-profile value-area edges + POC
        candidates += [lv for lv in (vp["poc"], vp["vah"], vp["val"])
                       if (lv > entry if direction == "long" else lv < entry)]
    if not candidates:
        return tp
    nearest = min(candidates, key=lambda lv: abs(lv - tp))
    if abs(nearest - tp) / abs(tp - entry) < 0.4:  # only clip if reasonably close
        return nearest
    return tp


def build_pathway_liquidity_reversal(symbol: str, bundle: dict, combo_name: str,
                                      regime: RegimeVector, vp: dict) -> Optional[Candidate]:
    combo = COMBOS[combo_name]
    struct_candles = bundle[combo["struct"]]
    exec_candles = bundle[combo["exec"]]
    ind_struct = compute_indicators(struct_candles)
    atr_val = ind_struct["atr"][-1]

    swings = find_swings(struct_candles)
    pools = build_liquidity_pools(swings)
    pd_zone = premium_discount_zone(struct_candles)

    for direction in ("long", "short"):
        # reversal longs want discount, reversal shorts want premium
        if direction == "long" and pd_zone["zone"] != "discount":
            continue
        if direction == "short" and pd_zone["zone"] != "premium":
            continue
        sweep = detect_sweep(struct_candles, pools, direction)
        if not sweep:
            continue
        mss = detect_mss(exec_candles, direction)
        if not mss:
            continue

        obs = find_order_blocks(exec_candles, compute_indicators(exec_candles)["atr"])
        obs = mark_untested(obs, exec_candles)
        wanted_kind = "bullish_ob" if direction == "long" else "bearish_ob"
        breaker = next((z for z in reversed(obs) if z.kind == wanted_kind and z.untested), None)

        entry = breaker.mid() if breaker else exec_candles[-1]["c"]
        sl_buf = adaptive_sl_buffer(struct_candles, atr_val, regime.vol_pctile)
        if direction == "long":
            sl = min(sweep["candle"]["l"], (breaker.low if breaker else entry)) - sl_buf
            raw_tp1 = entry + (entry - sl) * 1.5
            raw_tp2 = entry + (entry - sl) * 2.8
        else:
            sl = max(sweep["candle"]["h"], (breaker.high if breaker else entry)) + sl_buf
            raw_tp1 = entry - (sl - entry) * 1.5
            raw_tp2 = entry - (sl - entry) * 2.8

        tp1 = _clip_tp_to_liquidity(entry, raw_tp1, direction, pools, vp)
        tp2 = _clip_tp_to_liquidity(entry, raw_tp2, direction, pools, vp)

        confluences = ["liquidity sweep", f"MSS confirmed ({combo['exec']})",
                       f"{pd_zone['zone']} zone"]
        if breaker:
            confluences.append("untested breaker block")
        if sweep["touches"] > 1:
            confluences.append(f"pool tapped {sweep['touches']}x prior")
        div = ind_struct.get("rsi_divergence", {"type": None})
        if (direction == "long" and div["type"] == "bullish") or \
           (direction == "short" and div["type"] == "bearish"):
            confluences.append(f"RSI {div['type']} divergence ({combo['struct']})")

        cand = Candidate(symbol, direction, "liquidity_reversal", combo_name,
                          entry, sl, tp1, tp2, confluences, atr_val,
                          resting_entry=(breaker is not None))
        if cand.rr() >= min_rr_for(combo_name, "liquidity_reversal"):
            return cand
    return None


def _rsi_reset(ind: dict, direction: str) -> bool:
    window = ind["rsi"][-RSI_RESET_LOOKBACK:]
    if direction == "long":
        dipped = min(window[:-1], default=100) <= RSI_DIP_LONG
        turning = window[-1] > RSI_TURN_LONG
        return dipped and turning
    dipped = max(window[:-1], default=0) >= RSI_DIP_SHORT
    turning = window[-1] < RSI_TURN_SHORT
    return dipped and turning


def build_pathway_trend_continuation(symbol: str, bundle: dict, combo_name: str,
                                      regime: RegimeVector, vp: dict) -> Optional[Candidate]:
    combo = COMBOS[combo_name]
    bias_candles = bundle[combo["bias"]]
    exec_candles = bundle[combo["exec"]]
    ind_bias = compute_indicators(bias_candles)
    ind_exec = compute_indicators(exec_candles)

    if ind_bias["adx"][-1] < TREND_ADX_MIN:
        return None

    price = ind_bias["closes"][-1]
    ef, es, et = ind_bias["ema_fast"][-1], ind_bias["ema_slow"][-1], ind_bias["ema_trend"][-1]
    # require full EMA20/50/200 stack aligned, not just a 20/50 cross
    if price > ef > es > et:
        direction = "long"
    elif price < ef < es < et:
        direction = "short"
    else:
        return None

    if not _rsi_reset(ind_exec, direction):
        return None

    atr_val = ind_exec["atr"][-1]
    entry = ind_exec["closes"][-1]
    swings = find_swings(exec_candles)
    pools = build_liquidity_pools(swings)

    if direction == "long":
        recent_low = min(c["l"] for c in exec_candles[-8:])
        sl = recent_low - adaptive_sl_buffer(exec_candles, atr_val, regime.vol_pctile)
        raw_tp1 = entry + (entry - sl) * 1.5
        raw_tp2 = entry + (entry - sl) * 2.5
    else:
        recent_high = max(c["h"] for c in exec_candles[-8:])
        sl = recent_high + adaptive_sl_buffer(exec_candles, atr_val, regime.vol_pctile)
        raw_tp1 = entry - (sl - entry) * 1.5
        raw_tp2 = entry - (sl - entry) * 2.5

    tp1 = _clip_tp_to_liquidity(entry, raw_tp1, direction, pools, vp)
    tp2 = _clip_tp_to_liquidity(entry, raw_tp2, direction, pools, vp)

    confluences = [
        f"{combo['bias']} trend intact (ADX {ind_bias['adx'][-1]:.0f})",
        "RSI pullback reset on exec tf",
        "price above/below EMA20/50 stack" if direction == "long" else "price below EMA20/50 stack",
    ]
    div = ind_exec.get("rsi_divergence", {"type": None})
    if (direction == "long" and div["type"] == "bullish") or \
       (direction == "short" and div["type"] == "bearish"):
        confluences.append(f"RSI {div['type']} divergence ({combo['exec']})")

    cand = Candidate(symbol, direction, "trend_continuation", combo_name,
                      entry, sl, tp1, tp2, confluences, atr_val)
    if cand.rr() >= min_rr_for(combo_name, "trend_continuation"):
        return cand
    return None


def build_pathway_momentum_breakout(symbol: str, bundle: dict, combo_name: str,
                                     regime: RegimeVector, vp: dict) -> Optional[Candidate]:
    combo = COMBOS[combo_name]
    struct_candles = bundle[combo["struct"]]
    ind = compute_indicators(struct_candles)

    bb_hist = ind["bb_width"][-60:]
    if len(bb_hist) < 20:
        return None
    current_bw = bb_hist[-1]
    sorted_bw = sorted(bb_hist)
    pctile = sum(1 for x in sorted_bw if x <= current_bw) / len(sorted_bw)
    if pctile > BREAKOUT_BB_SQUEEZE_PCTILE:
        return None  # not squeezed enough for a breakout setup

    last = struct_candles[-1]
    avg_vol = ind["vol_sma20"][-2] if len(ind["vol_sma20"]) > 1 else ind["vol_sma20"][-1]
    if avg_vol <= 0 or last["v"] < BREAKOUT_VOL_MULT * avg_vol:
        return None

    window = struct_candles[-BREAKOUT_LOOKBACK_HIGH_LOW - 1:-1]
    hi = max(c["h"] for c in window)
    lo = min(c["l"] for c in window)

    if last["c"] > hi:
        direction = "long"
    elif last["c"] < lo:
        direction = "short"
    else:
        return None

    atr_val = ind["atr"][-1]
    entry = last["c"]
    sl_buf = adaptive_sl_buffer(struct_candles, atr_val, regime.vol_pctile)
    if direction == "long":
        sl = lo - sl_buf
        raw_tp1 = entry + (entry - sl) * 1.4
        raw_tp2 = entry + (entry - sl) * 2.4
    else:
        sl = hi + sl_buf
        raw_tp1 = entry - (sl - entry) * 1.4
        raw_tp2 = entry - (sl - entry) * 2.4

    swings = find_swings(struct_candles)
    pools = build_liquidity_pools(swings)
    tp1 = _clip_tp_to_liquidity(entry, raw_tp1, direction, pools, vp)
    tp2 = _clip_tp_to_liquidity(entry, raw_tp2, direction, pools, vp)

    confluences = [
        f"bollinger squeeze (pctile {pctile:.2f}) resolving",
        f"volume {last['v'] / avg_vol:.1f}x 20-bar avg",
        f"range breakout ({combo['struct']})",
    ]
    div = ind.get("rsi_divergence", {"type": None})
    opposing = (direction == "long" and div["type"] == "bearish") or \
               (direction == "short" and div["type"] == "bullish")
    if opposing:
        # flag rather than block -- breakouts can still work on pure volume
        confluences.append(f"caution: opposing RSI {div['type']} divergence")
    elif (direction == "long" and div["type"] == "bullish") or \
         (direction == "short" and div["type"] == "bearish"):
        confluences.append(f"RSI {div['type']} divergence supports breakout")

    cand = Candidate(symbol, direction, "momentum_breakout", combo_name,
                      entry, sl, tp1, tp2, confluences, atr_val)
    if cand.rr() >= min_rr_for(combo_name, "momentum_breakout"):
        return cand
    return None


PATHWAYS = [
    build_pathway_liquidity_reversal,
    build_pathway_trend_continuation,
    build_pathway_momentum_breakout,
]


# --- SCORING ---

def logistic(x: float) -> float:
    try:
        return 1.0 / (1.0 + math.exp(-x))
    except OverflowError:
        return 0.0 if x < 0 else 1.0


def score_candidate(cand: Candidate, regime: RegimeVector, state: dict,
                     btc_bias: str, book: dict, vp: dict) -> float:
    z = 0.0
    caution_count = sum(1 for c in cand.confluences if c.startswith("caution:"))
    positive_count = len(cand.confluences) - caution_count
    z += 0.9 * (positive_count - 1.5)
    z -= 0.8 * caution_count
    z += 1.1 * (cand.rr() - min_rr_for(cand.combo_name, cand.pathway))
    z += 1.3 * (regime.composite_favorability() - 0.5)

    # BTC macro alignment bonus/penalty (majors and high-beta alts especially)
    if cand.symbol != "BTC":
        if (cand.direction == "long" and btc_bias == "bullish") or \
           (cand.direction == "short" and btc_bias == "bearish"):
            z += 0.5
        elif (cand.direction == "long" and btc_bias == "bearish") or \
             (cand.direction == "short" and btc_bias == "bullish"):
            z -= 0.7

    # Orderbook microstructure confirmation
    imbalance = book.get("imbalance", 0.0) or 0.0
    if cand.direction == "long":
        z += 0.6 * imbalance
    else:
        z -= 0.6 * imbalance

    # session VWAP alignment; asymmetric since it's a soft confluence
    if vp:
        vwap_aligned = (cand.entry >= vp["vwap"]) if cand.direction == "long" else (cand.entry <= vp["vwap"])
        z += 0.4 if vwap_aligned else -0.25

    # self-tuning pathway/symbol/combo weights, drifted by
    # tune_pathway_weights(), tune_symbol_weights(), and tune_combo_weights()
    # toward recent win-rate, shrunk toward 1.0
    pathway_weight = state["pathway_weights"].get(cand.pathway, 1.0)
    z += 2.8 * (pathway_weight - 1.0)

    symbol_weight = state.get("symbol_weights", {}).get(cand.symbol, 1.0)
    z += 2.2 * (symbol_weight - 1.0)

    combo_weight = state.get("combo_weights", {}).get(cand.combo_name, 1.0)
    z += 2.5 * (combo_weight - 1.0)

    confidence = 100 * logistic(z)
    return round(confidence, 2)


SYMBOL_WEIGHT_MIN, SYMBOL_WEIGHT_MAX = 0.70, 1.15
SYMBOL_WEIGHT_LEARNING_RATE = 0.05
SYMBOL_MIN_SAMPLE = 5

# --- Live-performance circuit breaker ---
CIRCUIT_BREAKER_WINDOW = 30            # rolling resolved trades considered
CIRCUIT_BREAKER_WIN_RATE_DROP = 0.20   # absolute win-rate drop vs baseline that trips it
CIRCUIT_BREAKER_PF_DROP_FRAC = 0.25    # relative profit-factor drop vs baseline that trips it
BASELINE_MIN_SAMPLE = 30               # resolved trades required before a baseline is trusted

def tune_symbol_weights(state: dict):
    """Same shrink-toward-neutral self-tuning as tune_pathway_weights(),
    but per-symbol, to catch symbol-specific edge decay that pathway-level
    weighting alone is too coarse for."""
    weights = state.setdefault("symbol_weights", {})
    history = state["signal_history"]
    by_symbol: dict[str, list[dict]] = {}
    for h in history:
        if h.get("result") in ("win", "loss"):
            by_symbol.setdefault(h["symbol"], []).append(h)
    for symbol, trades in by_symbol.items():
        if len(trades) < SYMBOL_MIN_SAMPLE:
            continue
        recent = trades[-20:]
        wr = sum(1 for h in recent if h["result"] == "win") / len(recent)
        avg_r = sum(h.get("r_realized", 0) for h in recent) / len(recent)
        # blend win-rate and realized R so small-wins/big-losses symbols
        # aren't scored the same as genuine edge
        target = 0.85 + 0.4 * wr + 0.15 * max(-1.0, min(1.0, avg_r))
        target = max(SYMBOL_WEIGHT_MIN, min(SYMBOL_WEIGHT_MAX, target))
        current = weights.get(symbol, 1.0)
        weights[symbol] = current + SYMBOL_WEIGHT_LEARNING_RATE * (target - current)
        weights[symbol] = max(SYMBOL_WEIGHT_MIN, min(SYMBOL_WEIGHT_MAX, weights[symbol]))


def _update_baseline(state: dict):
    """Establishes the pre-adaptation-freeze baseline from the first
    BASELINE_MIN_SAMPLE resolved trades, then stops updating. Mirrors Vantage
    Annex's approach: the baseline is a fixed reference point, not a moving
    target, so the circuit breaker measures live drift against a stable
    anchor rather than one that could itself decay alongside performance."""
    base = state["baseline"]
    if base["n"] >= BASELINE_MIN_SAMPLE:
        return
    resolved = [h for h in state["signal_history"] if h.get("result") in ("win", "loss")]
    if not resolved:
        return
    base["n"] = len(resolved)
    wins = sum(1 for h in resolved if h["result"] == "win")
    base["win_rate"] = wins / len(resolved)
    base["avg_rr"] = sum(h.get("r_realized", 0.0) for h in resolved) / len(resolved)
    gross_win = sum(h["r_realized"] for h in resolved if h["result"] == "win")
    gross_loss = abs(sum(h["r_realized"] for h in resolved if h["result"] == "loss"))
    base["profit_factor"] = (gross_win / gross_loss) if gross_loss > 1e-9 else None


def evaluate_circuit_breaker(state: dict) -> Optional[str]:
    """Live-performance circuit breaker, ported from Vantage Annex. Dual-metric
    trip (win rate OR profit factor drops materially below baseline) with a
    deliberately stricter AND recovery (both metrics must recover) so a single
    good trade after a bad stretch can't immediately re-enable adaptation.
    Freezes tune_pathway_weights / tune_symbol_weights / tune_combo_weights
    only -- signal generation and trade monitoring are unaffected."""
    _update_baseline(state)
    base = state["baseline"]
    cb = state["circuit_breaker"]
    resolved = [h for h in state["signal_history"] if h.get("result") in ("win", "loss")]
    recent = resolved[-CIRCUIT_BREAKER_WINDOW:]
    if base["win_rate"] is None or len(recent) < CIRCUIT_BREAKER_WINDOW:
        return None

    rolling_wr = sum(1 for h in recent if h["result"] == "win") / len(recent)
    gains = sum(h["r_realized"] for h in recent if h["r_realized"] > 0)
    losses = abs(sum(h["r_realized"] for h in recent if h["r_realized"] < 0)) or 1e-9
    rolling_pf = gains / losses

    wr_trip = base["win_rate"] - rolling_wr >= CIRCUIT_BREAKER_WIN_RATE_DROP
    pf_trip = (base["profit_factor"] is not None and
               rolling_pf <= base["profit_factor"] * (1 - CIRCUIT_BREAKER_PF_DROP_FRAC))
    materially_below = wr_trip or pf_trip

    if not cb["active"] and materially_below:
        cb["active"] = True
        cb["since"] = datetime.now(timezone.utc).isoformat()
        pf_txt = f"{base['profit_factor']:.2f}" if base["profit_factor"] is not None else "n/a"
        cb["reason"] = (f"win_rate={rolling_wr:.2%} (baseline {base['win_rate']:.2%}), "
                         f"pf={rolling_pf:.2f} (baseline {pf_txt})")
        send_telegram(
            f"\U0001F92F *AXIS ENGINE CIRCUIT BREAKER TRIPPED*\n"
            f"Rolling live performance deviated materially below baseline: {cb['reason']}.\n"
            f"Pathway/symbol/combo weight tuning is now FROZEN at last-known-good values. "
            f"Signal generation continues unaffected."
        )
        return "tripped"

    pf_recovered = base["profit_factor"] is None or rolling_pf >= base["profit_factor"]
    if cb["active"] and rolling_wr >= base["win_rate"] and pf_recovered:
        cb["active"] = False
        cb["since"] = None
        cb["reason"] = None
        send_telegram(
            "\u2705 *AXIS ENGINE circuit breaker cleared*\n"
            "Rolling live performance recovered to baseline. Weight tuning resumed."
        )
        return "recovered"
    return None


def tune_pathway_weights(state: dict):
    """Nudges each pathway's scoring multiplier toward its recent win-rate,
    shrunk toward the neutral prior (1.0) with tight bounds and a small
    step size so it drifts slowly rather than snapping to noise."""
    weights = state.setdefault("pathway_weights", {
        "liquidity_reversal": 1.0, "trend_continuation": 1.0, "momentum_breakout": 1.0,
    })
    history = state["signal_history"]
    for pathway in weights:
        relevant = [h for h in history if h.get("pathway") == pathway and h.get("result") in ("win", "loss")]
        if len(relevant) < 15:
            continue
        recent = relevant[-40:]
        wr = sum(1 for h in recent if h["result"] == "win") / len(recent)
        target = 0.85 + 0.5 * wr  # wr=0.5 -> 1.10 neutral-ish; wr=0.3 -> 1.0; wr=0.7 -> 1.20
        target = max(PATHWAY_WEIGHT_MIN, min(PATHWAY_WEIGHT_MAX, target))
        weights[pathway] += PATHWAY_WEIGHT_LEARNING_RATE * (target - weights[pathway])
        weights[pathway] = max(PATHWAY_WEIGHT_MIN, min(PATHWAY_WEIGHT_MAX, weights[pathway]))


COMBO_MIN_SAMPLE = 15

def tune_combo_weights(state: dict):
    """Same shrink-toward-neutral self-tuning as tune_pathway_weights(), but
    keyed on `combo` (scalp/intraday/swing) rather than pathway. Wired into
    score_candidate() alongside pathway/symbol weights so a structurally
    weaker combo -- e.g. intraday, and especially intraday+liquidity_
    reversal -- needs a higher confluence/RR bar to clear the acceptance
    threshold, without having to touch pathway-level weighting (which is
    shared across all three combos and would over- or under-correct the
    other two)."""
    weights = state.setdefault("combo_weights", {
        "scalp": 1.0, "intraday": 1.0, "swing": 1.0,
    })
    history = state["signal_history"]
    for combo_name in weights:
        relevant = [h for h in history if h.get("combo") == combo_name and h.get("result") in ("win", "loss")]
        if len(relevant) < COMBO_MIN_SAMPLE:
            continue
        recent = relevant[-40:]
        wr = sum(1 for h in recent if h["result"] == "win") / len(recent)
        target = 0.85 + 0.5 * wr  # same mapping as tune_pathway_weights: wr=0.5 -> 1.10, wr=0.3 -> 1.0, wr=0.7 -> 1.20
        target = max(COMBO_WEIGHT_MIN, min(COMBO_WEIGHT_MAX, target))
        weights[combo_name] += COMBO_WEIGHT_LEARNING_RATE * (target - weights[combo_name])
        weights[combo_name] = max(COMBO_WEIGHT_MIN, min(COMBO_WEIGHT_MAX, weights[combo_name]))


def grade_for_confidence(confidence: float) -> str:
    if confidence >= 82:
        return "A+"
    if confidence >= 72:
        return "A"
    if confidence >= 62:
        return "B"
    return "C"


def classify_duration(combo_name: str) -> str:
    return COMBOS[combo_name]["hold_hint"]


# --- CORRELATION CLUSTERING & DEDUPLICATION ---

def compute_returns(candles: list[dict], lookback: int) -> list[float]:
    closes = [c["c"] for c in candles[-lookback - 1:]]
    return [safe((closes[i] - closes[i - 1]) / closes[i - 1], 0.0) for i in range(1, len(closes))]


def pearson(a: list[float], b: list[float]) -> float:
    n = min(len(a), len(b))
    if n < 5:
        return 0.0
    a, b = a[-n:], b[-n:]
    try:
        return statistics.correlation(a, b)
    except (statistics.StatisticsError, ValueError):
        return 0.0


def build_correlation_clusters(bundles: dict[str, dict]) -> list[set[str]]:
    returns = {sym: compute_returns(b["1h"], CORR_LOOKBACK_BARS) for sym, b in bundles.items()}
    symbols = list(returns.keys())
    parent = {s: s for s in symbols}

    def find(x):
        while parent[x] != x:
            x = parent[x]
        return x

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb

    for i in range(len(symbols)):
        for j in range(i + 1, len(symbols)):
            s1, s2 = symbols[i], symbols[j]
            if pearson(returns[s1], returns[s2]) >= CORR_CLUSTER_THRESHOLD:
                union(s1, s2)

    clusters: dict[str, set] = {}
    for s in symbols:
        root = find(s)
        clusters.setdefault(root, set()).add(s)
    return list(clusters.values())


def dedup_correlated(ranked: list[dict], clusters: list[set[str]]) -> list[dict]:
    """Keeps at most one candidate per correlated cluster, regardless of
    direction, so two correlated symbols can't fire in opposite directions
    (the engine betting against itself on the same underlying move)."""
    def cluster_of(sym: str) -> frozenset:
        for c in clusters:
            if sym in c:
                return frozenset(c)
        return frozenset({sym})

    seen: dict[frozenset, dict] = {}
    for r in ranked:
        key = cluster_of(r["symbol"])
        if key not in seen or r["confidence"] > seen[key]["confidence"]:
            seen[key] = r
    return list(seen.values())


def conflicts_with_open_positions(state: dict, symbol: str, direction: str,
                                   clusters: list[set[str]]) -> bool:
    """Blocks a new candidate correlated with an already-open position in
    the opposite direction (dedup_correlated only compares same-scan
    candidates, so cross-scan conflicts need this separate check)."""
    def cluster_of(sym: str) -> frozenset:
        for c in clusters:
            if sym in c:
                return frozenset(c)
        return frozenset({sym})

    target_cluster = cluster_of(symbol)
    for sig in state.get("active_signals", []):
        if sig["symbol"] == symbol:
            continue  # same-symbol cap handled separately (MAX_CONCURRENT_PER_SYMBOL)
        if cluster_of(sig["symbol"]) == target_cluster and sig["direction"] != direction:
            return True
    return False


# --- HARD FILTERS, COOLDOWN, GOVERNOR ---

def passes_hard_filters(symbol: str, snapshot: dict, atr_pct: float, cand: Candidate) -> tuple[bool, str]:
    info = snapshot.get(symbol)
    if not info:
        return False, "no market snapshot"
    if info["oi_usd"] < MIN_OI_USD:
        return False, f"OI too low (${info['oi_usd']:,.0f})"
    if not (MIN_ATR_PCT <= atr_pct <= MAX_ATR_PCT):
        return False, f"ATR% out of band ({atr_pct:.4f})"
    req_rr = min_rr_for(cand.combo_name, cand.pathway)
    if cand.rr() < req_rr:
        return False, f"RR too low ({cand.rr():.2f} < {req_rr:.2f})"
    poi_mult = POI_ATR_MULT.get(cand.combo_name, 1.0)
    max_dist = min(cand.atr_val * poi_mult, cand.entry * POI_MAX_PCT_OF_PRICE)
    if abs(cand.entry - info["mark"]) > max_dist:
        return False, "entry too far from live price"
    return True, "ok"


def check_cooldown(state: dict, symbol: str, direction: str, bar_index: int) -> bool:
    key = f"{symbol}:{direction}"
    last = state["cooldowns"].get(key, -999)
    return (bar_index - last) >= COOLDOWN_BARS


def update_cooldown(state: dict, symbol: str, direction: str, bar_index: int):
    state["cooldowns"][f"{symbol}:{direction}"] = bar_index


def is_recent_duplicate(state: dict, symbol: str, direction: str, entry: float) -> bool:
    cutoff = time.time() - DEDUP_TIME_WINDOW_HOURS * 3600
    for h in state["signal_history"]:
        if h.get("symbol") != symbol or h.get("direction") != direction:
            continue
        if h.get("ts", 0) < cutoff:
            continue
        if abs(h.get("entry", 0) - entry) / entry <= DEDUP_PRICE_TOL_PCT:
            return True
    return False


def governor_adjust_threshold(state: dict, signals_fired_today_estimate: float):
    gov = state["governor"]
    now = time.time()
    gov["daily_count_ema"] = 0.9 * gov["daily_count_ema"] + 0.1 * signals_fired_today_estimate
    if now - gov.get("last_adjust_ts", 0) < GOVERNOR_MIN_INTERVAL_S:
        return
    ema_count = gov["daily_count_ema"]
    if ema_count < TARGET_SIGNALS_MIN:
        gov["threshold"] = max(GOVERNOR_FLOOR, gov["threshold"] - GOVERNOR_STEP)
        gov["last_adjust_ts"] = now
    elif ema_count > TARGET_SIGNALS_MAX:
        gov["threshold"] = min(GOVERNOR_CEIL, gov["threshold"] + GOVERNOR_STEP)
        gov["last_adjust_ts"] = now


def estimate_signals_last_24h(state: dict) -> int:
    cutoff = time.time() - 86400
    return sum(1 for h in state["signal_history"] if h.get("ts", 0) >= cutoff)


# --- TELEGRAM ---

_TG_MD_SPECIAL = re.compile(r"([_*`\[])")


def tg_escape(value) -> str:
    """Escape `_` `*` `` ` `` `[`, which carry special meaning in
    Telegram's legacy Markdown (V1) parse mode. Apply to any data-derived
    string before it's dropped into a message as plain text -- an
    unmatched `_` or `*` makes the whole send fail with HTTP 400. Don't
    use on text deliberately wrapped as an entity (e.g. `*bold*`); escape
    the contents, not the markers."""
    return _TG_MD_SPECIAL.sub(r"\\\1", str(value))


def fmt_px(v: float) -> str:
    if v >= 100:
        return f"{v:,.2f}"
    if v >= 1:
        return f"{v:,.4f}"
    return f"{v:.6f}"


def pathway_label(pathway: str) -> str:
    """Display-only label for a pathway name, e.g. "liquidity_reversal" ->
    "Liquidity Reversal". The underscored form (cand.pathway / sig["pathway"])
    stays as-is everywhere else -- it's used as a dict key for pathway
    weighting/stats, so only the Telegram-facing text is prettified here."""
    return pathway.replace("_", " ").title()


def confidence_bar(confidence: float) -> str:
    filled = round(confidence / 10)
    return "\u2588" * filled + "\u2591" * (10 - filled)


def format_signal(cand: Candidate, confidence: float, grade: str) -> str:
    arrow = "\U0001F7E2 LONG" if cand.direction == "long" else "\U0001F534 SHORT"
    duration = classify_duration(cand.combo_name)
    lines = [
        f"*AXIS ENGINE v3.3.3* -- {tg_escape(cand.symbol)}/USD",
        f"{arrow}  |  Grade *{grade}*  |  Pathway: `{pathway_label(cand.pathway)}`",
        "",
        f"Entry:  `{fmt_px(cand.entry)}`",
        f"SL:     `{fmt_px(cand.sl)}`",
        f"TP1:    `{fmt_px(cand.tp1)}`",
        f"TP2:    `{fmt_px(cand.tp2)}`",
        f"R:R (TP2): `{cand.rr():.2f}`",
        f"Confidence: {confidence:.1f}%  {confidence_bar(confidence)}",
        f"Est. hold: {tg_escape(duration)}",
        "",
        "Confluences:",
    ] + [f"  \u2022 {tg_escape(c)}" for c in cand.confluences]
    return "\n".join(lines)


def send_telegram(text: str) -> int | None:
    if not TG_BOT_TOKEN or not TG_CHAT_ID:
        log.info("Telegram not configured; signal:\n%s", text)
        return None
    url = f"https://api.telegram.org/bot{TG_BOT_TOKEN}/sendMessage"
    payload = json.dumps({
        "chat_id": TG_CHAT_ID, "text": text, "parse_mode": "Markdown",
    }).encode()
    req = urllib.request.Request(url, data=payload, headers={"Content-Type": "application/json"})
    try:
        with urllib.request.urlopen(req, timeout=10) as resp:
            data = json.loads(resp.read().decode())
            return data.get("result", {}).get("message_id")
    except (urllib.error.URLError, urllib.error.HTTPError, ValueError) as e:
        log.error("Telegram send failed: %s", e)
        return None


def reply_telegram(text: str, reply_to_message_id: int | None) -> int | None:
    """Sends a message as a threaded reply to the original signal post so
    TP/SL/close-out updates stay attached to their trade."""
    if not TG_BOT_TOKEN or not TG_CHAT_ID:
        log.info("Telegram not configured; update:\n%s", text)
        return None
    url = f"https://api.telegram.org/bot{TG_BOT_TOKEN}/sendMessage"
    payload = {"chat_id": TG_CHAT_ID, "text": text, "parse_mode": "Markdown"}
    if reply_to_message_id:
        payload["reply_to_message_id"] = reply_to_message_id
    req = urllib.request.Request(url, data=json.dumps(payload).encode(),
                                  headers={"Content-Type": "application/json"})
    try:
        with urllib.request.urlopen(req, timeout=10) as resp:
            data = json.loads(resp.read().decode())
            return data.get("result", {}).get("message_id")
    except (urllib.error.URLError, urllib.error.HTTPError, ValueError) as e:
        log.error("Telegram reply failed: %s", e)
        return None


def react_telegram(message_id: int | None, emoji: str) -> None:
    """Best-effort emoji reaction on the original signal message; failures
    are logged and swallowed."""
    if not TG_BOT_TOKEN or not TG_CHAT_ID or not message_id:
        return
    url = f"https://api.telegram.org/bot{TG_BOT_TOKEN}/setMessageReaction"
    payload = json.dumps({
        "chat_id": TG_CHAT_ID, "message_id": message_id,
        "reaction": [{"type": "emoji", "emoji": emoji}],
    }).encode()
    req = urllib.request.Request(url, data=payload, headers={"Content-Type": "application/json"})
    try:
        with urllib.request.urlopen(req, timeout=10):
            pass
    except (urllib.error.URLError, urllib.error.HTTPError, ValueError) as e:
        log.debug("Telegram reaction failed (non-fatal): %s", e)


# --- ACTIVE SIGNAL TRACKING / OUTCOME RESOLUTION ---

def record_signal(state: dict, cand: Candidate, confidence: float, grade: str,
                   bar_index: int, message_id: int | None) -> dict:
    entry = {
        "symbol": cand.symbol, "direction": cand.direction, "pathway": cand.pathway,
        "combo": cand.combo_name, "entry": cand.entry, "sl": cand.sl,
        "risk": abs(cand.entry - cand.sl), "tp1": cand.tp1, "tp2": cand.tp2,
        "confidence": confidence, "grade": grade, "ts": int(time.time()),
        "bar_index": bar_index, "result": "open", "tp1_hit": False,
        "message_id": message_id,
        # Watermark for intrabar SL/TP monitoring: the "t" (open time) of the
        # last closed 15m candle already checked against this signal. None
        # means "not checked yet" -- the first check falls back to the
        # signal's creation timestamp. This MUST be bar-aligned, not a
        # wall-clock timestamp -- see check_active_signals for why.
        "last_checked_bar_t": None,
        # Market-price entries (trend_continuation, momentum_breakout, and
        # liquidity_reversal's no-breaker fallback) are filled the instant
        # the signal fires. Resting POI/zone entries start unfilled and
        # must be confirmed to trade before SL/TP can be evaluated.
        "entry_filled": not cand.resting_entry,
        "bars_pending": 0,
    }
    state["active_signals"].append(entry)
    state["signal_history"].append(dict(entry))
    update_cooldown(state, cand.symbol, cand.direction, bar_index)
    return entry


def _r_multiple(sig: dict, price: float) -> float:
    risk = sig.get("risk") or abs(sig["entry"] - sig["sl"])
    if not risk:
        return 0.0
    raw = (price - sig["entry"]) if sig["direction"] == "long" else (sig["entry"] - price)
    return round(raw / risk, 2)


def _sync_history(state: dict, sig: dict):
    # Audited: every current call site sets sig["tp1_r"] BEFORE calling this
    # (see the TP1-hit branches in _check_signal_against_candle and
    # _check_active_signals_by_mark), so h.update(sig) always propagates a
    # populated tp1_r once TP1 has been banked. The tp1_r: null rows seen in
    # existing history predate that ordering and are backfilled once at
    # startup by reconcile_tp1_r() below rather than left stale.
    for h in state["signal_history"]:
        if h.get("ts") == sig.get("ts") and h.get("symbol") == sig.get("symbol") \
           and h.get("direction") == sig.get("direction"):
            h.update(sig)
            return


def reconcile_tp1_r(state: dict) -> int:
    """One-time-per-entry backfill for history rows where tp1_hit is True
    but tp1_r was never recorded. tp1_r is fully determined by the stored
    entry/risk/tp1 fields (it's the R-multiple of the TP1 price, independent
    of when/how the row was written), so it can be recomputed exactly rather
    than left null. Idempotent: only touches rows currently missing it."""
    fixed = 0
    for h in state["signal_history"]:
        if h.get("tp1_hit") and h.get("tp1_r") is None and h.get("tp1") is not None:
            h["tp1_r"] = _r_multiple(h, h["tp1"])
            fixed += 1
    if fixed:
        log.info("Reconciled tp1_r for %d historical signal(s) with tp1_hit=True but tp1_r=null.", fixed)
    return fixed


def _guard_sl_at_entry_post_tp1(sig: dict):
    """SL is intentionally never moved to entry after TP1 (see the note in
    _check_signal_against_candle) -- doing so previously caused an immediate
    stop-out on the very next check whenever price pulled back to entry
    after a partial TP, and legacy history rows where it happened were still
    counted as "win" despite having negative realized R. If SL is ever found
    equal to entry with TP1 already banked, that invariant has been broken
    somewhere -- log it loudly rather than let it silently resolve as a
    bogus win."""
    if sig.get("tp1_hit") and sig["sl"] == sig["entry"]:
        log.error(
            "BUG: SL == entry (%.6f) with TP1 already banked for %s %s (ts=%s) -- "
            "SL should never move to breakeven; investigate before trusting this record.",
            sig["sl"], sig["symbol"], sig["direction"], sig.get("ts"),
        )


def _notify_tp1(sig: dict, price: float):
    r = _r_multiple(sig, price)
    text = (f"\U0001F525 *TP1 hit* -- {tg_escape(sig['symbol'])} {tg_escape(sig['direction'].upper())}\n"
            f"Price: `{fmt_px(price)}`  |  +{r:.2f}R banked\n"
            f"SL stays at (`{fmt_px(sig['sl'])}`) for tracking -- unchanged.\n"
            f"\U0001F4A1 Optional: you can manually move your SL to entry "
            f"(`{fmt_px(sig['entry'])}`) to lock in breakeven.")
    reply_telegram(text, sig.get("message_id"))
    react_telegram(sig.get("message_id"), "\U0001F525")
    log.info("TP1 hit: %s %s +%.2fR, SL unchanged at %.6f", sig["symbol"], sig["direction"], r, sig["sl"])


def _close_out(state: dict, sig: dict, result: str, price: float,
                r_override: float | None = None, exit_note: str | None = None):
    if result == "win" and exit_note == "tp1":
        _guard_sl_at_entry_post_tp1(sig)
    r = r_override if r_override is not None else _r_multiple(sig, price)
    if result == "win" and r < 0:
        log.error(
            "BUG: resolving %s %s (ts=%s) as a WIN with negative r_realized (%.2fR) -- "
            "this should never happen; investigate before trusting this record.",
            sig["symbol"], sig["direction"], sig.get("ts"), r,
        )
    sig["result"] = result
    sig["exit_price"] = price
    sig["r_realized"] = r
    sig["closed_ts"] = int(time.time())
    _sync_history(state, sig)

    if result == "expired":
        headline = "\u23F3 *Entry never filled -- signal expired*"
        emoji = "\U0001F937"
    elif result == "win" and exit_note == "tp1":
        headline = "\u2705 *TP1 secured -- WIN*"
        emoji = "\U0001F44D"
    elif result == "win":
        headline = "\u2705 *TP2 hit -- WIN*"
        emoji = "\U0001F44D"
    else:
        headline = "\u274C *SL hit -- LOSS*"
        emoji = "\U0001F44E"

    if result == "expired":
        text = (f"{headline} -- {tg_escape(sig['symbol'])} {tg_escape(sig['direction'].upper())}\n"
                f"Price never traded through entry (`{fmt_px(sig['entry'])}`) within "
                f"{PENDING_ENTRY_EXPIRY_BARS} {MONITOR_TF} bars -- cancelled, no result.")
    elif exit_note == "tp1":
        text = (f"{headline} -- {tg_escape(sig['symbol'])} {tg_escape(sig['direction'].upper())}\n"
                f"SL hit at `{fmt_px(price)}` after TP1 was already banked -- Result: {r:+.2f}R")
    else:
        text = (f"{headline} -- {tg_escape(sig['symbol'])} {tg_escape(sig['direction'].upper())}\n"
                f"Exit: `{fmt_px(price)}`  |  Result: {r:+.2f}R")
    reply_telegram(text, sig.get("message_id"))
    react_telegram(sig.get("message_id"), emoji)
    log.info("Signal resolved: %s %s %s -> %s (%.2fR)",
              sig["symbol"], sig["direction"], sig["pathway"], result, r)


def _closed_15m_candles_for(symbol: str, bundles: dict, candle_cache: dict) -> list[dict]:
    """15m candles already fetched this scan as part of the symbol's
    bundle; falls back to the on-disk cache if this cycle's fetch failed."""
    bundle = bundles.get(symbol)
    if bundle and bundle.get("15m"):
        return bundle["15m"]
    cached = (candle_cache or {}).get(symbol, {}).get("15m")
    return cached or []


def _level_hit(candle: dict, level: float, direction: str, side: str) -> bool:
    """side='sl' tests the adverse extreme of the bar; side='tp' tests the
    favorable extreme. Tests the wick, not just close/mark."""
    if side == "sl":
        return candle["l"] <= level if direction == "long" else candle["h"] >= level
    return candle["h"] >= level if direction == "long" else candle["l"] <= level


def _entry_hit(candle: dict, entry: float) -> bool:
    """True if this candle's [low, high] range traded through `entry`,
    regardless of direction -- that's the only thing that matters for a
    resting order to fill."""
    return candle["l"] <= entry <= candle["h"]


def _check_signal_against_candle(state: dict, sig: dict, candle: dict) -> bool:
    """Tests one signal against one closed candle's high/low, checked in
    SL -> TP2 -> TP1 order (worst case first when a bar spans levels).

    Resting/POI entries (sig["entry_filled"] starts False) must first be
    confirmed to actually trade before SL/TP are evaluated against them --
    otherwise a zone entry price never reaches could be recorded as a win
    or loss it never actually took. Market-price entries start with
    entry_filled already True and skip straight to SL/TP checks below."""
    direction = sig["direction"]

    if not sig.get("entry_filled"):
        if not _entry_hit(candle, sig["entry"]):
            sig["bars_pending"] = sig.get("bars_pending", 0) + 1
            if sig["bars_pending"] >= PENDING_ENTRY_EXPIRY_BARS:
                _close_out(state, sig, "expired", sig["entry"], r_override=0.0)
                return True
            return False
        # Entry traded this candle: flip filled and fall through so this
        # same candle can still register a same-candle SL/TP hit.
        sig["entry_filled"] = True

    if _level_hit(candle, sig["sl"], direction, "sl"):
        if sig.get("tp1_hit"):
            _close_out(state, sig, "win", sig["sl"], r_override=sig.get("tp1_r"), exit_note="tp1")
        else:
            _close_out(state, sig, "loss", sig["sl"])
        return True
    if _level_hit(candle, sig["tp2"], direction, "tp"):
        _close_out(state, sig, "win", sig["tp2"])
        return True
    if not sig.get("tp1_hit") and _level_hit(candle, sig["tp1"], direction, "tp"):
        sig["tp1_hit"] = True
        sig["tp1_r"] = _r_multiple(sig, sig["tp1"])  # R banked at TP1, credited even if SL is hit later
        # SL intentionally left at its original level -- moving it to
        # breakeven caused an immediate stop-out on the very next check
        # whenever price pulled back to entry after a partial TP.
        _notify_tp1(sig, sig["tp1"])
        _sync_history(state, sig)
    return False


def _check_active_signals_by_mark(state: dict, sigs: list[dict], snapshot: dict, symbol: str) -> list[dict]:
    """Fallback for when no 15m candles are available at all (bundle fetch
    failed and nothing cached). Checks against live mark price; leaves
    last_checked_bar_t untouched so the gap backfills once candles return."""
    info = snapshot.get(symbol)
    if not info or not info.get("mark"):
        return list(sigs)
    price = info["mark"]
    remaining = []
    for sig in sigs:
        direction = sig["direction"]

        if not sig.get("entry_filled"):
            # Point-sample approximation of _entry_hit: since sl always sits
            # farther from market than entry for these setups, "reached
            # entry" means price has moved to at-or-past it on the sl side.
            reached_entry = (price <= sig["entry"]) if direction == "long" else (price >= sig["entry"])
            if not reached_entry:
                sig["bars_pending"] = sig.get("bars_pending", 0) + 1
                if sig["bars_pending"] >= PENDING_ENTRY_EXPIRY_BARS:
                    _close_out(state, sig, "expired", sig["entry"], r_override=0.0)
                    continue
                remaining.append(sig)
                continue
            sig["entry_filled"] = True

        hit_sl = (price <= sig["sl"]) if direction == "long" else (price >= sig["sl"])
        hit_tp2 = (price >= sig["tp2"]) if direction == "long" else (price <= sig["tp2"])
        hit_tp1 = (not sig.get("tp1_hit")) and (
            (price >= sig["tp1"]) if direction == "long" else (price <= sig["tp1"])
        )
        if hit_sl:
            if sig.get("tp1_hit"):
                _close_out(state, sig, "win", price, r_override=sig.get("tp1_r"), exit_note="tp1")
            else:
                _close_out(state, sig, "loss", price)
        elif hit_tp2:
            _close_out(state, sig, "win", price)
        else:
            if hit_tp1:
                sig["tp1_hit"] = True
                sig["tp1_r"] = _r_multiple(sig, price)
                # SL intentionally left at its original level -- see note
                # in _check_signal_against_candle.
                _notify_tp1(sig, price)
                _sync_history(state, sig)
            remaining.append(sig)
    return remaining


def check_active_signals(state: dict, snapshot: dict, bundles: dict, candle_cache: dict):
    """Monitors every open signal against closed 15m candle highs/lows
    since it was last checked, using candles already fetched this scan.

    The watermark used to find "new" bars MUST be bar-aligned (a candle
    "t"), not a wall-clock timestamp. The previous implementation stored
    last_checked_ms = time.time() at the end of every scan and then tested
    `candle["t"] >= last_checked_ms`. Since candle "t" values are quantized
    to 15m boundaries while last_checked_ms is real wall-clock time (always
    a little *after* the boundary, due to scan/fetch processing time), the
    freshly-closed candle's "t" is always strictly less than the watermark
    recorded at the end of the previous scan -- so it was silently excluded
    from `new_bars` every single time. In practice this meant only the very
    first check after a signal was recorded could ever see a candle; every
    check after that saw an empty new_bars list, so TP/SL hits were never
    detected and no Telegram reply was ever sent."""
    by_symbol: dict[str, list[dict]] = {}
    for sig in state["active_signals"]:
        by_symbol.setdefault(sig["symbol"], []).append(sig)
    if not by_symbol:
        return

    still_active = []
    for symbol, sigs in by_symbol.items():
        candles = _closed_15m_candles_for(symbol, bundles, candle_cache)
        if not candles:
            still_active.extend(_check_active_signals_by_mark(state, sigs, snapshot, symbol))
            continue

        open_sigs = list(sigs)
        closed_ids = set()
        for sig in open_sigs:
            last_bar_t = sig.get("last_checked_bar_t")
            if last_bar_t is None:
                # Not checked yet: include any closed candle from the
                # signal's creation time onward (inclusive).
                watermark = int(sig.get("ts", 0)) * 1000
                new_bars = [c for c in candles if c["t"] >= watermark]
            else:
                # Already checked up through last_bar_t: only bars that
                # opened strictly after it are "new".
                new_bars = [c for c in candles if c["t"] > last_bar_t]
            for candle in new_bars:
                if _check_signal_against_candle(state, sig, candle):
                    closed_ids.add(id(sig))
                    break
                sig["last_checked_bar_t"] = candle["t"]
            if id(sig) not in closed_ids and new_bars:
                sig["last_checked_bar_t"] = new_bars[-1]["t"]

        for sig in open_sigs:
            if id(sig) not in closed_ids:
                still_active.append(sig)

    state["active_signals"] = still_active


def generate_daily_summary(state: dict) -> str:
    cutoff = time.time() - 86400
    recent = [h for h in state["signal_history"] if h.get("ts", 0) >= cutoff]
    # "breakeven" was a legacy result value from a since-removed SL-to-
    # breakeven code path; nothing sets it anymore, so only win/loss count
    # as resolved here.
    closed = [h for h in recent if h.get("result") in ("win", "loss")]
    open_raw = [h for h in recent if h.get("result") == "open"]
    # A still-open trade that already banked TP1 counts as a win for summary
    # purposes -- R is provisional (tp1_r) and will be re-synced to the
    # final r_realized once the trade actually closes, so this can't
    # double-count across days.
    tp1_pending = [h for h in open_raw if h.get("tp1_hit")]
    open_now = [h for h in open_raw if not h.get("tp1_hit")]
    expired = [h for h in recent if h.get("result") == "expired"]

    resolved = closed + tp1_pending
    wins = [h for h in closed if h["result"] == "win"] + tp1_pending
    losses = [h for h in closed if h["result"] == "loss"]
    # win-rate/R stats intentionally exclude "expired" (never filled, so no
    # trade was ever actually taken) -- only win/loss/tp1-pending count here.
    total_r = sum(h.get("r_realized", 0.0) for h in closed) + sum(h.get("tp1_r", 0.0) for h in tp1_pending)
    win_rate = (len(wins) / len(resolved) * 100) if resolved else 0.0

    lines = [
        "\U0001F4CA *AXIS ENGINE -- 24h Summary*",
        "",
        f"Signals fired: {len(recent)}",
        f"Resolved: {len(resolved)}  (\u2705 {len(wins)}  |  \u274C {len(losses)})"
        + (f"  [{len(tp1_pending)} via TP1, still running]" if tp1_pending else ""),
        f"Still open (no TP1 yet): {len(open_now)}",
        f"Expired (never filled): {len(expired)}",
        f"Win rate: {win_rate:.1f}%",
        f"Net R: {total_r:+.2f}",
    ]
    cb = state["circuit_breaker"]
    lines.append(f"Circuit breaker: {'ACTIVE -- weight tuning frozen (' + str(cb['reason']) + ')' if cb['active'] else 'Inactive'}")
    if resolved:
        by_pathway: dict[str, list] = {}
        by_combo: dict[str, list] = {}
        for h in resolved:
            by_pathway.setdefault(h["pathway"], []).append(h)
            by_combo.setdefault(h.get("combo", "?"), []).append(h)
        lines.append("")
        lines.append("By pathway:")
        for pw, items in by_pathway.items():
            w = sum(1 for i in items if i["result"] == "win" or i in tp1_pending)
            lines.append(f"  \u2022 `{pathway_label(pw)}`: {w}/{len(items)} ({100*w/len(items):.0f}%)")
        lines.append("")
        lines.append("By combo:")
        for combo_name, items in by_combo.items():
            w = sum(1 for i in items if i["result"] == "win" or i in tp1_pending)
            lines.append(f"  \u2022 `{combo_name}`: {w}/{len(items)} ({100*w/len(items):.0f}%)")
    return "\n".join(lines)


DAILY_SUMMARY_UTC_HOUR = 8  # send once per day, only in the scan(s) that land in this UTC hour


def maybe_send_daily_summary(state: dict):
    now = time.gmtime()
    today_str = time.strftime("%Y-%m-%d", now)
    if now.tm_hour != DAILY_SUMMARY_UTC_HOUR:
        return
    if state.get("last_summary_date") == today_str:
        return  # already sent today (scan runs every 15min, so this hour fires 4x)
    summary = generate_daily_summary(state)
    send_telegram(summary)
    state["last_summary_date"] = today_str
    state["last_summary_ts"] = int(time.time())


# --- MAIN EVALUATION / SCAN ---

def evaluate_symbol(symbol: str, bundle: dict, state: dict, btc_bias: str, btc_strength: float,
                     breadth: float, snapshot: dict, threshold: float) -> Optional[dict]:
    """Pure evaluation: reads state but never writes it, so per-symbol
    fetch+scoring is safe to run concurrently. State mutation happens
    centrally in run_scan after this returns."""
    regime = build_regime_vector(state, symbol, bundle, btc_bias, btc_strength, breadth, COMBOS["intraday"])
    combo_name = select_combo(regime)
    local_threshold = adaptive_thresholds(regime, threshold, combo_name)
    combo = COMBOS[combo_name]

    bar_index = bundle[combo["exec"]][-1]["t"] // TF_MS[combo["exec"]]
    market_price = snapshot.get(symbol, {}).get("mark") or bundle[combo["exec"]][-1]["c"]
    vp = volume_profile(bundle["1h"][-VOL_PROFILE_LOOKBACK_BARS:])

    # fetched lazily since most symbols get filtered out before needing it
    book: dict | None = None

    best: Optional[tuple[Candidate, float, str]] = None
    for builder in PATHWAYS:
        cand = builder(symbol, bundle, combo_name, regime, vp)
        if cand is None:
            continue
        cand = clamp_candidate_to_market(cand, market_price)
        if not check_cooldown(state, symbol, cand.direction, bar_index):
            continue
        if is_recent_duplicate(state, symbol, cand.direction, cand.entry):
            continue
        atr_pct = safe(cand.atr_val / cand.entry, 0.0)
        ok, reason = passes_hard_filters(symbol, snapshot, atr_pct, cand)
        if not ok:
            log.debug("%s %s filtered: %s", symbol, cand.pathway, reason)
            continue
        if book is None:
            book = analyze_orderbook(symbol)
        confidence = score_candidate(cand, regime, state, btc_bias, book, vp)
        if confidence < local_threshold:
            continue
        grade = grade_for_confidence(confidence)
        if best is None or confidence > best[1]:
            best = (cand, confidence, grade)

    if best is None:
        return None
    cand, confidence, grade = best
    return {"cand": cand, "confidence": confidence, "grade": grade, "bar_index": bar_index}


def count_open_same_direction(state: dict, direction: str) -> int:
    return sum(1 for s in state["active_signals"] if s["direction"] == direction)


def count_open_for_symbol(state: dict, symbol: str) -> int:
    return sum(1 for s in state["active_signals"] if s["symbol"] == symbol)


def _prefetch(symbol: str, candle_cache: dict[str, dict]) -> tuple[str, dict | None]:
    # safe without a lock: each thread only touches its own symbol's key
    return symbol, fetch_all_candles(symbol, candle_cache)


def run_scan():
    log.info("=== AXIS ENGINE v3.3.3 scan starting ===")
    t_start = time.monotonic()
    state = load_state()
    reconcile_tp1_r(state)
    candle_cache = load_candle_cache()
    snapshot = get_market_snapshot()

    symbols_to_fetch = ["BTC"] + [s for s in WATCHLIST if s != "BTC"]
    bundles: dict[str, dict] = {}
    with ThreadPoolExecutor(max_workers=FETCH_THREAD_WORKERS) as pool:
        futures = {pool.submit(_prefetch, sym, candle_cache): sym for sym in symbols_to_fetch}
        for fut in as_completed(futures):
            sym, bundle = fut.result()
            if bundle:
                bundles[sym] = bundle
            else:
                log.info("No candle bundle for %s this scan.", sym)
    save_candle_cache(candle_cache)
    log.info("Prefetched %d/%d symbol bundles in %.1fs",
              len(bundles), len(symbols_to_fetch), time.monotonic() - t_start)

    # reuses the 15m candles already fetched above; no extra request needed
    check_active_signals(state, snapshot, bundles, candle_cache)
    evaluate_circuit_breaker(state)

    btc_bundle = bundles.get("BTC")
    if not btc_bundle:
        log.error("Could not fetch BTC bundle; aborting scan.")
        save_state(state)
        return
    btc_bias, btc_strength = compute_btc_regime(btc_bundle)
    breadth = compute_breadth(bundles, btc_bias)
    log.info("BTC regime: %s (ADX %.1f) | breadth %.0f%%", btc_bias, btc_strength, breadth * 100)

    if not state["circuit_breaker"]["active"]:
        tune_pathway_weights(state)
        tune_symbol_weights(state)
        tune_combo_weights(state)
    else:
        log.info("Circuit breaker active (%s) -- skipping weight tuning this scan.",
                  state["circuit_breaker"]["reason"])

    fired = []
    threshold = state["governor"]["threshold"]

    for symbol in WATCHLIST:
        if symbol not in bundles:
            continue
        if count_open_for_symbol(state, symbol) >= MAX_CONCURRENT_PER_SYMBOL:
            continue
        try:
            result = evaluate_symbol(symbol, bundles[symbol], state, btc_bias,
                                      btc_strength, breadth, snapshot, threshold)
        except Exception as e:
            log.exception("Error evaluating %s: %s", symbol, e)
            continue
        if result:
            fired.append(result)

    # clusters cover the full watchlist bundle set so open positions that
    # didn't fire this scan are still covered by the cross-scan check below
    clusters = build_correlation_clusters(bundles) if bundles else []
    if len(fired) > 1:
        ranked = [{"symbol": r["cand"].symbol, "direction": r["cand"].direction,
                   "confidence": r["confidence"], "ref": r} for r in fired]
        kept = dedup_correlated(ranked, clusters)
        kept_ids = {id(k["ref"]) for k in kept}
        fired = [r for r in fired if id(r) in kept_ids]

    # blocks candidates correlated with an already-open position from a
    # prior scan; dedup_correlated above only compares same-scan candidates
    still_fired = []
    for r in fired:
        if conflicts_with_open_positions(state, r["cand"].symbol, r["cand"].direction, clusters):
            log.info("Skipping %s %s: correlated with an open position in the opposite direction",
                      r["cand"].symbol, r["cand"].direction)
            continue
        still_fired.append(r)
    fired = still_fired

    sent = 0
    for r in fired:
        direction = r["cand"].direction
        if count_open_same_direction(state, direction) >= MAX_CONCURRENT_SAME_DIRECTION:
            log.info("Skipping %s: same-direction cap reached", r["cand"].symbol)
            continue
        text = format_signal(r["cand"], r["confidence"], r["grade"])
        message_id = send_telegram(text)
        record_signal(state, r["cand"], r["confidence"], r["grade"], r["bar_index"], message_id)
        sent += 1
        log.info("Signal fired: %s %s (%s) conf=%.1f grade=%s",
                  r["cand"].symbol, r["cand"].direction, r["cand"].pathway,
                  r["confidence"], r["grade"])

    maybe_send_daily_summary(state)
    governor_adjust_threshold(state, estimate_signals_last_24h(state))
    prune_state(state)
    save_state(state)
    log.info("=== Scan complete: %d signal(s) fired, threshold now %.1f, took %.1fs ===",
              sent, state["governor"]["threshold"], time.monotonic() - t_start)


def _acquire_run_lock():
    """Prevents two overlapping invocations from scanning concurrently: if
    the scheduler fires again before a slow prior run has saved state,
    both processes could see "no active signal" for the same symbol and
    each fire one, possibly in opposite directions. A non-blocking flock
    makes the second process exit immediately instead of racing the first."""
    lock_file = open(LOCK_PATH, "w")
    try:
        fcntl.flock(lock_file, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        log.warning("Another scan is already running (lock held on %s); skipping this run.", LOCK_PATH)
        lock_file.close()
        return None
    lock_file.write(str(os.getpid()))
    lock_file.flush()
    return lock_file  # caller must keep this open for the life of the process


def _release_run_lock(lock_file):
    if lock_file is None:
        return
    try:
        fcntl.flock(lock_file, fcntl.LOCK_UN)
    except OSError:
        pass
    lock_file.close()


def main():
    lock_file = _acquire_run_lock()
    if lock_file is None:
        return
    try:
        run_scan()
    except Exception as e:
        log.exception("Fatal error during scan: %s", e)
        raise SystemExit(1)
    finally:
        _release_run_lock(lock_file)


if __name__ == "__main__":
    main()
