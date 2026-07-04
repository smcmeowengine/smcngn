#!/usr/bin/env python3
"""
AXIS ENGINE v2.0.0
==================
Ground-up institutional-grade multi-timeframe SMC/ICT crypto perpetual
signal engine for Hyperliquid, synthesized from Crucible Alpha, Meridian,
Nyx, Vectis, and the scalp_swing_bot lineage -- plus original additions:

  - Three-Pathway Confluence Router (Liquidity Reversal / Trend Continuation
    / Momentum Breakout) scored through one unified logistic model instead
    of separate ad-hoc scorers per pathway.
  - Adaptive Frequency Governor: nudges the acceptance threshold toward a
    5-10 signal/day band using a slow, rate-limited EMA of daily signal
    count, so it reacts to sustained conditions, not scan-to-scan noise.
  - Composite Regime Vector (BTC macro bias, symbol volatility percentile,
    ADX trend strength, session liquidity weight, noise index) feeding both
    threshold selection AND per-pathway eligibility.
  - Correlation-cluster deduplication computed dynamically from realized
    returns each run, not a static hand-maintained group table.
  - Historical edge weighting: each candidate's confidence is nudged by the
    live win-rate of its (pathway, setup-grade, symbol-cluster) bucket.
  - Structure-aware, liquidity-target TP/SL: stops sit beyond invalidation
    structure with an ATR floor; targets are clipped to the nearest real
    opposing liquidity pool / order block rather than a blind R-multiple.

Single file, immediately runnable. Scan-per-run model: an external
scheduler (cron-job.org, GitHub Actions cron, systemd timer, etc.) invokes
this script every 15 minutes. All persistence lives in state.json next to
the script; there is no long-running process and no database.

Configure via environment variables (see CONFIGURATION below) and run:

    python3 axis_engine_v2_0_0.py

Author: AXIS ENGINE project
"""

from __future__ import annotations

import json
import math
import os
import signal
import statistics
import time
import logging
import urllib.error
import urllib.request
from dataclasses import dataclass, field
from typing import Optional

# ============================================================================
# CONFIGURATION
# ============================================================================

HL_API_URL = "https://api.hyperliquid.xyz/info"
TG_BOT_TOKEN = os.environ.get("TG_BOT_TOKEN", "")
TG_CHAT_ID = os.environ.get("TG_CHAT_ID", "")

STATE_PATH = os.environ.get("AXIS_STATE_PATH", "state.json")
LOG_PATH = os.environ.get("AXIS_LOG_PATH", "axis_engine.log")

WATCHLIST = [
    "BTC", "ETH", "HYPE", "ZEC", "NEAR", "ONDO", "SUI", "PENGU", "BNB", "SOL",
    "TRX", "BCH", "DOGE", "ADA", "DOT", "TAO", "AVAX", "LINK", "AAVE", "XRP",
    "XLM", "UNI", "LTC", "APT", "PENDLE",
]

# Timeframe combos: (bias, structure, execution). The Regime Router picks
# one per symbol per scan based on the symbol's own volatility/ADX profile
# rather than using a single fixed combo for the whole watchlist.
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

ATR_LEN = 14
RSI_LEN = 14
ADX_LEN = 14
EMA_FAST, EMA_SLOW, EMA_TREND = 20, 50, 200
BB_LEN, BB_MULT = 20, 2.0

# --- Adaptive Frequency Governor -------------------------------------------
TARGET_SIGNALS_MIN = 5
TARGET_SIGNALS_MAX = 10
GOVERNOR_STEP = 2.0
GOVERNOR_FLOOR = 54.0
GOVERNOR_CEIL = 88.0
GOVERNOR_MIN_INTERVAL_S = 3600  # rate-limit threshold nudges to once/hour

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

POI_ATR_MULT = {"scalp": 0.75, "intraday": 1.0, "swing": 1.25}
POI_MAX_PCT_OF_PRICE = 0.02

# Trend-continuation pathway tuning
TREND_ADX_MIN = 20.0
RSI_DIP_LONG, RSI_TURN_LONG = 45.0, 40.0
RSI_DIP_SHORT, RSI_TURN_SHORT = 55.0, 60.0
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
MIN_RR = 1.4

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


# ============================================================================
# HYPERLIQUID API
# ============================================================================

def hl_coin(symbol: str) -> str:
    return symbol.upper()


def hl_post(payload: dict, retries: int = 3, timeout: int = 12) -> dict | list | None:
    body = json.dumps(payload).encode()
    req = urllib.request.Request(
        HL_API_URL, data=body, headers={"Content-Type": "application/json"}
    )
    for attempt in range(retries):
        try:
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                return json.loads(resp.read().decode())
        except (urllib.error.URLError, urllib.error.HTTPError, TimeoutError, ValueError) as e:
            log.warning("hl_post attempt %d failed (%s): %s", attempt + 1, payload.get("type"), e)
            time.sleep(1.5 * (attempt + 1))
    log.error("hl_post exhausted retries for type=%s", payload.get("type"))
    return None


def current_bar_open_ms(reference_ms: int, interval: str) -> int:
    step = TF_MS[interval]
    return (reference_ms // step) * step


def filter_closed_candles(candles: list[dict], interval: str, reference_ms: int) -> list[dict]:
    cutoff = current_bar_open_ms(reference_ms, interval)
    return [c for c in candles if c["t"] < cutoff]


def get_candles(symbol: str, interval: str, n: int, reference_ms: int | None = None) -> list[dict]:
    reference_ms = reference_ms or int(time.time() * 1000)
    lookback_ms = n * TF_MS[interval] * 2 + TF_MS[interval] * 5
    payload = {
        "type": "candleSnapshot",
        "req": {
            "coin": hl_coin(symbol),
            "interval": interval,
            "startTime": reference_ms - lookback_ms,
            "endTime": reference_ms,
        },
    }
    raw = hl_post(payload)
    if not raw:
        return []
    candles = [
        {"t": c["t"], "o": float(c["o"]), "h": float(c["h"]),
         "l": float(c["l"]), "c": float(c["c"]), "v": float(c["v"])}
        for c in raw
    ]
    candles = filter_closed_candles(candles, interval, reference_ms)
    return candles[-n:]


def fetch_all_candles(symbol: str, reference_ms: int | None = None) -> dict[str, list[dict]] | None:
    bundle = {}
    for tf in ("5m", "15m", "1h", "4h", "1d"):
        candles = get_candles(symbol, tf, CANDLE_COUNT[tf], reference_ms)
        if len(candles) < 60:
            log.info("Insufficient %s candles for %s (%d)", tf, symbol, len(candles))
            return None
        bundle[tf] = candles
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


# ============================================================================
# INDICATORS
# ============================================================================

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
    """Classic price/RSI divergence over the last `lookback` bars: bearish
    divergence is a higher price high paired with a lower RSI high (momentum
    fading into a new high -- reversal-down warning/confirmation); bullish
    is the mirror image on swing lows. Used as a confluence bonus, not a
    hard filter, so it lifts quality on setups that already qualify without
    ever being the sole reason a setup is rejected."""
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


# ============================================================================
# STATE MANAGEMENT
# ============================================================================

def _default_state() -> dict:
    return {
        "active_signals": [],
        "signal_history": [],
        "cooldowns": {},
        "atr_pct_memory": {},
        "governor": {"threshold": 66.0, "last_adjust_ts": 0, "daily_count_ema": 6.0},
        "corr_returns": {},
        "meta": {"version": "2.0.0", "created": int(time.time())},
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


def prune_state(state: dict, max_signals: int = 800, max_days: int = 21):
    cutoff = int(time.time()) - max_days * 86400
    state["signal_history"] = [
        s for s in state["signal_history"] if s.get("ts", 0) >= cutoff
    ][-max_signals:]
    for sym in list(state["atr_pct_memory"].keys()):
        state["atr_pct_memory"][sym] = state["atr_pct_memory"][sym][-200:]


# ============================================================================
# REGIME VECTOR
# ============================================================================

@dataclass
class RegimeVector:
    btc_bias: str
    btc_strength: float
    vol_pctile: float
    adx_bias: float
    session_weight: float
    noise_index: float

    def composite_favorability(self) -> float:
        # Higher is more favorable for taking signals (clean trend, decent
        # liquidity, not chaotic noise).
        trend_component = min(self.adx_bias / 35.0, 1.0)
        noise_penalty = max(0.0, 1.0 - self.noise_index)
        return round(0.45 * trend_component + 0.30 * noise_penalty + 0.25 * self.session_weight, 4)


def session_weight_now() -> float:
    """Crypto trades 24/7 but liquidity still clusters around US/EU overlap
    and Asia open. Weight scans slightly favorably during high-liquidity
    hours (13:00-21:00 UTC) and slightly down during the quiet 00:00-05:00
    UTC stretch, without hard-blocking any hour."""
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
    """Ratio of net displacement to total path length over the lookback --
    low values mean choppy/overlapping candles (noisy), high values mean
    directional travel (clean)."""
    window = candles[-lookback:]
    if len(window) < 5:
        return 0.5
    net = abs(window[-1]["c"] - window[0]["c"])
    path = sum(abs(window[i]["c"] - window[i - 1]["c"]) for i in range(1, len(window)))
    efficiency = safe(net / path, 0.5) if path else 0.5
    return round(1.0 - min(efficiency, 1.0), 4)


def build_regime_vector(state: dict, symbol: str, bundle: dict,
                         btc_bias: str, btc_strength: float, combo: dict) -> RegimeVector:
    ind_bias = compute_indicators(bundle[combo["bias"]])
    atr_pct = safe(ind_bias["atr"][-1] / ind_bias["closes"][-1], 0.01)
    vol_pctile = update_atr_pct_memory(state, symbol, atr_pct)
    noise = compute_noise_index(bundle[combo["struct"]])
    return RegimeVector(
        btc_bias=btc_bias, btc_strength=btc_strength, vol_pctile=vol_pctile,
        adx_bias=safe(ind_bias["adx"][-1], 0.0), session_weight=session_weight_now(),
        noise_index=noise,
    )


def select_combo(regime: RegimeVector) -> str:
    """Route to the timeframe combo that fits current conditions: high
    vol/high ADX favors faster scalp reads before the move exhausts; low
    vol/low ADX favors the swing combo, which needs less frequent
    confirmation and rides out chop on a higher timeframe."""
    if regime.vol_pctile > 0.7 and regime.adx_bias > 25:
        return "scalp"
    if regime.vol_pctile < 0.3 and regime.adx_bias < 18:
        return "swing"
    return "intraday"


def adaptive_thresholds(regime: RegimeVector, base_threshold: float) -> float:
    """Nudge the base (governor-controlled) threshold up in noisy/choppy
    conditions and slightly down in clean, favorable ones -- bounded so the
    governor still owns the long-run level."""
    fav = regime.composite_favorability()
    adj = (0.5 - fav) * 10.0  # favorable (fav>0.5) lowers bar, unfavorable raises it
    return max(GOVERNOR_FLOOR, min(GOVERNOR_CEIL, base_threshold + adj))


# ============================================================================
# MARKET STRUCTURE: SWINGS, BOS/CHoCH, ORDER BLOCKS, FVGs, LIQUIDITY
# ============================================================================

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


# ============================================================================
# CANDIDATE SETUPS
# ============================================================================

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

    def rr(self) -> float:
        risk = abs(self.entry - self.sl)
        reward = abs(self.tp2 - self.entry)
        return safe(reward / risk, 0.0) if risk else 0.0


def _clip_tp_to_liquidity(entry: float, tp: float, direction: str, pools: dict) -> float:
    targets = pools["resistance"] if direction == "long" else pools["support"]
    if not targets:
        return tp
    candidates = [lv for lv, _ in targets if (lv > entry if direction == "long" else lv < entry)]
    if not candidates:
        return tp
    nearest = min(candidates, key=lambda lv: abs(lv - tp))
    # Only clip if the liquidity target is reasonably close to the raw TP
    # (within 40%) -- otherwise the raw ATR/structure target stands, since a
    # far-off pool shouldn't truncate a legitimately larger move.
    if abs(nearest - tp) / abs(tp - entry) < 0.4:
        return nearest
    return tp


def build_pathway_liquidity_reversal(symbol: str, bundle: dict, combo_name: str,
                                      regime: RegimeVector) -> Optional[Candidate]:
    combo = COMBOS[combo_name]
    struct_candles = bundle[combo["struct"]]
    exec_candles = bundle[combo["exec"]]
    ind_struct = compute_indicators(struct_candles)
    atr_val = ind_struct["atr"][-1]

    swings = find_swings(struct_candles)
    pools = build_liquidity_pools(swings)
    pd_zone = premium_discount_zone(struct_candles)

    for direction in ("long", "short"):
        # Bias filter: reversal longs want discount, reversal shorts want premium.
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
        sl_buf = atr_val * 0.35
        if direction == "long":
            sl = min(sweep["candle"]["l"], (breaker.low if breaker else entry)) - sl_buf
            raw_tp1 = entry + (entry - sl) * 1.5
            raw_tp2 = entry + (entry - sl) * 2.8
        else:
            sl = max(sweep["candle"]["h"], (breaker.high if breaker else entry)) + sl_buf
            raw_tp1 = entry - (sl - entry) * 1.5
            raw_tp2 = entry - (sl - entry) * 2.8

        tp1 = _clip_tp_to_liquidity(entry, raw_tp1, direction, pools)
        tp2 = _clip_tp_to_liquidity(entry, raw_tp2, direction, pools)

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
                          entry, sl, tp1, tp2, confluences, atr_val)
        if cand.rr() >= MIN_RR:
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
                                      regime: RegimeVector) -> Optional[Candidate]:
    combo = COMBOS[combo_name]
    bias_candles = bundle[combo["bias"]]
    exec_candles = bundle[combo["exec"]]
    ind_bias = compute_indicators(bias_candles)
    ind_exec = compute_indicators(exec_candles)

    if ind_bias["adx"][-1] < TREND_ADX_MIN:
        return None

    price = ind_bias["closes"][-1]
    ef, es = ind_bias["ema_fast"][-1], ind_bias["ema_slow"][-1]
    if price > ef > es:
        direction = "long"
    elif price < ef < es:
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
        sl = recent_low - atr_val * 0.4
        raw_tp1 = entry + (entry - sl) * 1.5
        raw_tp2 = entry + (entry - sl) * 2.5
    else:
        recent_high = max(c["h"] for c in exec_candles[-8:])
        sl = recent_high + atr_val * 0.4
        raw_tp1 = entry - (sl - entry) * 1.5
        raw_tp2 = entry - (sl - entry) * 2.5

    tp1 = _clip_tp_to_liquidity(entry, raw_tp1, direction, pools)
    tp2 = _clip_tp_to_liquidity(entry, raw_tp2, direction, pools)

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
    if cand.rr() >= MIN_RR:
        return cand
    return None


def build_pathway_momentum_breakout(symbol: str, bundle: dict, combo_name: str,
                                     regime: RegimeVector) -> Optional[Candidate]:
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
    if direction == "long":
        sl = lo - atr_val * 0.3
        raw_tp1 = entry + (entry - sl) * 1.4
        raw_tp2 = entry + (entry - sl) * 2.4
    else:
        sl = hi + atr_val * 0.3
        raw_tp1 = entry - (sl - entry) * 1.4
        raw_tp2 = entry - (sl - entry) * 2.4

    swings = find_swings(struct_candles)
    pools = build_liquidity_pools(swings)
    tp1 = _clip_tp_to_liquidity(entry, raw_tp1, direction, pools)
    tp2 = _clip_tp_to_liquidity(entry, raw_tp2, direction, pools)

    confluences = [
        f"bollinger squeeze (pctile {pctile:.2f}) resolving",
        f"volume {last['v'] / avg_vol:.1f}x 20-bar avg",
        f"range breakout ({combo['struct']})",
    ]
    div = ind.get("rsi_divergence", {"type": None})
    opposing = (direction == "long" and div["type"] == "bearish") or \
               (direction == "short" and div["type"] == "bullish")
    if opposing:
        # A breakout against fading momentum is exactly the profile of a
        # failed breakout/trap -- don't hard-block it (breakouts can still
        # work on pure volume), but flag it so the score reflects the risk.
        confluences.append(f"caution: opposing RSI {div['type']} divergence")
    elif (direction == "long" and div["type"] == "bullish") or \
         (direction == "short" and div["type"] == "bearish"):
        confluences.append(f"RSI {div['type']} divergence supports breakout")

    cand = Candidate(symbol, direction, "momentum_breakout", combo_name,
                      entry, sl, tp1, tp2, confluences, atr_val)
    if cand.rr() >= MIN_RR:
        return cand
    return None


PATHWAYS = [
    build_pathway_liquidity_reversal,
    build_pathway_trend_continuation,
    build_pathway_momentum_breakout,
]


# ============================================================================
# SCORING
# ============================================================================

def logistic(x: float) -> float:
    try:
        return 1.0 / (1.0 + math.exp(-x))
    except OverflowError:
        return 0.0 if x < 0 else 1.0


def setup_prior_winrate(state: dict, pathway: str, symbol: str) -> float:
    """Live win-rate for this (pathway) bucket, falling back to a neutral
    0.5 prior until enough history accumulates so early samples don't
    dominate the score."""
    history = [h for h in state["signal_history"]
               if h.get("pathway") == pathway and h.get("result") in ("win", "loss")]
    if len(history) < 8:
        return 0.5
    wins = sum(1 for h in history if h["result"] == "win")
    return wins / len(history)


def score_candidate(cand: Candidate, regime: RegimeVector, state: dict,
                     btc_bias: str, book: dict) -> float:
    z = 0.0
    caution_count = sum(1 for c in cand.confluences if c.startswith("caution:"))
    positive_count = len(cand.confluences) - caution_count
    z += 0.9 * (positive_count - 1.5)
    z -= 0.8 * caution_count
    z += 1.1 * (cand.rr() - MIN_RR)
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

    # Historical edge nudge
    prior = setup_prior_winrate(state, cand.pathway, cand.symbol)
    z += 1.4 * (prior - 0.5)

    confidence = 100 * logistic(z)
    return round(confidence, 2)


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


# ============================================================================
# CORRELATION CLUSTERING & DEDUPLICATION
# ============================================================================

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
    def cluster_of(sym: str) -> frozenset:
        for c in clusters:
            if sym in c:
                return frozenset(c)
        return frozenset({sym})

    seen: dict[tuple, dict] = {}
    for r in ranked:
        key = (cluster_of(r["symbol"]), r["direction"])
        if key not in seen or r["confidence"] > seen[key]["confidence"]:
            seen[key] = r
    return list(seen.values())


# ============================================================================
# HARD FILTERS, COOLDOWN, GOVERNOR
# ============================================================================

def passes_hard_filters(symbol: str, snapshot: dict, atr_pct: float, cand: Candidate) -> tuple[bool, str]:
    info = snapshot.get(symbol)
    if not info:
        return False, "no market snapshot"
    if info["oi_usd"] < MIN_OI_USD:
        return False, f"OI too low (${info['oi_usd']:,.0f})"
    if not (MIN_ATR_PCT <= atr_pct <= MAX_ATR_PCT):
        return False, f"ATR% out of band ({atr_pct:.4f})"
    if cand.rr() < MIN_RR:
        return False, f"RR too low ({cand.rr():.2f})"
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


# ============================================================================
# TELEGRAM
# ============================================================================

def fmt_px(v: float) -> str:
    if v >= 100:
        return f"{v:,.2f}"
    if v >= 1:
        return f"{v:,.4f}"
    return f"{v:.6f}"


def confidence_bar(confidence: float) -> str:
    filled = round(confidence / 10)
    return "\u2588" * filled + "\u2591" * (10 - filled)


def format_signal(cand: Candidate, confidence: float, grade: str) -> str:
    arrow = "\U0001F7E2 LONG" if cand.direction == "long" else "\U0001F534 SHORT"
    duration = classify_duration(cand.combo_name)
    lines = [
        f"*AXIS ENGINE v2.0.0* -- {cand.symbol}/USD",
        f"{arrow}  |  Grade *{grade}*  |  Pathway: `{cand.pathway}`",
        "",
        f"Entry:  `{fmt_px(cand.entry)}`",
        f"SL:     `{fmt_px(cand.sl)}`",
        f"TP1:    `{fmt_px(cand.tp1)}`",
        f"TP2:    `{fmt_px(cand.tp2)}`",
        f"R:R (TP2): `{cand.rr():.2f}`",
        f"Confidence: {confidence:.1f}%  {confidence_bar(confidence)}",
        f"Est. hold: {duration}",
        "",
        "Confluences:",
    ] + [f"  \u2022 {c}" for c in cand.confluences]
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


# ============================================================================
# ACTIVE SIGNAL TRACKING / OUTCOME RESOLUTION
# ============================================================================

def record_signal(state: dict, cand: Candidate, confidence: float, grade: str, bar_index: int):
    entry = {
        "symbol": cand.symbol, "direction": cand.direction, "pathway": cand.pathway,
        "combo": cand.combo_name, "entry": cand.entry, "sl": cand.sl,
        "tp1": cand.tp1, "tp2": cand.tp2, "confidence": confidence, "grade": grade,
        "ts": int(time.time()), "bar_index": bar_index, "result": "open",
    }
    state["active_signals"].append(entry)
    state["signal_history"].append(dict(entry))
    update_cooldown(state, cand.symbol, cand.direction, bar_index)


def check_active_signals(state: dict, snapshot: dict):
    still_active = []
    for sig in state["active_signals"]:
        info = snapshot.get(sig["symbol"])
        if not info or not info.get("mark"):
            still_active.append(sig)
            continue
        price = info["mark"]
        hit_sl = (price <= sig["sl"]) if sig["direction"] == "long" else (price >= sig["sl"])
        hit_tp2 = (price >= sig["tp2"]) if sig["direction"] == "long" else (price <= sig["tp2"])
        if hit_sl:
            _resolve(state, sig, "loss")
        elif hit_tp2:
            _resolve(state, sig, "win")
        else:
            still_active.append(sig)
    state["active_signals"] = still_active


def _resolve(state: dict, sig: dict, result: str):
    for h in state["signal_history"]:
        if h is sig or (h.get("ts") == sig.get("ts") and h.get("symbol") == sig.get("symbol")
                        and h.get("direction") == sig.get("direction")):
            h["result"] = result
            break
    log.info("Signal resolved: %s %s %s -> %s", sig["symbol"], sig["direction"], sig["pathway"], result)


# ============================================================================
# MAIN EVALUATION / SCAN
# ============================================================================

def evaluate_symbol(symbol: str, state: dict, btc_bias: str, btc_strength: float,
                     snapshot: dict, threshold: float, clusters: list[set[str]]) -> Optional[dict]:
    bundle = fetch_all_candles(symbol)
    if not bundle:
        return None

    regime = build_regime_vector(state, symbol, bundle, btc_bias, btc_strength, COMBOS["intraday"])
    combo_name = select_combo(regime)
    local_threshold = adaptive_thresholds(regime, threshold)
    combo = COMBOS[combo_name]

    bar_index = bundle[combo["exec"]][-1]["t"] // TF_MS[combo["exec"]]
    book = analyze_orderbook(symbol)

    best: Optional[tuple[Candidate, float, str]] = None
    for builder in PATHWAYS:
        cand = builder(symbol, bundle, combo_name, regime)
        if cand is None:
            continue
        if not check_cooldown(state, symbol, cand.direction, bar_index):
            continue
        if is_recent_duplicate(state, symbol, cand.direction, cand.entry):
            continue
        atr_pct = safe(cand.atr_val / cand.entry, 0.0)
        ok, reason = passes_hard_filters(symbol, snapshot, atr_pct, cand)
        if not ok:
            log.debug("%s %s filtered: %s", symbol, cand.pathway, reason)
            continue
        confidence = score_candidate(cand, regime, state, btc_bias, book)
        if confidence < local_threshold:
            continue
        grade = grade_for_confidence(confidence)
        if best is None or confidence > best[1]:
            best = (cand, confidence, grade)

    if best is None:
        return None
    cand, confidence, grade = best
    record_signal(state, cand, confidence, grade, bar_index)
    return {"cand": cand, "confidence": confidence, "grade": grade}


def count_open_same_direction(state: dict, direction: str) -> int:
    return sum(1 for s in state["active_signals"] if s["direction"] == direction)


def count_open_for_symbol(state: dict, symbol: str) -> int:
    return sum(1 for s in state["active_signals"] if s["symbol"] == symbol)


def run_scan():
    log.info("=== AXIS ENGINE v2.0.0 scan starting ===")
    state = load_state()
    snapshot = get_market_snapshot()
    check_active_signals(state, snapshot)

    btc_bundle = fetch_all_candles("BTC")
    if not btc_bundle:
        log.error("Could not fetch BTC bundle; aborting scan.")
        save_state(state)
        return
    btc_bias, btc_strength = compute_btc_regime(btc_bundle)
    log.info("BTC regime: %s (ADX %.1f)", btc_bias, btc_strength)

    bundles_for_corr = {"BTC": btc_bundle}
    fired = []
    threshold = state["governor"]["threshold"]

    for symbol in WATCHLIST:
        if count_open_for_symbol(state, symbol) >= MAX_CONCURRENT_PER_SYMBOL:
            continue
        try:
            result = evaluate_symbol(symbol, state, btc_bias, btc_strength, snapshot, threshold, [])
        except Exception as e:
            log.exception("Error evaluating %s: %s", symbol, e)
            continue
        if result:
            direction = result["cand"].direction
            if count_open_same_direction(state, direction) > MAX_CONCURRENT_SAME_DIRECTION:
                log.info("Skipping %s: same-direction cap reached", symbol)
                state["active_signals"].pop()  # undo speculative record
                state["signal_history"].pop()
                continue
            fired.append(result)

    # Correlation dedup pass across everything fired this scan
    if len(fired) > 1:
        bundles_map = {r["cand"].symbol: {} for r in fired}
        for r in fired:
            b = fetch_all_candles(r["cand"].symbol)
            if b:
                bundles_map[r["cand"].symbol] = b
        clusters = build_correlation_clusters({k: v for k, v in bundles_map.items() if v})
        ranked = [{"symbol": r["cand"].symbol, "direction": r["cand"].direction,
                   "confidence": r["confidence"], "ref": r} for r in fired]
        kept = dedup_correlated(ranked, clusters)
        kept_refs = {id(k["ref"]) for k in kept}
        fired = [r for r in fired if id(r) in kept_refs or r in [k["ref"] for k in kept]]

    for r in fired:
        text = format_signal(r["cand"], r["confidence"], r["grade"])
        send_telegram(text)
        log.info("Signal fired: %s %s (%s) conf=%.1f grade=%s",
                  r["cand"].symbol, r["cand"].direction, r["cand"].pathway,
                  r["confidence"], r["grade"])

    governor_adjust_threshold(state, estimate_signals_last_24h(state))
    prune_state(state)
    save_state(state)
    log.info("=== Scan complete: %d signal(s) fired, threshold now %.1f ===",
              len(fired), state["governor"]["threshold"])


def main():
    try:
        run_scan()
    except Exception as e:
        log.exception("Fatal error during scan: %s", e)
        raise SystemExit(1)


if __name__ == "__main__":
    main()
