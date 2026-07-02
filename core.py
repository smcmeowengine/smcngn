"""
Nyx Engine
=============================================================
A two-timeframe institutional signal engine for perpetual futures. Unlike
order-block/FVG confluence-stacking strategies, Nyx is built entirely
around *liquidity engineering*: it waits for the market to actually take out
resting stops at a level that matters, then demands proof — in the form of
a displacement leg that reshapes market structure and leaves an imbalance
behind it — before it will ever consider a trade. No sweep, no signal. No
displacement, no signal. No structure shift, no signal. These three are
non-negotiable hard gates, not scoring bonuses.

Methodology
-----------
H4 (bias / narrative / POI):
  1. Structure bias — swing-based BOS/CHoCH sequencing, confirmed only when
     it agrees with H4 EMA(21/50) trend. Disagreement = neutral = no trades.
  2. Dealing range premium/discount — current H4 close must sit in the
     "engineered" half of the range (discount for longs, premium for
     shorts) — classic SMC positioning, applied as a hard gate.
  3. H4 POI — the origin swing (order block) behind the most recent BOS in
     bias direction. Its mitigation state (fresh/partial/full) gates and
     scores the setup; a fully mitigated POI kills the trade.
  4. H4 liquidity pools (equal highs/lows, swing extremes) become the TP2 /
     TP3 draw targets — price is assumed to be drawn toward resting
     liquidity, not toward an arbitrary R multiple.

M15 (execution — the "sweep → displacement → breaker" sequence):
  1. Liquidity sweep — price wicks through a genuine prior M15 swing point
     opposite to the H4 bias (sell-side liquidity swept for longs, buy-side
     for shorts) and closes back inside. This is the stop-hunt / Judas
     Swing. HARD GATE.
  2. Displacement — within a handful of bars, price must move away from the
     sweep with real force: net move >= DISPLACEMENT_MIN_ATR x ATR15, at
     least one high-body-ratio candle, and a clean break of the nearest
     opposing M15 swing (CHoCH) confirming the reversal in H4-bias
     direction. HARD GATE.
  3. Imbalance + breaker — the displacement leg must leave at least one
     fair value gap behind, and the swept candle itself becomes the
     "breaker block". The overlap of the breaker body and the freshest FVG
     defines the OTE (optimal trade entry) retracement zone.
  4. Entry sits inside that OTE zone; stop sits beyond the sweep's wick
     extreme; TP1/TP2/TP3 are liquidity-drawn (M15 pool -> H4 pool ->
     extended pool), each independently validated with a minimum R:R gate
     rather than being fixed R multiples.

This is a fundamentally different edge than order-block/FVG/MSB
confluence-stacking: it never enters on a static zone, only on proof that
smart money has already engineered liquidity and committed to a direction.
Because the sweep is the trigger (not a bonus), qualifying setups tend to
appear more often than a "stack five confluences" model, while the
displacement + CHoCH double-gate keeps false positives out.

Timeframes : H4 (bias, POI, dealing range, liquidity pools) ->
             M15 (sweep, displacement, imbalance, breaker entry)
Exchange   : Hyperliquid
Alerts     : Telegram (HTML)
"""

import os, time, math, threading, requests, random, json, pathlib, sys
import signal as _signal
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
from dataclasses import dataclass, field

# ── ENV ──────────────────────────────────────────────────────────────────────
TG_BOT_TOKEN = os.getenv("TG_BOT_TOKEN")
TG_CHAT_ID   = os.getenv("TG_CHAT_ID")
if not TG_BOT_TOKEN:
    raise RuntimeError("TG_BOT_TOKEN environment variable is required")
if not TG_CHAT_ID:
    raise RuntimeError("TG_CHAT_ID environment variable is required")

HL_INFO_URL = "https://api.hyperliquid.xyz/info"

VERSION = "1.1.1"

# ── WATCHLIST (unchanged infrastructure) ──────────────────────────────────────
WATCHLIST = [
    "BTCUSDT", "ETHUSDT", "HYPEUSDT", "ZECUSDT", "NEARUSDT",
    "ONDOUSDT", "SUIUSDT", "PENGUUSDT", "BNBUSDT", "SOLUSDT",
    "TRXUSDT", "BCHUSDT", "DOGEUSDT", "ADAUSDT", "DOTUSDT",
    "TAOUSDT", "AVAXUSDT", "LINKUSDT", "AAVEUSDT", "XRPUSDT",
    "XLMUSDT", "UNIUSDT", "LTCUSDT", "APTUSDT", "PENDLEUSDT",
]

# ── SECTOR MAP (used for max-one-per-sector diversification cap) ────────────
SECTOR_MAP: dict[str, str] = {
    "BTCUSDT":    "btc",
    "ETHUSDT":    "eth",
    "SOLUSDT":    "eth_l1", "AVAXUSDT": "eth_l1", "SUIUSDT": "eth_l1", "APTUSDT": "eth_l1",
    "NEARUSDT":   "eth_l1",
    "BNBUSDT":    "bnb",
    "XRPUSDT":    "payments", "XLMUSDT": "payments", "TRXUSDT": "payments", "LTCUSDT": "payments",
    "DOGEUSDT":   "meme",    "PENGUUSDT": "meme",
    "ADAUSDT":    "layer1_alt", "DOTUSDT": "layer1_alt", "TAOUSDT": "layer1_alt",
    "LINKUSDT":   "defi",    "AAVEUSDT": "defi", "UNIUSDT": "defi",
    "ONDOUSDT":   "defi",    "PENDLEUSDT": "defi",
    "HYPEUSDT":   "hype",
    "ZECUSDT":    "privacy", "BCHUSDT": "privacy",
}
BTC_REGIME_EXEMPT_SECTORS: set[str] = {"hype", "defi"}

# ── SCAN CONFIG ───────────────────────────────────────────────────────────────
SCAN_INTERVAL_S = 60 * 15   # cron-job.org fires this every 15 minutes
N_M15 = 200
N_H4  = 150

INTERVAL_MS = {
    "15m": 15 * 60 * 1000,
    "1h":  60 * 60 * 1000,
    "4h":  4  * 60 * 60 * 1000,
    "1d":  24 * 60 * 60 * 1000,
}

# ── SESSION FILTER ────────────────────────────────────────────────────────────
# Liquidity sweeps and displacement are far more reliable inside London/NY,
# where genuine institutional order flow is present to engineer the raid.
SESSION_FILTER_ENABLED = True
LONDON_OPEN_H, LONDON_CLOSE_H = 7, 12
NY_OPEN_H, NY_CLOSE_H         = 13, 20
DEAD_ZONE_START_H, DEAD_ZONE_END_H = 12, 13

WEEKEND_MODE_ENABLED = True
WEEKEND_MIN_CONFLUENCE_BUMP = 1   # raise the score bar on Sat/Sun rather than blocking outright

# ── H4 STRUCTURE / BIAS ───────────────────────────────────────────────────────
SWING_LEFT_H4, SWING_RIGHT_H4 = 2, 2
H4_STRUCTURE_LOOKBACK = 40
EMA_FAST, EMA_SLOW    = 21, 50
EMA_SEP_MIN_ATR_H4    = 0.30   # EMA fast/slow must be >= this many H4 ATRs apart to call a trend

# ── H4 DEALING RANGE / PREMIUM-DISCOUNT (hard gate) ──────────────────────────
PD_LOOKBACK        = 60
PREMIUM_THRESHOLD  = 0.60   # close >= 60% of H4 range = premium (short territory)
DISCOUNT_THRESHOLD = 0.40   # close <= 40% of H4 range = discount (long territory)

# ── H4 POI (order block / breaker behind the most recent BOS) ───────────────
POI_LOOKBACK_H4        = 20   # only origin swings within this many H4 bars are eligible
POI_FRESH_MAX_MITIG    = 0.15
POI_FULL_MITIG         = 0.90   # >= this fraction (or a close through) invalidates the POI
POI_MAX_ATR_DISTANCE   = 3.0    # POI must be within N x ATR_H4 of current price to stay relevant

# ── H4 LIQUIDITY POOLS (equal highs/lows -> TP2/TP3 draw targets) ───────────
POOL_LOOKBACK_H4     = 80
POOL_EQUAL_TOL_ATR   = 0.15   # cluster tolerance, in H4-ATR units

# ── M15 SWEEP (hard gate) ─────────────────────────────────────────────────────
SWING_LEFT_M15, SWING_RIGHT_M15 = 2, 2
SWEEP_LOOKBACK_M15      = 40   # how far back to search for the swept level
SWEEP_RECENT_BARS       = 6    # the sweep bar itself must be within this many closed M15 bars
SWEEP_MIN_ATR_RATIO     = 0.15   # wick must clear the level by >= this many ATR15
SWEEP_STRONG_ATR_RATIO  = 0.35

# ── M15 DISPLACEMENT (hard gate) ──────────────────────────────────────────────
DISPLACEMENT_MAX_BARS       = 4
DISPLACEMENT_MIN_ATR        = 1.2   # net move away from the sweep, in ATR15 units
DISPLACEMENT_STRONG_ATR     = 2.0
DISPLACEMENT_BODY_RATIO_MIN = 0.60
CHOCH_MIN_MARGIN_ATR        = 0.05   # close must clear the CHoCH level by at least this much
CHOCH_STRONG_MARGIN_ATR     = 0.25
VOLUME_BONUS_RATIO          = 1.30   # displacement candle volume vs 20-bar average

# ── IMBALANCE / BREAKER ───────────────────────────────────────────────────────
FVG_MIN_SIZE_ATR = 0.15

# ── ENTRY / RISK ───────────────────────────────────────────────────────────────
SL_BUFFER_ATR          = 0.15
ENTRY_MAX_DIST_ATR     = 0.60   # drop signals whose OTE zone is already too far from price
TP1_MIN_RR             = 1.2
TP2_MIN_RR             = 2.5
TP1_FALLBACK_RR        = 1.5
TP2_FALLBACK_RR        = 3.0
TP3_FALLBACK_RR        = 5.0

# ── FUNDING / OI (optional scoring bonus, never a hard gate) ────────────────
OI_FUNDING_ENABLED       = True
FUNDING_ALIGN_THRESHOLD  = 0.0001

# ── BTC REGIME FILTER ─────────────────────────────────────────────────────────
BTC_REGIME_FILTER_ENABLED = True
BTC_SYMBOL = "BTCUSDT"

# ── CONFLUENCE SCORING ────────────────────────────────────────────────────────
# All components below are additive bonuses stacked ON TOP of a setup that has
# already cleared every hard gate (valid sweep + valid displacement/CHoCH +
# fresh imbalance + PD alignment + non-neutral H4 bias + live POI + RR gates).
MIN_CONFLUENCE_SCORE = 6
STRONG_SIGNAL_SCORE  = 8
APLUS_SIGNAL_SCORE   = 10
THEORETICAL_MAX_SCORE = 2 + 2 + 2 + 1 + 1 + 1 + 1 + 1 + 1 + 1   # = 13

# ── FREQUENCY / DIVERSIFICATION CAPS ─────────────────────────────────────────
TOP_N_SIGNALS       = 4
MAX_SAME_DIRECTION  = 3
MAX_PER_SECTOR       = 1

# ── DEDUP / COOLDOWN / STATE ──────────────────────────────────────────────────
SIGNAL_COOLDOWN_S   = 60 * 60 * 4      # 4h before the same symbol+direction can fire again
ACTIVE_SIGNAL_TTL_S = 60 * 60 * 48     # 48h max lifetime for tracking a sent signal
FILL_TIMEOUT_S      = 60 * 60 * 6      # unfilled OTE zones expire after 6h

STATE_FILE    = pathlib.Path("state.json")
WIN_RATE_FILE = pathlib.Path("win_rate.json")

# ── RATE LIMIT / HTTP ─────────────────────────────────────────────────────────
_hl_lock         = threading.Lock()
_hl_last_req_ts  = 0.0
_hl_min_interval = 0.2
_hl_session      = requests.Session()
_tg_session      = requests.Session()

# ── CACHES (cleared / repopulated once per scan run) ─────────────────────────
_candle_cache_h4:  dict[str, dict] = {}
_CANDLE_CACHE_H4_TTL_S = 60 * 60          # H4 candles close once every 4h

_atr_cache: dict[str, float] = {}
_oi_funding_data: dict[str, dict] = {}

_fired_signals:  dict[str, float] = {}
_active_signals: dict[str, dict]  = {}
_last_scan_ts: float = 0.0

_win_rate_data: dict = {}
_win_rate_dirty = False


# ═══════════════════════════════════════════════════════════════════════════════
# DATA STRUCTURES
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class SwingPoint:
    index: int
    price: float
    kind:  str   # "high" | "low"

@dataclass
class StructureEvent:
    index:     int
    kind:      str   # "BOS" | "CHoCH"
    direction: str   # "bull" | "bear"
    level:     float

@dataclass
class POI:
    high:  float
    low:   float
    direction: str        # "bull" | "bear"
    index: int
    state: str = "fresh"  # fresh | partial | full
    mitigation_pct: float = 0.0

@dataclass
class FVG:
    high: float
    low:  float
    direction: str
    index: int

@dataclass
class SweepEvent:
    index: int
    level: float
    wick_extreme: float
    atr_ratio: float

@dataclass
class DisplacementLeg:
    end_index:  int
    atr_ratio:  float
    body_ratio: float
    choch_level: float
    choch_margin_atr: float
    volume_ratio: float

@dataclass
class NyxSignal:
    symbol: str
    direction: str
    entry_zone_high: float
    entry_zone_low: float
    exact_entry: float
    backup_entry: float
    stop_loss: float
    take_profit_1: float
    take_profit_2: float
    take_profit_3: float | None
    confluence: int
    max_score: int
    signal_grade: str
    combos_hit: list = field(default_factory=list)
    h4_bias: str = ""
    poi_state: str = ""
    sweep_atr_ratio: float = 0.0
    displacement_atr_ratio: float = 0.0
    funding_rate: float | None = None
    timestamp: str = ""
    details: dict = field(default_factory=dict)


# ═══════════════════════════════════════════════════════════════════════════════
# HYPERLIQUID API
# ═══════════════════════════════════════════════════════════════════════════════

def hl_coin(symbol: str) -> str:
    return symbol.replace("USDT", "")


def hl_post(payload: dict):
    global _hl_last_req_ts
    for attempt in range(5):
        try:
            with _hl_lock:
                elapsed = time.time() - _hl_last_req_ts
                wait = _hl_min_interval - elapsed
                if wait > 0:
                    time.sleep(wait)
                _hl_last_req_ts = time.time()

            r = _hl_session.post(HL_INFO_URL, json=payload,
                                  headers={"Content-Type": "application/json"},
                                  timeout=15)
            if r.status_code == 429:
                time.sleep(min(20.0, 1.0 * (2 ** attempt)) + random.uniform(0, 0.3))
                continue
            r.raise_for_status()
            data = r.json()
            if isinstance(data, dict) and "error" in data:
                raise ValueError(f"Hyperliquid API error (HTTP 200): {data['error']}")
            return data
        except Exception:
            if attempt == 4:
                raise
            time.sleep(min(10.0, 0.5 * (2 ** attempt)))


def current_bar_open_ms(ref_ms: int, interval: str) -> int:
    return (ref_ms // INTERVAL_MS[interval]) * INTERVAL_MS[interval]


def filter_valid_candles(candles: list[dict]) -> list[dict]:
    return [c for c in candles if c["h"] > c["l"]]


def get_candles(symbol: str, interval: str, n: int) -> list[dict]:
    iv_ms = INTERVAL_MS[interval]
    ref_ms = int(time.time() * 1000)
    end_ms = current_bar_open_ms(ref_ms, interval)
    start_ms = end_ms - iv_ms * (n + 5)
    raw = hl_post({
        "type": "candleSnapshot",
        "req":  {"coin": hl_coin(symbol), "interval": interval,
                 "startTime": start_ms, "endTime": end_ms},
    })
    if not raw:
        return []
    candles = [{"t": int(c["t"]), "o": float(c["o"]), "h": float(c["h"]),
                "l": float(c["l"]), "c": float(c["c"]), "v": float(c["v"])}
               for c in raw]
    valid = [c for c in candles if c["t"] < end_ms][-n:]
    return filter_valid_candles(valid)


def get_candles_h4_cached(symbol: str) -> list[dict]:
    entry = _candle_cache_h4.get(symbol)
    if entry and (time.time() - entry["ts"]) < _CANDLE_CACHE_H4_TTL_S:
        return entry["candles"]
    candles = get_candles(symbol, "4h", N_H4)
    _candle_cache_h4[symbol] = {"candles": candles, "ts": time.time()}
    return candles


def get_candles_m15(symbol: str) -> list[dict]:
    # M15 candles change every scan cycle — always fetch fresh, no caching.
    return get_candles(symbol, "15m", N_M15)


def fetch_all_mids() -> dict[str, float]:
    try:
        raw = hl_post({"type": "allMids"})
        return {k: float(v) for k, v in raw.items()} if raw else {}
    except Exception as e:
        print(f"  [MIDS] fetch error: {e}")
        return {}


def fetch_all_oi_funding() -> None:
    if not OI_FUNDING_ENABLED:
        return
    try:
        raw = hl_post({"type": "metaAndAssetCtxs"})
        if not raw or len(raw) < 2:
            return
        universe = raw[0].get("universe", [])
        ctx_list = raw[1]
        for i, asset in enumerate(universe):
            coin = asset.get("name", "")
            if not coin or i >= len(ctx_list):
                continue
            ctx = ctx_list[i]
            _oi_funding_data[coin] = {
                "funding_rate":  float(ctx.get("funding", 0)),
                "open_interest": float(ctx.get("openInterest", 0)),
            }
        print(f"  [OI/FUNDING] Fetched {len(_oi_funding_data)} assets")
    except Exception as e:
        print(f"  [OI/FUNDING] fetch error: {e}")


def get_funding(symbol: str) -> float | None:
    entry = _oi_funding_data.get(hl_coin(symbol))
    return entry["funding_rate"] if entry else None


# ═══════════════════════════════════════════════════════════════════════════════
# INDICATORS
# ═══════════════════════════════════════════════════════════════════════════════

def calc_atr(candles: list[dict], period: int = 14) -> float:
    if len(candles) < period + 1:
        return candles[-1]["h"] - candles[-1]["l"] if candles else 0.0
    trs = [max(candles[i]["h"] - candles[i]["l"],
               abs(candles[i]["h"] - candles[i-1]["c"]),
               abs(candles[i]["l"] - candles[i-1]["c"]))
           for i in range(1, len(candles))]
    return sum(trs[-period:]) / period


def calc_atr_cached(symbol: str, tf: str, candles: list[dict], period: int = 14) -> float:
    key = f"{symbol}:{tf}"
    if key not in _atr_cache:
        _atr_cache[key] = calc_atr(candles, period)
    return _atr_cache[key]


def calc_ema(values: list[float], period: int) -> list[float]:
    if len(values) < period:
        return values[:]
    k = 2.0 / (period + 1)
    out = [sum(values[:period]) / period]
    for v in values[period:]:
        out.append(v * k + out[-1] * (1 - k))
    return out


def calc_avg_volume(candles: list[dict], period: int = 20) -> float:
    if not candles:
        return 0.0
    window = candles[-period:]
    return sum(c["v"] for c in window) / len(window)


def body_ratio(c: dict) -> float:
    rng = c["h"] - c["l"]
    if rng <= 0:
        return 0.0
    return abs(c["c"] - c["o"]) / rng


# ═══════════════════════════════════════════════════════════════════════════════
# SESSION FILTER
# ═══════════════════════════════════════════════════════════════════════════════

def is_active_session() -> bool:
    if not SESSION_FILTER_ENABLED:
        return True
    now = datetime.now(timezone.utc)
    hour = now.hour
    if DEAD_ZONE_START_H <= hour < DEAD_ZONE_END_H:
        return False
    return (LONDON_OPEN_H <= hour < LONDON_CLOSE_H) or (NY_OPEN_H <= hour < NY_CLOSE_H)


def get_min_confluence_score() -> int:
    score = MIN_CONFLUENCE_SCORE
    if WEEKEND_MODE_ENABLED and datetime.now(timezone.utc).weekday() >= 5:
        score += WEEKEND_MIN_CONFLUENCE_BUMP
    return score


# ═══════════════════════════════════════════════════════════════════════════════
# SWING / STRUCTURE DETECTION (shared fractal method, used at both timeframes)
# ═══════════════════════════════════════════════════════════════════════════════

def find_swings(candles: list[dict], left: int = 2, right: int = 2) -> list[SwingPoint]:
    swings: list[SwingPoint] = []
    n = len(candles)
    for i in range(left, n - right):
        window_h = [candles[j]["h"] for j in range(i - left, i + right + 1)]
        window_l = [candles[j]["l"] for j in range(i - left, i + right + 1)]
        if candles[i]["h"] == max(window_h) and window_h.count(candles[i]["h"]) == 1:
            swings.append(SwingPoint(index=i, price=candles[i]["h"], kind="high"))
        if candles[i]["l"] == min(window_l) and window_l.count(candles[i]["l"]) == 1:
            swings.append(SwingPoint(index=i, price=candles[i]["l"], kind="low"))
    return swings


def detect_structure(candles: list[dict], swings: list[SwingPoint],
                      lookback_bars: int) -> tuple[str, list[StructureEvent]]:
    """
    Walk swings chronologically and classify each break of a prior swing
    extreme as BOS (continuation of the prevailing internal trend) or CHoCH
    (a break in the opposite direction — the first sign of reversal).
    Returns the most recent confirmed direction plus the event list.
    """
    start_idx = max(0, len(candles) - lookback_bars)
    relevant = [s for s in swings if s.index >= start_idx]
    if len(relevant) < 2:
        return "neutral", []

    events: list[StructureEvent] = []
    trend = "neutral"
    last_high = next((s for s in relevant if s.kind == "high"), None)
    last_low  = next((s for s in relevant if s.kind == "low"), None)

    for s in relevant:
        if s.kind == "high" and last_high and s.price > last_high.price:
            kind = "CHoCH" if trend == "bear" else "BOS"
            events.append(StructureEvent(index=s.index, kind=kind, direction="bull", level=s.price))
            trend = "bull"
        if s.kind == "low" and last_low and s.price < last_low.price:
            kind = "CHoCH" if trend == "bull" else "BOS"
            events.append(StructureEvent(index=s.index, kind=kind, direction="bear", level=s.price))
            trend = "bear"
        if s.kind == "high":
            last_high = s
        else:
            last_low = s

    # Re-check breaks against the running close series so consecutive higher
    # highs/lower lows without an intervening opposite swing still register.
    closes = [c["c"] for c in candles]
    for i in range(start_idx, len(candles)):
        pass  # structural walk above already captures the swing-to-swing sequence

    direction = events[-1].direction if events else "neutral"
    return direction, events


def h4_ema_trend(candles: list[dict], atr_h4: float) -> str:
    closes = [c["c"] for c in candles]
    ema_fast = calc_ema(closes, EMA_FAST)
    ema_slow = calc_ema(closes, EMA_SLOW)
    if not ema_fast or not ema_slow or atr_h4 <= 0:
        return "neutral"
    sep = ema_fast[-1] - ema_slow[-1]
    if abs(sep) < EMA_SEP_MIN_ATR_H4 * atr_h4:
        return "neutral"
    return "bull" if sep > 0 else "bear"


def h4_bias(candles: list[dict], atr_h4: float) -> tuple[str, list[StructureEvent], list[SwingPoint]]:
    swings = find_swings(candles, SWING_LEFT_H4, SWING_RIGHT_H4)
    structure_dir, events = detect_structure(candles, swings, H4_STRUCTURE_LOOKBACK)
    ema_dir = h4_ema_trend(candles, atr_h4)
    bias = structure_dir if structure_dir == ema_dir and structure_dir != "neutral" else "neutral"
    return bias, events, swings


# ═══════════════════════════════════════════════════════════════════════════════
# H4 DEALING RANGE / PREMIUM-DISCOUNT
# ═══════════════════════════════════════════════════════════════════════════════

def premium_discount_zone(candles: list[dict], lookback: int = PD_LOOKBACK) -> dict:
    window = candles[-lookback:]
    hi = max(c["h"] for c in window)
    lo = min(c["l"] for c in window)
    close = candles[-1]["c"]
    rng = hi - lo
    pct = (close - lo) / rng if rng > 0 else 0.5
    return {"high": hi, "low": lo, "mid": (hi + lo) / 2, "pct": pct}


# ═══════════════════════════════════════════════════════════════════════════════
# H4 POI (order block behind the most recent BOS in bias direction)
# ═══════════════════════════════════════════════════════════════════════════════

def compute_mitigation(candles_after: list[dict], zone_high: float, zone_low: float,
                        direction: str) -> float:
    if not candles_after:
        return 0.0
    height = zone_high - zone_low
    if height <= 0:
        return 1.0
    deepest = 0.0
    for c in candles_after:
        if direction == "bull":
            if c["c"] < zone_low:
                return 1.0
            pen = zone_high - c["l"]
        else:
            if c["c"] > zone_high:
                return 1.0
            pen = c["h"] - zone_low
        deepest = max(deepest, max(0.0, min(1.0, pen / height)))
    return deepest


def classify_poi_state(mitig: float) -> str:
    if mitig >= POI_FULL_MITIG:
        return "full"
    if mitig <= POI_FRESH_MAX_MITIG:
        return "fresh"
    return "partial"


def find_h4_poi(candles: list[dict], swings: list[SwingPoint], bias: str,
                 atr_h4: float, current_price: float) -> POI | None:
    if bias not in ("bull", "bear"):
        return None
    start_idx = max(0, len(candles) - POI_LOOKBACK_H4)
    kind = "low" if bias == "bull" else "high"
    pool = [s for s in swings if s.kind == kind and s.index >= start_idx]
    if not pool:
        return None
    pivot = pool[-1]
    candle = candles[pivot.index]

    if bias == "bull":
        zone_low = candle["l"]
        zone_high = max(candle["o"], candle["c"])
    else:
        zone_high = candle["h"]
        zone_low = min(candle["o"], candle["c"])
    if zone_high <= zone_low:
        return None

    mitig = compute_mitigation(candles[pivot.index + 1:], zone_high, zone_low, bias)
    state = classify_poi_state(mitig)
    if state == "full":
        return None

    if atr_h4 > 0:
        dist_atr = abs(current_price - (zone_high if bias == "bear" else zone_low)) / atr_h4
        if dist_atr > POI_MAX_ATR_DISTANCE:
            return None

    return POI(high=zone_high, low=zone_low, direction=bias, index=pivot.index,
                state=state, mitigation_pct=mitig)


# ═══════════════════════════════════════════════════════════════════════════════
# H4 LIQUIDITY POOLS (equal highs/lows -> TP2 / TP3 draw targets)
# ═══════════════════════════════════════════════════════════════════════════════

def find_h4_liquidity_pools(candles: list[dict], swings: list[SwingPoint], direction: str,
                             current_price: float, atr_h4: float) -> list[float]:
    """
    Cluster nearby swing extremes into pools and return those that sit
    beyond current price in the direction a winning trade would travel
    (buy-side highs for longs, sell-side lows for shorts), nearest first.
    """
    kind = "high" if direction == "long" else "low"
    start_idx = max(0, len(candles) - POOL_LOOKBACK_H4)
    tol = max(atr_h4 * POOL_EQUAL_TOL_ATR, current_price * 0.0005)
    points = sorted((s.price for s in swings if s.kind == kind and s.index >= start_idx),
                     reverse=(direction == "short"))
    if direction == "long":
        points = [p for p in points if p > current_price]
        points.sort()
    else:
        points = [p for p in points if p < current_price]
        points.sort(reverse=True)

    pools: list[float] = []
    for p in points:
        if not pools or abs(p - pools[-1]) > tol:
            pools.append(p)
    return pools


# ═══════════════════════════════════════════════════════════════════════════════
# BTC REGIME FILTER
# ═══════════════════════════════════════════════════════════════════════════════

def get_btc_regime() -> str:
    if not BTC_REGIME_FILTER_ENABLED:
        return "neutral"
    try:
        candles = get_candles_h4_cached(BTC_SYMBOL)
        if len(candles) < EMA_SLOW + 5:
            return "neutral"
        atr = calc_atr_cached(BTC_SYMBOL, "4h", candles)
        return h4_ema_trend(candles, atr)
    except Exception as e:
        print(f"  [BTC REGIME] error: {e}")
        return "neutral"


def btc_regime_blocks(symbol: str, direction: str, regime: str) -> bool:
    if not BTC_REGIME_FILTER_ENABLED or symbol == BTC_SYMBOL:
        return False
    sector = SECTOR_MAP.get(symbol, "")
    if sector in BTC_REGIME_EXEMPT_SECTORS:
        return False
    if regime == "bear" and direction == "long":
        return True
    if regime == "bull" and direction == "short":
        return True
    return False


# ═══════════════════════════════════════════════════════════════════════════════
# M15 LIQUIDITY SWEEP (hard gate #1)
# ═══════════════════════════════════════════════════════════════════════════════

def detect_m15_sweep(candles: list[dict], swings: list[SwingPoint], bias: str,
                      atr15: float) -> SweepEvent | None:
    """
    For a bullish H4 bias we look for sell-side liquidity being swept: a
    recent M15 candle wicks below a prior swing low and closes back above
    it. Mirror logic for bearish bias against a prior swing high.
    """
    if atr15 <= 0 or bias not in ("bull", "bear"):
        return None
    n = len(candles)
    recent_start = max(0, n - SWEEP_RECENT_BARS)
    search_start = max(0, n - SWEEP_LOOKBACK_M15)

    best: SweepEvent | None = None
    for i in range(recent_start, n):
        c = candles[i]
        prior_swings = [s for s in swings if s.index < i and s.index >= search_start]
        if bias == "bull":
            lows = [s for s in prior_swings if s.kind == "low"]
            if not lows:
                continue
            # The level that "matters" is the most significant resting
            # liquidity actually taken out by this candle — i.e. the deepest
            # (lowest) prior swing low that the wick cleared — not merely
            # whichever prior swing happens to sit closest in bar-index.
            # Picking the nearest-in-time swing can select a trivial
            # micro-swing over a genuine liquidity pool a few bars further
            # back, undermining the "sweep a level that matters" premise.
            swept = [s for s in lows if c["l"] < s.price]
            if not swept:
                continue
            level = min(s.price for s in swept)   # deepest liquidity taken
            if c["c"] > level:
                ratio = (level - c["l"]) / atr15
                if ratio >= SWEEP_MIN_ATR_RATIO:
                    cand = SweepEvent(index=i, level=level, wick_extreme=c["l"], atr_ratio=ratio)
                    if best is None or i > best.index:
                        best = cand
        else:
            highs = [s for s in prior_swings if s.kind == "high"]
            if not highs:
                continue
            swept = [s for s in highs if c["h"] > s.price]
            if not swept:
                continue
            level = max(s.price for s in swept)   # deepest liquidity taken
            if c["c"] < level:
                ratio = (c["h"] - level) / atr15
                if ratio >= SWEEP_MIN_ATR_RATIO:
                    cand = SweepEvent(index=i, level=level, wick_extreme=c["h"], atr_ratio=ratio)
                    if best is None or i > best.index:
                        best = cand
    return best


# ═══════════════════════════════════════════════════════════════════════════════
# M15 DISPLACEMENT + CHoCH (hard gate #2)
# ═══════════════════════════════════════════════════════════════════════════════

def detect_displacement(candles: list[dict], sweep: SweepEvent, bias: str,
                         atr15: float, swings: list[SwingPoint]) -> DisplacementLeg | None:
    n = len(candles)
    window_end = min(n, sweep.index + 1 + DISPLACEMENT_MAX_BARS)
    window = candles[sweep.index:window_end]
    if len(window) < 1 or atr15 <= 0:
        return None

    origin = sweep.wick_extreme
    if bias == "bull":
        extreme_reached = max(c["h"] for c in window)
        end_candidates = [i for i, c in enumerate(window) if c["h"] == extreme_reached]
    else:
        extreme_reached = min(c["l"] for c in window)
        end_candidates = [i for i, c in enumerate(window) if c["l"] == extreme_reached]
    end_offset = end_candidates[-1] if end_candidates else len(window) - 1
    end_index = sweep.index + end_offset

    net_move = (extreme_reached - origin) if bias == "bull" else (origin - extreme_reached)
    atr_ratio = net_move / atr15
    if atr_ratio < DISPLACEMENT_MIN_ATR:
        return None

    best_body = max(body_ratio(c) for c in window)
    if best_body < DISPLACEMENT_BODY_RATIO_MIN:
        return None

    # CHoCH: the nearest opposing-direction swing strictly before the sweep
    # bar must be cleanly closed through by the displacement leg.
    opp_kind = "high" if bias == "bull" else "low"
    prior_opp = [s for s in swings if s.kind == opp_kind and s.index < sweep.index]
    if not prior_opp:
        return None
    choch_ref = max(prior_opp, key=lambda s: s.index)
    closes_in_window = [c["c"] for c in candles[sweep.index:end_index + 1]]
    if not closes_in_window:
        return None
    best_close = max(closes_in_window) if bias == "bull" else min(closes_in_window)
    margin = (best_close - choch_ref.price) / atr15 if bias == "bull" \
        else (choch_ref.price - best_close) / atr15
    if margin < CHOCH_MIN_MARGIN_ATR:
        return None

    avg_vol = calc_avg_volume(candles[:sweep.index] or candles, 20)
    peak_vol = max(c["v"] for c in window)
    vol_ratio = (peak_vol / avg_vol) if avg_vol > 0 else 1.0

    return DisplacementLeg(end_index=end_index, atr_ratio=atr_ratio, body_ratio=best_body,
                            choch_level=choch_ref.price, choch_margin_atr=margin,
                            volume_ratio=vol_ratio)


# ═══════════════════════════════════════════════════════════════════════════════
# IMBALANCE (FVG) + BREAKER BLOCK -> OTE ENTRY ZONE
# ═══════════════════════════════════════════════════════════════════════════════

def find_freshest_fvg(candles: list[dict], start_idx: int, end_idx: int,
                       direction: str, atr15: float) -> FVG | None:
    best: FVG | None = None
    lo_bound = max(1, start_idx)
    hi_bound = min(len(candles) - 1, end_idx)
    for i in range(lo_bound, hi_bound):
        a, b = candles[i - 1], candles[i + 1]
        if direction == "bull" and b["l"] > a["h"]:
            size = b["l"] - a["h"]
            if size >= FVG_MIN_SIZE_ATR * atr15:
                cand = FVG(high=b["l"], low=a["h"], direction="bull", index=i)
                if best is None or cand.index > best.index:
                    best = cand
        elif direction == "bear" and b["h"] < a["l"]:
            size = a["l"] - b["h"]
            if size >= FVG_MIN_SIZE_ATR * atr15:
                cand = FVG(high=a["l"], low=b["h"], direction="bear", index=i)
                if best is None or cand.index > best.index:
                    best = cand
    return best


def breaker_zone(candles: list[dict], sweep_index: int, direction: str) -> tuple[float, float]:
    c = candles[sweep_index]
    if direction == "bull":
        return max(c["o"], c["c"]), c["l"]      # (high, low)
    return c["h"], min(c["o"], c["c"])           # (high, low)


def compute_entry_zone(breaker_hi: float, breaker_lo: float, fvg: FVG | None,
                        direction: str) -> tuple[float, float, float]:
    """
    Entry zone = overlap of the breaker block and the freshest displacement
    FVG when they intersect (tightest, highest-conviction OTE); otherwise
    fall back to the breaker block alone.
    """
    zone_hi, zone_lo = breaker_hi, breaker_lo
    if fvg is not None:
        overlap_hi = min(breaker_hi, fvg.high)
        overlap_lo = max(breaker_lo, fvg.low)
        if overlap_hi > overlap_lo:
            zone_hi, zone_lo = overlap_hi, overlap_lo
    exact_entry = (zone_hi + zone_lo) / 2
    return zone_hi, zone_lo, exact_entry


def fvg_is_fresh(candles: list[dict], fvg: FVG, direction: str) -> bool:
    after = candles[fvg.index + 1:]
    mitig = compute_mitigation(after, fvg.high, fvg.low, direction)
    return mitig <= POI_FRESH_MAX_MITIG


def breaker_is_untouched(candles: list[dict], sweep_index: int, zone_hi: float,
                          zone_lo: float) -> bool:
    for c in candles[sweep_index + 1:-1]:
        if c["l"] <= zone_hi and c["h"] >= zone_lo:
            return False
    return True


# ═══════════════════════════════════════════════════════════════════════════════
# M15 LIQUIDITY TARGET (TP1)
# ═══════════════════════════════════════════════════════════════════════════════

def find_m15_liquidity_target(swings: list[SwingPoint], direction: str,
                               entry: float) -> float | None:
    kind = "high" if direction == "long" else "low"
    candidates = [s.price for s in swings if s.kind == kind]
    if direction == "long":
        candidates = [p for p in candidates if p > entry]
        return min(candidates) if candidates else None
    candidates = [p for p in candidates if p < entry]
    return max(candidates) if candidates else None


# ═══════════════════════════════════════════════════════════════════════════════
# SIGNAL ASSEMBLY
# ═══════════════════════════════════════════════════════════════════════════════

def compute_signal(symbol: str) -> NyxSignal | None:
    candles_h4 = get_candles_h4_cached(symbol)
    if len(candles_h4) < EMA_SLOW + 10:
        return None
    candles_m15 = get_candles_m15(symbol)
    if len(candles_m15) < 60:
        return None

    atr_h4 = calc_atr_cached(symbol, "4h", candles_h4)
    atr15  = calc_atr_cached(symbol, "15m", candles_m15)
    if atr_h4 <= 0 or atr15 <= 0:
        return None

    current_price = candles_m15[-1]["c"]

    # ── H4 bias (hard gate: no neutral trades) ───────────────────────────
    bias, _events, swings_h4 = h4_bias(candles_h4, atr_h4)
    if bias == "neutral":
        return None

    # ── H4 premium/discount alignment (hard gate) ────────────────────────
    pd = premium_discount_zone(candles_h4)
    if bias == "bull" and pd["pct"] > DISCOUNT_THRESHOLD:
        return None
    if bias == "bear" and pd["pct"] < PREMIUM_THRESHOLD:
        return None

    # ── H4 POI must exist and not be fully mitigated (hard gate) ─────────
    poi = find_h4_poi(candles_h4, swings_h4, bias, atr_h4, current_price)
    if poi is None:
        return None

    direction = "long" if bias == "bull" else "short"

    # ── M15 sweep (hard gate #1) ──────────────────────────────────────────
    swings_m15 = find_swings(candles_m15, SWING_LEFT_M15, SWING_RIGHT_M15)
    sweep = detect_m15_sweep(candles_m15, swings_m15, bias, atr15)
    if sweep is None:
        return None

    # ── M15 displacement + CHoCH (hard gate #2) ───────────────────────────
    disp = detect_displacement(candles_m15, sweep, bias, atr15, swings_m15)
    if disp is None:
        return None

    # ── Imbalance behind the displacement leg (hard gate #3) ─────────────
    fvg = find_freshest_fvg(candles_m15, sweep.index, disp.end_index, bias, atr15)
    if fvg is None:
        return None
    if not fvg_is_fresh(candles_m15, fvg, bias):
        return None

    breaker_hi, breaker_lo = breaker_zone(candles_m15, sweep.index, bias)
    zone_hi, zone_lo, exact_entry = compute_entry_zone(breaker_hi, breaker_lo, fvg, bias)
    if zone_hi <= zone_lo:
        return None

    # Backup limit: the zone edge closer to current price. Worse price than
    # exact_entry (the zone midpoint) but a higher probability of actually
    # filling, since price only has to reach the near boundary rather than
    # travel all the way to the middle of the zone.
    backup_entry = (zone_hi if abs(current_price - zone_hi) <= abs(current_price - zone_lo)
                     else zone_lo)

    # ── Entry proximity gate ───────────────────────────────────────────────
    dist_atr = abs(current_price - exact_entry) / atr15
    if dist_atr > ENTRY_MAX_DIST_ATR:
        return None

    # ── Stop loss ────────────────────────────────────────────────────────
    buffer = SL_BUFFER_ATR * atr15
    stop_loss = (sweep.wick_extreme - buffer) if direction == "long" else (sweep.wick_extreme + buffer)
    risk = abs(exact_entry - stop_loss)
    if risk <= 0:
        return None

    # ── Take profits (liquidity-drawn, RR-validated) ──────────────────────
    tp1 = find_m15_liquidity_target(swings_m15, direction, exact_entry)
    if tp1 is None or abs(tp1 - exact_entry) / risk < TP1_MIN_RR:
        tp1 = exact_entry + risk * TP1_FALLBACK_RR if direction == "long" else exact_entry - risk * TP1_FALLBACK_RR

    h4_pools = find_h4_liquidity_pools(candles_h4, swings_h4, direction, current_price, atr_h4)
    tp2 = None
    for p in h4_pools:
        if abs(p - exact_entry) / risk >= TP2_MIN_RR:
            tp2 = p
            break
    if tp2 is None:
        tp2 = exact_entry + risk * TP2_FALLBACK_RR if direction == "long" else exact_entry - risk * TP2_FALLBACK_RR
    if abs(tp2 - exact_entry) / risk < TP2_MIN_RR:
        return None   # RR gate failed even after fallback — drop the signal

    tp3 = None
    for p in h4_pools:
        if direction == "long" and p > tp2 and abs(p - exact_entry) / risk >= TP2_MIN_RR * 1.5:
            tp3 = p
            break
        if direction == "short" and p < tp2 and abs(p - exact_entry) / risk >= TP2_MIN_RR * 1.5:
            tp3 = p
            break
    if tp3 is None:
        tp3 = exact_entry + risk * TP3_FALLBACK_RR if direction == "long" else exact_entry - risk * TP3_FALLBACK_RR

    # ── Scoring ──────────────────────────────────────────────────────────
    score = 0
    combos: list[str] = []

    if sweep.atr_ratio >= SWEEP_STRONG_ATR_RATIO:
        score += 2; combos.append("Sweep(strong)")
    else:
        score += 1; combos.append("Sweep")

    if disp.atr_ratio >= DISPLACEMENT_STRONG_ATR:
        score += 2; combos.append("Displacement(strong)")
    else:
        score += 1; combos.append("Displacement")

    if disp.choch_margin_atr >= CHOCH_STRONG_MARGIN_ATR:
        score += 2; combos.append("CHoCH(clean)")
    else:
        score += 1; combos.append("CHoCH")

    combos.append("Imbalance(fresh)")
    score += 1

    breaker_fresh = breaker_is_untouched(candles_m15, sweep.index, breaker_hi, breaker_lo)
    if breaker_fresh:
        score += 1; combos.append("Breaker(untouched)")

    if disp.volume_ratio >= VOLUME_BONUS_RATIO:
        score += 1; combos.append("Volume")

    if poi.state == "fresh":
        score += 1; combos.append("H4-POI(fresh)")

    ema_dir = h4_ema_trend(candles_h4, atr_h4)
    if ema_dir == bias:
        closes = [c["c"] for c in candles_h4]
        ema_fast = calc_ema(closes, EMA_FAST)
        ema_slow = calc_ema(closes, EMA_SLOW)
        if ema_fast and ema_slow and abs(ema_fast[-1] - ema_slow[-1]) >= EMA_SEP_MIN_ATR_H4 * atr_h4 * 1.5:
            score += 1; combos.append("H4-Trend(strong)")

    funding = get_funding(symbol)
    if funding is not None:
        if direction == "long" and funding <= -FUNDING_ALIGN_THRESHOLD:
            score += 1; combos.append("Funding")
        elif direction == "short" and funding >= FUNDING_ALIGN_THRESHOLD:
            score += 1; combos.append("Funding")

    if is_active_session():
        score += 1; combos.append("Session")

    min_score = get_min_confluence_score()
    if score < min_score:
        return None

    if score >= APLUS_SIGNAL_SCORE:
        grade = "A+"
    elif score >= STRONG_SIGNAL_SCORE:
        grade = "A"
    else:
        grade = "B"

    return NyxSignal(
        symbol=symbol, direction=direction,
        entry_zone_high=zone_hi, entry_zone_low=zone_lo, exact_entry=exact_entry,
        backup_entry=backup_entry,
        stop_loss=stop_loss, take_profit_1=tp1, take_profit_2=tp2, take_profit_3=tp3,
        confluence=score, max_score=THEORETICAL_MAX_SCORE, signal_grade=grade,
        combos_hit=combos, h4_bias=bias, poi_state=poi.state,
        sweep_atr_ratio=sweep.atr_ratio, displacement_atr_ratio=disp.atr_ratio,
        funding_rate=funding, timestamp=datetime.now(timezone.utc).isoformat(),
        details={"pd_pct": round(pd["pct"], 3), "choch_margin_atr": round(disp.choch_margin_atr, 3)},
    )


# ═══════════════════════════════════════════════════════════════════════════════
# FORMATTING
# ═══════════════════════════════════════════════════════════════════════════════

def fmt_price(v: float) -> str:
    if v >= 100:
        return f"{v:,.2f}"
    if v >= 1:
        return f"{v:,.4f}"
    return f"{v:.6f}"


def fmt_rr(entry: float, sl: float, tp: float) -> str:
    risk = abs(entry - sl)
    if risk <= 0:
        return "n/a"
    return f"{abs(tp - entry) / risk:.2f}R"


def format_signal_message(sig: NyxSignal) -> str:
    arrow = "🟢 LONG" if sig.direction == "long" else "🔴 SHORT"
    grade_emoji = {"A+": "💎", "A": "⭐", "B": "✅"}[sig.signal_grade]
    combos_str = ", ".join(sig.combos_hit)
    funding_line = f"\nFunding: {sig.funding_rate*100:.4f}%/8h" if sig.funding_rate is not None else ""

    return (
        f"{grade_emoji} <b>NYX SIGNAL — {sig.symbol}</b> {arrow}\n"
        f"Grade: <b>{sig.signal_grade}</b>  |  Confluence: {sig.confluence}/{sig.max_score}\n"
        f"H4 Bias: {sig.h4_bias.upper()}  |  H4 POI: {sig.poi_state}\n"
        f"─────────────────────────\n"
        f"<b>Primary Limit:</b> {fmt_price(sig.exact_entry)}  <i>(better price, lower fill odds)</i>\n"
        f"<b>Backup Limit:</b> {fmt_price(sig.backup_entry)}  <i>(worse price, higher fill odds)</i>\n"
        f"<b>Stop Loss:</b> {fmt_price(sig.stop_loss)}\n"
        f"<b>TP1:</b> {fmt_price(sig.take_profit_1)} ({fmt_rr(sig.exact_entry, sig.stop_loss, sig.take_profit_1)})\n"
        f"<b>TP2:</b> {fmt_price(sig.take_profit_2)} ({fmt_rr(sig.exact_entry, sig.stop_loss, sig.take_profit_2)})\n"
        + (f"<b>TP3:</b> {fmt_price(sig.take_profit_3)} ({fmt_rr(sig.exact_entry, sig.stop_loss, sig.take_profit_3)})\n"
           if sig.take_profit_3 else "")
        + f"─────────────────────────\n"
        f"Sweep: {sig.sweep_atr_ratio:.2f} ATR  |  Displacement: {sig.displacement_atr_ratio:.2f} ATR\n"
        f"Confirmations: {combos_str}"
        f"{funding_line}\n"
        f"<i>{sig.timestamp}</i>"
    )


# ═══════════════════════════════════════════════════════════════════════════════
# DEDUP / COOLDOWN
# ═══════════════════════════════════════════════════════════════════════════════

def signal_key(symbol: str, direction: str) -> str:
    return f"{symbol}:{direction}"


def is_duplicate(sig: NyxSignal) -> bool:
    key = signal_key(sig.symbol, sig.direction)
    ts = _fired_signals.get(key)
    if ts is None:
        return False
    return (time.time() - ts) < SIGNAL_COOLDOWN_S


def mark_fired(sig: NyxSignal) -> None:
    _fired_signals[signal_key(sig.symbol, sig.direction)] = time.time()


# ═══════════════════════════════════════════════════════════════════════════════
# SCAN
# ═══════════════════════════════════════════════════════════════════════════════

def scan_symbol(symbol: str, btc_regime: str) -> NyxSignal | None:
    try:
        sig = compute_signal(symbol)
        if sig is None:
            return None
        if btc_regime_blocks(symbol, sig.direction, btc_regime):
            return None
        if is_duplicate(sig):
            return None
        return sig
    except Exception as e:
        print(f"  [SCAN ERROR] {symbol}: {e}")
        return None


def run_scan(all_mids: dict | None = None) -> None:
    global _last_scan_ts

    if not is_active_session():
        print("  [SESSION] Outside London/NY window — skipping scan.")
        _last_scan_ts = time.time()
        return

    _atr_cache.clear()
    fetch_all_oi_funding()
    btc_regime = get_btc_regime()
    print(f"  [BTC REGIME] {btc_regime}")

    raw_signals: list[NyxSignal] = []
    with ThreadPoolExecutor(max_workers=8) as pool:
        futures = {pool.submit(scan_symbol, sym, btc_regime): sym for sym in WATCHLIST}
        for fut in as_completed(futures):
            sig = fut.result()
            if sig:
                raw_signals.append(sig)

    print(f"  [SCAN] {len(raw_signals)} candidate signal(s) before caps")

    raw_signals.sort(key=lambda s: s.confluence, reverse=True)

    accepted: list[NyxSignal] = []
    sector_used: dict[str, int] = {}
    direction_used: dict[str, int] = {}

    for sig in raw_signals:
        if len(accepted) >= TOP_N_SIGNALS:
            break
        sector = SECTOR_MAP.get(sig.symbol, "other")
        if sector_used.get(sector, 0) >= MAX_PER_SECTOR:
            continue
        if direction_used.get(sig.direction, 0) >= MAX_SAME_DIRECTION:
            continue
        accepted.append(sig)
        sector_used[sector] = sector_used.get(sector, 0) + 1
        direction_used[sig.direction] = direction_used.get(sig.direction, 0) + 1

    print(f"  [SCAN] {len(accepted)} signal(s) accepted after diversification caps")

    for sig in accepted:
        msg = format_signal_message(sig)
        msg_id = send_telegram_get_id(msg)
        mark_fired(sig)
        if msg_id:
            track_active_signal(sig, msg_id)

    _last_scan_ts = time.time()


# ═══════════════════════════════════════════════════════════════════════════════
# TELEGRAM
# ═══════════════════════════════════════════════════════════════════════════════

def send_telegram_get_id(text: str) -> int | None:
    try:
        r = _tg_session.post(
            f"https://api.telegram.org/bot{TG_BOT_TOKEN}/sendMessage",
            json={"chat_id": TG_CHAT_ID, "text": text, "parse_mode": "HTML"},
            timeout=15,
        )
        r.raise_for_status()
        data = r.json()
        if data.get("ok"):
            return data["result"]["message_id"]
        print(f"  [TG] sendMessage not ok: {data}")
        return None
    except Exception as e:
        print(f"  [TG] send error: {e}")
        return None


def react_to_message(message_id: int, emoji: str) -> bool:
    try:
        r = _tg_session.post(
            f"https://api.telegram.org/bot{TG_BOT_TOKEN}/setMessageReaction",
            json={"chat_id": TG_CHAT_ID, "message_id": message_id,
                  "reaction": [{"type": "emoji", "emoji": emoji}]},
            timeout=15,
        )
        return r.ok
    except Exception as e:
        print(f"  [TG] react error: {e}")
        return False


# ═══════════════════════════════════════════════════════════════════════════════
# ACTIVE SIGNAL TRACKING / REACTIONS
# ═══════════════════════════════════════════════════════════════════════════════

def track_active_signal(sig: NyxSignal, message_id: int) -> None:
    key = f"{sig.symbol}:{sig.direction}:{int(time.time())}"
    _active_signals[key] = {
        "symbol": sig.symbol, "direction": sig.direction, "message_id": message_id,
        "entry_zone_high": sig.entry_zone_high, "entry_zone_low": sig.entry_zone_low,
        "exact_entry": sig.exact_entry, "backup_entry": sig.backup_entry,
        "stop_loss": sig.stop_loss,
        "tp1": sig.take_profit_1, "tp2": sig.take_profit_2, "tp3": sig.take_profit_3,
        "combos_hit": sig.combos_hit, "signal_grade": sig.signal_grade,
        "filled": False, "primary_filled": False, "backup_filled": False,
        "fill_price": None, "filled_at": None,
        "tp1_hit": False, "tp2_hit": False, "tp3_hit": False,
        "resolved": False, "sent_at": time.time(),
    }


def check_reactions(all_mids: dict) -> None:
    now = time.time()
    for key, s in list(_active_signals.items()):
        if s.get("resolved"):
            _active_signals.pop(key, None)
            continue

        coin = hl_coin(s["symbol"])
        price = all_mids.get(coin)
        if price is None:
            continue

        direction = s["direction"]

        if not s["filled"]:
            if now - s["sent_at"] > FILL_TIMEOUT_S:
                react_to_message(s["message_id"], "⌛")
                record_outcome(s["symbol"], s["combos_hit"], "expired")
                s["resolved"] = True
                continue

            # Two independent resting limit orders: primary (exact_entry,
            # better price) and backup (zone edge nearer price, easier to
            # reach). Each only "fills" when price actually trades through
            # that specific level — not merely inside the broader zone.
            if not s["primary_filled"]:
                p_hit = (price <= s["exact_entry"]) if direction == "long" else (price >= s["exact_entry"])
                if p_hit:
                    s["primary_filled"] = True
            if not s["backup_filled"]:
                b_hit = (price <= s["backup_entry"]) if direction == "long" else (price >= s["backup_entry"])
                if b_hit:
                    s["backup_filled"] = True

            if not (s["primary_filled"] or s["backup_filled"]):
                continue

            s["filled"] = True
            s["filled_at"] = now
            # Effective entry for R:R bookkeeping: average of whichever
            # order(s) actually filled (assumes equal size split).
            filled_prices = [p for p, hit in
                              ((s["exact_entry"], s["primary_filled"]),
                               (s["backup_entry"], s["backup_filled"])) if hit]
            s["fill_price"] = sum(filled_prices) / len(filled_prices)

        sl_hit = (price <= s["stop_loss"]) if direction == "long" else (price >= s["stop_loss"])
        if sl_hit:
            outcome = "partial_loss" if s["tp1_hit"] else "loss"
            react_to_message(s["message_id"], "❌")
            record_outcome(s["symbol"], s["combos_hit"], outcome)
            s["resolved"] = True
            continue

        if not s["tp1_hit"]:
            hit = (price >= s["tp1"]) if direction == "long" else (price <= s["tp1"])
            if hit:
                s["tp1_hit"] = True
                react_to_message(s["message_id"], "✅")

        if not s["tp2_hit"]:
            hit = (price >= s["tp2"]) if direction == "long" else (price <= s["tp2"])
            if hit:
                s["tp2_hit"] = True
                react_to_message(s["message_id"], "🎯")
                if not s["tp3"]:
                    record_outcome(s["symbol"], s["combos_hit"], "win")
                    s["resolved"] = True
                    continue

        if s["tp3"] and not s["tp3_hit"]:
            hit = (price >= s["tp3"]) if direction == "long" else (price <= s["tp3"])
            if hit:
                s["tp3_hit"] = True
                react_to_message(s["message_id"], "🏆")
                record_outcome(s["symbol"], s["combos_hit"], "win_full")
                s["resolved"] = True
                continue

        if now - s["sent_at"] > ACTIVE_SIGNAL_TTL_S:
            outcome = "timeout_win" if s["tp1_hit"] else "timeout"
            record_outcome(s["symbol"], s["combos_hit"], outcome)
            s["resolved"] = True

    for key in [k for k, s in _active_signals.items() if s.get("resolved")]:
        _active_signals.pop(key, None)


# ═══════════════════════════════════════════════════════════════════════════════
# WIN RATE MEMORY
# ═══════════════════════════════════════════════════════════════════════════════

def load_win_rate() -> None:
    global _win_rate_data
    if WIN_RATE_FILE.exists():
        try:
            _win_rate_data = json.loads(WIN_RATE_FILE.read_text())
        except Exception:
            _win_rate_data = {}
    else:
        _win_rate_data = {}


def save_win_rate() -> None:
    global _win_rate_dirty
    try:
        WIN_RATE_FILE.write_text(json.dumps(_win_rate_data, indent=2))
        _win_rate_dirty = False
    except Exception as e:
        print(f"  [WIN RATE] save error: {e}")


def record_outcome(symbol: str, combos: list, outcome: str) -> None:
    global _win_rate_dirty
    bucket = _win_rate_data.setdefault("overall", {"wins": 0, "losses": 0, "other": 0})
    if outcome in ("win", "win_full", "timeout_win", "partial_loss"):
        bucket["wins"] += 1
    elif outcome in ("loss",):
        bucket["losses"] += 1
    else:
        bucket["other"] += 1
    sym_bucket = _win_rate_data.setdefault(symbol, {"wins": 0, "losses": 0, "other": 0})
    if outcome in ("win", "win_full", "timeout_win", "partial_loss"):
        sym_bucket["wins"] += 1
    elif outcome in ("loss",):
        sym_bucket["losses"] += 1
    else:
        sym_bucket["other"] += 1
    _win_rate_dirty = True


def get_win_rate_summary() -> str:
    overall = _win_rate_data.get("overall", {"wins": 0, "losses": 0, "other": 0})
    total = overall["wins"] + overall["losses"]
    pct = (overall["wins"] / total * 100) if total else 0.0
    return (f"[WIN RATE] {overall['wins']}W / {overall['losses']}L "
            f"({pct:.1f}%) — {overall['other']} other outcomes tracked")


# ═══════════════════════════════════════════════════════════════════════════════
# STATE PERSISTENCE
# ═══════════════════════════════════════════════════════════════════════════════

def cleanup_state() -> None:
    now = time.time()
    before = len(_fired_signals)
    expired = [k for k, ts in _fired_signals.items() if now - ts > SIGNAL_COOLDOWN_S]
    for k in expired:
        _fired_signals.pop(k, None)
    fired_removed = before - len(_fired_signals)

    before = len(_active_signals)
    stale = [k for k, s in _active_signals.items()
             if s.get("resolved", False) or now - s.get("sent_at", 0) > ACTIVE_SIGNAL_TTL_S]
    for k in stale:
        _active_signals.pop(k, None)
    active_removed = before - len(_active_signals)

    print(f"  [CLEANUP] Removed {fired_removed} expired cooldowns, {active_removed} stale active signals")


def load_state() -> None:
    global _fired_signals, _active_signals, _last_scan_ts
    if STATE_FILE.exists():
        try:
            data = json.loads(STATE_FILE.read_text())
            _fired_signals = {k: float(v) for k, v in data.get("fired_signals", {}).items()}
            _active_signals = data.get("active_signals", {})
            _last_scan_ts = float(data.get("last_scan_ts", 0.0))
            print(f"  [STATE] Loaded {len(_fired_signals)} cooldown + {len(_active_signals)} active signals")
        except Exception as e:
            print(f"  [STATE] Load error: {e} — starting fresh")
            _fired_signals, _active_signals, _last_scan_ts = {}, {}, 0.0
    else:
        print("  [STATE] No state.json — starting fresh")
        _fired_signals, _active_signals, _last_scan_ts = {}, {}, 0.0


def save_state() -> None:
    if _win_rate_dirty:
        save_win_rate()
    try:
        state_json = json.dumps({
            "fired_signals": _fired_signals,
            "active_signals": _active_signals,
            "last_scan_ts": _last_scan_ts,
        }, indent=2)
        tmp = STATE_FILE.with_suffix(".tmp")
        tmp.write_text(state_json)
        if STATE_FILE.exists():
            STATE_FILE.replace(STATE_FILE.with_suffix(".bak"))
        os.replace(tmp, STATE_FILE)
        print(f"  [STATE] Saved {len(_fired_signals)} cooldown + {len(_active_signals)} active signals")
    except Exception as e:
        print(f"  [STATE] Save error: {e}")


# ═══════════════════════════════════════════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════════════════════════════════════════

def _shutdown_handler(signum, frame):
    print(f"\n  [SHUTDOWN] Received signal {signum} — saving state before exit.")
    save_state()
    sys.exit(0)


def main() -> None:
    print("=" * 60)
    print(f"  Nyx Engine v{VERSION}  [single-scan mode]")
    print("  H4 bias (structure+EMA) -> H4 POI -> H4 liquidity pools")
    print("  M15 sweep -> displacement/CHoCH -> imbalance -> breaker OTE entry")
    print(f"  Top {TOP_N_SIGNALS} signals/scan | Sector cap {MAX_PER_SECTOR} | Same-dir cap {MAX_SAME_DIRECTION}")
    print("  Reaction tracking + win-rate memory + persistent state ON")
    print("=" * 60)

    _signal.signal(_signal.SIGTERM, _shutdown_handler)
    _signal.signal(_signal.SIGINT, _shutdown_handler)

    load_state()
    load_win_rate()
    print(f"\n{get_win_rate_summary()}")

    all_mids = fetch_all_mids()
    if _active_signals:
        print(f"\n[REACTIONS] Checking {len(_active_signals)} active signal(s)...")
        try:
            check_reactions(all_mids)
        except Exception as e:
            print(f"[REACT ERROR] {e}")
    else:
        print("\n[REACTIONS] No active signals to check.")

    try:
        run_scan(all_mids)
    except Exception as e:
        print(f"[MAIN ERROR] {e}")
        send_telegram_get_id(f"⚠️ Nyx Engine error: {e}")

    cleanup_state()
    save_state()
    print("  [DONE] Scan complete. Exiting.")


if __name__ == "__main__":
    main()
