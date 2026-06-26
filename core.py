"""
SMC Signal Engine — Combo 1 + Combo 2 + Fibonacci Confluence
=============================================================
Combo 1 : HTF OB (4H) + FVG + MSB
Combo 2 : Liquidity Sweep + OB + FVG
Combo 3 : Fibonacci 0.5 / 0.618 / 0.786 confluence layer

Timeframes : 1D (macro bias) → 4H (bias) → 1H (zone refinement) → 15M (entry trigger)
Exchange   : Hyperliquid (same API as original bot)
Alerts     : Telegram (HTML)

Signals are PREDICTIVE — exact limit entry price set BEFORE price arrives.
"""

import os, time, math, threading, requests, random, json, pathlib
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

# ── WATCHLIST ─────────────────────────────────────────────────────────────────
WATCHLIST = [
    "BTCUSDT", "ETHUSDT", "HYPEUSDT", "ZECUSDT", "NEARUSDT",
    "ONDOUSDT", "SUIUSDT", "PENGUUSDT", "BNBUSDT", "SOLUSDT",
    "TRXUSDT", "BCHUSDT", "DOGEUSDT", "ADAUSDT", "DOTUSDT",
    "TAOUSDT", "AVAXUSDT", "LINKUSDT", "AAVEUSDT", "XRPUSDT",
    "XLMUSDT", "UNIUSDT", "LTCUSDT", "APTUSDT", "PENDLEUSDT",
]

# ── SCAN CONFIG ───────────────────────────────────────────────────────────────
SCAN_INTERVAL_S = 60 * 15   # Every 15 minutes (aligns with candle close)
N_15M           = 200
N_1H            = 150
N_4H            = 100
N_1D            = 60        # 60 daily candles (~2 months) — plenty for bias

# ── SESSION FILTER (High priority upgrade) ────────────────────────────────────
# Only trade during London (07:00–12:00 UTC) and New York (13:00–20:00 UTC)
SESSION_FILTER_ENABLED = True
LONDON_OPEN_H  = 7
LONDON_CLOSE_H = 12
NY_OPEN_H      = 13
NY_CLOSE_H     = 20

# IMP-07: 12:00–13:00 UTC is a low-liquidity London→NY transition window.
# Scans during this hour are suppressed unconditionally (even the emergency scan bypass).
DEAD_ZONE_START_H = 12
DEAD_ZONE_END_H   = 13

# ── VOLUME CONFIRMATION (High priority upgrade) ───────────────────────────────
# Require sweep candle volume > N× average volume to filter fake sweeps
VOLUME_GATE_ENABLED     = True
VOLUME_GATE_MULTIPLIER  = 1.4   # sweep volume must be > 1.4× the 20-bar avg

# ── BTC REGIME FILTER (Medium priority upgrade) ───────────────────────────────
# Block altcoin longs when BTC is in a confirmed bear regime
BTC_REGIME_FILTER_ENABLED = True
BTC_SYMBOL                = "BTCUSDT"
BTC_BEAR_EMA_FAST         = 21
BTC_BEAR_EMA_SLOW         = 50

# ── MINIMUM TP2 R:R GATE (Medium priority upgrade) ───────────────────────────
# Drop signals whose TP2 reward-to-risk is below 1:3
TP2_MIN_RR                = 2.5

# ── ENTRY ZONE PROXIMITY GATE ─────────────────────────────────────────────────
# Drop signals where the entry zone midpoint is more than N× ATR_15m away from
# current price. Zones too far away will almost never fill within the 2h expiry.
ENTRY_ZONE_MAX_ATR_DISTANCE = 2.0   # tune up to loosen, down to tighten

# ── ENTRY ZONE % DISTANCE GATE (run_scan) ─────────────────────────────────────
# Second, independent proximity gate applied later in run_scan(): drop signals
# whose entry zone top/bottom is more than this % away from current price.
# Units differ from ENTRY_ZONE_MAX_ATR_DISTANCE above (% vs ATR multiples) —
# both gates are applied at different stages; a signal must pass both.
MAX_ENTRY_DIST_PCT = 2.5   # max % distance from current price to entry zone top/bottom

# ── MULTI-BAR SWEEP DETECTION (Medium priority upgrade) ──────────────────────
# Look back N bars for a sweep cluster, not just the last closed bar
SWEEP_MULTIBAR_LOOKBACK   = 3   # check last 3 bars for sweep confirmation

# ── WIN RATE MEMORY (Later upgrade) ──────────────────────────────────────────
WIN_RATE_FILE = pathlib.Path("win_rate.json")

# ── SMC PARAMETERS ───────────────────────────────────────────────────────────
OB_LOOKBACK        = 50
OB_MIN_MOVE_ATR    = 1.5
OB_MAX_AGE_BARS    = 40
OB_IMPULSE_LOOKFORWARD = 8   # IMP-08: bars to look ahead for impulse move (was hardcoded 3)
FVG_MIN_SIZE_ATR   = 0.3
FVG_MAX_AGE_BARS   = 30
SWEEP_LOOKBACK     = 30
EQUAL_HL_TOLERANCE = 0.002
MSB_LOOKBACK       = 20
MSB_SWING_BARS     = 3
ATR_LEN            = 14

# ── FIBONACCI CONFIG ─────────────────────────────────────────────────────────
# Key retracement levels (golden zone = 0.618–0.786)
FIB_LEVELS        = [0.382, 0.5, 0.618, 0.786]
FIB_GOLDEN_LOW    = 0.618
FIB_GOLDEN_HIGH   = 0.786
FIB_TOLERANCE_PCT = 0.005   # 0.5% tolerance for "at a fib level"
FIB_SWING_LOOKBACK = 50     # Bars to find the last major swing for fib draw

# ── CONFLUENCE SCORING ───────────────────────────────────────────────────────
# Max score is 8: 6 base factors + 1 Fib confluence + 1 Fib golden zone bonus
MIN_CONFLUENCE_SCORE  = 6
STRONG_SIGNAL_SCORE   = 5
APLUS_SIGNAL_SCORE    = 6

# ── INTERVAL MAP ─────────────────────────────────────────────────────────────
INTERVAL_MS = {
    "15m": 15 * 60 * 1000,
    "1h":  60 * 60 * 1000,
    "4h":  4  * 60 * 60 * 1000,
    "1d":  24 * 60 * 60 * 1000,
}

# ── RATE LIMIT ────────────────────────────────────────────────────────────────
_hl_lock         = threading.Lock()
_hl_last_req_ts  = 0.0
_hl_min_interval = 0.2
_hl_session      = requests.Session()

# ── 4H CANDLE CACHE ───────────────────────────────────────────────────────────
# 4H candles only close every 4 hours; caching them for 60 min per scan run
# cuts API calls from 75 → ~50 (saves one round-trip per symbol).
_candle_cache: dict[str, dict] = {}   # key: symbol → {"candles": [...], "ts": float}
_CANDLE_CACHE_TTL_S = 60 * 60         # 60-minute TTL (well within a 4H close)

# ── 1D CANDLE CACHE ───────────────────────────────────────────────────────────
# Daily candles close once per day; safe to cache for 4–6 hours.
# Stored separately so the TTL can differ from the 4H cache.
_candle_cache_1d: dict[str, dict] = {}
_CANDLE_CACHE_1D_TTL_S = 60 * 60 * 4  # 4-hour TTL

# ── 1H CANDLE CACHE (PERF-05B) ────────────────────────────────────────────────
# 1H candles are currently fetched fresh per symbol. Since the 1H bias doesn't
# change between 15-minute scans, caching them within each scan run halves API
# calls for multi-timeframe analysis (~25 fewer calls per scan).
_candle_cache_1h: dict[str, dict] = {}
_CANDLE_CACHE_1H_TTL_S = 60 * 15  # 15-minute TTL — aligns with scan interval

# ── PER-RUN ATR CACHE (PERF-02) ───────────────────────────────────────────────
# ATR is recomputed from scratch on every call and called 3× per symbol per
# scan (4H, 1H, 15M). Cache by (symbol, timeframe) within each scan run.
# Cleared at the top of run_scan() so results are never stale.
_atr_cache: dict[str, float] = {}


# ═══════════════════════════════════════════════════════════════════════════════
# DATA STRUCTURES
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class OrderBlock:
    price_high: float
    price_low:  float
    direction:  str       # "bull" | "bear"
    bar_index:  int
    timeframe:  str

@dataclass
class FairValueGap:
    gap_high:  float
    gap_low:   float
    direction: str
    bar_index: int
    timeframe: str

@dataclass
class FibResult:
    swing_high:    float
    swing_low:     float
    fib_382:       float
    fib_50:        float
    fib_618:       float
    fib_786:       float
    nearest_level: float
    nearest_name:  str
    in_golden_zone: bool   # price inside 0.618–0.786
    direction:     str     # which side the fib is drawn toward

@dataclass
class SMCSignal:
    symbol:          str
    direction:       str        # "long" | "short"
    entry_zone_high: float
    entry_zone_low:  float
    exact_entry:     float      # precise limit order price
    stop_loss:       float
    take_profit_1:   float      # TP1 — conservative (1:2)
    take_profit_2:   float      # TP2 — full target (next liquidity)
    confluence:      int        # Score out of 7
    signal_grade:    str        # "A+" | "A" | "B"
    combos_hit:      list = field(default_factory=list)
    fib:             FibResult | None = None
    details:         dict = field(default_factory=dict)
    timestamp:       str = ""


# ═══════════════════════════════════════════════════════════════════════════════
# HYPERLIQUID API
# ═══════════════════════════════════════════════════════════════════════════════

def hl_coin(symbol: str) -> str:
    return symbol.replace("USDT", "")

def hl_post(payload: dict):
    global _hl_last_req_ts, _hl_min_interval
    for attempt in range(5):
        try:
            # BUG-09 fix: claim the next rate-limit slot atomically, *inside* the
            # lock, before releasing it. With the old code the wait-check and the
            # timestamp update were two separate lock acquisitions with the actual
            # request in between — under ThreadPoolExecutor (PERF-05A) every worker
            # thread could pass the "is it time yet?" check before any of them had
            # recorded a request, defeating the rate limit entirely. Sleeping while
            # still holding the lock forces threads to queue up and serialize their
            # request *starts* exactly _hl_min_interval apart, while the request
            # itself still runs outside the lock so I/O overlaps across threads.
            with _hl_lock:
                elapsed = time.time() - _hl_last_req_ts
                wait    = _hl_min_interval - elapsed
                if wait > 0:
                    time.sleep(wait)
                _hl_last_req_ts = time.time()   # reserve slot before unlocking

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
    return None

def current_bar_open_ms(ref_ms: int, interval: str) -> int:
    return (ref_ms // INTERVAL_MS[interval]) * INTERVAL_MS[interval]

def filter_valid_candles(candles: list[dict]) -> list[dict]:
    """IMP-02: Remove flat/stale candles where h == l (zero True Range). These corrupt ATR."""
    return [c for c in candles if c["h"] > c["l"]]


def get_candles(symbol: str, interval: str, n: int) -> list[dict]:
    iv_ms    = INTERVAL_MS[interval]
    ref_ms   = int(time.time() * 1000)
    end_ms   = current_bar_open_ms(ref_ms, interval)
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
    return filter_valid_candles(valid)   # IMP-02: strip flat/stale candles (h == l)


def get_candles_4h_cached(symbol: str) -> list[dict]:
    """
    Return 4H candles from the in-memory cache when fresh (< 60 min old).
    Falls back to a live fetch and populates the cache on miss/expiry.
    This avoids fetching the same 4H data 25 times per scan run.
    """
    entry = _candle_cache.get(symbol)
    if entry and (time.time() - entry["ts"]) < _CANDLE_CACHE_TTL_S:
        return entry["candles"]
    candles = get_candles(symbol, "4h", N_4H)
    _candle_cache[symbol] = {"candles": candles, "ts": time.time()}
    return candles


def get_candles_1d_cached(symbol: str) -> list[dict]:
    """
    Return 1D candles from the in-memory cache when fresh (< 4 hours old).
    Daily candles rarely change during a scan window, so this TTL is generous.
    One fetch per symbol per 4-hour window across all scan runs.
    """
    entry = _candle_cache_1d.get(symbol)
    if entry and (time.time() - entry["ts"]) < _CANDLE_CACHE_1D_TTL_S:
        return entry["candles"]
    candles = get_candles(symbol, "1d", N_1D)
    _candle_cache_1d[symbol] = {"candles": candles, "ts": time.time()}
    return candles


def get_candles_1h_cached(symbol: str) -> list[dict]:
    """
    PERF-05B: Return 1H candles from the in-memory cache when fresh (< 15 min).
    1H candles don't change between 15-minute scan cycles; caching them cuts
    ~25 API calls per full-watchlist scan.
    """
    entry = _candle_cache_1h.get(symbol)
    if entry and (time.time() - entry["ts"]) < _CANDLE_CACHE_1H_TTL_S:
        return entry["candles"]
    candles = get_candles(symbol, "1h", N_1H)
    _candle_cache_1h[symbol] = {"candles": candles, "ts": time.time()}
    return candles


# ═══════════════════════════════════════════════════════════════════════════════
# INDICATORS
# ═══════════════════════════════════════════════════════════════════════════════

def calc_atr(candles: list[dict], period: int = ATR_LEN) -> float:
    if len(candles) < period + 1:
        return candles[-1]["h"] - candles[-1]["l"]
    trs = [max(candles[i]["h"] - candles[i]["l"],
               abs(candles[i]["h"] - candles[i-1]["c"]),
               abs(candles[i]["l"] - candles[i-1]["c"]))
           for i in range(1, len(candles))]
    return sum(trs[-period:]) / period

def calc_atr_cached(symbol: str, tf: str, candles: list, period: int = ATR_LEN) -> float:
    """PERF-02: Memoized ATR. Returns cached value within the same scan run."""
    key = f"{symbol}:{tf}"
    if key not in _atr_cache:
        _atr_cache[key] = calc_atr(candles, period)
    return _atr_cache[key]


def calc_ema(values: list[float], period: int) -> list[float]:
    # BUG-17: returns only computed values (no zero-padding); callers use [-1], [-3] etc.
    if len(values) < period:
        return values[:]
    k   = 2.0 / (period + 1)
    out = [sum(values[:period]) / period]
    for v in values[period:]:
        out.append(v * k + out[-1] * (1 - k))
    return out   # no zero-padding

# ═══════════════════════════════════════════════════════════════════════════════
# SESSION FILTER  (High priority upgrade)
# ═══════════════════════════════════════════════════════════════════════════════

def is_active_session() -> bool:
    """
    Return True if current UTC hour falls inside London or New York sessions.
    London : 07:00–12:00 UTC
    New York: 13:00–20:00 UTC
    IMP-07: 12:00–13:00 UTC dead zone is always excluded (not even emergency-bypassed).
    """
    if not SESSION_FILTER_ENABLED:
        return True
    hour = datetime.now(timezone.utc).hour
    # IMP-07: dead zone is unconditional — never trade during this window
    if DEAD_ZONE_START_H <= hour < DEAD_ZONE_END_H:
        return False
    in_london = LONDON_OPEN_H <= hour < LONDON_CLOSE_H
    in_ny     = NY_OPEN_H     <= hour < NY_CLOSE_H
    return in_london or in_ny


# ═══════════════════════════════════════════════════════════════════════════════
# BTC REGIME FILTER  (Medium priority upgrade)
# ═══════════════════════════════════════════════════════════════════════════════

_btc_regime_cache: dict = {}   # {"regime": "bull"|"bear"|"neutral", "ts": float}
_BTC_REGIME_TTL_S = 60 * 30   # recheck every 30 minutes


def get_btc_regime() -> str:
    """
    Return "bull", "bear", or "neutral" based on BTC 4H EMA21 vs EMA50.
    Cached for 30 minutes to avoid extra API calls per symbol scan.
    """
    if not BTC_REGIME_FILTER_ENABLED:
        return "bull"   # filter disabled → treat as always bullish (don't block)

    now = time.time()
    if _btc_regime_cache and (now - _btc_regime_cache.get("ts", 0)) < _BTC_REGIME_TTL_S:
        return _btc_regime_cache["regime"]

    try:
        candles = get_candles(BTC_SYMBOL, "4h", 60)
        if len(candles) < BTC_BEAR_EMA_SLOW + 5:
            return "neutral"
        closes  = [c["c"] for c in candles]
        ema_fast = calc_ema(closes, BTC_BEAR_EMA_FAST)
        ema_slow = calc_ema(closes, BTC_BEAR_EMA_SLOW)
        cur      = closes[-1]
        fast, slow = ema_fast[-1], ema_slow[-1]
        if cur > fast > slow:
            regime = "bull"
        elif cur < fast < slow:
            regime = "bear"
        else:
            regime = "neutral"
        _btc_regime_cache["regime"] = regime
        _btc_regime_cache["ts"]     = now
        print(f"  [BTC REGIME] {regime.upper()} | price={fmt_price(cur)} "
              f"EMA{BTC_BEAR_EMA_FAST}={fmt_price(fast)} EMA{BTC_BEAR_EMA_SLOW}={fmt_price(slow)}")
        return regime
    except Exception as e:
        print(f"  [BTC REGIME ERROR] {e}")
        return "neutral"


def btc_regime_blocks_long() -> bool:
    """Return True when BTC is bearish and altcoin longs should be blocked."""
    return BTC_REGIME_FILTER_ENABLED and get_btc_regime() == "bear"


def btc_regime_blocks_short() -> bool:
    """IMP-03: Return True when BTC is strongly bullish and altcoin shorts carry elevated risk."""
    return BTC_REGIME_FILTER_ENABLED and get_btc_regime() == "bull"


# ═══════════════════════════════════════════════════════════════════════════════
# VOLUME CONFIRMATION GATE  (High priority upgrade)
# ═══════════════════════════════════════════════════════════════════════════════

def calc_avg_volume(candles: list[dict], period: int = 20) -> float:
    vols = [c["v"] for c in candles[-period:] if c["v"] > 0]
    return sum(vols) / len(vols) if vols else 0.0


def sweep_has_volume_confirmation(candles: list[dict], sweep_bar_idx: int) -> bool:
    """
    Check that the sweep candle's volume exceeds VOLUME_GATE_MULTIPLIER × 20-bar avg.
    sweep_bar_idx is the absolute index into candles.
    """
    if not VOLUME_GATE_ENABLED:
        return True
    if sweep_bar_idx < 20:
        return True   # not enough history to judge — allow through
    avg_vol  = calc_avg_volume(candles[:sweep_bar_idx], period=20)
    sweep_vol = candles[sweep_bar_idx]["v"]
    confirmed = sweep_vol >= avg_vol * VOLUME_GATE_MULTIPLIER
    if not confirmed:
        print(f"    [VOL GATE] sweep vol={sweep_vol:.2f} < "
              f"{VOLUME_GATE_MULTIPLIER}× avg={avg_vol:.2f} — rejected")
    return confirmed


def is_swing_high(candles: list[dict], i: int, n: int) -> bool:
    if i < n or i >= len(candles) - n:
        return False
    h = candles[i]["h"]
    return (all(candles[i-k]["h"] < h for k in range(1, n+1)) and   # IMP-05: strict < (was <=)
            all(candles[i+k]["h"] < h for k in range(1, n+1)))

def is_swing_low(candles: list[dict], i: int, n: int) -> bool:
    if i < n or i >= len(candles) - n:
        return False
    l = candles[i]["l"]
    return (all(candles[i-k]["l"] > l for k in range(1, n+1)) and   # IMP-05: strict > (was >=)
            all(candles[i+k]["l"] > l for k in range(1, n+1)))


# ═══════════════════════════════════════════════════════════════════════════════
# FIBONACCI CONFLUENCE (Combo 3)
# ═══════════════════════════════════════════════════════════════════════════════

def calc_fib_levels(swing_high: float, swing_low: float) -> dict:
    """Calculate all fib retracement levels from a swing."""
    rng = swing_high - swing_low
    return {
        "0.0":   swing_high,
        "0.236": swing_high - rng * 0.236,
        "0.382": swing_high - rng * 0.382,
        "0.5":   swing_high - rng * 0.5,
        "0.618": swing_high - rng * 0.618,
        "0.786": swing_high - rng * 0.786,
        "1.0":   swing_low,
    }

def find_fib_confluence(candles_4h: list[dict], direction: str,
                         entry_zone_high: float, entry_zone_low: float) -> FibResult | None:
    """
    Find the most recent significant swing on 4H and check if
    the entry zone sits at a key Fibonacci retracement level.

    For LONG: draw fib from swing LOW to swing HIGH (retracement coming down)
    For SHORT: draw fib from swing HIGH to swing LOW (retracement going up)

    Golden zone (0.618–0.786) = highest probability.
    """
    n      = len(candles_4h)
    lb     = min(FIB_SWING_LOOKBACK + 2, n - 2)   # BUG-24: +2 recovers edge bars excluded by swing detector's 2-bar side requirement
    window = candles_4h[-(lb):]

    # Find the most recent significant swing pair
    if direction == "long":
        # Need: swing LOW first, then swing HIGH (price moved up, now pulling back)
        swing_l_idx = None
        swing_h_idx = None
        # Find most recent swing high
        for i in range(len(window) - 3, 2, -1):
            if is_swing_high(window, i, 2):
                swing_h_idx = i
                break
        if swing_h_idx is None:
            return None
        # Find swing low BEFORE that swing high
        for i in range(swing_h_idx - 2, 0, -1):
            if is_swing_low(window, i, 2):
                swing_l_idx = i
                break
        if swing_l_idx is None:
            return None

        s_low  = window[swing_l_idx]["l"]
        s_high = window[swing_h_idx]["h"]

    else:  # short
        # Need: swing HIGH first, then swing LOW (price moved down, now pulling back up)
        swing_h_idx = None
        swing_l_idx = None
        for i in range(len(window) - 3, 2, -1):
            if is_swing_low(window, i, 2):
                swing_l_idx = i
                break
        if swing_l_idx is None:
            return None
        for i in range(swing_l_idx - 2, 0, -1):
            if is_swing_high(window, i, 2):
                swing_h_idx = i
                break
        if swing_h_idx is None:
            return None

        s_low  = window[swing_l_idx]["l"]
        s_high = window[swing_h_idx]["h"]

    if s_high <= s_low:
        return None

    rng   = s_high - s_low
    fibs  = calc_fib_levels(s_high, s_low)

    # Entry zone midpoint — this is what we check against fib levels
    zone_mid = (entry_zone_high + entry_zone_low) / 2

    # Check which fib levels the entry zone overlaps
    key_levels = {
        "0.382": fibs["0.382"],
        "0.5":   fibs["0.5"],
        "0.618": fibs["0.618"],
        "0.786": fibs["0.786"],
    }

    nearest_name  = ""
    nearest_level = 0.0
    nearest_dist  = float("inf")

    for name, lvl in key_levels.items():
        dist = abs(zone_mid - lvl)
        tol  = rng * FIB_TOLERANCE_PCT       # BUG-04 fix: removed *3 multiplier; tol is now enforced below
        if dist < tol and dist < nearest_dist:   # gate: zone must be within 0.5% of a fib level
            nearest_dist  = dist
            nearest_name  = name
            nearest_level = lvl

    # Is the entry zone sitting inside the golden zone (0.618–0.786)?
    # BUG-03 fix (corrected): calc_fib_levels() always computes levels as
    # swing_high - rng*ratio, regardless of direction — it is called the
    # same way for both long and short. Since 0.786 > 0.618, fib_786 is
    # ALWAYS numerically lower than fib_618, for both directions. The
    # previous version of this fix incorrectly assumed the short fib
    # formula was inverted, which made golden_low > golden_high for shorts
    # and silently broke in_golden_zone for nearly all SHORT setups —
    # reproducing the original BUG-03 symptom on the opposite branch.
    golden_low  = fibs["0.786"]   # numerically lower, both directions
    golden_high = fibs["0.618"]   # numerically higher, both directions
    in_golden   = (entry_zone_low <= golden_high and entry_zone_high >= golden_low)

    # Only return result if zone is reasonably close to a key fib level
    if nearest_dist > rng * 0.08:   # more than 8% of range away = not a fib confluence
        return None

    return FibResult(
        swing_high=s_high,
        swing_low=s_low,
        fib_382=fibs["0.382"],
        fib_50=fibs["0.5"],
        fib_618=fibs["0.618"],
        fib_786=fibs["0.786"],
        nearest_level=nearest_level,
        nearest_name=nearest_name,
        in_golden_zone=in_golden,
        direction=direction,
    )


# ═══════════════════════════════════════════════════════════════════════════════
# COMBO 1 — HTF BIAS + ORDER BLOCK + FVG + MSB
# ═══════════════════════════════════════════════════════════════════════════════

def get_htf_bias(candles_4h: list[dict]) -> str:
    # BUG-17: calc_ema no longer zero-pads; need enough bars so ema[-3] is valid.
    # With period=50 we get len(closes)-49 EMA values; 55 bars → 6 EMA values → safe.
    if len(candles_4h) < 55:
        return "neutral"
    closes = [c["c"] for c in candles_4h]
    ema21  = calc_ema(closes, 21)
    ema50  = calc_ema(closes, 50)
    if len(ema21) < 3 or len(ema50) < 3:
        return "neutral"
    cur    = closes[-1]
    e21, e50 = ema21[-1], ema50[-1]
    if cur > e21 > e50 and ema21[-1] > ema21[-3] and ema50[-1] > ema50[-3]:
        return "bull"
    if cur < e21 < e50 and ema21[-1] < ema21[-3] and ema50[-1] < ema50[-3]:
        return "bear"
    return "neutral"

def find_order_blocks(candles: list[dict], timeframe: str,
                      atr: float, bias: str) -> list[OrderBlock]:
    # PERF-03: detection and validity filter merged into one pass (halves iterations).
    valid     = []
    n         = len(candles)
    cur_price = candles[-1]["c"]
    last_idx  = n - 1
    start_i   = n - min(OB_LOOKBACK, n - 2)

    for i in range(start_i, n - 2):
        # Age gate — apply before building the OB object to avoid allocation
        if last_idx - i > OB_MAX_AGE_BARS:
            continue

        cur = candles[i]
        if bias in ("bull", "neutral") and cur["c"] < cur["o"]:
            move_up = max(candles[j]["h"] for j in range(i+1, min(i + OB_IMPULSE_LOOKFORWARD + 1, n))) - cur["h"]
            if move_up >= atr * OB_MIN_MOVE_ATR:
                # BUG-10 fix: price must be above zone_high for a bull OB re-test
                if cur_price > cur["h"]:
                    valid.append(OrderBlock(cur["h"], cur["l"], "bull", i, timeframe))

        if bias in ("bear", "neutral") and cur["c"] > cur["o"]:
            move_dn = cur["l"] - min(candles[j]["l"] for j in range(i+1, min(i + OB_IMPULSE_LOOKFORWARD + 1, n)))
            if move_dn >= atr * OB_MIN_MOVE_ATR:
                # BUG-10 fix: price must be below zone_low for a bear OB re-test
                if cur_price < cur["l"]:
                    valid.append(OrderBlock(cur["h"], cur["l"], "bear", i, timeframe))

    return valid

def find_fvgs(candles: list[dict], timeframe: str, atr: float) -> list[FairValueGap]:
    fvgs  = []
    n     = len(candles)
    cur_p = candles[-1]["c"]
    for i in range(max(0, n - FVG_MAX_AGE_BARS - 2), n - 2):
        c1, c3 = candles[i], candles[i+2]
        if c3["l"] > c1["h"] and (c3["l"] - c1["h"]) >= atr * FVG_MIN_SIZE_ATR:
            if cur_p > c1["h"]:
                fvgs.append(FairValueGap(c3["l"], c1["h"], "bull", i+1, timeframe))
        if c3["h"] < c1["l"] and (c1["l"] - c3["h"]) >= atr * FVG_MIN_SIZE_ATR:
            if cur_p < c1["l"]:
                fvgs.append(FairValueGap(c1["l"], c3["h"], "bear", i+1, timeframe))
    return fvgs

def detect_msb(candles: list[dict], direction: str) -> bool:
    n = len(candles)
    if n < MSB_LOOKBACK + MSB_SWING_BARS:
        return False
    cur_close = candles[-1]["c"]
    lookback  = candles[-(MSB_LOOKBACK):]
    nb        = MSB_SWING_BARS
    if direction == "long":
        highs = [c["h"] for i, c in enumerate(lookback)
                 if nb <= i <= len(lookback) - nb - 2 and is_swing_high(lookback, i, nb)]
        if not highs:
            return False
        return cur_close > max(highs[-3:] if len(highs) >= 3 else highs)
    else:
        lows = [c["l"] for i, c in enumerate(lookback)
                if nb <= i <= len(lookback) - nb - 2 and is_swing_low(lookback, i, nb)]
        if not lows:
            return False
        return cur_close < min(lows[-3:] if len(lows) >= 3 else lows)


# ═══════════════════════════════════════════════════════════════════════════════
# COMBO 2 — LIQUIDITY SWEEP
# ═══════════════════════════════════════════════════════════════════════════════

def find_equal_levels(candles: list[dict], direction: str) -> list[float]:
    # PERF-04: O(n²) replaced with sort + O(n) adjacent scan.
    # Sorting guarantees any pair within EQUAL_HL_TOLERANCE must be adjacent
    # in the sorted array, so a single linear pass suffices.
    # Complexity: O(n log n) vs O(n²) — future-proofs for larger SWEEP_LOOKBACK.
    window = candles[max(0, len(candles) - SWEEP_LOOKBACK):]
    values = sorted([c["l"] for c in window] if direction == "long"
                    else [c["h"] for c in window])
    levels = []
    for i in range(len(values) - 1):
        a, b = values[i], values[i + 1]
        if abs(a - b) / max(a, 1e-9) <= EQUAL_HL_TOLERANCE:
            levels.append((a + b) / 2)
    return sorted(set(round(l, 8) for l in levels))

def detect_liquidity_sweep(candles_1h: list[dict], direction: str) -> dict | None:
    """
    Detect a liquidity sweep on the 1H timeframe.

    Multi-bar sweep detection (Medium upgrade): check the last SWEEP_MULTIBAR_LOOKBACK
    closed bars, not just the most recent one. This catches sweeps that closed 1-2
    bars ago and prevents missed signals.

    Volume confirmation gate (High upgrade): the sweep candle's volume must be at
    least VOLUME_GATE_MULTIPLIER × the 20-bar average volume. Low-volume wicks
    into equal lows/highs are fake sweeps — we filter them out here.
    """
    if len(candles_1h) < SWEEP_LOOKBACK + 2:
        return None

    prior  = candles_1h[:-SWEEP_MULTIBAR_LOOKBACK]   # BUG-25: exclude only the sweep-check bars (was -SWEEP_MULTIBAR_LOOKBACK - 1, which excluded 4 bars)
    levels = find_equal_levels(prior, direction)
    if not levels:
        return None

    # Check the last SWEEP_MULTIBAR_LOOKBACK bars (most recent first)
    n = len(candles_1h)
    for offset in range(1, SWEEP_MULTIBAR_LOOKBACK + 1):
        bar_idx = n - offset
        if bar_idx < 20:
            continue
        bar = candles_1h[bar_idx]

        if direction == "long":
            for lvl in levels:
                if bar["l"] < lvl and bar["c"] > lvl:
                    # Volume gate
                    if not sweep_has_volume_confirmation(candles_1h, bar_idx):
                        continue
                    return {"level": lvl,
                            "wick_depth": lvl - bar["l"],
                            "direction": "long",
                            "sweep_bar": bar_idx,
                            "bars_ago": offset}
        else:
            for lvl in levels:
                if bar["h"] > lvl and bar["c"] < lvl:
                    if not sweep_has_volume_confirmation(candles_1h, bar_idx):
                        continue
                    return {"level": lvl,
                            "wick_height": bar["h"] - lvl,
                            "direction": "short",
                            "sweep_bar": bar_idx,
                            "bars_ago": offset}
    return None


# ═══════════════════════════════════════════════════════════════════════════════
# EXACT ENTRY PRICE LOGIC
# ═══════════════════════════════════════════════════════════════════════════════

def compute_exact_entry(direction: str,
                         entry_zone_high: float,
                         entry_zone_low: float,
                         fib: FibResult | None,
                         sweep: dict | None,
                         atr_15m: float) -> tuple[float, str]:
    """
    Compute a single precise limit order price within the entry zone.

    Priority logic:
    1. If Fibonacci golden zone overlaps → use the 0.618 level (strongest)
    2. If 0.5 Fib is inside zone → use it
    3. If liquidity sweep occurred → use 50% of the entry zone (midpoint)
    4. Default → upper 30% of zone for longs, lower 30% for shorts
       (enter conservatively, leave room for wick)

    Returns (exact_price, reason_string)
    """
    zone_mid  = (entry_zone_high + entry_zone_low) / 2
    zone_size = entry_zone_high - entry_zone_low

    # Priority 1: Fib golden zone (0.618)
    if fib and fib.in_golden_zone:
        lvl = fib.fib_618
        if entry_zone_low <= lvl <= entry_zone_high:
            return round(lvl, 8), f"Fib 0.618 = {fmt_price(lvl)}"

    # Priority 2: Any fib level inside the zone
    if fib:
        for name, lvl in [("0.618", fib.fib_618), ("0.786", fib.fib_786),
                          ("0.5",   fib.fib_50),  ("0.382", fib.fib_382)]:
            if entry_zone_low <= lvl <= entry_zone_high:
                return round(lvl, 8), f"Fib {name} = {fmt_price(lvl)}"

    # Priority 3: Sweep level if inside zone
    if sweep and entry_zone_low <= sweep["level"] <= entry_zone_high:
        return round(sweep["level"], 8), f"Sweep level = {fmt_price(sweep['level'])}"

    # Priority 4: Conservative zone placement
    if direction == "long":
        # Enter at 67th percentile of zone (upper third) — IMP-06: was labelled "upper 30%" but 0.67 = upper third
        price = entry_zone_low + zone_size * 0.67
    else:
        # Enter at 33rd percentile of zone (lower third)
        price = entry_zone_high - zone_size * 0.67

    return round(price, 8), "Zone midpoint (conservative)"


# ═══════════════════════════════════════════════════════════════════════════════
# MASTER SIGNAL ENGINE
# ═══════════════════════════════════════════════════════════════════════════════

def compute_smc_signal(symbol: str,
                        candles_15m: list[dict],
                        candles_1h:  list[dict],
                        candles_4h:  list[dict],
                        candles_1d:  list[dict]) -> SMCSignal | None:
    """
    Full Combo 1 + Combo 2 + Fibonacci confluence engine.

    Scoring (max 7):
      +1  HTF 4H bias confirmed
      +1  4H Order Block (approaching zone)
      +1  4H or 1H Fair Value Gap
      +1  1H Liquidity Sweep
      +1  15M Market Structure Break
      +1  15M OB / FVG (precision entry layer)
      +1  Fibonacci confluence (0.382 / 0.5 / 0.618 / 0.786)
              → +2 if in golden zone (0.618–0.786)  [upgrades score]
    """
    if len(candles_4h) < 60 or len(candles_1h) < 60 or len(candles_15m) < 60:
        return None
    # BUG-20: explicit 1D validation distinguishes "insufficient data" from "neutral bias"
    if len(candles_1d) < 55:
        print(f"[{symbol}] 1D candles insufficient ({len(candles_1d)} bars) — skipping bias")

    atr_4h  = calc_atr_cached(symbol, "4h",  candles_4h)   # PERF-02
    atr_1h  = calc_atr_cached(symbol, "1h",  candles_1h)   # PERF-02
    atr_15m = calc_atr_cached(symbol, "15m", candles_15m)  # PERF-02
    cur_p   = candles_15m[-1]["c"]

    # ── Step 1: HTF Bias ─────────────────────────────────────────────────────
    bias = get_htf_bias(candles_4h)
    if bias == "neutral":
        return None
    direction = "long" if bias == "bull" else "short"

    # ── Step 1b: 1D Bias Alignment Filter ───────────────────────────────────
    # Only trade with the daily trend.  If 4H is bullish but 1D is bearish
    # (or vice-versa) the setup is counter-trend — skip entirely.
    bias_1d = get_htf_bias(candles_1d) if len(candles_1d) >= 55 else "neutral"
    if bias_1d != "neutral" and bias_1d != bias:
        return None   # 4H and 1D disagree — skip

    score = 1
    combos = ["HTF_BIAS"]
    details: dict = {"htf_bias": bias, "bias_1d": bias_1d}

    # ── Step 2: 4H Order Block ───────────────────────────────────────────────
    obs_4h  = find_order_blocks(candles_4h, "4h", atr_4h, bias)
    near_ob = None
    if direction == "long":
        candidates = [ob for ob in obs_4h if ob.direction == "bull" and ob.price_high < cur_p]
        if candidates:
            near_ob = max(candidates, key=lambda x: x.price_high)
    else:
        candidates = [ob for ob in obs_4h if ob.direction == "bear" and ob.price_low > cur_p]
        if candidates:
            near_ob = min(candidates, key=lambda x: x.price_low)
    if near_ob:
        score += 1
        combos.append("4H_OB")
        details["4h_ob"] = {"high": near_ob.price_high, "low": near_ob.price_low}

    # ── Step 3: FVG (4H or 1H) ─────────────────────────────────────────────
    fvgs_4h  = find_fvgs(candles_4h, "4h", atr_4h)
    fvgs_1h  = find_fvgs(candles_1h, "1h", atr_1h)
    all_fvgs = fvgs_4h + fvgs_1h
    near_fvg = None
    if direction == "long":
        bf = [f for f in all_fvgs if f.direction == "bull" and f.gap_high < cur_p]
        if bf:
            near_fvg = max(bf, key=lambda x: x.gap_high)
    else:
        bf = [f for f in all_fvgs if f.direction == "bear" and f.gap_low > cur_p]
        if bf:
            near_fvg = min(bf, key=lambda x: x.gap_low)
    if near_fvg:
        score += 1
        combos.append("FVG")
        details["fvg"] = {"high": near_fvg.gap_high, "low": near_fvg.gap_low,
                          "tf": near_fvg.timeframe}

    # ── Step 4: Liquidity Sweep ──────────────────────────────────────────────
    sweep = detect_liquidity_sweep(candles_1h, direction)
    if sweep:
        score += 1
        combos.append("LIQ_SWEEP")
        details["sweep"] = sweep

    # ── Step 5: 15M MSB ─────────────────────────────────────────────────────
    if detect_msb(candles_15m, direction):
        score += 1
        combos.append("15M_MSB")
        details["msb_15m"] = True

    # ── Step 6: 15M OB / FVG ────────────────────────────────────────────────
    obs_15m  = find_order_blocks(candles_15m, "15m", atr_15m, bias)
    fvgs_15m = find_fvgs(candles_15m, "15m", atr_15m)
    near_ob_15m  = None
    near_fvg_15m = None
    if direction == "long":
        b = [ob for ob in obs_15m if ob.direction == "bull" and ob.price_high < cur_p]
        if b: near_ob_15m = max(b, key=lambda x: x.price_high)
        b = [f for f in fvgs_15m if f.direction == "bull" and f.gap_high < cur_p]
        if b: near_fvg_15m = max(b, key=lambda x: x.gap_high)
    else:
        b = [ob for ob in obs_15m if ob.direction == "bear" and ob.price_low > cur_p]
        if b: near_ob_15m = min(b, key=lambda x: x.price_low)
        b = [f for f in fvgs_15m if f.direction == "bear" and f.gap_low > cur_p]
        if b: near_fvg_15m = min(b, key=lambda x: x.gap_low)
    if near_ob_15m or near_fvg_15m:
        score += 1
        combos.append("15M_OB_FVG")
        if near_ob_15m:
            details["15m_ob"] = {"high": near_ob_15m.price_high, "low": near_ob_15m.price_low}
        if near_fvg_15m:
            details["15m_fvg"] = {"high": near_fvg_15m.gap_high, "low": near_fvg_15m.gap_low}

    # ── Gate (pre-Fib fast exit) ─────────────────────────────────────────────
    # BUG-05 fix: use a loose gate here (3) so clearly weak setups are skipped
    # cheaply, but valid setups that need Fibonacci to reach MIN_CONFLUENCE_SCORE
    # are not discarded prematurely.
    if score < 3:
        return None

    # ── Build Entry Zone ─────────────────────────────────────────────────────
    if near_ob_15m:
        entry_high, entry_low = near_ob_15m.price_high, near_ob_15m.price_low
        entry_src = "15M OB"
    elif near_fvg_15m:
        entry_high, entry_low = near_fvg_15m.gap_high, near_fvg_15m.gap_low
        entry_src = "15M FVG"
    elif near_fvg:
        entry_high, entry_low = near_fvg.gap_high, near_fvg.gap_low
        entry_src = f"{near_fvg.timeframe.upper()} FVG"
    elif near_ob:
        entry_high, entry_low = near_ob.price_high, near_ob.price_low
        entry_src = "4H OB"
    else:
        entry_high = cur_p + atr_15m * 0.3
        entry_low  = cur_p - atr_15m * 0.3
        entry_src  = "ATR zone"
    details["entry_source"] = entry_src

    # ── IMP-01 fix: guard against zero/flat ATR and zero-width or inverted
    # entry zones (e.g. stale candle data where h == l). Without this, a
    # zero-risk signal with TP1 == TP2 == exact_entry can slip through to
    # Telegram with garbage R:R values.
    if atr_15m <= 0:
        print(f"[{symbol}] Skipping — ATR is zero (stale/flat candle data)")
        return None
    if entry_high <= entry_low:
        print(f"[{symbol}] Skipping — entry zone is zero-width or inverted")
        return None

    # ── Step 7: Fibonacci Confluence ─────────────────────────────────────────
    fib = find_fib_confluence(candles_4h, direction, entry_high, entry_low)
    if fib:
        if fib.in_golden_zone:
            score += 2            # Golden zone = double bonus
            combos.append("FIB_GOLDEN")
            details["fib_zone"] = "golden (0.618–0.786)"
        else:
            score += 1
            combos.append("FIB_LEVEL")
            details["fib_zone"] = f"Fib {fib.nearest_name}"
        details["fib_levels"] = {
            "swing_high": fib.swing_high,
            "swing_low":  fib.swing_low,
            "0.382": fib.fib_382,
            "0.5":   fib.fib_50,
            "0.618": fib.fib_618,
            "0.786": fib.fib_786,
        }

    # ── Final confluence gate (after all scoring including Fibonacci) ────────
    # BUG-05 fix: this gate now runs after Fibonacci adds its +1 or +2 points,
    # so setups that rely on Fibonacci to reach MIN_CONFLUENCE_SCORE are no
    # longer incorrectly dropped.
    if score < MIN_CONFLUENCE_SCORE:
        return None

    # ── Exact Entry Price ────────────────────────────────────────────────────
    exact_entry, entry_reason = compute_exact_entry(
        direction, entry_high, entry_low, fib, sweep, atr_15m
    )
    details["exact_entry_reason"] = entry_reason

    # ── Stop Loss ────────────────────────────────────────────────────────────
    if direction == "long":
        sl_base = entry_low - atr_15m * 1.0
        if sweep:
            sl_base = min(sl_base, sweep["level"] - atr_1h * 0.3)
        if fib:
            sl_base = min(sl_base, fib.fib_786 - atr_4h * 0.2)
        stop_loss = sl_base
    else:
        sl_base = entry_high + atr_15m * 1.0
        if sweep:
            sl_base = max(sl_base, sweep["level"] + atr_1h * 0.3)
        if fib:
            # BUG-07 fix: for shorts, SL must be above entry.
            # Only use fib_786 if it is actually above entry_high (valid invalidation).
            # Otherwise fall back to swing_high (the fib 0.0 level = top of the range).
            if fib.fib_786 > entry_high:
                sl_base = max(sl_base, fib.fib_786 + atr_4h * 0.2)
            else:
                sl_base = max(sl_base, fib.swing_high + atr_4h * 0.2)
        stop_loss = sl_base

    # ── Take Profit (TP1 conservative, TP2 full target) ──────────────────────
    if direction == "long":
        risk      = exact_entry - stop_loss
        tp1       = exact_entry + risk * 2.0     # 1:2 R:R minimum
        highs_4h  = [c["h"] for c in candles_4h[-40:] if c["h"] > cur_p]
        tp2       = max(highs_4h) if highs_4h else exact_entry + risk * 4.0  # BUG-01 fix: max = furthest swing high
        if tp2 < tp1:
            tp2 = exact_entry + risk * 3.0
    else:
        risk      = stop_loss - exact_entry
        tp1       = exact_entry - risk * 2.0
        lows_4h   = [c["l"] for c in candles_4h[-40:] if c["l"] < cur_p]
        tp2       = min(lows_4h) if lows_4h else exact_entry - risk * 4.0  # BUG-02 fix: min = furthest swing low
        if tp2 > tp1:
            tp2 = exact_entry - risk * 3.0

    # ── Grade ────────────────────────────────────────────────────────────────
    if score >= APLUS_SIGNAL_SCORE:
        grade = "A+"
    elif score >= STRONG_SIGNAL_SCORE:
        grade = "A"
    else:
        grade = "B"

    ts = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")

    # ── Stale signal gate ────────────────────────────────────────────────────
    # Current price must be between SL and TP1 — if the move has already started
    # (price past TP1) or already stopped out (price past SL), the setup is stale.
    if direction == "long":
        if cur_p >= tp1:
            print(f"  [GATE] {symbol} LONG rejected — price {fmt_price(cur_p)} "
                  f"already at/past TP1 {fmt_price(tp1)}")
            return None
        if cur_p <= stop_loss:
            print(f"  [GATE] {symbol} LONG rejected — price {fmt_price(cur_p)} "
                  f"already at/past SL {fmt_price(stop_loss)}")
            return None
    else:
        if cur_p <= tp1:
            print(f"  [GATE] {symbol} SHORT rejected — price {fmt_price(cur_p)} "
                  f"already at/past TP1 {fmt_price(tp1)}")
            return None
        if cur_p >= stop_loss:
            print(f"  [GATE] {symbol} SHORT rejected — price {fmt_price(cur_p)} "
                  f"already at/past SL {fmt_price(stop_loss)}")
            return None

    # ── Entry zone proximity gate ────────────────────────────────────────────
    # Reject if the entry zone midpoint is too far from current price.
    zone_mid      = (entry_high + entry_low) / 2
    zone_distance = abs(zone_mid - cur_p)
    max_distance  = atr_15m * ENTRY_ZONE_MAX_ATR_DISTANCE
    if zone_distance > max_distance:
        print(f"  [GATE] {symbol} {direction.upper()} rejected — entry zone midpoint "
              f"{fmt_price(zone_mid)} is {zone_distance:.6f} from price {fmt_price(cur_p)} "
              f"(max allowed {max_distance:.6f} = {ENTRY_ZONE_MAX_ATR_DISTANCE}× ATR)")
        return None

    return SMCSignal(
        symbol=symbol,
        direction=direction,
        entry_zone_high=entry_high,
        entry_zone_low=entry_low,
        exact_entry=exact_entry,
        stop_loss=stop_loss,
        take_profit_1=tp1,
        take_profit_2=tp2,
        confluence=score,
        signal_grade=grade,
        combos_hit=combos,
        fib=fib,
        details=details,
        timestamp=ts,
    )


# ═══════════════════════════════════════════════════════════════════════════════
# FORMATTING HELPERS
# ═══════════════════════════════════════════════════════════════════════════════

def fmt_price(v: float) -> str:
    if v >= 1000: return f"{v:,.2f}"
    if v >= 1:    return f"{v:.4f}"
    return f"{v:.6f}"

def fmt_rr(entry: float, sl: float, tp: float, direction: str) -> str:
    risk   = abs(entry - sl)
    reward = abs(tp - entry)
    rr     = reward / risk if risk > 0 else 0
    return f"1 : {rr:.1f}"


# ═══════════════════════════════════════════════════════════════════════════════
# TELEGRAM ALERT
# ═══════════════════════════════════════════════════════════════════════════════

def format_signal_message(sig: SMCSignal) -> str:
    dir_label   = "LONG" if sig.direction == "long" else "SHORT"
    dir_marker  = "▲" if sig.direction == "long" else "▼"

    # Combo labels (no emojis)
    combo_labels = {
        "HTF_BIAS":      "HTF Bias (4H)",
        "4H_OB":         "4H Order Block",
        "FVG":           "FVG (Combo 1)",
        "LIQ_SWEEP":     "Liquidity Sweep (Combo 2)",
        "15M_MSB":       "15M MSB Confirmed",
        "15M_OB_FVG":    "15M OB/FVG Entry",
        "FIB_GOLDEN":    "Fib Golden Zone 0.618–0.786",
        "FIB_LEVEL":     f"Fib Level ({sig.details.get('fib_zone', '')})",
    }
    combo_str = "\n".join("· " + combo_labels.get(c, c) for c in sig.combos_hit)

    # Fibonacci section (compact, no emojis)
    fib_section = ""
    if sig.fib:
        f = sig.fib
        golden_line = (
            f"  🟡 Golden zone: {fmt_price(f.fib_786)}–{fmt_price(f.fib_618)}\n"
            if f.in_golden_zone else ""
        )
        fib_section = (
            f"\n<b>Fibonacci (4H)</b>\n"
            f"  0.382 → <code>{fmt_price(f.fib_382)}</code>\n"
            f"  0.500 → <code>{fmt_price(f.fib_50)}</code>\n"
            f"  0.618 → <code>{fmt_price(f.fib_618)}</code>\n"
            f"  0.786 → <code>{fmt_price(f.fib_786)}</code>\n"
            f"{golden_line}"
        )

    entry_reason = sig.details.get("exact_entry_reason", "")
    entry_src    = sig.details.get("entry_source", "Zone")
    htf_bias     = sig.details.get("htf_bias", "").upper()
    bias_1d      = sig.details.get("bias_1d", "neutral").upper()
    max_score    = 8

    rr1 = fmt_rr(sig.exact_entry, sig.stop_loss, sig.take_profit_1, sig.direction)
    rr2 = fmt_rr(sig.exact_entry, sig.stop_loss, sig.take_profit_2, sig.direction)

    cur_price = sig.details.get("current_price")
    dist_pct  = sig.details.get("entry_dist_pct")
    if cur_price is not None:
        dist_str       = f"  ({dist_pct:.1f}% from entry)" if dist_pct is not None else ""
        cur_price_line = f"Current price: <code>{fmt_price(cur_price)}</code>{dist_str}\n"
    else:
        cur_price_line = ""

    msg = (
        f"<b>{dir_marker} {sig.symbol} — {dir_label}</b>  |  Grade <b>{sig.signal_grade}</b>  |  {sig.confluence}/{max_score}\n"
        f"1D: <b>{bias_1d}</b>  |  4H: <b>{htf_bias}</b>  |  {sig.timestamp}\n"
        f"━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"{cur_price_line}"
        f"\n<b>Entry Zone</b> ({entry_src})\n"
        f"  High: <code>{fmt_price(sig.entry_zone_high)}</code>\n"
        f"  Low:  <code>{fmt_price(sig.entry_zone_low)}</code>\n"
        f"\n<b>Limit Entry: <code>{fmt_price(sig.exact_entry)}</code></b>\n"
        f"  ↳ {entry_reason}\n"
        f"\n<b>Stop Loss:</b>  <code>{fmt_price(sig.stop_loss)}</code>\n"
        f"<b>TP1:</b>        <code>{fmt_price(sig.take_profit_1)}</code>  ({rr1})\n"
        f"<b>TP2:</b>        <code>{fmt_price(sig.take_profit_2)}</code>  ({rr2})\n"
        f"━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"{fib_section}"
        f"\n<i>SMC Signal Engine v4 | Min confluence {MIN_CONFLUENCE_SCORE}/{max_score}</i>\n"
    )
    return msg


# ═══════════════════════════════════════════════════════════════════════════════
# DEDUP
# ═══════════════════════════════════════════════════════════════════════════════

_fired_signals: dict[str, float] = {}
SIGNAL_COOLDOWN_S = 4 * 60 * 60
_last_scan_ts: float = 0.0   # last time run_scan() actually executed a scan (persisted in state.json)

def is_duplicate(sig: SMCSignal) -> bool:
    key = f"{sig.symbol}_{sig.direction}"
    # Block if still an active unresolved signal (regardless of cooldown age)
    active = _active_signals.get(key)
    if active and not active.get("resolved", False):
        age_s = time.time() - active.get("sent_at", 0)
        if age_s < ACTIVE_SIGNAL_TTL_S:
            print(f"  [DEDUP] {key} blocked — trade still active ({age_s/3600:.1f}h old)")
            return True
        else:
            print(f"  [DEDUP] {key} — active signal expired ({age_s/3600:.1f}h), allowing re-signal")
            _active_signals.pop(key, None)
            _fired_signals.pop(key, None)
    # Block if within the 4-hour cooldown window
    last = _fired_signals.get(key, 0)
    return (time.time() - last) < SIGNAL_COOLDOWN_S

def mark_fired(sig: SMCSignal) -> None:
    _fired_signals[f"{sig.symbol}_{sig.direction}"] = time.time()


# ═══════════════════════════════════════════════════════════════════════════════
# SCAN LOOP
# ═══════════════════════════════════════════════════════════════════════════════

def scan_symbol(symbol: str) -> SMCSignal | None:
    try:
        c4h  = get_candles_4h_cached(symbol)   # served from cache after first fetch
        c1d  = get_candles_1d_cached(symbol)   # 1D bias filter — 4-hour cache
        c1h  = get_candles_1h_cached(symbol)   # PERF-05B: cached within scan run
        c15m = get_candles(symbol, "15m", N_15M)
        if len(c4h) < 60 or len(c1h) < 60 or len(c15m) < 60:
            # BUG-20: log which timeframe is insufficient to distinguish from neutral bias
            if len(c4h) < 60:
                print(f"  [{symbol}] 4H candles insufficient ({len(c4h)} bars) — skipping")
            if len(c1h) < 60:
                print(f"  [{symbol}] 1H candles insufficient ({len(c1h)} bars) — skipping")
            if len(c15m) < 60:
                print(f"  [{symbol}] 15M candles insufficient ({len(c15m)} bars) — skipping")
            return None

        # ── Volatility Filter ─────────────────────────────────────────────────
        # If the current 15M ATR is > 3× its 20-period average, price is in a
        # news spike or erratic expansion — skip to avoid unreliable signals.
        if len(c15m) >= 21:
            # Use the True Range of the last bar as "current ATR"
            last = c15m[-1]
            prev = c15m[-2]
            current_atr = max(last["h"] - last["l"],
                              abs(last["h"] - prev["c"]),
                              abs(last["l"] - prev["c"]))
            avg_atr_20 = calc_atr(c15m, period=20)
            if avg_atr_20 > 0 and current_atr > avg_atr_20 * 3.0:
                print(f"  [VOLATILE — skipped] {symbol} | "
                      f"current TR={current_atr:.6f} > 3× avg ATR({avg_atr_20:.6f})")
                return None

        return compute_smc_signal(symbol, c15m, c1h, c4h, c1d)
    except Exception as e:
        print(f"  [SCAN ERROR] {symbol}: {e}")
        return None

TOP_N_SIGNALS = 5   # Only send the best N signals per scan

# Direction cap: max longs / shorts in the final batch (correlation guard)
MAX_SAME_DIRECTION = 2


def fetch_all_mids() -> dict[str, float]:
    """Fetch all mid prices in a single API call. Returns {coin: price}."""
    try:
        raw = hl_post({"type": "allMids"})
        if raw:
            return {k: float(v) for k, v in raw.items() if v}
    except Exception as e:
        print(f"  [MIDS ERROR] {e}")
    return {}


def run_scan(all_mids: dict | None = None) -> None:
    global _last_scan_ts, _atr_cache
    _atr_cache = {}   # PERF-02: clear per-run ATR memoization cache
    print(f"\n[SCAN] {datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M UTC')} "
          f"— {len(WATCHLIST)} symbols")

    # ── Session Filter (High priority upgrade) ────────────────────────────────
    hour = datetime.now(timezone.utc).hour
    # IMP-07: dead zone (12:00–13:00 UTC) is unconditional — skip even emergency scans
    if SESSION_FILTER_ENABLED and DEAD_ZONE_START_H <= hour < DEAD_ZONE_END_H:
        print(f"  [SESSION] Dead zone (UTC hour={hour}, {DEAD_ZONE_START_H}:00–{DEAD_ZONE_END_H}:00) — scan skipped unconditionally.")
        return
    if SESSION_FILTER_ENABLED and not is_active_session():
        hours_since_scan = (time.time() - _last_scan_ts) / 3600
        if hours_since_scan < 8.0:
            print(f"  [SESSION] Outside London/NY hours (UTC hour={hour}) — scan skipped "
                  f"(last scan {hours_since_scan:.1f}h ago).")
            return
        print(f"  [SESSION] Outside London/NY hours but {hours_since_scan:.1f}h since last scan "
              f"— running emergency scan.")

    # Mark scan time now that we've committed to actually scanning.
    _last_scan_ts = time.time()


    # ── BTC Regime (Medium priority upgrade) — fetch once for whole scan ─────
    btc_bear  = btc_regime_blocks_long()
    btc_bull  = btc_regime_blocks_short()   # IMP-03: block altcoin shorts in strong bull regime
    if btc_bear:
        print("  [BTC REGIME] Bear market detected — altcoin LONGS will be blocked.")
    if btc_bull:
        print("  [BTC REGIME] Bull market detected — altcoin SHORTS will be blocked.")

    # PERF-05A: parallelize the per-symbol scan with a thread pool. Each
    # scan_symbol() call is I/O-bound (waiting on HL API responses), so
    # overlapping them collapses scan time from ~60-90s to ~15-20s for 25
    # symbols. The shared rate limit is still enforced centrally in hl_post()
    # (see the BUG-09 fix above) so workers don't exceed _hl_min_interval in
    # aggregate. Candle/ATR caches are plain dicts; concurrent get/set on them
    # is safe under the GIL — a rare double-fetch on a cache miss is the only
    # possible side effect, never corrupted data.
    results = {}
    with ThreadPoolExecutor(max_workers=5) as executor:
        futures = {executor.submit(scan_symbol, sym): sym for sym in WATCHLIST}
        for future in as_completed(futures):
            sym = futures[future]
            try:
                results[sym] = future.result()
            except Exception as e:
                print(f"  [SCAN ERROR] {sym}: {e}")
                results[sym] = None

    # Process results back in WATCHLIST order (not completion order) so that
    # dedup, regime filtering, and logging stay deterministic across runs —
    # only scan_symbol() itself runs concurrently; everything below is
    # single-threaded and mutates global state exactly as before.
    signals = []
    for symbol in WATCHLIST:
        sig = results.get(symbol)
        if sig:
            # BTC regime: block altcoin longs (allow BTC itself through)
            if btc_bear and sig.direction == "long" and symbol != BTC_SYMBOL:
                print(f"  [BTC REGIME] {symbol} LONG blocked — BTC bear regime")
                continue
            # IMP-03: block altcoin shorts when BTC is in a strong bull regime
            if btc_bull and sig.direction == "short" and symbol != BTC_SYMBOL:
                print(f"  [BTC REGIME] {symbol} SHORT blocked — BTC bull regime")
                continue
            if not is_duplicate(sig):
                signals.append(sig)
                print(f"  ✅ {symbol} {sig.direction.upper()} | {sig.signal_grade} "
                      f"| {sig.confluence}/8 | {sig.combos_hit}")
        else:
            print(f"  —  {symbol} no signal")

    # ── Sort by confluence desc ──────────────────────────────────────────────
    signals.sort(key=lambda s: s.confluence, reverse=True)

    # ── R:R Sanity Check — TP1 ≥ 1.5, TP2 ≥ 3.0 (upgraded gate) ────────────
    rr_passed = []
    for sig in signals:
        risk    = abs(sig.exact_entry - sig.stop_loss)
        if risk == 0:
            continue
        rr_tp1  = abs(sig.take_profit_1 - sig.exact_entry) / risk
        rr_tp2  = abs(sig.take_profit_2 - sig.exact_entry) / risk
        if rr_tp1 < 1.5:
            print(f"  [RR FILTER] {sig.symbol} {sig.direction.upper()} dropped "
                  f"— TP1 RR={rr_tp1:.2f} < 1.5")
            continue
        if rr_tp2 < TP2_MIN_RR:
            print(f"  [TP2 RR FILTER] {sig.symbol} {sig.direction.upper()} dropped "
                  f"— TP2 RR={rr_tp2:.2f} < {TP2_MIN_RR} (1:{TP2_MIN_RR:.0f} gate)")
            continue
        rr_passed.append(sig)

    # ── Direction Cap (correlation guard) ────────────────────────────────────
    capped: list[SMCSignal] = []
    long_count = short_count = 0
    for sig in rr_passed:
        if sig.direction == "long":
            if long_count < MAX_SAME_DIRECTION:
                capped.append(sig)
                long_count += 1
            else:
                print(f"  [DIR CAP] {sig.symbol} LONG dropped — "
                      f"already have {long_count} longs in batch")
        else:
            if short_count < MAX_SAME_DIRECTION:
                capped.append(sig)
                short_count += 1
            else:
                print(f"  [DIR CAP] {sig.symbol} SHORT dropped — "
                      f"already have {short_count} shorts in batch")

    # Final top-N slice
    final = capped[:TOP_N_SIGNALS]

    if not final:
        print("  [SCAN] No signals this round.")
        return

    # ── Fetch current prices (reuse from caller if provided, PERF-01) ─────────
    if all_mids is None:
        all_mids = fetch_all_mids()

    # ── Pre-send staleness filters ────────────────────────────────────────────
    # MAX_ENTRY_DIST_PCT : drop signals whose entry zone is too far from price
    # (predictive is fine, but >3% away rarely fills within the 2h window)

    print(f"\n  [TOP {TOP_N_SIGNALS}] Sending best signals:")
    for sig in final:
        coin      = hl_coin(sig.symbol)
        cur_price = all_mids.get(coin)

        # IMP-11: warn and skip when the coin name lookup fails — avoids silently skipping stale-price check
        if cur_price is None:
            print(f"  ⚠️  [{sig.symbol}] WARNING: no mid price found in allMids — skipping stale check")
            # Proceed without staleness validation rather than dropping the signal silently
        elif cur_price is not None:
            dist_pct = abs(cur_price - sig.exact_entry) / cur_price * 100
            sig.details["current_price"]  = cur_price
            sig.details["entry_dist_pct"] = dist_pct

            # ── Guard 1: price already past TP2 or SL ────────────────────────
            if sig.direction == "long":
                already_tp = cur_price >= sig.take_profit_2
                already_sl = cur_price <= sig.stop_loss
            else:
                already_tp = cur_price <= sig.take_profit_2
                already_sl = cur_price >= sig.stop_loss

            if already_tp:
                print(f"  ⛔ STALE-TP {sig.symbol} {sig.direction.upper()} — "
                      f"price {fmt_price(cur_price)} already past TP2 "
                      f"{fmt_price(sig.take_profit_2)} — skipped")
                continue
            if already_sl:
                print(f"  ⛔ STALE-SL {sig.symbol} {sig.direction.upper()} — "
                      f"price {fmt_price(cur_price)} already past SL "
                      f"{fmt_price(sig.stop_loss)} — skipped")
                continue

            # ── Guard 2: price already past the exact entry (limit already missed) ──
            # Being inside the zone is fine — the limit order is still valid.
            # Only skip if price has blown past the exact entry price itself.
            if sig.direction == "long":
                past_exact_entry = cur_price < sig.entry_zone_low
            else:
                past_exact_entry = cur_price > sig.entry_zone_high

            if past_exact_entry:
                if sig.direction == "long":
                    print(f"  ⛔ PAST-ENTRY {sig.symbol} {sig.direction.upper()} — "
                          f"price below entry zone "
                          f"{fmt_price(cur_price)} — skipped")
                else:
                    print(f"  ⛔ PAST-ENTRY {sig.symbol} {sig.direction.upper()} — "
                          f"price above entry zone "
                          f"{fmt_price(cur_price)} — skipped")
                continue

            # ── Guard 3: entry zone too far from current price ────────────────
            if dist_pct > MAX_ENTRY_DIST_PCT:
                print(f"  ⛔ TOO-FAR {sig.symbol} {sig.direction.upper()} — "
                      f"entry {dist_pct:.1f}% away (max {MAX_ENTRY_DIST_PCT}%) — skipped")
                continue

        msg    = format_signal_message(sig)
        msg_id = send_telegram_get_id(msg)
        mark_fired(sig)
        if msg_id:
            track_active_signal(sig, msg_id)
        print(f"  📤 Sent: {sig.symbol} {sig.direction.upper()} "
              f"{sig.signal_grade} | Entry: {fmt_price(sig.exact_entry)} "
              f"| dist: {sig.details.get('entry_dist_pct', 0):.1f}% "
              f"| msg_id: {msg_id}")
        time.sleep(0.5)


# ═══════════════════════════════════════════════════════════════════════════════
# TELEGRAM — send and return message_id
# ═══════════════════════════════════════════════════════════════════════════════

def send_telegram_get_id(text: str) -> int | None:
    """Send a Telegram message and return its message_id."""
    url = f"https://api.telegram.org/bot{TG_BOT_TOKEN}/sendMessage"
    for attempt in range(3):
        try:
            r = requests.post(url, json={"chat_id": TG_CHAT_ID, "text": text,
                                          "parse_mode": "HTML"}, timeout=10)
            r.raise_for_status()
            return r.json().get("result", {}).get("message_id")
        except Exception as e:
            if attempt == 2:
                print(f"[TG ERROR] {e}")
            time.sleep(2)
    return None

def react_to_message(message_id: int, emoji: str) -> bool:
    """
    Send a reaction to an existing Telegram message.
    Uses setMessageReaction (Bot API 7.0+).
    Returns True on success.
    """
    url = f"https://api.telegram.org/bot{TG_BOT_TOKEN}/setMessageReaction"
    try:
        r = requests.post(url, json={
            "chat_id":    TG_CHAT_ID,
            "message_id": message_id,
            "reaction":   [{"type": "emoji", "emoji": emoji}],
            "is_big":     True,
        }, timeout=10)
        data = r.json()
        if not data.get("ok"):
            print(f"  [REACT FAIL] msg {message_id} {emoji}: {data.get('description', 'unknown error')}")
            return False
        print(f"  [REACT] {emoji} → msg {message_id}")
        return True
    except Exception as e:
        print(f"  [REACT ERROR] msg {message_id}: {e}")
        return False

def delete_message(message_id: int) -> bool:
    """Delete a Telegram message (used for expired/invalid signals).
    Returns True on success.
    """
    url = f"https://api.telegram.org/bot{TG_BOT_TOKEN}/deleteMessage"
    try:
        r = requests.post(url, json={
            "chat_id":    TG_CHAT_ID,
            "message_id": message_id,
        }, timeout=10)
        data = r.json()
        if not data.get("ok"):
            print(f"  [DELETE FAIL] msg {message_id}: {data.get('description', 'unknown error')}")
            return False
        print(f"  [DELETE] msg {message_id} removed")
        return True
    except Exception as e:
        print(f"  [DELETE ERROR] msg {message_id}: {e}")
        return False


# ═══════════════════════════════════════════════════════════════════════════════
# ACTIVE SIGNAL TRACKING  (for reaction feature)
# ═══════════════════════════════════════════════════════════════════════════════
#
# _active_signals stores signals that have been sent but not yet resolved.
# Each entry:
#   key   : "{symbol}_{direction}"
#   value : {
#       "symbol", "direction", "exact_entry", "stop_loss",
#       "take_profit_1", "take_profit_2",
#       "message_id",          ← Telegram message to react to
#       "tp1_hit": bool,       ← True once TP1 reacted
#       "resolved": bool,      ← True once SL or TP2 reacted (final)
#       "sent_at": float       ← Unix timestamp
#   }
#
# Signals are removed from tracking after 7 days (max trade duration assumed).

_active_signals: dict[str, dict] = {}
ACTIVE_SIGNAL_TTL_S   = 7 * 24 * 60 * 60   # 7 days  — max trade duration
ENTRY_EXPIRY_S        = 2 * 60 * 60         # 2 hours — if entry not hit, signal expires


def track_active_signal(sig: SMCSignal, message_id: int) -> None:
    key = f"{sig.symbol}_{sig.direction}"
    _active_signals[key] = {
        "symbol":          sig.symbol,
        "direction":       sig.direction,
        "exact_entry":     sig.exact_entry,
        "entry_zone_high": sig.entry_zone_high,
        "entry_zone_low":  sig.entry_zone_low,
        "stop_loss":       sig.stop_loss,
        "take_profit_1":   sig.take_profit_1,
        "take_profit_2":   sig.take_profit_2,
        "combos_hit":      sig.combos_hit,
        "message_id":      message_id,
        "entered":         False,
        "tp1_hit":         False,
        "resolved":        False,
        "sent_at":         time.time(),
    }


def check_reactions(all_mids: dict) -> None:
    """
    For every active (unresolved) signal, check the current mid price against
    entry/TP/SL levels. Accepts the already-batched fetch_all_mids() result
    from the caller (PERF-01) — eliminates N separate API calls (one per active
    signal). Wick-level fills between scans are not detected, only the price
    snapshot at the time this scan runs.

    Phase 1 — Waiting for entry zone touch:
      Entry requires price to actually reach exact_entry (the limit price),
      not just the wider zone_high/zone_low boundary (BUG-22 fix).

    Phase 2 — Trade active:
      🔥  TP1 hit
      🏆  TP2 hit (full winner)
      😭  SL hit after entry
      😢  SL or TP1 hit before entry zone was ever touched (missed entry)
    """
    now     = time.time()
    to_drop = []

    for key, s in list(_active_signals.items()):  # BUG-06: iterate snapshot to prevent mutation-during-iteration
        if s["resolved"]:
            to_drop.append(key)
            continue

        # Expire old signals
        if now - s["sent_at"] > ACTIVE_SIGNAL_TTL_S:
            print(f"  [REACT] {key} expired after 7d — dropping")
            to_drop.append(key)
            continue

        coin  = hl_coin(s["symbol"])
        price = all_mids.get(coin)
        if price is None:
            continue

        direction   = s["direction"]
        zone_high   = s["entry_zone_high"]
        zone_low    = s["entry_zone_low"]
        exact_entry = s["exact_entry"]
        sl          = s["stop_loss"]
        tp1         = s["take_profit_1"]
        tp2         = s["take_profit_2"]
        msg_id      = s["message_id"]

        # IMP-04 fix: avoid a per-signal get_intrabar_range() API call (20+ extra
        # calls/scan with a full watchlist of active signals). Use the already-
        # fetched mid price instead; wick-level fills between scans are rare and
        # debatable anyway for limit orders.
        bar_low = bar_high = price

        print(f"  [REACT] {key} | mid={fmt_price(price)} "
              f"bar=[{fmt_price(bar_low)}–{fmt_price(bar_high)}]")

        # ── Phase 1: Waiting for entry zone touch ─────────────────────────────
        if not s["entered"]:

            # Entry expiration — zone not touched within 2h → delete silently
            if now - s["sent_at"] > ENTRY_EXPIRY_S:
                print(f"  [REACT] {key} — entry expired (zone not touched in 2h), deleting message")
                delete_message(msg_id)
                _fired_signals.pop(key, None)
                s["resolved"] = True
                to_drop.append(key)
                continue

            if direction == "long":
                # BUG-22 fix: a wick to zone_high doesn't guarantee a fill — the
                # limit order sits at exact_entry, which can be well below zone_high.
                in_zone       = bar_low <= exact_entry
                past_sl       = bar_low  <= sl
                tp1_pre_entry = bar_high >= tp1   # bar spiked to TP1 without entering zone
            else:
                # BUG-22 fix: symmetric — short limit fills only once price rises
                # to meet exact_entry, not merely into the zone.
                in_zone       = bar_high >= exact_entry
                past_sl       = bar_high >= sl
                tp1_pre_entry = bar_low  <= tp1   # bar dropped to TP1 without entering zone

            # Pre-entry SL: bar blew through zone AND past SL in same move
            if in_zone and past_sl:
                print(f"  [REACT] {key} — SL hit before entry zone filled — reacting 😢")
                react_to_message(msg_id, "😢")
                record_outcome(s["symbol"], s.get("combos_hit", []), "missed")
                _fired_signals.pop(key, None)
                s["resolved"] = True
                to_drop.append(key)
                continue

            # Pre-entry TP1: bar moved in our favour but zone was never touched
            elif tp1_pre_entry and not in_zone:
                print(f"  [REACT] {key} — TP1 hit before entry zone filled — reacting 😢")
                react_to_message(msg_id, "😢")
                record_outcome(s["symbol"], s.get("combos_hit", []), "missed")
                _fired_signals.pop(key, None)
                s["resolved"] = True
                to_drop.append(key)
                continue

            elif in_zone:
                s["entered"] = True
                print(f"  [REACT] {key} — entry zone touched "
                      f"(zone: {fmt_price(zone_low)}–{fmt_price(zone_high)})")
            else:
                print(f"  [REACT WAIT] {key} | waiting for zone "
                      f"{fmt_price(zone_low)}–{fmt_price(zone_high)}")
                continue

        # ── Phase 2: Monitor TP / SL (intrabar-aware) ─────────────────────────
        print(f"  [REACT CHECK] {key} | sl={fmt_price(sl)} "
              f"tp1={fmt_price(tp1)} tp2={fmt_price(tp2)}")

        if direction == "long":
            sl_hit  = bar_low  <= sl
            tp1_hit = bar_high >= tp1
            tp2_hit = bar_high >= tp2
        else:
            sl_hit  = bar_high >= sl
            tp1_hit = bar_low  <= tp1
            tp2_hit = bar_low  <= tp2

        # Priority: if both TP2 and SL are inside the same bar range,
        # we favour TP2 (price had to pass through TP2 to reach SL on the way back).
        if tp2_hit:
            if not s["tp1_hit"]:
                react_to_message(msg_id, "🔥")
                s["tp1_hit"] = True
            react_to_message(msg_id, "🏆")
            record_outcome(s["symbol"], s.get("combos_hit", []), "win")
            s["resolved"] = True
            to_drop.append(key)

        elif sl_hit and tp1_hit and not s["tp1_hit"]:
            # Both SL and TP1 touched in same bar — favour TP1 hit first
            # (price had to pass TP1 before reversing to SL)
            react_to_message(msg_id, "🔥")
            react_to_message(msg_id, "😭")
            record_outcome(s["symbol"], s.get("combos_hit", []), "tp1")
            s["resolved"] = True
            to_drop.append(key)

        elif sl_hit:
            if not s["tp1_hit"]:
                react_to_message(msg_id, "😭")
                record_outcome(s["symbol"], s.get("combos_hit", []), "loss")
            else:
                react_to_message(msg_id, "😭")
                record_outcome(s["symbol"], s.get("combos_hit", []), "tp1_then_loss")  # BUG-23: distinct from clean tp1
            s["resolved"] = True
            to_drop.append(key)

        elif tp1_hit and not s["tp1_hit"]:
            react_to_message(msg_id, "🔥")
            record_outcome(s["symbol"], s.get("combos_hit", []), "tp1")
            s["tp1_hit"] = True

        time.sleep(0.2)

    for key in to_drop:
        _active_signals.pop(key, None)

    # PERF-06: flush win rate to disk once per check_reactions() call instead of
    # after every individual outcome (avoids N sequential file writes per scan).
    global _win_rate_dirty
    if _win_rate_dirty:
        save_win_rate()
        _win_rate_dirty = False


# ═══════════════════════════════════════════════════════════════════════════════
# WIN RATE MEMORY  (Later upgrade — self-improving system)
# ═══════════════════════════════════════════════════════════════════════════════
#
# Tracks outcomes per symbol and per combo set so the engine can surface which
# setups have the highest historical win rate.  Stored in win_rate.json.
#
# Schema:
#   {
#     "by_symbol": { "BTCUSDT": {"wins": 3, "losses": 1, "tp1s": 2} },
#     "by_combo":  { "HTF_BIAS+4H_OB+FVG": {"wins": 5, "losses": 2} },
#     "total":     {"wins": 8, "losses": 3, "tp1s": 2}
#   }

_win_rate_data: dict = {"by_symbol": {}, "by_combo": {}, "total": {"wins": 0, "losses": 0, "tp1s": 0, "missed": 0}}
_win_rate_dirty: bool = False   # PERF-06: deferred write flag


def load_win_rate() -> None:
    global _win_rate_data
    if WIN_RATE_FILE.exists():
        try:
            _win_rate_data = json.loads(WIN_RATE_FILE.read_text())
            total = _win_rate_data.get("total", {})
            print(f"  [WIN RATE] Loaded — W:{total.get('wins',0)} "
                  f"L:{total.get('losses',0)} TP1:{total.get('tp1s',0)}")
        except Exception as e:
            print(f"  [WIN RATE] Load error: {e} — starting fresh")


def save_win_rate() -> None:
    try:
        WIN_RATE_FILE.write_text(json.dumps(_win_rate_data, indent=2))
    except Exception as e:
        print(f"  [WIN RATE] Save error: {e}")


def record_outcome(symbol: str, combos: list, outcome: str) -> None:
    """
    outcome: "win"          (TP2 hit)
             "tp1"          (TP1 hit, not TP2 — trade still running or closed at TP1)
             "tp1_then_loss" (TP1 hit, then SL hit on residual — BUG-23)
             "loss"         (SL hit after entry, TP1 never reached)
             "missed"       (SL or TP1 hit before entry zone was ever filled — 😢)
    """
    combo_key = "+".join(sorted(combos)) if combos else "unknown"

    for bucket, key in [("by_symbol", symbol), ("by_combo", combo_key)]:
        if key not in _win_rate_data[bucket]:
            _win_rate_data[bucket][key] = {"wins": 0, "losses": 0, "tp1s": 0, "missed": 0, "tp1_then_loss": 0}
        entry = _win_rate_data[bucket][key]
        if outcome == "win":
            entry["wins"] += 1
        elif outcome == "loss":
            entry["losses"] += 1
        elif outcome == "tp1":
            entry["tp1s"] += 1
        elif outcome == "tp1_then_loss":
            entry.setdefault("tp1_then_loss", 0)
            entry["tp1_then_loss"] += 1
        elif outcome == "missed":
            entry.setdefault("missed", 0)
            entry["missed"] += 1

    t = _win_rate_data["total"]
    if outcome == "win":
        t["wins"] += 1
    elif outcome == "loss":
        t["losses"] += 1
    elif outcome == "tp1":
        t["tp1s"] += 1
    elif outcome == "tp1_then_loss":
        t.setdefault("tp1_then_loss", 0)
        t["tp1_then_loss"] += 1
    elif outcome == "missed":
        t.setdefault("missed", 0)
        t["missed"] += 1

    total_trades = t["wins"] + t["losses"]
    wr = (t["wins"] / total_trades * 100) if total_trades else 0
    missed = t.get("missed", 0)
    tp1tl  = t.get("tp1_then_loss", 0)
    print(f"  [WIN RATE] {symbol} → {outcome.upper()} | "
          f"Overall: {t['wins']}W / {t['losses']}L = {wr:.1f}% WR | "
          f"Missed: {missed} | TP1→SL: {tp1tl}")
    global _win_rate_dirty
    _win_rate_dirty = True   # PERF-06: defer write to end of check_reactions()


def get_win_rate_summary() -> str:
    """Return a short human-readable win rate summary for Telegram."""
    t = _win_rate_data.get("total", {})
    wins, losses = t.get("wins", 0), t.get("losses", 0)
    tp1s         = t.get("tp1s", 0)
    tp1tl        = t.get("tp1_then_loss", 0)   # BUG-23: show TP1→SL separately
    missed       = t.get("missed", 0)
    total        = wins + losses
    if total == 0:
        return "No closed trades yet."
    wr = wins / total * 100
    lines = [f"📊 Win rate: {wins}W / {losses}L ({wr:.1f}%) | TP1 partials: {tp1s} | TP1→SL: {tp1tl} | 😢 Missed: {missed}"]
    # Top 3 symbols by win rate (min 2 trades)
    by_sym = _win_rate_data.get("by_symbol", {})
    ranked = [(s, d) for s, d in by_sym.items() if d["wins"] + d["losses"] >= 2]
    ranked.sort(key=lambda x: x[1]["wins"] / (x[1]["wins"] + x[1]["losses"]), reverse=True)
    if ranked:
        lines.append("Top symbols:")
        for sym, d in ranked[:3]:
            n = d["wins"] + d["losses"]
            lines.append(f"  {sym}: {d['wins']}/{n} ({d['wins']/n*100:.0f}%)")
    return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════════════════
# STATE PERSISTENCE
# ═══════════════════════════════════════════════════════════════════════════════

STATE_FILE = pathlib.Path("state.json")


def cleanup_state() -> None:
    """
    Prune stale entries from both dicts before saving.

    fired_signals  — remove entries older than the cooldown window (4h).
                     Once the cooldown has passed the entry serves no purpose.

    active_signals — remove entries that are resolved or have exceeded the
                     7-day TTL. These should already be dropped by
                     check_reactions() but this is a safety net.
    """
    now = time.time()

    # ── fired_signals cleanup ────────────────────────────────────────────────
    before = len(_fired_signals)
    expired_fired = [k for k, ts in _fired_signals.items()
                     if now - ts > SIGNAL_COOLDOWN_S]
    for k in expired_fired:
        _fired_signals.pop(k, None)
    fired_removed = before - len(_fired_signals)

    # ── active_signals cleanup ───────────────────────────────────────────────
    before = len(_active_signals)
    stale_active = [k for k, s in _active_signals.items()
                    if s.get("resolved", False)
                    or now - s.get("sent_at", 0) > ACTIVE_SIGNAL_TTL_S]
    for k in stale_active:
        _active_signals.pop(k, None)
    active_removed = before - len(_active_signals)

    if fired_removed or active_removed:
        print(f"  [CLEANUP] Removed {fired_removed} expired cooldowns, "
              f"{active_removed} stale active signals")
    else:
        print(f"  [CLEANUP] Nothing to clean "
              f"({len(_fired_signals)} cooldowns, {len(_active_signals)} active)")


def load_state() -> None:
    global _fired_signals, _active_signals, _last_scan_ts
    if STATE_FILE.exists():
        try:
            data            = json.loads(STATE_FILE.read_text())
            _fired_signals  = {k: float(v)
                               for k, v in data.get("fired_signals", {}).items()}
            _active_signals = data.get("active_signals", {})
            _last_scan_ts   = float(data.get("last_scan_ts", 0.0))
            print(f"  [STATE] Loaded {len(_fired_signals)} cooldown + "
                  f"{len(_active_signals)} active signals")
        except Exception as e:
            print(f"  [STATE] Load error: {e} — starting fresh")
            _fired_signals  = {}
            _active_signals = {}
            _last_scan_ts   = 0.0
    else:
        print("  [STATE] No state.json — starting fresh")
        _fired_signals  = {}
        _active_signals = {}
        _last_scan_ts   = 0.0


def save_state() -> None:
    # IMP-09: cleanup_state() is no longer called here; call it explicitly once per scan in main()
    try:
        state_json = json.dumps({
            "fired_signals":  _fired_signals,
            "active_signals": _active_signals,
            "last_scan_ts":   _last_scan_ts,
        }, indent=2)

        tmp = STATE_FILE.with_suffix(".tmp")
        tmp.write_text(state_json)

        if STATE_FILE.exists():
            STATE_FILE.replace(STATE_FILE.with_suffix(".bak"))   # keep last known-good copy

        os.replace(tmp, STATE_FILE)   # atomic on POSIX; near-atomic on Windows

        print(f"  [STATE] Saved {len(_fired_signals)} cooldown + "
              f"{len(_active_signals)} active signals")
    except Exception as e:
        print(f"  [STATE] Save error: {e}")


# ═══════════════════════════════════════════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════════════════════════════════════════

def main() -> None:
    print("=" * 60)
    print("  SMC Signal Engine v6.0  [single-scan mode]")
    print("  Combo 1 (HTF OB+FVG+MSB) + Combo 2 (Sweep+OB+FVG)")
    print("  + Fibonacci Confluence (0.382 / 0.5 / 0.618 / 0.786)")
    print(f"  Top {TOP_N_SIGNALS} signals per scan | Reaction tracking ON")
    print("  Upgrades: Session filter | Volume gate | BTC regime")
    print("            TP2 1:3 gate | Multi-bar sweep | Win rate memory")
    print("  Perf: Parallel scan (5 workers) | Candle/ATR caching")
    print("  Timeframes: 1D (macro bias) / 4H / 1H / 15M")
    print("=" * 60)

    load_state()
    load_win_rate()

    # ── Print win rate summary ───────────────────────────────────────────────
    print(f"\n{get_win_rate_summary()}")

    # ── Step 1: Check reactions on previously sent signals ───────────────────
    # PERF-01: fetch all mids once here; pass to both check_reactions and run_scan
    all_mids = fetch_all_mids()
    if _active_signals:
        print(f"\n[REACTIONS] Checking {len(_active_signals)} active signal(s)...")
        try:
            check_reactions(all_mids)
        except Exception as e:
            print(f"[REACT ERROR] {e}")
    else:
        print("\n[REACTIONS] No active signals to check.")

    # ── Step 2: Run new scan ─────────────────────────────────────────────────
    try:
        run_scan(all_mids)
    except Exception as e:
        print(f"[MAIN ERROR] {e}")
        send_telegram_get_id(f"⚠️ SMC Engine error: {e}")  # discard the returned message_id

    cleanup_state()   # IMP-09: called once per scan, not embedded inside save_state()
    save_state()
    print("  [DONE] Scan complete. Exiting.")


if __name__ == "__main__":
    main()
