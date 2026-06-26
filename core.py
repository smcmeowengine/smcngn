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

# ── MULTI-BAR SWEEP DETECTION (Medium priority upgrade) ──────────────────────
# Look back N bars for a sweep cluster, not just the last closed bar
SWEEP_MULTIBAR_LOOKBACK   = 3   # check last 3 bars for sweep confirmation

# ── WIN RATE MEMORY (Later upgrade) ──────────────────────────────────────────
WIN_RATE_FILE = pathlib.Path("win_rate.json")

# ── SMC PARAMETERS ───────────────────────────────────────────────────────────
OB_LOOKBACK        = 50
OB_MIN_MOVE_ATR    = 1.5
OB_MAX_AGE_BARS    = 40
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
# Max score is now 7 (added Fibonacci layer)
MIN_CONFLUENCE_SCORE  = 5
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
            with _hl_lock:
                elapsed = time.time() - _hl_last_req_ts
                wait    = _hl_min_interval - elapsed
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
            return r.json()
        except Exception:
            if attempt == 4:
                raise
            time.sleep(min(10.0, 0.5 * (2 ** attempt)))
    return None

def current_bar_open_ms(ref_ms: int, interval: str) -> int:
    return (ref_ms // INTERVAL_MS[interval]) * INTERVAL_MS[interval]

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
    return [c for c in candles if c["t"] < end_ms][-n:]


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

def calc_ema(values: list[float], period: int) -> list[float]:
    if len(values) < period:
        return values[:]
    k   = 2.0 / (period + 1)
    out = [sum(values[:period]) / period]
    for v in values[period:]:
        out.append(v * k + out[-1] * (1 - k))
    return [0.0] * (period - 1) + out

# ═══════════════════════════════════════════════════════════════════════════════
# SESSION FILTER  (High priority upgrade)
# ═══════════════════════════════════════════════════════════════════════════════

def is_active_session() -> bool:
    """
    Return True if current UTC hour falls inside London or New York sessions.
    London : 07:00–12:00 UTC
    New York: 13:00–20:00 UTC
    """
    if not SESSION_FILTER_ENABLED:
        return True
    hour = datetime.now(timezone.utc).hour
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
    return (all(candles[i-k]["h"] <= h for k in range(1, n+1)) and
            all(candles[i+k]["h"] <= h for k in range(1, n+1)))

def is_swing_low(candles: list[dict], i: int, n: int) -> bool:
    if i < n or i >= len(candles) - n:
        return False
    l = candles[i]["l"]
    return (all(candles[i-k]["l"] >= l for k in range(1, n+1)) and
            all(candles[i+k]["l"] >= l for k in range(1, n+1)))


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
    lb     = min(FIB_SWING_LOOKBACK, n - 4)
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
        tol  = rng * FIB_TOLERANCE_PCT * 3   # generous tolerance for zone overlap
        if dist < nearest_dist:
            nearest_dist  = dist
            nearest_name  = name
            nearest_level = lvl

    # Is the entry zone sitting inside the golden zone (0.618–0.786)?
    golden_low  = fibs["0.786"]  # lower price = higher retracement for long
    golden_high = fibs["0.618"]
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
    if len(candles_4h) < 55:
        return "neutral"
    closes = [c["c"] for c in candles_4h]
    ema21  = calc_ema(closes, 21)
    ema50  = calc_ema(closes, 50)
    cur    = closes[-1]
    e21, e50 = ema21[-1], ema50[-1]
    if cur > e21 > e50 and ema21[-1] > ema21[-3] and ema50[-1] > ema50[-3]:
        return "bull"
    if cur < e21 < e50 and ema21[-1] < ema21[-3] and ema50[-1] < ema50[-3]:
        return "bear"
    return "neutral"

def find_order_blocks(candles: list[dict], timeframe: str,
                      atr: float, bias: str) -> list[OrderBlock]:
    obs = []
    n   = len(candles)
    for i in range(n - min(OB_LOOKBACK, n - 2), n - 2):
        cur = candles[i]
        if bias in ("bull", "neutral") and cur["c"] < cur["o"]:
            move_up = max(candles[j]["h"] for j in range(i+1, min(i+4, n))) - cur["h"]
            if move_up >= atr * OB_MIN_MOVE_ATR:
                obs.append(OrderBlock(cur["h"], cur["l"], "bull", i, timeframe))
        if bias in ("bear", "neutral") and cur["c"] > cur["o"]:
            move_dn = cur["l"] - min(candles[j]["l"] for j in range(i+1, min(i+4, n)))
            if move_dn >= atr * OB_MIN_MOVE_ATR:
                obs.append(OrderBlock(cur["h"], cur["l"], "bear", i, timeframe))

    cur_price = candles[-1]["c"]
    last_idx  = len(candles) - 1
    valid = []
    for ob in obs:
        if last_idx - ob.bar_index > OB_MAX_AGE_BARS:
            continue
        if ob.direction == "bull" and cur_price < ob.price_low:
            continue
        if ob.direction == "bear" and cur_price > ob.price_high:
            continue
        valid.append(ob)
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
    lookback  = candles[-(MSB_LOOKBACK):-1]
    nb        = MSB_SWING_BARS
    if direction == "long":
        highs = [c["h"] for i, c in enumerate(lookback)
                 if nb <= i <= len(lookback) - nb - 1 and is_swing_high(lookback, i, nb)]
        if not highs:
            return False
        return cur_close > max(highs[-3:] if len(highs) >= 3 else highs)
    else:
        lows = [c["l"] for i, c in enumerate(lookback)
                if nb <= i <= len(lookback) - nb - 1 and is_swing_low(lookback, i, nb)]
        if not lows:
            return False
        return cur_close < min(lows[-3:] if len(lows) >= 3 else lows)


# ═══════════════════════════════════════════════════════════════════════════════
# COMBO 2 — LIQUIDITY SWEEP
# ═══════════════════════════════════════════════════════════════════════════════

def find_equal_levels(candles: list[dict], direction: str) -> list[float]:
    window = candles[max(0, len(candles) - SWEEP_LOOKBACK):]
    levels = []
    if direction == "long":
        lows = [c["l"] for c in window]
        for i in range(len(lows) - 1):
            for j in range(i + 2, len(lows)):
                if abs(lows[i] - lows[j]) / max(lows[i], 1e-9) <= EQUAL_HL_TOLERANCE:
                    levels.append((lows[i] + lows[j]) / 2)
    else:
        highs = [c["h"] for c in window]
        for i in range(len(highs) - 1):
            for j in range(i + 2, len(highs)):
                if abs(highs[i] - highs[j]) / max(highs[i], 1e-9) <= EQUAL_HL_TOLERANCE:
                    levels.append((highs[i] + highs[j]) / 2)
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

    prior  = candles_1h[:-SWEEP_MULTIBAR_LOOKBACK - 1]
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
        # Enter at upper 33% of zone (closer to current price, less slippage risk)
        price = entry_zone_low + zone_size * 0.67
    else:
        # Enter at lower 33% of zone
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

    atr_4h  = calc_atr(candles_4h)
    atr_1h  = calc_atr(candles_1h)
    atr_15m = calc_atr(candles_15m)
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

    # ── Gate (pre-Fib) ───────────────────────────────────────────────────────
    if score < MIN_CONFLUENCE_SCORE:
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
            sl_base = max(sl_base, fib.fib_786 + atr_4h * 0.2)
        stop_loss = sl_base

    # ── Take Profit (TP1 conservative, TP2 full target) ──────────────────────
    if direction == "long":
        risk      = exact_entry - stop_loss
        tp1       = exact_entry + risk * 2.0     # 1:2 R:R minimum
        highs_4h  = [c["h"] for c in candles_4h[-40:] if c["h"] > cur_p]
        tp2       = min(highs_4h) if highs_4h else exact_entry + risk * 4.0
        if tp2 < tp1:
            tp2 = exact_entry + risk * 3.0
    else:
        risk      = stop_loss - exact_entry
        tp1       = exact_entry - risk * 2.0
        lows_4h   = [c["l"] for c in candles_4h[-40:] if c["l"] < cur_p]
        tp2       = max(lows_4h) if lows_4h else exact_entry - risk * 4.0
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

def send_telegram(text: str) -> None:
    url = f"https://api.telegram.org/bot{TG_BOT_TOKEN}/sendMessage"
    for attempt in range(3):
        try:
            r = requests.post(url, json={"chat_id": TG_CHAT_ID, "text": text,
                                          "parse_mode": "HTML"}, timeout=10)
            r.raise_for_status()
            return
        except Exception as e:
            if attempt == 2:
                print(f"[TG ERROR] {e}")
            time.sleep(2)

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
        golden_tag = "  ← golden zone" if f.in_golden_zone else ""
        fib_section = (
            f"\n<b>Fibonacci (4H)</b>\n"
            f"  0.382 → <code>{fmt_price(f.fib_382)}</code>\n"
            f"  0.500 → <code>{fmt_price(f.fib_50)}</code>\n"
            f"  0.618 → <code>{fmt_price(f.fib_618)}</code>{golden_tag}\n"
            f"  0.786 → <code>{fmt_price(f.fib_786)}</code>{golden_tag}\n"
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
        c1h  = get_candles(symbol, "1h",  N_1H)
        c15m = get_candles(symbol, "15m", N_15M)
        if len(c4h) < 60 or len(c1h) < 60 or len(c15m) < 60:
            return None

        # ── Volatility Filter ─────────────────────────────────────────────────
        # If the current 15M ATR is > 3× its 20-period average, price is in a
        # news spike or erratic expansion — skip to avoid unreliable signals.
        if len(c15m) >= 21:
            current_atr = calc_atr(c15m[-2:] + [c15m[-1]], period=1)   # single-bar TR
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


def run_scan() -> None:
    print(f"\n[SCAN] {datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M UTC')} "
          f"— {len(WATCHLIST)} symbols")

    # ── Session Filter (High priority upgrade) ────────────────────────────────
    if SESSION_FILTER_ENABLED and not is_active_session():
        hour = datetime.now(timezone.utc).hour
        last_fired = max(_fired_signals.values(), default=0)
        hours_since_signal = (time.time() - last_fired) / 3600
        if hours_since_signal < 8.0:
            print(f"  [SESSION] Outside London/NY hours (UTC hour={hour}) — scan skipped "
                  f"(last signal {hours_since_signal:.1f}h ago).")
            return
        print(f"  [SESSION] Outside London/NY hours but {hours_since_signal:.1f}h since last signal "
              f"— running emergency scan.")

    # ── BTC Regime (Medium priority upgrade) — fetch once for whole scan ─────
    btc_bear = btc_regime_blocks_long()
    if btc_bear:
        print("  [BTC REGIME] Bear market detected — altcoin LONGS will be blocked.")

    signals = []
    for symbol in WATCHLIST:
        sig = scan_symbol(symbol)
        if sig:
            # BTC regime: block altcoin longs (allow BTC itself through)
            if btc_bear and sig.direction == "long" and symbol != BTC_SYMBOL:
                print(f"  [BTC REGIME] {symbol} LONG blocked — BTC bear regime")
                continue
            if not is_duplicate(sig):
                signals.append(sig)
                print(f"  ✅ {symbol} {sig.direction.upper()} | {sig.signal_grade} "
                      f"| {sig.confluence}/8 | {sig.combos_hit}")
        else:
            print(f"  —  {symbol} no signal")
        time.sleep(0.25)

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

    # ── Fetch current prices in one batch call ───────────────────────────────
    all_mids = fetch_all_mids()

    # ── Pre-send staleness filters ────────────────────────────────────────────
    # MAX_ENTRY_DIST_PCT : drop signals whose entry zone is too far from price
    # (predictive is fine, but >3% away rarely fills within the 2h window)
    MAX_ENTRY_DIST_PCT = 2.5

    print(f"\n  [TOP {TOP_N_SIGNALS}] Sending best signals:")
    for sig in final:
        coin      = hl_coin(sig.symbol)
        cur_price = all_mids.get(coin)

        if cur_price is not None:
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


def get_mid_price(symbol: str) -> float | None:
    """Fetch current mid price from Hyperliquid."""
    try:
        raw = hl_post({"type": "allMids"})
        if raw:
            coin = hl_coin(symbol)
            val  = raw.get(coin)
            if val:
                return float(val)
    except Exception as e:
        print(f"  [PRICE ERROR] {symbol}: {e}")
    return None


def check_reactions() -> None:
    """
    For every active (unresolved) signal, fetch current price and:

    Phase 1 — Waiting for entry zone touch:
      Price must touch the entry zone before TP/SL monitoring begins.

    Phase 2 — Trade active:
      🔥  TP1 hit
      🏆  TP2 hit (full winner)
      😭  SL hit before TP1 (loss) or after TP1 (partial — still resolves)
    """
    now     = time.time()
    to_drop = []

    # Fetch all prices in one API call instead of one call per signal
    all_mids = fetch_all_mids()

    for key, s in _active_signals.items():
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

        direction  = s["direction"]
        entry      = s["exact_entry"]
        zone_high  = s["entry_zone_high"]
        zone_low   = s["entry_zone_low"]
        sl         = s["stop_loss"]
        tp1        = s["take_profit_1"]
        tp2        = s["take_profit_2"]
        msg_id     = s["message_id"]

        # ── Phase 1: Check if price has touched the entry zone ───────────────
        if not s["entered"]:

            # Entry expiration — zone not touched within 2 hours → delete and drop silently
            # Not a win or loss, cooldown cleared so symbol can signal again
            if now - s["sent_at"] > ENTRY_EXPIRY_S:
                print(f"  [REACT] {key} — entry expired (zone not touched in 2h), deleting message")
                delete_message(msg_id)
                _fired_signals.pop(key, None)   # clear cooldown
                s["resolved"] = True
                to_drop.append(key)
                continue

            if direction == "long":
                in_zone      = price <= zone_high
                past_sl      = price <= sl
                tp1_pre_entry = price >= tp1   # price ran up to TP1 before dropping into zone
            else:
                in_zone      = price >= zone_low
                past_sl      = price >= sl
                tp1_pre_entry = price <= tp1   # price fell to TP1 before rising into zone

            # ── Pre-entry SL hit: price blew through zone AND past SL ────────
            # e.g. long: zone 50-55, sl 47 — price drops straight to 46
            # e.g. short: zone 60-65, sl 68 — price spikes straight to 69
            if in_zone and past_sl:
                print(f"  [REACT] {key} — SL hit before entry zone filled "
                      f"({fmt_price(price)}) — reacting 😢")
                react_to_message(msg_id, "😢")
                record_outcome(s["symbol"], s.get("combos_hit", []), "missed")
                _fired_signals.pop(key, None)   # clear cooldown so symbol can signal again
                s["resolved"] = True
                to_drop.append(key)
                continue

            # ── Pre-entry TP1 hit: price moved in our favor without filling ──
            # e.g. long: zone 50-55, tp1 57 — price jumps straight to 57+
            # e.g. short: zone 60-65, tp1 58 — price drops straight to 58
            elif tp1_pre_entry and not in_zone:
                print(f"  [REACT] {key} — TP1 hit before entry zone filled "
                      f"({fmt_price(price)}) — reacting 😢")
                react_to_message(msg_id, "😢")
                record_outcome(s["symbol"], s.get("combos_hit", []), "missed")
                _fired_signals.pop(key, None)   # clear cooldown so symbol can signal again
                s["resolved"] = True
                to_drop.append(key)
                continue

            elif in_zone:
                s["entered"] = True
                print(f"  [REACT] {key} — entry zone touched at {fmt_price(price)} "
                      f"(zone: {fmt_price(zone_low)}–{fmt_price(zone_high)})")
            else:
                print(f"  [REACT WAIT] {key} | price={fmt_price(price)} "
                      f"| waiting for zone {fmt_price(zone_low)}–{fmt_price(zone_high)}")
                continue   # zone not touched yet

        # ── Phase 2: Monitor TP / SL ──────────────────────────────────────────
        print(f"  [REACT CHECK] {key} | price={fmt_price(price)} "
              f"| sl={fmt_price(sl)} tp1={fmt_price(tp1)} tp2={fmt_price(tp2)}")

        if direction == "long":
            sl_hit  = price <= sl
            tp1_hit = price >= tp1
            tp2_hit = price >= tp2
        else:
            sl_hit  = price >= sl
            tp1_hit = price <= tp1
            tp2_hit = price <= tp2

        if tp2_hit:
            if not s["tp1_hit"]:
                react_to_message(msg_id, "🔥")
                s["tp1_hit"] = True
            react_to_message(msg_id, "🏆")
            record_outcome(s["symbol"], s.get("combos_hit", []), "win")
            s["resolved"] = True
            to_drop.append(key)

        elif sl_hit:
            if not s["tp1_hit"]:
                # Clean loss — SL hit before TP1
                react_to_message(msg_id, "😭")
                record_outcome(s["symbol"], s.get("combos_hit", []), "loss")
            else:
                # TP1 was already hit, SL hit after — partial win, still resolve
                react_to_message(msg_id, "😭")
                record_outcome(s["symbol"], s.get("combos_hit", []), "tp1")
            s["resolved"] = True
            to_drop.append(key)

        elif tp1_hit and not s["tp1_hit"]:
            react_to_message(msg_id, "🔥")
            record_outcome(s["symbol"], s.get("combos_hit", []), "tp1")
            s["tp1_hit"] = True

        time.sleep(0.2)

    for key in to_drop:
        _active_signals.pop(key, None)


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

_win_rate_data: dict = {"by_symbol": {}, "by_combo": {}, "total": {"wins": 0, "losses": 0, "tp1s": 0}}


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
    outcome: "win"    (TP2 hit)
             "tp1"    (TP1 hit, not TP2)
             "loss"   (SL hit after entry)
             "missed" (SL or TP1 hit before entry zone was ever filled — 😢)
    """
    combo_key = "+".join(sorted(combos)) if combos else "unknown"

    for bucket, key in [("by_symbol", symbol), ("by_combo", combo_key)]:
        if key not in _win_rate_data[bucket]:
            _win_rate_data[bucket][key] = {"wins": 0, "losses": 0, "tp1s": 0, "missed": 0}
        entry = _win_rate_data[bucket][key]
        if outcome == "win":
            entry["wins"] += 1
        elif outcome == "loss":
            entry["losses"] += 1
        elif outcome == "tp1":
            entry["tp1s"] += 1
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
    elif outcome == "missed":
        t.setdefault("missed", 0)
        t["missed"] += 1

    total_trades = t["wins"] + t["losses"]
    wr = (t["wins"] / total_trades * 100) if total_trades else 0
    missed = t.get("missed", 0)
    print(f"  [WIN RATE] {symbol} → {outcome.upper()} | "
          f"Overall: {t['wins']}W / {t['losses']}L = {wr:.1f}% WR | Missed: {missed}")
    save_win_rate()


def get_win_rate_summary() -> str:
    """Return a short human-readable win rate summary for Telegram."""
    t = _win_rate_data.get("total", {})
    wins, losses = t.get("wins", 0), t.get("losses", 0)
    tp1s         = t.get("tp1s", 0)
    missed       = t.get("missed", 0)
    total        = wins + losses
    if total == 0:
        return "No closed trades yet."
    wr = wins / total * 100
    lines = [f"📊 Win rate: {wins}W / {losses}L ({wr:.1f}%) | TP1 partials: {tp1s} | 😢 Missed entries: {missed}"]
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
    global _fired_signals, _active_signals
    if STATE_FILE.exists():
        try:
            data            = json.loads(STATE_FILE.read_text())
            _fired_signals  = {k: float(v)
                               for k, v in data.get("fired_signals", {}).items()}
            _active_signals = data.get("active_signals", {})
            print(f"  [STATE] Loaded {len(_fired_signals)} cooldown + "
                  f"{len(_active_signals)} active signals")
        except Exception as e:
            print(f"  [STATE] Load error: {e} — starting fresh")
            _fired_signals  = {}
            _active_signals = {}
    else:
        print("  [STATE] No state.json — starting fresh")
        _fired_signals  = {}
        _active_signals = {}


def save_state() -> None:
    cleanup_state()   # prune before writing
    try:
        STATE_FILE.write_text(json.dumps({
            "fired_signals":  _fired_signals,
            "active_signals": _active_signals,
        }, indent=2))
        print(f"  [STATE] Saved {len(_fired_signals)} cooldown + "
              f"{len(_active_signals)} active signals")
    except Exception as e:
        print(f"  [STATE] Save error: {e}")


# ═══════════════════════════════════════════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════════════════════════════════════════

def main() -> None:
    print("=" * 60)
    print("  SMC Signal Engine v4.0  [single-scan mode]")
    print("  Combo 1 (HTF OB+FVG+MSB) + Combo 2 (Sweep+OB+FVG)")
    print("  + Fibonacci Confluence (0.382 / 0.5 / 0.618 / 0.786)")
    print(f"  Top {TOP_N_SIGNALS} signals per scan | Reaction tracking ON")
    print("  Upgrades: Session filter | Volume gate | BTC regime")
    print("            TP2 1:3 gate | Multi-bar sweep | Win rate memory")
    print("  Timeframes: 1D (macro bias) / 4H / 1H / 15M")
    print("=" * 60)

    load_state()
    load_win_rate()

    # ── Print win rate summary ───────────────────────────────────────────────
    print(f"\n{get_win_rate_summary()}")

    # ── Step 1: Check reactions on previously sent signals ───────────────────
    if _active_signals:
        print(f"\n[REACTIONS] Checking {len(_active_signals)} active signal(s)...")
        try:
            check_reactions()
        except Exception as e:
            print(f"[REACT ERROR] {e}")
    else:
        print("\n[REACTIONS] No active signals to check.")

    # ── Step 2: Run new scan ─────────────────────────────────────────────────
    try:
        run_scan()
    except Exception as e:
        print(f"[MAIN ERROR] {e}")
        send_telegram(f"⚠️ SMC Engine error: {e}")

    save_state()
    print("  [DONE] Scan complete. Exiting.")


if __name__ == "__main__":
    main()
