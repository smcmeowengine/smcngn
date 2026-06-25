"""
SMC Signal Engine — Combo 1 + Combo 2 + Fibonacci Confluence
=============================================================
Combo 1 : HTF OB (4H) + FVG + MSB
Combo 2 : Liquidity Sweep + OB + FVG
Combo 3 : Fibonacci 0.5 / 0.618 / 0.786 confluence layer

Timeframes : 4H (bias) → 1H (zone refinement) → 15M (entry trigger)
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
    "BTCUSDT", "ETHUSDT", "SOLUSDT", "BNBUSDT", "XRPUSDT",
    "ADAUSDT", "AVAXUSDT", "DOGEUSDT", "LINKUSDT", "SUIUSDT",
    "AAVEUSDT", "NEARUSDT", "APTUSDT", "DOTUSDT", "UNIUSDT",
]

# ── SCAN CONFIG ───────────────────────────────────────────────────────────────
SCAN_INTERVAL_S = 60 * 15   # Every 15 minutes (aligns with candle close)
N_15M           = 200
N_1H            = 150
N_4H            = 100

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
MIN_CONFLUENCE_SCORE  = 3
STRONG_SIGNAL_SCORE   = 5
APLUS_SIGNAL_SCORE    = 6

# ── INTERVAL MAP ─────────────────────────────────────────────────────────────
INTERVAL_MS = {
    "15m": 15 * 60 * 1000,
    "1h":  60 * 60 * 1000,
    "4h":  4  * 60 * 60 * 1000,
}

# ── RATE LIMIT ────────────────────────────────────────────────────────────────
_hl_lock         = threading.Lock()
_hl_last_req_ts  = 0.0
_hl_min_interval = 0.2
_hl_session      = requests.Session()


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
    if len(candles_1h) < SWEEP_LOOKBACK + 2:
        return None
    cur   = candles_1h[-1]
    prior = candles_1h[:-2]
    levels = find_equal_levels(prior, direction)
    if not levels:
        return None
    if direction == "long":
        for lvl in levels:
            if cur["l"] < lvl and cur["c"] > lvl:
                return {"level": lvl, "wick_depth": lvl - cur["l"],
                        "direction": "long", "sweep_bar": len(candles_1h) - 1}
    else:
        for lvl in levels:
            if cur["h"] > lvl and cur["c"] < lvl:
                return {"level": lvl, "wick_height": cur["h"] - lvl,
                        "direction": "short", "sweep_bar": len(candles_1h) - 1}
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
                        candles_4h:  list[dict]) -> SMCSignal | None:
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
    score = 1
    combos = ["HTF_BIAS"]
    details: dict = {"htf_bias": bias}

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
    dir_emoji   = "🟢" if sig.direction == "long" else "🔴"
    dir_label   = "▲ LONG" if sig.direction == "long" else "▼ SHORT"
    grade_emoji = {"A+": "🏆", "A": "⭐", "B": "📊"}.get(sig.signal_grade, "📊")

    # Max score is 7 (or 8 with golden zone double)
    max_score = 8
    filled    = "🔵" * min(sig.confluence, max_score)
    empty     = "⚪" * max(0, max_score - sig.confluence)
    conf_bar  = filled + empty

    # Combo labels
    combo_labels = {
        "HTF_BIAS":   "✅ HTF Bias (4H)",
        "4H_OB":      "✅ 4H Order Block",
        "FVG":        "✅ FVG (Combo 1)",
        "LIQ_SWEEP":  "✅ Liquidity Sweep (Combo 2)",
        "15M_MSB":    "✅ 15M MSB Confirmed",
        "15M_OB_FVG": "✅ 15M OB/FVG Entry",
        "FIB_GOLDEN": "✅ Fib Golden Zone 0.618–0.786 🔥",
        "FIB_LEVEL":  f"✅ Fib Level ({sig.details.get('fib_zone', '')})",
    }
    combo_str = "\n".join(combo_labels.get(c, c) for c in sig.combos_hit)

    # Fibonacci section
    fib_section = ""
    if sig.fib:
        f = sig.fib
        golden_tag = "  🔥 GOLDEN ZONE" if f.in_golden_zone else ""
        fib_section = (
            f"\n<b>📐 Fibonacci (4H Swing)</b>\n"
            f"  Swing High: <code>{fmt_price(f.swing_high)}</code>\n"
            f"  Swing Low:  <code>{fmt_price(f.swing_low)}</code>\n"
            f"  0.382 → <code>{fmt_price(f.fib_382)}</code>\n"
            f"  0.500 → <code>{fmt_price(f.fib_50)}</code>\n"
            f"  0.618 → <code>{fmt_price(f.fib_618)}</code>{golden_tag}\n"
            f"  0.786 → <code>{fmt_price(f.fib_786)}</code>{golden_tag}\n"
            f"  Nearest level: <b>{f.nearest_name}</b>\n"
        )

    # Entry reason
    entry_reason = sig.details.get("exact_entry_reason", "")
    entry_src    = sig.details.get("entry_source", "Zone")
    htf_bias     = sig.details.get("htf_bias", "").upper()

    # R:R lines
    rr1 = fmt_rr(sig.exact_entry, sig.stop_loss, sig.take_profit_1, sig.direction)
    rr2 = fmt_rr(sig.exact_entry, sig.stop_loss, sig.take_profit_2, sig.direction)

    msg = (
        f"{dir_emoji} <b>SMC SIGNAL — {sig.symbol}</b>  {grade_emoji} Grade <b>{sig.signal_grade}</b>\n"
        f"<b>{dir_label}</b>  |  4H Bias: <b>{htf_bias}</b>  |  {sig.timestamp}\n"
        f"━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"<b>📌 Entry Zone ({entry_src})</b>\n"
        f"  Zone High: <code>{fmt_price(sig.entry_zone_high)}</code>\n"
        f"  Zone Low:  <code>{fmt_price(sig.entry_zone_low)}</code>\n\n"
        f"<b>🎯 EXACT LIMIT ENTRY: <code>{fmt_price(sig.exact_entry)}</code></b>\n"
        f"  ↳ Based on: {entry_reason}\n"
        f"━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"<b>🛑 Stop Loss:</b>   <code>{fmt_price(sig.stop_loss)}</code>\n"
        f"<b>💰 TP1 (1:2):</b>  <code>{fmt_price(sig.take_profit_1)}</code>  ({rr1})\n"
        f"<b>🚀 TP2 (full):</b> <code>{fmt_price(sig.take_profit_2)}</code>  ({rr2})\n"
        f"━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"{fib_section}"
        f"<b>Confluence:</b> {conf_bar}  {sig.confluence}/{max_score}\n"
        f"{combo_str}\n"
        f"━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"⏰ TF Stack: 4H → 1H → 15M\n"
        f"🤖 SMC Engine v2.0 | Combo 1+2+Fib"
    )
    return msg


# ═══════════════════════════════════════════════════════════════════════════════
# DEDUP
# ═══════════════════════════════════════════════════════════════════════════════

_fired_signals: dict[str, float] = {}
SIGNAL_COOLDOWN_S = 4 * 60 * 60

def is_duplicate(sig: SMCSignal) -> bool:
    key  = f"{sig.symbol}_{sig.direction}"
    last = _fired_signals.get(key, 0)
    return (time.time() - last) < SIGNAL_COOLDOWN_S

def mark_fired(sig: SMCSignal) -> None:
    _fired_signals[f"{sig.symbol}_{sig.direction}"] = time.time()


# ═══════════════════════════════════════════════════════════════════════════════
# SCAN LOOP
# ═══════════════════════════════════════════════════════════════════════════════

def scan_symbol(symbol: str) -> SMCSignal | None:
    try:
        c4h  = get_candles(symbol, "4h",  N_4H)
        c1h  = get_candles(symbol, "1h",  N_1H)
        c15m = get_candles(symbol, "15m", N_15M)
        if len(c4h) < 60 or len(c1h) < 60 or len(c15m) < 60:
            return None
        return compute_smc_signal(symbol, c15m, c1h, c4h)
    except Exception as e:
        print(f"  [SCAN ERROR] {symbol}: {e}")
        return None

def run_scan() -> None:
    print(f"\n[SCAN] {datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M UTC')} "
          f"— {len(WATCHLIST)} symbols")
    signals = []
    for symbol in WATCHLIST:
        sig = scan_symbol(symbol)
        if sig and not is_duplicate(sig):
            signals.append(sig)
            print(f"  ✅ {symbol} {sig.direction.upper()} | {sig.signal_grade} "
                  f"| {sig.confluence}/8 | {sig.combos_hit}")
        else:
            print(f"  —  {symbol} no signal")
        time.sleep(0.25)

    signals.sort(key=lambda s: s.confluence, reverse=True)

    if not signals:
        print("  [SCAN] No signals this round.")
        return

    for sig in signals:
        send_telegram(format_signal_message(sig))
        mark_fired(sig)
        print(f"  📤 Sent: {sig.symbol} {sig.direction.upper()} "
              f"{sig.signal_grade} | Entry: {fmt_price(sig.exact_entry)}")
        time.sleep(0.5)

# ═══════════════════════════════════════════════════════════════════════════════
# STATE PERSISTENCE  (cooldown memory across GitHub Actions runs)
# ═══════════════════════════════════════════════════════════════════════════════

STATE_FILE = pathlib.Path("state.json")

def load_state() -> None:
    """Load _fired_signals from state.json (written by previous run)."""
    global _fired_signals
    if STATE_FILE.exists():
        try:
            data = json.loads(STATE_FILE.read_text())
            # Values are Unix timestamps (floats)
            _fired_signals = {k: float(v) for k, v in data.items()}
            print(f"  [STATE] Loaded {len(_fired_signals)} cooldown entries from {STATE_FILE}")
        except Exception as e:
            print(f"  [STATE] Could not load state.json: {e} — starting fresh")
            _fired_signals = {}
    else:
        print("  [STATE] No state.json found — starting fresh")
        _fired_signals = {}

def save_state() -> None:
    """Persist _fired_signals to state.json for the next run."""
    try:
        STATE_FILE.write_text(json.dumps(_fired_signals, indent=2))
        print(f"  [STATE] Saved {len(_fired_signals)} cooldown entries to {STATE_FILE}")
    except Exception as e:
        print(f"  [STATE] Could not save state.json: {e}")


# ═══════════════════════════════════════════════════════════════════════════════
# MAIN  —  single scan, then exit
#          GitHub Actions cron (every 15 min) replaces the while True loop
# ═══════════════════════════════════════════════════════════════════════════════

def main() -> None:
    print("=" * 60)
    print("  SMC Signal Engine v2.0  [single-scan mode]")
    print("  Combo 1 (HTF OB+FVG+MSB) + Combo 2 (Sweep+OB+FVG)")
    print("  + Fibonacci Confluence (0.382 / 0.5 / 0.618 / 0.786)")
    print("  Timeframes: 4H / 1H / 15M")
    print("  Scheduled via GitHub Actions cron every 15 minutes")
    print("=" * 60)

    # Restore cooldown memory from the previous run
    load_state()

    # Run one scan
    try:
        run_scan()
    except Exception as e:
        print(f"[MAIN ERROR] {e}")
        send_telegram(f"⚠️ SMC Engine error: {e}")

    # Persist cooldown memory for the next run
    save_state()

    print("  [DONE] Scan complete. Exiting.")

if __name__ == "__main__":
    main()
