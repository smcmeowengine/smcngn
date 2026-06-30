"""
Smart Money Concept (SMC) Signal Engine — built from scratch
==============================================================
Multi-timeframe institutional order-flow engine for Hyperliquid perpetuals.

Timeframes : 1D (macro bias) -> 4H (HTF structure/POI) -> 1H (refinement,
             sweep, BOS/CHoCH/MSS) -> 15M (execution confirmation only)
Exchange   : Hyperliquid
Alerts     : Telegram (HTML)

Reused from the reference engine (infrastructure only, per spec): Hyperliquid
REST integration, candle caching, Telegram send/react/delete, active-signal
tracking + reaction-based outcome checking, state.json persistence, and the
scan-per-run / cron execution model.

Everything related to market analysis, structure, liquidity, order blocks,
FVGs, confluence scoring, and entry/SL/TP construction is new and built on
genuine Smart Money Concept principles (BOS/CHoCH/MSS, liquidity sweeps,
order blocks, FVGs, premium/discount, OTE).
"""

import os, time, json, pathlib, sys, math, threading, random
import signal as _signal
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
from dataclasses import dataclass, field

# ═══════════════════════════════════════════════════════════════════════════
# ENV
# ═══════════════════════════════════════════════════════════════════════════
TG_BOT_TOKEN = os.getenv("TG_BOT_TOKEN")
TG_CHAT_ID   = os.getenv("TG_CHAT_ID")
if not TG_BOT_TOKEN:
    raise RuntimeError("TG_BOT_TOKEN environment variable is required")
if not TG_CHAT_ID:
    raise RuntimeError("TG_CHAT_ID environment variable is required")

HL_INFO_URL = "https://api.hyperliquid.xyz/info"
VERSION     = "1.0"

import requests

# ═══════════════════════════════════════════════════════════════════════════
# WATCHLIST  (same universe as reference engine)
# ═══════════════════════════════════════════════════════════════════════════
WATCHLIST = [
    "BTCUSDT", "ETHUSDT", "HYPEUSDT", "ZECUSDT", "NEARUSDT",
    "ONDOUSDT", "SUIUSDT", "PENGUUSDT", "BNBUSDT", "SOLUSDT",
    "TRXUSDT", "BCHUSDT", "DOGEUSDT", "ADAUSDT", "DOTUSDT",
    "TAOUSDT", "AVAXUSDT", "LINKUSDT", "AAVEUSDT", "XRPUSDT",
    "XLMUSDT", "UNIUSDT", "LTCUSDT", "APTUSDT", "PENDLEUSDT",
]

SECTOR_MAP: dict[str, str] = {
    "BTCUSDT": "btc", "ETHUSDT": "eth",
    "SOLUSDT": "l1", "AVAXUSDT": "l1", "SUIUSDT": "l1", "APTUSDT": "l1", "NEARUSDT": "l1",
    "BNBUSDT": "bnb",
    "XRPUSDT": "payments", "XLMUSDT": "payments", "TRXUSDT": "payments", "LTCUSDT": "payments",
    "DOGEUSDT": "meme", "PENGUUSDT": "meme",
    "ADAUSDT": "l1_alt", "DOTUSDT": "l1_alt", "TAOUSDT": "l1_alt",
    "LINKUSDT": "defi", "AAVEUSDT": "defi", "UNIUSDT": "defi", "ONDOUSDT": "defi", "PENDLEUSDT": "defi",
    "HYPEUSDT": "hype", "ZECUSDT": "privacy", "BCHUSDT": "privacy",
}

# ═══════════════════════════════════════════════════════════════════════════
# SCAN / RUNTIME CONFIG
# ═══════════════════════════════════════════════════════════════════════════
SCAN_INTERVAL_S = 60 * 15      # cron/GitHub Actions cadence — informational only
N_15M, N_1H, N_4H, N_1D = 200, 200, 150, 90

TOP_N_SIGNALS       = 5
MAX_SAME_DIRECTION  = 2
MAX_PER_SECTOR      = 1
SIGNAL_COOLDOWN_S   = 4 * 60 * 60
ACTIVE_SIGNAL_TTL_S = 48 * 3600
ENTRY_EXPIRY_S      = 2 * 60 * 60

# ── Market-structure params ─────────────────────────────────────────────────
SWING_LOOKBACK      = 3          # bars each side to confirm a swing pivot
STRUCTURE_LOOKBACK  = 60         # bars scanned for structure events
ATR_LEN             = 14

# ── Liquidity params ─────────────────────────────────────────────────────────
EQUAL_HL_TOLERANCE_ATR = 0.15    # equal highs/lows: within 0.15x ATR
SWEEP_LOOKBACK         = 40
SWEEP_WICK_MIN_ATR     = 0.15    # minimum wick protrusion beyond the pool

# ── Order block params ───────────────────────────────────────────────────────
OB_LOOKBACK         = 50
OB_MIN_DISPLACEMENT_ATR = 1.2    # impulse leg leaving the OB must be >=1.2x ATR
OB_MAX_AGE_BARS     = 40
OB_MAX_MITIGATIONS  = 1          # an OB tested more than once is considered weak

# ── FVG params ────────────────────────────────────────────────────────────────
FVG_MIN_SIZE_ATR    = 0.25
FVG_MAX_AGE_BARS    = 30

# ── Premium / discount ────────────────────────────────────────────────────────
PREMIUM_THRESHOLD    = 0.60      # >60% of range = premium
DISCOUNT_THRESHOLD   = 0.40      # <40% of range = discount

# ── OTE (Optimal Trade Entry) ────────────────────────────────────────────────
OTE_LOW, OTE_MID, OTE_HIGH = 0.62, 0.705, 0.79

# ── Displacement / momentum ──────────────────────────────────────────────────
DISPLACEMENT_BODY_RATIO_MIN = 0.60   # body/range required for a displacement candle
DISPLACEMENT_MIN_ATR        = 1.0    # candle range must be >=1.0x ATR to count as displacement

# ── ADX-style trend strength (daily) — used only as a confluence factor ─────
ADX_PERIOD      = 14
ADX_TREND_MIN   = 18

# ── Confluence / quality gates ───────────────────────────────────────────────
MIN_CONFLUENCE_SCORE = 6     # out of 10 — coarse pre-filter
STRONG_SIGNAL_SCORE  = 6
APLUS_SIGNAL_SCORE   = 8
TP2_MIN_RR           = 2.0
TP1_MIN_RR           = 1.2
MAX_ENTRY_DIST_PCT   = 0.5    # entry zone must be within 0.5% of current price to send

INTERVAL_MS = {"15m": 15*60*1000, "1h": 60*60*1000, "4h": 4*60*60*1000, "1d": 24*60*60*1000}

# ═══════════════════════════════════════════════════════════════════════════
# RATE LIMIT / SESSIONS
# ═══════════════════════════════════════════════════════════════════════════
_hl_lock, _hl_last_req_ts, _hl_min_interval = threading.Lock(), 0.0, 0.2
_hl_session = requests.Session()
_tg_session = requests.Session()

_candle_cache_15m: dict[str, dict] = {}
_candle_cache_1h:  dict[str, dict] = {}
_candle_cache_4h:  dict[str, dict] = {}
_candle_cache_1d:  dict[str, dict] = {}
_CACHE_TTL = {"15m": 60*10, "1h": 60*15, "4h": 60*60, "1d": 60*60*4}
_atr_cache: dict[str, float] = {}


# ═══════════════════════════════════════════════════════════════════════════
# HYPERLIQUID API  (infrastructure reused from reference engine)
# ═══════════════════════════════════════════════════════════════════════════
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
                                  headers={"Content-Type": "application/json"}, timeout=15)
            if r.status_code == 429:
                time.sleep(min(20.0, 1.0 * (2 ** attempt)) + random.uniform(0, 0.3))
                continue
            r.raise_for_status()
            data = r.json()
            if isinstance(data, dict) and "error" in data:
                raise ValueError(f"Hyperliquid API error: {data['error']}")
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
    raw = hl_post({"type": "candleSnapshot",
                    "req": {"coin": hl_coin(symbol), "interval": interval,
                             "startTime": start_ms, "endTime": end_ms}})
    if not raw:
        return []
    candles = [{"t": int(c["t"]), "o": float(c["o"]), "h": float(c["h"]),
                "l": float(c["l"]), "c": float(c["c"]), "v": float(c["v"])} for c in raw]
    valid = [c for c in candles if c["t"] < end_ms][-n:]
    return filter_valid_candles(valid)

def _cached_candles(symbol: str, interval: str, n: int, cache: dict) -> list[dict]:
    entry = cache.get(symbol)
    if entry and (time.time() - entry["ts"]) < _CACHE_TTL[interval]:
        return entry["candles"]
    candles = get_candles(symbol, interval, n)
    cache[symbol] = {"candles": candles, "ts": time.time()}
    return candles

def get_15m(symbol): return _cached_candles(symbol, "15m", N_15M, _candle_cache_15m)
def get_1h(symbol):  return _cached_candles(symbol, "1h",  N_1H,  _candle_cache_1h)
def get_4h(symbol):  return _cached_candles(symbol, "4h",  N_4H,  _candle_cache_4h)
def get_1d(symbol):  return _cached_candles(symbol, "1d",  N_1D,  _candle_cache_1d)

def fetch_all_mids() -> dict[str, float]:
    try:
        raw = hl_post({"type": "allMids"})
        if raw:
            return {k: float(v) for k, v in raw.items() if v}
    except Exception as e:
        print(f"  [MIDS ERROR] {e}")
    return {}

# ── OI / funding (used as confluence + crowding gate) ───────────────────────
_oi_funding_data: dict[str, dict] = {}
OI_FUNDING_ENABLED = True
FUNDING_BLOCK_THRESHOLD = 0.0005

def fetch_all_oi_funding() -> None:
    if not OI_FUNDING_ENABLED:
        return
    try:
        raw = hl_post({"type": "metaAndAssetCtxs"})
        if not raw or len(raw) < 2:
            return
        universe, ctx_list = raw[0].get("universe", []), raw[1]
        now = time.time()
        for i, asset in enumerate(universe):
            coin = asset.get("name", "")
            if not coin or i >= len(ctx_list):
                continue
            ctx = ctx_list[i]
            new_oi = float(ctx.get("openInterest", 0))
            prev = _oi_funding_data.get(coin)
            prev_oi = prev["open_interest"] if prev else None
            _oi_funding_data[coin] = {"funding_rate": float(ctx.get("funding", 0)),
                                       "open_interest": new_oi, "prev_oi": prev_oi, "ts": now}
        print(f"  [OI/FUNDING] Fetched {len(_oi_funding_data)} assets")
    except Exception as e:
        print(f"  [OI/FUNDING] error: {e}")

def get_oi_funding(symbol: str) -> dict | None:
    return _oi_funding_data.get(hl_coin(symbol)) if OI_FUNDING_ENABLED else None


# ═══════════════════════════════════════════════════════════════════════════
# CORE INDICATORS
# ═══════════════════════════════════════════════════════════════════════════
def calc_atr(candles: list[dict], period: int = ATR_LEN) -> float:
    if len(candles) < period + 1:
        return 0.0
    trs = []
    for i in range(1, len(candles)):
        h, l, pc = candles[i]["h"], candles[i]["l"], candles[i-1]["c"]
        trs.append(max(h - l, abs(h - pc), abs(l - pc)))
    if len(trs) < period:
        return 0.0
    # Wilder smoothing
    atr = sum(trs[:period]) / period
    for t in trs[period:]:
        atr = (atr * (period - 1) + t) / period
    return atr

def calc_atr_cached(symbol: str, tf: str, candles: list[dict]) -> float:
    key = f"{symbol}:{tf}"
    if key not in _atr_cache:
        _atr_cache[key] = calc_atr(candles)
    return _atr_cache[key]

def calc_ema(values: list[float], period: int) -> list[float]:
    if len(values) < period:
        return values[:]
    k = 2.0 / (period + 1)
    out = [sum(values[:period]) / period]
    for v in values[period:]:
        out.append(v * k + out[-1] * (1 - k))
    return out

def calc_adx(candles: list[dict], period: int = ADX_PERIOD) -> float:
    n = len(candles)
    if n < period * 2 + 1:
        return 0.0
    plus_dm, minus_dm, tr_list = [], [], []
    for i in range(1, n):
        h_diff = candles[i]["h"] - candles[i-1]["h"]
        l_diff = candles[i-1]["l"] - candles[i]["l"]
        plus_dm.append(h_diff if h_diff > l_diff and h_diff > 0 else 0)
        minus_dm.append(l_diff if l_diff > h_diff and l_diff > 0 else 0)
        tr_list.append(max(candles[i]["h"] - candles[i]["l"],
                            abs(candles[i]["h"] - candles[i-1]["c"]),
                            abs(candles[i]["l"] - candles[i-1]["c"])))
    def smooth(data, p):
        out = [sum(data[:p])]
        for v in data[p:]:
            out.append(out[-1] - out[-1] / p + v)
        return out
    tr_s, pdm_s, mdm_s = smooth(tr_list, period), smooth(plus_dm, period), smooth(minus_dm, period)
    dx = []
    for t, p, m in zip(tr_s, pdm_s, mdm_s):
        if t == 0:
            continue
        pdi, mdi = 100 * p / t, 100 * m / t
        denom = pdi + mdi
        if denom == 0:
            continue
        dx.append(100 * abs(pdi - mdi) / denom)
    if len(dx) < period:
        return 0.0
    return sum(dx[-period:]) / period

def body_ratio(c: dict) -> float:
    rng = c["h"] - c["l"]
    if rng == 0:
        return 0.0
    return abs(c["c"] - c["o"]) / rng

def is_displacement(c: dict, atr: float) -> bool:
    """A true institutional displacement candle: large body, large range vs ATR."""
    if atr <= 0:
        return False
    rng = c["h"] - c["l"]
    return body_ratio(c) >= DISPLACEMENT_BODY_RATIO_MIN and rng >= atr * DISPLACEMENT_MIN_ATR


# ═══════════════════════════════════════════════════════════════════════════
# DATA STRUCTURES
# ═══════════════════════════════════════════════════════════════════════════
@dataclass
class SwingPoint:
    index: int
    price: float
    kind: str          # "high" | "low"
    protected: bool = False   # a swing that has not yet been violated (still valid liquidity)

@dataclass
class StructureEvent:
    kind: str           # "BOS" | "CHoCH" | "MSS"
    direction: str       # "bull" | "bear"
    index: int
    level: float
    body_ratio: float

@dataclass
class LiquidityPool:
    price: float
    kind: str            # "buyside" | "sellside"
    equal: bool           # True if formed by >=2 equal highs/lows
    index: int

@dataclass
class SweepEvent:
    direction: str        # "bull" (swept sell-side, reversing up) | "bear"
    swept_price: float
    wick_extreme: float
    index: int
    volume_ratio: float

@dataclass
class OrderBlock:
    high: float
    low: float
    direction: str         # "bull" | "bear"
    index: int
    timeframe: str
    mitigations: int = 0
    state: str = "fresh"    # "fresh" | "mitigated" | "invalidated" | "breaker"

@dataclass
class FairValueGap:
    high: float
    low: float
    direction: str
    index: int
    timeframe: str
    mitigated_pct: float = 0.0   # 0 = untouched, 1 = fully filled
    inverse: bool = False         # True once price closes through it (flips polarity)

@dataclass
class OTEZone:
    swing_high: float
    swing_low: float
    level_62: float
    level_705: float
    level_79: float
    direction: str
    in_zone: bool

@dataclass
class SMCSignal:
    symbol: str
    direction: str
    entry_zone_high: float
    entry_zone_low: float
    exact_entry: float
    stop_loss: float
    take_profit_1: float
    take_profit_2: float
    confluence: int
    signal_grade: str
    combos_hit: list = field(default_factory=list)
    details: dict = field(default_factory=dict)
    timestamp: str = ""


# ═══════════════════════════════════════════════════════════════════════════
# MARKET STRUCTURE — swing points, BOS, CHoCH, MSS, internal/external
# ═══════════════════════════════════════════════════════════════════════════
def find_swings(candles: list[dict], left: int = SWING_LOOKBACK, right: int = SWING_LOOKBACK) -> list[SwingPoint]:
    """Fractal swing-point detection: a swing high/low must be the local
    extreme over `left` bars before and `right` bars after it."""
    swings = []
    n = len(candles)
    for i in range(left, n - right):
        window_h = [candles[j]["h"] for j in range(i - left, i + right + 1)]
        window_l = [candles[j]["l"] for j in range(i - left, i + right + 1)]
        if candles[i]["h"] == max(window_h):
            swings.append(SwingPoint(i, candles[i]["h"], "high"))
        if candles[i]["l"] == min(window_l):
            swings.append(SwingPoint(i, candles[i]["l"], "low"))
    return swings


def mark_protected_swings(swings: list[SwingPoint], candles: list[dict]) -> None:
    """A swing is 'protected' (still untapped liquidity) if no later candle
    close has traded through it. Mutates swings in place."""
    for s in swings:
        violated = False
        for c in candles[s.index + 1:]:
            if s.kind == "high" and c["c"] > s.price:
                violated = True
                break
            if s.kind == "low" and c["c"] < s.price:
                violated = True
                break
        s.protected = not violated


def detect_structure_events(candles: list[dict], atr: float) -> list[StructureEvent]:
    """
    Walks the swing sequence and classifies breaks:
      BOS   — break of structure in the direction of the prevailing trend
              (continuation: higher-high taken out in an uptrend, etc.)
      CHoCH — first break against the prevailing trend (early reversal signal)
      MSS   — Market Structure Shift: a CHoCH confirmed by a displacement
              candle closing beyond the broken swing with a strong body.
    Only candle *closes* count as valid breaks (wick-only pokes are sweeps,
    not structure breaks — handled separately by detect_liquidity_sweep).
    """
    swings = find_swings(candles)
    if len(swings) < 4:
        return []
    events: list[StructureEvent] = []
    trend = None  # "bull" | "bear" | None

    highs = [s for s in swings if s.kind == "high"]
    lows  = [s for s in swings if s.kind == "low"]
    last_high = last_low = None

    for i, c in enumerate(candles):
        # Update the most recent confirmed swing reference points behind us
        eligible_highs = [s for s in highs if s.index < i]
        eligible_lows  = [s for s in lows  if s.index < i]
        if eligible_highs:
            last_high = eligible_highs[-1]
        if eligible_lows:
            last_low = eligible_lows[-1]
        if not last_high or not last_low:
            continue

        bullish_break = c["c"] > last_high.price
        bearish_break = c["c"] < last_low.price

        if bullish_break:
            kind = "BOS" if trend == "bull" else "CHoCH"
            if kind == "CHoCH" and is_displacement(c, atr):
                kind = "MSS"
            events.append(StructureEvent(kind, "bull", i, last_high.price, body_ratio(c)))
            trend = "bull"
        elif bearish_break:
            kind = "BOS" if trend == "bear" else "CHoCH"
            if kind == "CHoCH" and is_displacement(c, atr):
                kind = "MSS"
            events.append(StructureEvent(kind, "bear", i, last_low.price, body_ratio(c)))
            trend = "bear"

    return events[-12:]   # keep recent history only


def get_trend_from_structure(events: list[StructureEvent]) -> str:
    """Most recent structural direction. 'neutral' if no events yet."""
    if not events:
        return "neutral"
    return events[-1].direction


# ═══════════════════════════════════════════════════════════════════════════
# LIQUIDITY — equal highs/lows, pools, sweeps/grabs/stop hunts
# ═══════════════════════════════════════════════════════════════════════════
def find_liquidity_pools(candles: list[dict], atr: float) -> list[LiquidityPool]:
    """
    Detect buy-side liquidity (resting above equal/relative highs) and
    sell-side liquidity (resting below equal/relative lows). Equal levels
    within EQUAL_HL_TOLERANCE_ATR are merged into a single, stronger pool.
    """
    swings = find_swings(candles[-SWEEP_LOOKBACK:] if len(candles) > SWEEP_LOOKBACK else candles)
    offset = max(0, len(candles) - SWEEP_LOOKBACK)
    pools: list[LiquidityPool] = []
    tol = atr * EQUAL_HL_TOLERANCE_ATR if atr > 0 else 0

    highs = sorted([s for s in swings if s.kind == "high"], key=lambda s: s.price, reverse=True)
    lows  = sorted([s for s in swings if s.kind == "low"], key=lambda s: s.price)

    used = set()
    for i, h in enumerate(highs):
        if i in used:
            continue
        cluster = [h]
        for j, h2 in enumerate(highs):
            if j != i and j not in used and abs(h2.price - h.price) <= tol:
                cluster.append(h2)
                used.add(j)
        used.add(i)
        avg_price = sum(s.price for s in cluster) / len(cluster)
        pools.append(LiquidityPool(avg_price, "buyside", len(cluster) >= 2,
                                    max(s.index for s in cluster) + offset))

    used = set()
    for i, l in enumerate(lows):
        if i in used:
            continue
        cluster = [l]
        for j, l2 in enumerate(lows):
            if j != i and j not in used and abs(l2.price - l.price) <= tol:
                cluster.append(l2)
                used.add(j)
        used.add(i)
        avg_price = sum(s.price for s in cluster) / len(cluster)
        pools.append(LiquidityPool(avg_price, "sellside", len(cluster) >= 2,
                                    max(s.index for s in cluster) + offset))

    return pools


def calc_avg_volume(candles: list[dict], period: int = 20) -> float:
    if len(candles) < period:
        return 0.0
    return sum(c["v"] for c in candles[-period:]) / period


def detect_liquidity_sweep(candles: list[dict], atr: float, lookback: int = SWEEP_LOOKBACK) -> SweepEvent | None:
    """
    A liquidity sweep = price wicks beyond a resting pool (engineered
    liquidity) and then closes back inside the prior range — a stop-hunt /
    grab, not a genuine breakout. Only the most recent closed bar is
    evaluated as the sweep candle; the pool must have existed before it.
    """
    if len(candles) < lookback + 5:
        return None
    pools = find_liquidity_pools(candles[:-1], atr)
    if not pools:
        return None
    last = candles[-1]
    avg_vol = calc_avg_volume(candles[:-1], 20)
    vol_ratio = (last["v"] / avg_vol) if avg_vol > 0 else 1.0
    min_wick = atr * SWEEP_WICK_MIN_ATR if atr > 0 else 0

    # Sell-side sweep -> bullish reversal signal: wick below a sell-side pool,
    # close back above it.
    sellside = [p for p in pools if p.kind == "sellside"]
    if sellside:
        nearest = min(sellside, key=lambda p: abs(p.price - last["l"]))
        if last["l"] < nearest.price - min_wick and last["c"] > nearest.price:
            return SweepEvent("bull", nearest.price, last["l"], len(candles) - 1, vol_ratio)

    buyside = [p for p in pools if p.kind == "buyside"]
    if buyside:
        nearest = min(buyside, key=lambda p: abs(p.price - last["h"]))
        if last["h"] > nearest.price + min_wick and last["c"] < nearest.price:
            return SweepEvent("bear", nearest.price, last["h"], len(candles) - 1, vol_ratio)

    return None


# ═══════════════════════════════════════════════════════════════════════════
# ORDER BLOCKS — fresh / mitigated / invalidated / breaker / flip zones
# ═══════════════════════════════════════════════════════════════════════════
def find_order_blocks(candles: list[dict], timeframe: str, atr: float,
                       lookback: int = OB_LOOKBACK) -> list[OrderBlock]:
    """
    An order block is the last opposite-direction candle immediately before
    a displacement leg. Bullish OB = last down-close candle before an
    impulsive up-move; bearish OB = last up-close candle before an impulsive
    down-move. The impulse leg must clear OB_MIN_DISPLACEMENT_ATR to qualify
    — this filters out the weak/noise zones flagged as a quality requirement.
    """
    if atr <= 0 or len(candles) < lookback + 5:
        return []
    start = max(0, len(candles) - lookback)
    obs: list[OrderBlock] = []

    for i in range(start, len(candles) - 2):
        c = candles[i]
        nxt = candles[i + 1]
        # Bullish OB candidate: down candle followed by a displacement up-close
        if c["c"] < c["o"]:
            leg_high = max(candles[i+1:i+4], key=lambda x: x["h"], default=c)["h"] if i + 4 <= len(candles) else nxt["h"]
            displacement = leg_high - c["h"]
            if displacement >= atr * OB_MIN_DISPLACEMENT_ATR and is_displacement(nxt, atr):
                obs.append(OrderBlock(c["h"], c["l"], "bull", i, timeframe))
        # Bearish OB candidate: up candle followed by a displacement down-close
        if c["c"] > c["o"]:
            leg_low = min(candles[i+1:i+4], key=lambda x: x["l"], default=c)["l"] if i + 4 <= len(candles) else nxt["l"]
            displacement = c["l"] - leg_low
            if displacement >= atr * OB_MIN_DISPLACEMENT_ATR and is_displacement(nxt, atr):
                obs.append(OrderBlock(c["h"], c["l"], "bear", i, timeframe))

    # ── State classification: fresh / mitigated / invalidated / breaker ─────
    for ob in obs:
        age = len(candles) - 1 - ob.index
        if age > OB_MAX_AGE_BARS:
            ob.state = "invalidated"
            continue
        mitigations = 0
        invalidated = False
        for c in candles[ob.index + 1:]:
            if ob.direction == "bull":
                if c["l"] <= ob.high:
                    mitigations += 1
                if c["c"] < ob.low:
                    invalidated = True
            else:
                if c["h"] >= ob.low:
                    mitigations += 1
                if c["c"] > ob.high:
                    invalidated = True
        ob.mitigations = mitigations
        if invalidated:
            # Price closed clean through the block: it has flipped polarity
            # (breaker block) rather than simply failed.
            ob.state = "breaker"
        elif mitigations == 0:
            ob.state = "fresh"
        elif mitigations <= OB_MAX_MITIGATIONS:
            ob.state = "mitigated"
        else:
            ob.state = "invalidated"

    return obs


def best_order_block(obs: list[OrderBlock], direction: str, current_price: float) -> OrderBlock | None:
    """Pick the freshest, nearest still-valid OB in the requested direction."""
    want = "bull" if direction == "long" else "bear"
    candidates = [o for o in obs if o.direction == want and o.state in ("fresh", "mitigated")]
    if not candidates:
        return None
    # Prefer fresh over mitigated, then nearest to current price
    candidates.sort(key=lambda o: (0 if o.state == "fresh" else 1,
                                    abs(current_price - (o.high + o.low) / 2)))
    return candidates[0]


# ═══════════════════════════════════════════════════════════════════════════
# FAIR VALUE GAPS — bullish / bearish / inverse / mitigation tracking
# ═══════════════════════════════════════════════════════════════════════════
def find_fvgs(candles: list[dict], timeframe: str, atr: float,
              lookback: int = OB_LOOKBACK) -> list[FairValueGap]:
    """
    Classic 3-candle imbalance: gap between candle[i-1].high/low and
    candle[i+1].low/high, with candle[i] as the displacement (impulse) bar.
    """
    if atr <= 0 or len(candles) < 5:
        return []
    start = max(2, len(candles) - lookback)
    fvgs: list[FairValueGap] = []
    min_size = atr * FVG_MIN_SIZE_ATR

    for i in range(start, len(candles) - 1):
        c0, c1, c2 = candles[i - 1], candles[i], candles[i + 1]
        # Bullish FVG: gap up — c0.high < c2.low
        if c2["l"] > c0["h"] and (c2["l"] - c0["h"]) >= min_size:
            fvgs.append(FairValueGap(c2["l"], c0["h"], "bull", i, timeframe))
        # Bearish FVG: gap down — c0.low > c2.high
        if c0["l"] > c2["h"] and (c0["l"] - c2["h"]) >= min_size:
            fvgs.append(FairValueGap(c0["l"], c2["h"], "bear", i, timeframe))

    # ── Mitigation tracking + inverse-FVG flip detection ────────────────────
    for g in fvgs:
        age = len(candles) - 1 - g.index
        if age > FVG_MAX_AGE_BARS:
            g.mitigated_pct = 1.0
            continue
        size = g.high - g.low
        deepest = 0.0
        flipped = False
        for c in candles[g.index + 2:]:
            if g.direction == "bull":
                if c["l"] < g.high:
                    depth = min(1.0, (g.high - max(c["l"], g.low)) / size) if size > 0 else 0
                    deepest = max(deepest, depth)
                if c["c"] < g.low:
                    flipped = True
            else:
                if c["h"] > g.low:
                    depth = min(1.0, (min(c["h"], g.high) - g.low) / size) if size > 0 else 0
                    deepest = max(deepest, depth)
                if c["c"] > g.high:
                    flipped = True
        g.mitigated_pct = deepest
        g.inverse = flipped

    return fvgs


def best_fvg(fvgs: list[FairValueGap], direction: str, current_price: float) -> FairValueGap | None:
    want = "bull" if direction == "long" else "bear"
    candidates = [g for g in fvgs if g.direction == want and not g.inverse and g.mitigated_pct < 1.0]
    if not candidates:
        return None
    candidates.sort(key=lambda g: (g.mitigated_pct, abs(current_price - (g.high + g.low) / 2)))
    return candidates[0]


def ob_fvg_intersection(ob: OrderBlock | None, fvg: FairValueGap | None) -> tuple[float, float] | None:
    """Tightest possible entry zone: where an order block and an FVG overlap."""
    if not ob or not fvg:
        return None
    lo = max(ob.low, fvg.low)
    hi = min(ob.high, fvg.high)
    if lo < hi:
        return (lo, hi)
    return None


# ═══════════════════════════════════════════════════════════════════════════
# PREMIUM / DISCOUNT / EQUILIBRIUM
# ═══════════════════════════════════════════════════════════════════════════
def premium_discount_zone(candles: list[dict], lookback: int = 50) -> dict:
    """
    Returns the range high/low over `lookback` bars plus where the current
    close sits within that range (0 = range low, 1 = range high).
    """
    window = candles[-lookback:] if len(candles) > lookback else candles
    hi = max(c["h"] for c in window)
    lo = min(c["l"] for c in window)
    close = candles[-1]["c"]
    pos = (close - lo) / (hi - lo) if hi > lo else 0.5
    if pos >= PREMIUM_THRESHOLD:
        zone = "premium"
    elif pos <= DISCOUNT_THRESHOLD:
        zone = "discount"
    else:
        zone = "equilibrium"
    return {"high": hi, "low": lo, "position": pos, "zone": zone}


# ═══════════════════════════════════════════════════════════════════════════
# OPTIMAL TRADE ENTRY (OTE) — Fibonacci 0.62 / 0.705 / 0.79
# ═══════════════════════════════════════════════════════════════════════════
def compute_ote(candles: list[dict], direction: str, lookback: int = 50) -> OTEZone | None:
    """
    Draws the fib retracement across the most recent significant swing in the
    direction of the trade: for a long, from the swing low up to the swing
    high (retracement zone below); for a short, the inverse.
    """
    swings = find_swings(candles[-lookback:] if len(candles) > lookback else candles)
    if len(swings) < 2:
        return None
    highs = [s for s in swings if s.kind == "high"]
    lows  = [s for s in swings if s.kind == "low"]
    if not highs or not lows:
        return None
    swing_high = max(highs, key=lambda s: s.price).price
    swing_low  = min(lows,  key=lambda s: s.price).price
    if swing_high <= swing_low:
        return None
    rng = swing_high - swing_low
    current = candles[-1]["c"]

    if direction == "long":
        l62, l705, l79 = swing_high - rng*OTE_LOW, swing_high - rng*OTE_MID, swing_high - rng*OTE_HIGH
        in_zone = l79 <= current <= l62
    else:
        l62, l705, l79 = swing_low + rng*OTE_LOW, swing_low + rng*OTE_MID, swing_low + rng*OTE_HIGH
        in_zone = l62 <= current <= l79

    return OTEZone(swing_high, swing_low, l62, l705, l79, direction, in_zone)


# ═══════════════════════════════════════════════════════════════════════════
# MULTI-TIMEFRAME BIAS
# ═══════════════════════════════════════════════════════════════════════════
def daily_macro_bias(candles_1d: list[dict]) -> dict:
    """
    Daily timeframe: macro institutional bias via EMA stack + structure +
    ADX, plus premium/discount context for the macro range.
    """
    if len(candles_1d) < 55:
        return {"bias": "neutral", "adx": 0.0, "pd": None}
    closes = [c["c"] for c in candles_1d]
    ema21, ema50 = calc_ema(closes, 21), calc_ema(closes, 50)
    if len(ema21) < 3 or len(ema50) < 3:
        return {"bias": "neutral", "adx": 0.0, "pd": None}
    atr = calc_atr(candles_1d)
    events = detect_structure_events(candles_1d, atr)
    trend = get_trend_from_structure(events)
    adx = calc_adx(candles_1d)
    pd = premium_discount_zone(candles_1d, 60)

    ema_bull = closes[-1] > ema21[-1] > ema50[-1]
    ema_bear = closes[-1] < ema21[-1] < ema50[-1]

    if ema_bull and trend in ("bull", "neutral") and adx >= ADX_TREND_MIN:
        bias = "bull"
    elif ema_bear and trend in ("bear", "neutral") and adx >= ADX_TREND_MIN:
        bias = "bear"
    elif trend in ("bull", "bear") and adx >= ADX_TREND_MIN:
        bias = trend
    else:
        bias = "neutral"

    return {"bias": bias, "adx": adx, "pd": pd, "structure": events}


def htf_4h_analysis(candles_4h: list[dict]) -> dict:
    """4H: major structure, institutional OBs/FVGs, liquidity pools, POIs."""
    atr = calc_atr(candles_4h)
    events = detect_structure_events(candles_4h, atr)
    trend = get_trend_from_structure(events)
    obs = find_order_blocks(candles_4h, "4h", atr)
    fvgs = find_fvgs(candles_4h, "4h", atr)
    pools = find_liquidity_pools(candles_4h, atr)
    pd = premium_discount_zone(candles_4h, 60)
    return {"trend": trend, "atr": atr, "obs": obs, "fvgs": fvgs,
            "pools": pools, "pd": pd, "structure": events}


def refine_1h(candles_1h: list[dict]) -> dict:
    """1H: refine HTF zones, detect sweeps and BOS/CHoCH/MSS."""
    atr = calc_atr(candles_1h)
    events = detect_structure_events(candles_1h, atr)
    sweep = detect_liquidity_sweep(candles_1h, atr)
    obs = find_order_blocks(candles_1h, "1h", atr)
    fvgs = find_fvgs(candles_1h, "1h", atr)
    return {"atr": atr, "structure": events, "sweep": sweep, "obs": obs, "fvgs": fvgs,
            "trend": get_trend_from_structure(events)}


def confirm_15m(candles_15m: list[dict]) -> dict:
    """
    15M is execution-only: requires sweep + displacement + MSS/CHoCH +
    entry inside a valid institutional zone. Never generates trades alone.
    """
    atr = calc_atr(candles_15m)
    events = detect_structure_events(candles_15m, atr)
    sweep = detect_liquidity_sweep(candles_15m, atr, lookback=25)
    last = candles_15m[-1]
    displacement = is_displacement(last, atr)
    recent_mss = any(e.kind in ("MSS", "CHoCH") for e in events[-3:]) if events else False
    return {"atr": atr, "sweep": sweep, "displacement": displacement,
            "recent_shift": recent_mss, "events": events}


# ═══════════════════════════════════════════════════════════════════════════
# SMART CONFLUENCE ENGINE
# ═══════════════════════════════════════════════════════════════════════════
def compute_smc_signal(symbol: str, c15m: list[dict], c1h: list[dict],
                        c4h: list[dict], c1d: list[dict],
                        oi_data: dict | None = None) -> SMCSignal | None:
    """
    Builds a signal only when daily bias, 4H structure/POI, 1H refinement,
    and 15M execution all align with genuine institutional confluence.
    Quality-first: any missing critical leg aborts before scoring.
    """
    current_price = c15m[-1]["c"]

    macro = daily_macro_bias(c1d)
    if macro["bias"] == "neutral":
        return None   # no macro edge — do not trade choppy/ranging daily context

    direction = "long" if macro["bias"] == "bull" else "short"
    want_ob_dir = "bull" if direction == "long" else "bear"

    htf = htf_4h_analysis(c4h)
    # HTF structure must not be flatly opposed to macro bias.
    if htf["trend"] != "neutral" and htf["trend"] != macro["bias"]:
        return None

    # Premium/discount filter: never buy in premium, never sell in discount.
    if direction == "long" and htf["pd"]["zone"] == "premium":
        return None
    if direction == "short" and htf["pd"]["zone"] == "discount":
        return None

    h1 = refine_1h(c1h)
    m15 = confirm_15m(c15m)

    # 15M execution gate — hard requirement per spec: sweep + displacement +
    # MSS/CHoCH on the entry timeframe, confirming (not generating) the trade.
    if not (m15["displacement"] and m15["recent_shift"]):
        return None
    if m15["sweep"] is None and h1["sweep"] is None:
        return None   # no engineered liquidity grabbed anywhere — reject

    sweep_tf = "15m" if m15["sweep"] else "1h"
    sweep = m15["sweep"] or h1["sweep"]
    want_sweep_dir = "bull" if direction == "long" else "bear"
    if sweep.direction != want_sweep_dir:
        return None   # sweep direction disagrees with intended trade direction

    ob = best_order_block(htf["obs"], direction, current_price) or \
         best_order_block(h1["obs"], direction, current_price)
    fvg = best_fvg(htf["fvgs"], direction, current_price) or \
          best_fvg(h1["fvgs"], direction, current_price)
    if not ob and not fvg:
        return None   # reject weak/non-existent institutional zones

    ote = compute_ote(c4h, direction)

    # ── Smart confluence scoring (factor-based, not arbitrary point soup) ───
    score = 0
    combos: list[str] = []

    # 1) Daily macro bias confirmed + trending (ADX)
    score += 1; combos.append("DAILY_BIAS")
    if macro["adx"] >= ADX_TREND_MIN + 7:
        score += 1; combos.append("DAILY_STRONG_TREND")

    # 2) 4H structure agreement
    if htf["trend"] == macro["bias"]:
        score += 1; combos.append("4H_STRUCTURE_ALIGN")

    # 3) 1H refinement structure agreement (BOS/CHoCH/MSS same direction)
    if h1["trend"] == direction.replace("long", "bull").replace("short", "bear"):
        score += 1; combos.append("1H_STRUCTURE_ALIGN")

    # 4) Liquidity sweep present (engineered liquidity grabbed before move)
    score += 1
    combos.append(f"LIQUIDITY_SWEEP_{sweep_tf.upper()}")
    if sweep.volume_ratio >= 1.3:
        score += 1; combos.append("SWEEP_VOLUME_CONFIRM")

    # 5) Order block present and fresh
    if ob:
        combos.append("ORDER_BLOCK" if ob.state == "fresh" else "ORDER_BLOCK_MITIGATED")
        score += 1 if ob.state == "fresh" else 0

    # 6) Fair value gap present and unmitigated
    if fvg:
        combos.append("FVG")
        score += 1 if fvg.mitigated_pct < 0.3 else 0

    # 7) OB∩FVG intersection — tightest, highest quality entry zone
    intersection = ob_fvg_intersection(ob, fvg)
    if intersection:
        score += 1; combos.append("OB_FVG_INTERSECTION")

    # 8) Premium/discount alignment (buying discount / selling premium)
    if (direction == "long" and htf["pd"]["zone"] == "discount") or \
       (direction == "short" and htf["pd"]["zone"] == "premium"):
        score += 1; combos.append("PD_ALIGN")

    # 9) OTE golden-zone confluence
    if ote and ote.in_zone:
        score += 1; combos.append("OTE_GOLDEN_ZONE")

    # 10) 15M displacement + MSS confirmation (execution trigger)
    score += 1; combos.append("15M_DISPLACEMENT_MSS")

    # ── Funding / OI confluence (institutional positioning context) ─────────
    if oi_data:
        funding = oi_data.get("funding_rate", 0.0)
        if direction == "long" and funding < -FUNDING_BLOCK_THRESHOLD:
            return None   # crowd already maximally short-squeezed against us in reverse — skip
        if direction == "short" and funding > FUNDING_BLOCK_THRESHOLD:
            return None
        prev_oi, new_oi = oi_data.get("prev_oi"), oi_data.get("open_interest")
        if prev_oi and new_oi and prev_oi > 0:
            oi_delta = (new_oi - prev_oi) / prev_oi
            if oi_delta > 0.05:
                score += 1; combos.append("OI_BUILDUP")

    if score < MIN_CONFLUENCE_SCORE:
        return None

    # ── Entry / SL / TP construction ─────────────────────────────────────────
    if intersection:
        entry_zone_low, entry_zone_high = intersection
        entry_source = "OB∩FVG"
    elif ob:
        entry_zone_low, entry_zone_high = ob.low, ob.high
        entry_source = "Order Block"
    else:
        entry_zone_low, entry_zone_high = fvg.low, fvg.high
        entry_source = "Fair Value Gap"

    # Reject overextended entries — zone must not already be far behind price.
    zone_mid = (entry_zone_high + entry_zone_low) / 2
    atr_15m = m15["atr"] or calc_atr(c15m)
    if atr_15m > 0 and abs(current_price - zone_mid) > atr_15m * 2.5:
        return None

    if direction == "long":
        exact_entry = min(entry_zone_high, max(entry_zone_low, current_price))
        # Stop beyond true invalidation: below the OB/FVG zone and the sweep wick.
        invalidation = min(entry_zone_low, sweep.wick_extreme) - atr_15m * 0.25
        stop_loss = invalidation
        risk = exact_entry - stop_loss
        # Targets: nearest opposing liquidity pool / HTF objective.
        opposing_pools = [p for p in htf["pools"] if p.kind == "buyside" and p.price > exact_entry]
        tp2 = min(opposing_pools, key=lambda p: p.price).price if opposing_pools else exact_entry + risk * TP2_MIN_RR
        take_profit_1 = exact_entry + risk * 1.5
        take_profit_2 = max(tp2, exact_entry + risk * TP2_MIN_RR)
    else:
        exact_entry = max(entry_zone_low, min(entry_zone_high, current_price))
        invalidation = max(entry_zone_high, sweep.wick_extreme) + atr_15m * 0.25
        stop_loss = invalidation
        risk = stop_loss - exact_entry
        opposing_pools = [p for p in htf["pools"] if p.kind == "sellside" and p.price < exact_entry]
        tp2 = max(opposing_pools, key=lambda p: p.price).price if opposing_pools else exact_entry - risk * TP2_MIN_RR
        take_profit_1 = exact_entry - risk * 1.5
        take_profit_2 = min(tp2, exact_entry - risk * TP2_MIN_RR)

    if risk <= 0:
        return None

    rr_tp1 = abs(take_profit_1 - exact_entry) / risk
    rr_tp2 = abs(take_profit_2 - exact_entry) / risk
    if rr_tp1 < TP1_MIN_RR or rr_tp2 < TP2_MIN_RR:
        return None

    grade = "A+" if score >= APLUS_SIGNAL_SCORE else ("A" if score >= STRONG_SIGNAL_SCORE else "B")

    return SMCSignal(
        symbol=symbol, direction=direction,
        entry_zone_high=entry_zone_high, entry_zone_low=entry_zone_low,
        exact_entry=exact_entry, stop_loss=stop_loss,
        take_profit_1=take_profit_1, take_profit_2=take_profit_2,
        confluence=score, signal_grade=grade, combos_hit=combos,
        details={
            "daily_bias": macro["bias"], "adx_1d": round(macro["adx"], 1),
            "htf_trend": htf["trend"], "h1_trend": h1["trend"],
            "pd_zone_4h": htf["pd"]["zone"], "entry_source": entry_source,
            "sweep_tf": sweep_tf, "current_price": current_price,
        },
        timestamp=datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC"),
    )


# ═══════════════════════════════════════════════════════════════════════════
# FORMATTING
# ═══════════════════════════════════════════════════════════════════════════
def fmt_price(v: float) -> str:
    if v >= 1000: return f"{v:,.2f}"
    if v >= 1:    return f"{v:.4f}"
    return f"{v:.6f}"

def fmt_rr(entry: float, sl: float, tp: float) -> str:
    risk, reward = abs(entry - sl), abs(tp - entry)
    rr = reward / risk if risk > 0 else 0
    return f"1 : {rr:.1f}"

COMBO_LABELS = {
    "DAILY_BIAS": "Daily Macro Bias", "DAILY_STRONG_TREND": "Daily Strong Trend (ADX)",
    "4H_STRUCTURE_ALIGN": "4H Structure Aligned", "1H_STRUCTURE_ALIGN": "1H Structure Aligned",
    "LIQUIDITY_SWEEP_15M": "Liquidity Sweep (15M)", "LIQUIDITY_SWEEP_1H": "Liquidity Sweep (1H)",
    "SWEEP_VOLUME_CONFIRM": "Sweep Volume Confirmed", "ORDER_BLOCK": "Fresh Order Block",
    "ORDER_BLOCK_MITIGATED": "Order Block (mitigated)", "FVG": "Fair Value Gap",
    "OB_FVG_INTERSECTION": "OB ∩ FVG Intersection", "PD_ALIGN": "Premium/Discount Aligned",
    "OTE_GOLDEN_ZONE": "OTE Golden Zone (0.62-0.79)", "15M_DISPLACEMENT_MSS": "15M Displacement + MSS",
    "OI_BUILDUP": "OI Buildup (fresh positioning)",
}

def format_signal_message(sig: SMCSignal) -> str:
    dir_label  = "LONG" if sig.direction == "long" else "SHORT"
    dir_marker = "▲" if sig.direction == "long" else "▼"
    combo_str  = "\n".join("· " + COMBO_LABELS.get(c, c) for c in sig.combos_hit)
    rr1 = fmt_rr(sig.exact_entry, sig.stop_loss, sig.take_profit_1)
    rr2 = fmt_rr(sig.exact_entry, sig.stop_loss, sig.take_profit_2)
    d = sig.details
    cur_price = d.get("current_price")
    cur_line = f"Current price: <code>{fmt_price(cur_price)}</code>\n" if cur_price else ""
    max_score = 10

    return (
        f"<b>{dir_marker} {sig.symbol} — {dir_label}</b>  |  Grade <b>{sig.signal_grade}</b>  |  {sig.confluence}/{max_score}\n"
        f"1D: <b>{d.get('daily_bias','').upper()}</b> ADX={d.get('adx_1d','-')}  |  "
        f"4H: <b>{d.get('htf_trend','').upper()}</b>  |  1H: <b>{d.get('h1_trend','').upper()}</b>  |  {sig.timestamp}\n"
        f"━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"{cur_line}"
        f"\n<b>Entry Zone</b> ({d.get('entry_source','Zone')})\n"
        f"  High: <code>{fmt_price(sig.entry_zone_high)}</code>\n"
        f"  Low:  <code>{fmt_price(sig.entry_zone_low)}</code>\n"
        f"<b>Limit Entry:</b> <code>{fmt_price(sig.exact_entry)}</code>\n"
        f"\n<b>Stop Loss:</b>  <code>{fmt_price(sig.stop_loss)}</code>\n"
        f"<b>TP1:</b>        <code>{fmt_price(sig.take_profit_1)}</code>  ({rr1})\n"
        f"<b>TP2:</b>        <code>{fmt_price(sig.take_profit_2)}</code>  ({rr2})\n"
        f"━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"<b>Confluence</b>\n{combo_str}\n"
        f"\n<i>SMC Engine v{VERSION} | Min confluence {MIN_CONFLUENCE_SCORE}/{max_score}</i>\n"
    )


# ═══════════════════════════════════════════════════════════════════════════
# TELEGRAM  (infrastructure reused from reference engine)
# ═══════════════════════════════════════════════════════════════════════════
def send_telegram_get_id(text: str) -> int | None:
    url = f"https://api.telegram.org/bot{TG_BOT_TOKEN}/sendMessage"
    for attempt in range(3):
        try:
            r = _tg_session.post(url, json={"chat_id": TG_CHAT_ID, "text": text,
                                             "parse_mode": "HTML"}, timeout=10)
            r.raise_for_status()
            return r.json().get("result", {}).get("message_id")
        except Exception as e:
            if attempt == 2:
                print(f"[TG ERROR] {e}")
            time.sleep(2)
    return None

def react_to_message(message_id: int, emoji) -> bool:
    emojis = [emoji] if isinstance(emoji, str) else list(emoji)
    url = f"https://api.telegram.org/bot{TG_BOT_TOKEN}/setMessageReaction"
    try:
        r = _tg_session.post(url, json={"chat_id": TG_CHAT_ID, "message_id": message_id,
                                         "reaction": [{"type": "emoji", "emoji": e} for e in emojis],
                                         "is_big": True}, timeout=10)
        data = r.json()
        if not data.get("ok"):
            print(f"  [REACT FAIL] msg {message_id}: {data.get('description')}")
            return False
        return True
    except Exception as e:
        print(f"  [REACT ERROR] msg {message_id}: {e}")
        return False

def delete_message(message_id: int) -> bool:
    url = f"https://api.telegram.org/bot{TG_BOT_TOKEN}/deleteMessage"
    try:
        r = _tg_session.post(url, json={"chat_id": TG_CHAT_ID, "message_id": message_id}, timeout=10)
        return bool(r.json().get("ok"))
    except Exception as e:
        print(f"  [DELETE ERROR] msg {message_id}: {e}")
        return False


# ═══════════════════════════════════════════════════════════════════════════
# DEDUP / ACTIVE-SIGNAL TRACKING  (infrastructure pattern reused)
# ═══════════════════════════════════════════════════════════════════════════
_fired_signals: dict[str, float] = {}
_active_signals: dict[str, dict] = {}
_last_scan_ts: float = 0.0

def is_duplicate(sig: SMCSignal) -> bool:
    for direction in ("long", "short"):
        key = f"{sig.symbol}_{direction}"
        active = _active_signals.get(key)
        if active and not active.get("resolved", False):
            if time.time() - active.get("sent_at", 0) < ACTIVE_SIGNAL_TTL_S:
                return True
    key = f"{sig.symbol}_{sig.direction}"
    if time.time() - _fired_signals.get(key, 0) < SIGNAL_COOLDOWN_S:
        return True
    return False

def mark_fired(sig: SMCSignal) -> None:
    _fired_signals[f"{sig.symbol}_{sig.direction}"] = time.time()

def track_active_signal(sig: SMCSignal, message_id: int) -> None:
    key = f"{sig.symbol}_{sig.direction}"
    _active_signals[key] = {
        "symbol": sig.symbol, "direction": sig.direction,
        "exact_entry": sig.exact_entry, "entry_zone_high": sig.entry_zone_high,
        "entry_zone_low": sig.entry_zone_low, "stop_loss": sig.stop_loss,
        "take_profit_1": sig.take_profit_1, "take_profit_2": sig.take_profit_2,
        "combos_hit": sig.combos_hit, "message_id": message_id,
        "signal_grade": sig.signal_grade, "entered": False,
        "tp1_hit": False, "resolved": False, "sent_at": time.time(),
    }

def check_reactions(all_mids: dict) -> None:
    """Update active signals against current price; react/resolve on SL/TP hits."""
    for key, s in list(_active_signals.items()):
        if s.get("resolved"):
            continue
        coin = hl_coin(s["symbol"])
        price = all_mids.get(coin)
        if price is None:
            continue
        direction = s["direction"]
        msg_id = s.get("message_id")
        if not s.get("entered"):
            in_zone = (s["entry_zone_low"] <= price <= s["entry_zone_high"])
            if in_zone:
                s["entered"] = True
            elif time.time() - s["sent_at"] > ENTRY_EXPIRY_S:
                s["resolved"] = True
                if msg_id:
                    delete_message(msg_id)
                continue
            else:
                continue

        if direction == "long":
            if price <= s["stop_loss"]:
                s["resolved"] = True
                if msg_id: react_to_message(msg_id, "💔")
            elif not s["tp1_hit"] and price >= s["take_profit_1"]:
                s["tp1_hit"] = True
                if msg_id: react_to_message(msg_id, "🔥")
            elif price >= s["take_profit_2"]:
                s["resolved"] = True
                if msg_id: react_to_message(msg_id, ["🔥", "🏆"])
        else:
            if price >= s["stop_loss"]:
                s["resolved"] = True
                if msg_id: react_to_message(msg_id, "💔")
            elif not s["tp1_hit"] and price <= s["take_profit_1"]:
                s["tp1_hit"] = True
                if msg_id: react_to_message(msg_id, "🔥")
            elif price <= s["take_profit_2"]:
                s["resolved"] = True
                if msg_id: react_to_message(msg_id, ["🔥", "🏆"])


# ═══════════════════════════════════════════════════════════════════════════
# SCAN LOOP
# ═══════════════════════════════════════════════════════════════════════════
def scan_symbol(symbol: str) -> SMCSignal | None:
    try:
        c1d  = get_1d(symbol)
        c4h  = get_4h(symbol)
        c1h  = get_1h(symbol)
        c15m = get_15m(symbol)
        if len(c1d) < 55 or len(c4h) < 60 or len(c1h) < 60 or len(c15m) < 60:
            print(f"  [{symbol}] insufficient candles — skipping")
            return None
        oi_data = get_oi_funding(symbol)
        return compute_smc_signal(symbol, c15m, c1h, c4h, c1d, oi_data=oi_data)
    except Exception as e:
        print(f"  [SCAN ERROR] {symbol}: {e}")
        return None


def run_scan(all_mids: dict | None = None) -> None:
    global _last_scan_ts, _atr_cache
    _atr_cache = {}
    fetch_all_oi_funding()
    _last_scan_ts = time.time()

    print(f"\n[SCAN] {datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M UTC')} — {len(WATCHLIST)} symbols")

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

    signals = []
    for symbol in WATCHLIST:
        sig = results.get(symbol)
        if not sig:
            print(f"  —  {symbol} no signal")
            continue
        if is_duplicate(sig):
            print(f"  [DUPLICATE] {sig.symbol} {sig.direction.upper()} blocked")
            continue
        signals.append(sig)
        print(f"  ✅ {symbol} {sig.direction.upper()} | {sig.signal_grade} | {sig.confluence}/10")

    signals.sort(key=lambda s: s.confluence, reverse=True)

    # Direction cap
    capped, long_n, short_n = [], 0, 0
    for sig in signals:
        if sig.direction == "long":
            if long_n < MAX_SAME_DIRECTION:
                capped.append(sig); long_n += 1
        else:
            if short_n < MAX_SAME_DIRECTION:
                capped.append(sig); short_n += 1

    # Sector cap
    sector_counts, sector_capped = {}, []
    for sig in capped:
        sec = SECTOR_MAP.get(sig.symbol, sig.symbol)
        if sector_counts.get(sec, 0) < MAX_PER_SECTOR:
            sector_capped.append(sig)
            sector_counts[sec] = sector_counts.get(sec, 0) + 1

    final = sector_capped[:TOP_N_SIGNALS]
    if not final:
        print("  [SCAN] No signals this round.")
        return

    if all_mids is None:
        all_mids = fetch_all_mids()

    print(f"\n  [TOP {TOP_N_SIGNALS}] Sending best signals:")
    for sig in final:
        coin = hl_coin(sig.symbol)
        cur_price = all_mids.get(coin)
        if cur_price is not None:
            dist_pct = abs(cur_price - sig.exact_entry) / cur_price * 100
            if dist_pct > MAX_ENTRY_DIST_PCT:
                print(f"  ⛔ TOO-FAR {sig.symbol} {sig.direction.upper()} — {dist_pct:.1f}% away — skipped")
                continue
            if sig.direction == "long" and (cur_price <= sig.stop_loss or cur_price >= sig.take_profit_2):
                print(f"  ⛔ STALE {sig.symbol} — already past SL/TP2 — skipped")
                continue
            if sig.direction == "short" and (cur_price >= sig.stop_loss or cur_price <= sig.take_profit_2):
                print(f"  ⛔ STALE {sig.symbol} — already past SL/TP2 — skipped")
                continue

        msg = format_signal_message(sig)
        msg_id = send_telegram_get_id(msg)
        if msg_id:
            mark_fired(sig)
            track_active_signal(sig, msg_id)
            print(f"  📤 Sent: {sig.symbol} {sig.direction.upper()} {sig.signal_grade} | "
                  f"Entry: {fmt_price(sig.exact_entry)} | msg_id: {msg_id}")
        else:
            print(f"  ⚠️ TG send failed for {sig.symbol} {sig.direction.upper()}")
        time.sleep(0.5)


# ═══════════════════════════════════════════════════════════════════════════
# STATE PERSISTENCE  (infrastructure reused from reference engine)
# ═══════════════════════════════════════════════════════════════════════════
STATE_FILE = pathlib.Path("state.json")

def cleanup_state() -> None:
    now = time.time()
    expired = [k for k, ts in _fired_signals.items() if now - ts > SIGNAL_COOLDOWN_S]
    for k in expired:
        _fired_signals.pop(k, None)
    stale = [k for k, s in _active_signals.items()
             if s.get("resolved", False) or now - s.get("sent_at", 0) > ACTIVE_SIGNAL_TTL_S]
    for k in stale:
        _active_signals.pop(k, None)
    print(f"  [CLEANUP] {len(expired)} cooldowns removed, {len(stale)} active removed")

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
    try:
        state_json = json.dumps({"fired_signals": _fired_signals, "active_signals": _active_signals,
                                  "last_scan_ts": _last_scan_ts}, indent=2)
        tmp = STATE_FILE.with_suffix(".tmp")
        tmp.write_text(state_json)
        if STATE_FILE.exists():
            STATE_FILE.replace(STATE_FILE.with_suffix(".bak"))
        os.replace(tmp, STATE_FILE)
        print(f"  [STATE] Saved {len(_fired_signals)} cooldown + {len(_active_signals)} active signals")
    except Exception as e:
        print(f"  [STATE] Save error: {e}")


# ═══════════════════════════════════════════════════════════════════════════
# MAIN  (scan-per-run model — same execution pattern as reference engine)
# ═══════════════════════════════════════════════════════════════════════════
def _shutdown_handler(signum, frame):
    print(f"\n  [SHUTDOWN] Received signal {signum} — saving state before exit.")
    save_state()
    sys.exit(0)

def main() -> None:
    print("=" * 60)
    print(f"  SMC Signal Engine v{VERSION} [single-scan mode]")
    print("  Built from scratch: BOS/CHoCH/MSS structure, liquidity sweeps,")
    print("  order blocks, FVGs, premium/discount, OTE, smart confluence")
    print(f"  Timeframes: 1D bias -> 4H structure -> 1H refine -> 15M execution")
    print("=" * 60)

    _signal.signal(_signal.SIGTERM, _shutdown_handler)
    _signal.signal(_signal.SIGINT, _shutdown_handler)

    load_state()

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
        send_telegram_get_id(f"⚠️ SMC Engine error: {e}")

    cleanup_state()
    save_state()
    print("  [DONE] Scan complete. Exiting.")


if __name__ == "__main__":
    main()
