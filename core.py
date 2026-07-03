"""
NYX ENGINE v2.0.0 — DUAL PIPELINE
=============================================================
Nyx's liquidity-engineering edge (sweep -> displacement/CHoCH -> imbalance ->
breaker OTE entry, gated by H4 structure+EMA bias, premium/discount, and a
live POI) run across TWO independent timeframe pipelines in parallel,
Castellan-style:

    H4  / 15m   (original Nyx combo — session-gated, fast)
    12H / 1h    (new slow combo — always-on, wider stops/targets)

Each pipeline has its own tuned thresholds, its own cooldown/TTL scaling,
and its own candle cache. A symbol can produce a candidate on either
pipeline, or both, in the same scan; final selection is unified (see below).

This is a deliberate merge of the two prior engines (Nyx Engine v1.1.1 and
Castellan Protocol v1.2.0), keeping what each did better and fixing what
each did worse:

Kept from Nyx (this is the base architecture):
  - Hard-gate sequence: sweep -> displacement+CHoCH -> imbalance are
    non-negotiable, not scoring bonuses.
  - H4 structure+EMA double-confirmed bias (a lone swing read can't set
    direction; EMA must agree).
  - BTC regime filter + sector/direction diversification caps — the
    portfolio-correlation controls Castellan never had.
  - Selection ranks candidates by confluence score before capping —
    Castellan's per-scan cap took candidates in hardcoded watchlist order
    with no ranking at all, silently dropping better setups in favor of
    earlier-listed symbols. That's fixed here by construction: every
    candidate from every pipeline is scored, pooled, and sorted before any
    cap is applied.

Ported in from Castellan:
  - Two independent timeframe pipelines instead of one.
  - A live-price staleness/drift re-check performed immediately before
    each Telegram send (not just once, earlier, against a stale candle
    close) — refuses to fire if price has already run away from plan.
  - A global concurrency cap on unresolved active signals, across both
    pipelines combined — a portfolio-level brake Nyx didn't have.
  - An open-interest liquidity floor — refuses to signal on thin books.
  - Adaptive rate limiting (backs off on 429s, eases back down on a streak
    of clean requests) to handle the ~2x API load of running two pipelines.
  - More defensive state loading: falls back to a `.bak` copy on a corrupt
    primary state file, and checks a schema version before trusting it.

Fixed relative to both originals:
  - Nyx v1's confluence score gave a free, undiscriminating point for
    "Session" that was already guaranteed true (the whole scan skipped
    itself when out of session, so anything reaching scoring had already
    passed that check). That point is gone; session is a hard gate only,
    per-pipeline, not also a score bonus. This meaningfully raises the real
    bar a setup has to clear.
  - Session gating is now per-pipeline instead of global: the fast H4/15m
    combo still only fires in London/NY (genuine institutional flow
    matters most for a stop-hunt read at that horizon); the slow 12H/1h
    combo is not session-gated at all (a 12H swing isn't really an
    intraday-session phenomenon), so the engine keeps scanning around the
    clock the way Castellan did, without loosening the fast combo's logic.
  - A same-symbol-across-pipelines cap (max 1 accepted signal per symbol
    per scan) prevents the two pipelines from firing correlated, largely
    redundant signals on the same asset in the same scan — something
    Castellan's dual-combo design explicitly allowed and never dealt with.

Timeframes : H4/15m and 12H/1h, run independently per symbol per scan.
Exchange   : Hyperliquid
Alerts     : Telegram (HTML)
"""

import os, time, math, threading, requests, random, json, pathlib, sys
import signal as _signal
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
from dataclasses import dataclass, field

# ═══════════════════════════════════════════════════════════════════════════════
# ENV
# ═══════════════════════════════════════════════════════════════════════════════
TG_BOT_TOKEN = os.getenv("TG_BOT_TOKEN")
TG_CHAT_ID   = os.getenv("TG_CHAT_ID")
if not TG_BOT_TOKEN:
    raise RuntimeError("TG_BOT_TOKEN environment variable is required")
if not TG_CHAT_ID:
    raise RuntimeError("TG_CHAT_ID environment variable is required")

HL_INFO_URL = "https://api.hyperliquid.xyz/info"
VERSION = "2.0.0"

# ── WATCHLIST / SECTOR MAP (unchanged from both prior engines) ──────────────
WATCHLIST = [
    "BTCUSDT", "ETHUSDT", "HYPEUSDT", "ZECUSDT", "NEARUSDT",
    "ONDOUSDT", "SUIUSDT", "PENGUUSDT", "BNBUSDT", "SOLUSDT",
    "TRXUSDT", "BCHUSDT", "DOGEUSDT", "ADAUSDT", "DOTUSDT",
    "TAOUSDT", "AVAXUSDT", "LINKUSDT", "AAVEUSDT", "XRPUSDT",
    "XLMUSDT", "UNIUSDT", "LTCUSDT", "APTUSDT", "PENDLEUSDT",
]

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

INTERVAL_MS = {
    "15m": 15 * 60 * 1000,
    "1h":  60 * 60 * 1000,
    "4h":  4  * 60 * 60 * 1000,
    "12h": 12 * 60 * 60 * 1000,
    "1d":  24 * 60 * 60 * 1000,
}

# ── SESSION FILTER (applied per-pipeline, see Combo.session_filter_enabled) ─
LONDON_OPEN_H, LONDON_CLOSE_H = 7, 12
NY_OPEN_H, NY_CLOSE_H         = 13, 20
DEAD_ZONE_START_H, DEAD_ZONE_END_H = 12, 13
WEEKEND_MODE_ENABLED = True
WEEKEND_MIN_CONFLUENCE_BUMP = 1

# ── FREQUENCY / DIVERSIFICATION / PORTFOLIO CAPS (global, across pipelines) ─
TOP_N_SIGNALS               = 4
MAX_SAME_DIRECTION          = 3
MAX_PER_SECTOR              = 1
MAX_PER_SYMBOL              = 1     # NEW: stops both pipelines double-firing one symbol
MAX_CONCURRENT_ACTIVE_SIGNALS = 10  # ported from Castellan: global brake across pipelines

# ── LIQUIDITY / EXECUTION SAFETY (ported from Castellan) ────────────────────
MIN_OI_USD          = 500_000
MAX_ENTRY_DRIFT_R   = 0.5   # re-checked against a live price fetch immediately before send

# ── OI / FUNDING (scoring bonus + liquidity gate, never a directional gate) ─
OI_FUNDING_ENABLED       = True
FUNDING_ALIGN_THRESHOLD  = 0.0001

# ── BTC REGIME FILTER ────────────────────────────────────────────────────────
BTC_REGIME_FILTER_ENABLED = True
BTC_SYMBOL = "BTCUSDT"

STATE_FILE    = pathlib.Path("state.json")
WIN_RATE_FILE = pathlib.Path("win_rate.json")
STATE_VERSION = 2

SIGNAL_COOLDOWN_S_DEFAULT = 60 * 60 * 4  # fallback for legacy state entries


# ═══════════════════════════════════════════════════════════════════════════════
# COMBO CONFIG — the two independent pipelines
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class Combo:
    id: str
    label: str
    htf_tf: str
    exec_tf: str
    n_htf: int
    n_exec: int

    swing_left_htf: int
    swing_right_htf: int
    structure_lookback_htf: int
    ema_fast: int
    ema_slow: int
    ema_sep_min_atr: float

    pd_lookback: int
    premium_threshold: float
    discount_threshold: float

    poi_lookback_htf: int
    poi_fresh_max_mitig: float
    poi_full_mitig: float
    poi_max_atr_distance: float

    pool_lookback_htf: int
    pool_equal_tol_atr: float

    swing_left_exec: int
    swing_right_exec: int
    sweep_lookback_exec: int
    sweep_recent_bars: int
    sweep_min_atr_ratio: float
    sweep_strong_atr_ratio: float

    displacement_max_bars: int
    displacement_min_atr: float
    displacement_strong_atr: float
    displacement_body_ratio_min: float
    choch_min_margin_atr: float
    choch_strong_margin_atr: float
    volume_bonus_ratio: float

    fvg_min_size_atr: float

    sl_buffer_atr: float
    entry_max_dist_atr: float
    tp1_min_rr: float
    tp2_min_rr: float
    tp1_fallback_rr: float
    tp2_fallback_rr: float
    tp3_fallback_rr: float

    min_confluence_score: int
    strong_signal_score: int
    aplus_signal_score: int
    theoretical_max_score: int

    session_filter_enabled: bool
    cooldown_hours: float
    active_signal_ttl_hours: float
    fill_timeout_hours: float


COMBOS: dict[str, Combo] = {
    "h4_15m": Combo(
        id="h4_15m", label="H4/15m", htf_tf="4h", exec_tf="15m",
        n_htf=150, n_exec=200,
        swing_left_htf=2, swing_right_htf=2, structure_lookback_htf=40,
        ema_fast=21, ema_slow=50, ema_sep_min_atr=0.30,
        pd_lookback=60, premium_threshold=0.60, discount_threshold=0.40,
        poi_lookback_htf=20, poi_fresh_max_mitig=0.15, poi_full_mitig=0.90, poi_max_atr_distance=3.0,
        pool_lookback_htf=80, pool_equal_tol_atr=0.15,
        swing_left_exec=2, swing_right_exec=2,
        sweep_lookback_exec=40, sweep_recent_bars=6, sweep_min_atr_ratio=0.15, sweep_strong_atr_ratio=0.35,
        displacement_max_bars=4, displacement_min_atr=1.2, displacement_strong_atr=2.0,
        displacement_body_ratio_min=0.60, choch_min_margin_atr=0.05, choch_strong_margin_atr=0.25,
        volume_bonus_ratio=1.30,
        fvg_min_size_atr=0.15,
        sl_buffer_atr=0.15, entry_max_dist_atr=0.60,
        tp1_min_rr=1.2, tp2_min_rr=2.5, tp1_fallback_rr=1.5, tp2_fallback_rr=3.0, tp3_fallback_rr=5.0,
        min_confluence_score=6, strong_signal_score=8, aplus_signal_score=10, theoretical_max_score=12,
        session_filter_enabled=True,
        cooldown_hours=4, active_signal_ttl_hours=48, fill_timeout_hours=6,
    ),
    "12h_1h": Combo(
        id="12h_1h", label="12H/1h", htf_tf="12h", exec_tf="1h",
        n_htf=100, n_exec=200,
        swing_left_htf=2, swing_right_htf=2, structure_lookback_htf=30,
        ema_fast=21, ema_slow=50, ema_sep_min_atr=0.30,
        pd_lookback=45, premium_threshold=0.60, discount_threshold=0.40,
        poi_lookback_htf=16, poi_fresh_max_mitig=0.15, poi_full_mitig=0.90, poi_max_atr_distance=3.0,
        pool_lookback_htf=60, pool_equal_tol_atr=0.18,
        swing_left_exec=2, swing_right_exec=2,
        sweep_lookback_exec=30, sweep_recent_bars=8, sweep_min_atr_ratio=0.15, sweep_strong_atr_ratio=0.35,
        displacement_max_bars=6, displacement_min_atr=1.2, displacement_strong_atr=2.0,
        displacement_body_ratio_min=0.60, choch_min_margin_atr=0.05, choch_strong_margin_atr=0.25,
        volume_bonus_ratio=1.30,
        fvg_min_size_atr=0.15,
        sl_buffer_atr=0.15, entry_max_dist_atr=0.60,
        tp1_min_rr=1.2, tp2_min_rr=2.5, tp1_fallback_rr=1.5, tp2_fallback_rr=3.0, tp3_fallback_rr=5.0,
        min_confluence_score=6, strong_signal_score=8, aplus_signal_score=10, theoretical_max_score=12,
        session_filter_enabled=False,   # slow combo is not an intraday-session phenomenon
        cooldown_hours=16, active_signal_ttl_hours=96, fill_timeout_hours=18,
    ),
}
# NOTE: the constants above are reasonable starting points carried over by
# analogy from the two source engines' own scaling choices, not the product
# of a backtest. Validate against historical data before running live.


# ── RATE LIMIT / HTTP (adaptive backoff, ported from Castellan — needed more
#    here since two pipelines roughly double outbound API volume) ───────────
_hl_lock              = threading.Lock()
_hl_last_req_ts       = 0.0
_hl_min_interval      = 0.20
_HL_MIN_INTERVAL_FLOOR = 0.20
_HL_MIN_INTERVAL_CEIL  = 0.60
_hl_consecutive_ok    = 0
_hl_session           = requests.Session()
_tg_session           = requests.Session()

# ── CACHES (cleared / repopulated once per scan run) ─────────────────────────
_candle_cache: dict[str, dict] = {}          # keyed "{symbol}:{tf}", htf only
_CANDLE_CACHE_TTL_S = 60 * 60

_atr_cache: dict[str, float] = {}
_market_ctx: dict[str, dict] = {}            # {coin: {funding_rate, oi_coins, mark_px}}

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
    kind: str

@dataclass
class StructureEvent:
    index: int
    kind: str
    direction: str
    level: float

@dataclass
class POI:
    high: float
    low: float
    direction: str
    index: int
    state: str = "fresh"
    mitigation_pct: float = 0.0

@dataclass
class FVG:
    high: float
    low: float
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
    end_index: int
    atr_ratio: float
    body_ratio: float
    choch_level: float
    choch_margin_atr: float
    volume_ratio: float

@dataclass
class NyxSignal:
    symbol: str
    direction: str
    combo_id: str
    combo_label: str
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


# ═══════════════════════════════════════════════════════════════════════════════
# HYPERLIQUID API
# ═══════════════════════════════════════════════════════════════════════════════

def hl_coin(symbol: str) -> str:
    return symbol.replace("USDT", "")


def hl_post(payload: dict):
    global _hl_last_req_ts, _hl_min_interval, _hl_consecutive_ok
    max_attempts = 5
    for attempt in range(max_attempts):
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
                with _hl_lock:
                    _hl_min_interval = min(_HL_MIN_INTERVAL_CEIL, _hl_min_interval * 1.25 + 0.02)
                    _hl_consecutive_ok = 0
                time.sleep(min(20.0, 1.0 * (2 ** attempt)) + random.uniform(0, 0.3))
                continue
            r.raise_for_status()
            data = r.json()
            if isinstance(data, dict) and "error" in data:
                raise ValueError(f"Hyperliquid API error (HTTP 200): {data['error']}")
            with _hl_lock:
                _hl_consecutive_ok += 1
                if _hl_consecutive_ok >= 10:
                    _hl_min_interval = _HL_MIN_INTERVAL_FLOOR
                    _hl_consecutive_ok = 0
                else:
                    _hl_min_interval = max(_HL_MIN_INTERVAL_FLOOR, _hl_min_interval - 0.0025)
            return data
        except Exception:
            if attempt == max_attempts - 1:
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


def get_candles_cached(symbol: str, tf: str, n: int) -> list[dict]:
    """HTF candles only — a 4h/12h bar closes rarely enough to cache safely.
    Execution-tf candles are always fetched fresh by the caller."""
    key = f"{symbol}:{tf}"
    entry = _candle_cache.get(key)
    if entry and (time.time() - entry["ts"]) < _CANDLE_CACHE_TTL_S and entry["n"] >= n:
        return entry["candles"][-n:]
    candles = get_candles(symbol, tf, n)
    _candle_cache[key] = {"candles": candles, "ts": time.time(), "n": n}
    return candles


def fetch_all_mids() -> dict[str, float]:
    try:
        raw = hl_post({"type": "allMids"})
        return {k: float(v) for k, v in raw.items()} if raw else {}
    except Exception as e:
        print(f"  [MIDS] fetch error: {e}")
        return {}


def fetch_all_market_ctx() -> None:
    """Funding + open interest (coins) + mark price in one call — used for
    the OI liquidity gate, the funding scoring bonus, and available as a
    price fallback."""
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
            _market_ctx[coin] = {
                "funding_rate": float(ctx["funding"]) if ctx.get("funding") is not None else None,
                "oi_coins":     float(ctx["openInterest"]) if ctx.get("openInterest") is not None else None,
                "mark_px":      float(ctx["markPx"]) if ctx.get("markPx") is not None else None,
            }
        print(f"  [MARKET CTX] Fetched {len(_market_ctx)} assets")
    except Exception as e:
        print(f"  [MARKET CTX] fetch error: {e}")


def get_funding(symbol: str) -> float | None:
    row = _market_ctx.get(hl_coin(symbol))
    return row["funding_rate"] if row else None


def get_open_interest_usd(symbol: str) -> float | None:
    row = _market_ctx.get(hl_coin(symbol))
    if not row or row.get("oi_coins") is None or row.get("mark_px") is None:
        return None
    return row["oi_coins"] * row["mark_px"]


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
# SESSION FILTER (per-pipeline, see Combo.session_filter_enabled)
# ═══════════════════════════════════════════════════════════════════════════════

def is_active_session() -> bool:
    now = datetime.now(timezone.utc)
    hour = now.hour
    if DEAD_ZONE_START_H <= hour < DEAD_ZONE_END_H:
        return False
    return (LONDON_OPEN_H <= hour < LONDON_CLOSE_H) or (NY_OPEN_H <= hour < NY_CLOSE_H)


def get_min_confluence_score(combo: Combo) -> int:
    score = combo.min_confluence_score
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
    """Walk swings chronologically and classify each break of a prior swing
    extreme as BOS (continuation) or CHoCH (reversal). Returns the most
    recent confirmed direction plus the event list."""
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

    direction = events[-1].direction if events else "neutral"
    return direction, events


def htf_ema_trend(candles: list[dict], atr_htf: float, combo: Combo) -> str:
    closes = [c["c"] for c in candles]
    ema_fast = calc_ema(closes, combo.ema_fast)
    ema_slow = calc_ema(closes, combo.ema_slow)
    if not ema_fast or not ema_slow or atr_htf <= 0:
        return "neutral"
    sep = ema_fast[-1] - ema_slow[-1]
    if abs(sep) < combo.ema_sep_min_atr * atr_htf:
        return "neutral"
    return "bull" if sep > 0 else "bear"


def htf_bias(candles: list[dict], atr_htf: float,
             combo: Combo) -> tuple[str, list[StructureEvent], list[SwingPoint]]:
    swings = find_swings(candles, combo.swing_left_htf, combo.swing_right_htf)
    structure_dir, events = detect_structure(candles, swings, combo.structure_lookback_htf)
    ema_dir = htf_ema_trend(candles, atr_htf, combo)
    bias = structure_dir if structure_dir == ema_dir and structure_dir != "neutral" else "neutral"
    return bias, events, swings


# ═══════════════════════════════════════════════════════════════════════════════
# HTF DEALING RANGE / PREMIUM-DISCOUNT
# ═══════════════════════════════════════════════════════════════════════════════

def premium_discount_zone(candles: list[dict], lookback: int) -> dict:
    window = candles[-lookback:]
    hi = max(c["h"] for c in window)
    lo = min(c["l"] for c in window)
    close = candles[-1]["c"]
    rng = hi - lo
    pct = (close - lo) / rng if rng > 0 else 0.5
    return {"high": hi, "low": lo, "mid": (hi + lo) / 2, "pct": pct}


# ═══════════════════════════════════════════════════════════════════════════════
# HTF POI (order block behind the most recent BOS in bias direction)
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


def classify_poi_state(mitig: float, combo: Combo) -> str:
    if mitig >= combo.poi_full_mitig:
        return "full"
    if mitig <= combo.poi_fresh_max_mitig:
        return "fresh"
    return "partial"


def find_htf_poi(candles: list[dict], swings: list[SwingPoint], bias: str,
                  atr_htf: float, current_price: float, combo: Combo) -> POI | None:
    if bias not in ("bull", "bear"):
        return None
    start_idx = max(0, len(candles) - combo.poi_lookback_htf)
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
    state = classify_poi_state(mitig, combo)
    if state == "full":
        return None

    if atr_htf > 0:
        dist_atr = abs(current_price - (zone_high if bias == "bear" else zone_low)) / atr_htf
        if dist_atr > combo.poi_max_atr_distance:
            return None

    return POI(high=zone_high, low=zone_low, direction=bias, index=pivot.index,
                state=state, mitigation_pct=mitig)


# ═══════════════════════════════════════════════════════════════════════════════
# HTF LIQUIDITY POOLS (equal highs/lows -> TP2 / TP3 draw targets)
# ═══════════════════════════════════════════════════════════════════════════════

def find_htf_liquidity_pools(candles: list[dict], swings: list[SwingPoint], direction: str,
                              current_price: float, atr_htf: float, combo: Combo) -> list[float]:
    kind = "high" if direction == "long" else "low"
    start_idx = max(0, len(candles) - combo.pool_lookback_htf)
    tol = max(atr_htf * combo.pool_equal_tol_atr, current_price * 0.0005)
    points = [s.price for s in swings if s.kind == kind and s.index >= start_idx]
    if direction == "long":
        points = sorted(p for p in points if p > current_price)
    else:
        points = sorted((p for p in points if p < current_price), reverse=True)

    pools: list[float] = []
    for p in points:
        if not pools or abs(p - pools[-1]) > tol:
            pools.append(p)
    return pools


# ═══════════════════════════════════════════════════════════════════════════════
# BTC REGIME FILTER
# ═══════════════════════════════════════════════════════════════════════════════

_btc_regime_combo = COMBOS["h4_15m"]  # regime read off the fast pipeline's HTF

def get_btc_regime() -> str:
    if not BTC_REGIME_FILTER_ENABLED:
        return "neutral"
    try:
        candles = get_candles_cached(BTC_SYMBOL, _btc_regime_combo.htf_tf, _btc_regime_combo.n_htf)
        if len(candles) < _btc_regime_combo.ema_slow + 5:
            return "neutral"
        atr = calc_atr_cached(BTC_SYMBOL, _btc_regime_combo.htf_tf, candles)
        return htf_ema_trend(candles, atr, _btc_regime_combo)
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
# EXEC-TF LIQUIDITY SWEEP (hard gate #1)
# ═══════════════════════════════════════════════════════════════════════════════

def detect_exec_sweep(candles: list[dict], swings: list[SwingPoint], bias: str,
                       atr_exec: float, combo: Combo) -> SweepEvent | None:
    if atr_exec <= 0 or bias not in ("bull", "bear"):
        return None
    n = len(candles)
    recent_start = max(0, n - combo.sweep_recent_bars)
    search_start = max(0, n - combo.sweep_lookback_exec)

    best: SweepEvent | None = None
    for i in range(recent_start, n):
        c = candles[i]
        prior_swings = [s for s in swings if s.index < i and s.index >= search_start]
        if bias == "bull":
            lows = [s for s in prior_swings if s.kind == "low"]
            if not lows:
                continue
            swept = [s for s in lows if c["l"] < s.price]
            if not swept:
                continue
            level = min(s.price for s in swept)   # deepest liquidity taken, not nearest-in-time
            if c["c"] > level:
                ratio = (level - c["l"]) / atr_exec
                if ratio >= combo.sweep_min_atr_ratio:
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
            level = max(s.price for s in swept)
            if c["c"] < level:
                ratio = (c["h"] - level) / atr_exec
                if ratio >= combo.sweep_min_atr_ratio:
                    cand = SweepEvent(index=i, level=level, wick_extreme=c["h"], atr_ratio=ratio)
                    if best is None or i > best.index:
                        best = cand
    return best


# ═══════════════════════════════════════════════════════════════════════════════
# EXEC-TF DISPLACEMENT + CHoCH (hard gate #2)
# ═══════════════════════════════════════════════════════════════════════════════

def detect_displacement(candles: list[dict], sweep: SweepEvent, bias: str,
                         atr_exec: float, swings: list[SwingPoint], combo: Combo) -> DisplacementLeg | None:
    n = len(candles)
    window_end = min(n, sweep.index + 1 + combo.displacement_max_bars)
    window = candles[sweep.index:window_end]
    if len(window) < 1 or atr_exec <= 0:
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
    atr_ratio = net_move / atr_exec
    if atr_ratio < combo.displacement_min_atr:
        return None

    best_body = max(body_ratio(c) for c in window)
    if best_body < combo.displacement_body_ratio_min:
        return None

    opp_kind = "high" if bias == "bull" else "low"
    prior_opp = [s for s in swings if s.kind == opp_kind and s.index < sweep.index]
    if not prior_opp:
        return None
    choch_ref = max(prior_opp, key=lambda s: s.index)
    closes_in_window = [c["c"] for c in candles[sweep.index:end_index + 1]]
    if not closes_in_window:
        return None
    best_close = max(closes_in_window) if bias == "bull" else min(closes_in_window)
    margin = (best_close - choch_ref.price) / atr_exec if bias == "bull" \
        else (choch_ref.price - best_close) / atr_exec
    if margin < combo.choch_min_margin_atr:
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
                       direction: str, atr_exec: float, combo: Combo) -> FVG | None:
    best: FVG | None = None
    lo_bound = max(1, start_idx)
    hi_bound = min(len(candles) - 1, end_idx)
    for i in range(lo_bound, hi_bound):
        a, b = candles[i - 1], candles[i + 1]
        if direction == "bull" and b["l"] > a["h"]:
            size = b["l"] - a["h"]
            if size >= combo.fvg_min_size_atr * atr_exec:
                cand = FVG(high=b["l"], low=a["h"], direction="bull", index=i)
                if best is None or cand.index > best.index:
                    best = cand
        elif direction == "bear" and b["h"] < a["l"]:
            size = a["l"] - b["h"]
            if size >= combo.fvg_min_size_atr * atr_exec:
                cand = FVG(high=a["l"], low=b["h"], direction="bear", index=i)
                if best is None or cand.index > best.index:
                    best = cand
    return best


def breaker_zone(candles: list[dict], sweep_index: int, direction: str) -> tuple[float, float]:
    c = candles[sweep_index]
    if direction == "bull":
        return max(c["o"], c["c"]), c["l"]
    return c["h"], min(c["o"], c["c"])


def compute_entry_zone(breaker_hi: float, breaker_lo: float, fvg: FVG | None,
                        direction: str) -> tuple[float, float, float]:
    zone_hi, zone_lo = breaker_hi, breaker_lo
    if fvg is not None:
        overlap_hi = min(breaker_hi, fvg.high)
        overlap_lo = max(breaker_lo, fvg.low)
        if overlap_hi > overlap_lo:
            zone_hi, zone_lo = overlap_hi, overlap_lo
    exact_entry = (zone_hi + zone_lo) / 2
    return zone_hi, zone_lo, exact_entry


def fvg_is_fresh(candles: list[dict], fvg: FVG, direction: str, combo: Combo) -> bool:
    after = candles[fvg.index + 1:]
    mitig = compute_mitigation(after, fvg.high, fvg.low, direction)
    return mitig <= combo.poi_fresh_max_mitig


def breaker_is_untouched(candles: list[dict], sweep_index: int, zone_hi: float,
                          zone_lo: float) -> bool:
    for c in candles[sweep_index + 1:-1]:
        if c["l"] <= zone_hi and c["h"] >= zone_lo:
            return False
    return True


def find_exec_liquidity_target(swings: list[SwingPoint], direction: str,
                                entry: float) -> float | None:
    kind = "high" if direction == "long" else "low"
    candidates = [s.price for s in swings if s.kind == kind]
    if direction == "long":
        candidates = [p for p in candidates if p > entry]
        return min(candidates) if candidates else None
    candidates = [p for p in candidates if p < entry]
    return max(candidates) if candidates else None


# ═══════════════════════════════════════════════════════════════════════════════
# SIGNAL ASSEMBLY (per pipeline)
# ═══════════════════════════════════════════════════════════════════════════════

def compute_signal(symbol: str, combo: Combo, btc_regime: str) -> NyxSignal | None:
    # ── Liquidity floor (ported from Castellan) — cheapest check first ────
    oi_usd = get_open_interest_usd(symbol)
    if oi_usd is not None and oi_usd < MIN_OI_USD:
        return None

    # ── Session gate — per pipeline, not global (see module docstring) ───
    if combo.session_filter_enabled and not is_active_session():
        return None

    candles_htf = get_candles_cached(symbol, combo.htf_tf, combo.n_htf)
    if len(candles_htf) < combo.ema_slow + 10:
        return None
    candles_exec = get_candles(symbol, combo.exec_tf, combo.n_exec)  # always fresh
    if len(candles_exec) < 60:
        return None

    atr_htf  = calc_atr_cached(symbol, combo.htf_tf, candles_htf)
    atr_exec = calc_atr_cached(symbol, combo.exec_tf, candles_exec)
    if atr_htf <= 0 or atr_exec <= 0:
        return None

    current_price = candles_exec[-1]["c"]

    # ── HTF bias: structure AND EMA must agree (hard gate) ────────────────
    bias, _events, swings_htf = htf_bias(candles_htf, atr_htf, combo)
    if bias == "neutral":
        return None

    direction = "long" if bias == "bull" else "short"

    # ── BTC regime filter (hard gate) ──────────────────────────────────────
    if btc_regime_blocks(symbol, direction, btc_regime):
        return None

    # ── Premium/discount alignment (hard gate) ────────────────────────────
    pd = premium_discount_zone(candles_htf, combo.pd_lookback)
    if bias == "bull" and pd["pct"] > combo.discount_threshold:
        return None
    if bias == "bear" and pd["pct"] < combo.premium_threshold:
        return None

    # ── HTF POI must exist and not be fully mitigated (hard gate) ─────────
    poi = find_htf_poi(candles_htf, swings_htf, bias, atr_htf, current_price, combo)
    if poi is None:
        return None

    # ── Exec-tf sweep (hard gate #1) ───────────────────────────────────────
    swings_exec = find_swings(candles_exec, combo.swing_left_exec, combo.swing_right_exec)
    sweep = detect_exec_sweep(candles_exec, swings_exec, bias, atr_exec, combo)
    if sweep is None:
        return None

    # ── Displacement + CHoCH (hard gate #2) ────────────────────────────────
    disp = detect_displacement(candles_exec, sweep, bias, atr_exec, swings_exec, combo)
    if disp is None:
        return None

    # ── Fresh imbalance behind the displacement leg (hard gate #3) ────────
    fvg = find_freshest_fvg(candles_exec, sweep.index, disp.end_index, bias, atr_exec, combo)
    if fvg is None:
        return None
    if not fvg_is_fresh(candles_exec, fvg, bias, combo):
        return None

    breaker_hi, breaker_lo = breaker_zone(candles_exec, sweep.index, bias)
    zone_hi, zone_lo, exact_entry = compute_entry_zone(breaker_hi, breaker_lo, fvg, bias)
    if zone_hi <= zone_lo:
        return None

    backup_entry = (zone_hi if abs(current_price - zone_hi) <= abs(current_price - zone_lo)
                     else zone_lo)

    dist_atr = abs(current_price - exact_entry) / atr_exec
    if dist_atr > combo.entry_max_dist_atr:
        return None

    buffer = combo.sl_buffer_atr * atr_exec
    stop_loss = (sweep.wick_extreme - buffer) if direction == "long" else (sweep.wick_extreme + buffer)
    risk = abs(exact_entry - stop_loss)
    if risk <= 0:
        return None

    tp1 = find_exec_liquidity_target(swings_exec, direction, exact_entry)
    if tp1 is None or abs(tp1 - exact_entry) / risk < combo.tp1_min_rr:
        tp1 = exact_entry + risk * combo.tp1_fallback_rr if direction == "long" \
            else exact_entry - risk * combo.tp1_fallback_rr

    htf_pools = find_htf_liquidity_pools(candles_htf, swings_htf, direction, current_price, atr_htf, combo)
    tp2 = None
    for p in htf_pools:
        if abs(p - exact_entry) / risk >= combo.tp2_min_rr:
            tp2 = p
            break
    if tp2 is None:
        tp2 = exact_entry + risk * combo.tp2_fallback_rr if direction == "long" \
            else exact_entry - risk * combo.tp2_fallback_rr
    if abs(tp2 - exact_entry) / risk < combo.tp2_min_rr:
        return None

    tp3 = None
    for p in htf_pools:
        if direction == "long" and p > tp2 and abs(p - exact_entry) / risk >= combo.tp2_min_rr * 1.5:
            tp3 = p
            break
        if direction == "short" and p < tp2 and abs(p - exact_entry) / risk >= combo.tp2_min_rr * 1.5:
            tp3 = p
            break
    if tp3 is None:
        tp3 = exact_entry + risk * combo.tp3_fallback_rr if direction == "long" \
            else exact_entry - risk * combo.tp3_fallback_rr

    # ── Confluence scoring ─────────────────────────────────────────────────
    # NOTE: no "Session" point here (fixed vs. Nyx v1) — session is already
    # a hard gate above when combo.session_filter_enabled, so awarding it a
    # score point too was giving every qualifying signal a free point that
    # discriminated nothing.
    score = 0
    combos_hit: list[str] = []

    if sweep.atr_ratio >= combo.sweep_strong_atr_ratio:
        score += 2; combos_hit.append("Sweep(strong)")
    else:
        score += 1; combos_hit.append("Sweep")

    if disp.atr_ratio >= combo.displacement_strong_atr:
        score += 2; combos_hit.append("Displacement(strong)")
    else:
        score += 1; combos_hit.append("Displacement")

    if disp.choch_margin_atr >= combo.choch_strong_margin_atr:
        score += 2; combos_hit.append("CHoCH(clean)")
    else:
        score += 1; combos_hit.append("CHoCH")

    combos_hit.append("Imbalance(fresh)")
    score += 1

    if breaker_is_untouched(candles_exec, sweep.index, breaker_hi, breaker_lo):
        score += 1; combos_hit.append("Breaker(untouched)")

    if disp.volume_ratio >= combo.volume_bonus_ratio:
        score += 1; combos_hit.append("Volume")

    if poi.state == "fresh":
        score += 1; combos_hit.append("HTF-POI(fresh)")

    ema_dir = htf_ema_trend(candles_htf, atr_htf, combo)
    if ema_dir == bias:
        closes = [c["c"] for c in candles_htf]
        ema_fast = calc_ema(closes, combo.ema_fast)
        ema_slow = calc_ema(closes, combo.ema_slow)
        if ema_fast and ema_slow and abs(ema_fast[-1] - ema_slow[-1]) >= combo.ema_sep_min_atr * atr_htf * 1.5:
            score += 1; combos_hit.append("HTF-Trend(strong)")

    funding = get_funding(symbol)
    if funding is not None:
        if direction == "long" and funding <= -FUNDING_ALIGN_THRESHOLD:
            score += 1; combos_hit.append("Funding")
        elif direction == "short" and funding >= FUNDING_ALIGN_THRESHOLD:
            score += 1; combos_hit.append("Funding")

    min_score = get_min_confluence_score(combo)
    if score < min_score:
        return None

    if score >= combo.aplus_signal_score:
        grade = "A+"
    elif score >= combo.strong_signal_score:
        grade = "A"
    else:
        grade = "B"

    return NyxSignal(
        symbol=symbol, direction=direction, combo_id=combo.id, combo_label=combo.label,
        entry_zone_high=zone_hi, entry_zone_low=zone_lo, exact_entry=exact_entry,
        backup_entry=backup_entry,
        stop_loss=stop_loss, take_profit_1=tp1, take_profit_2=tp2, take_profit_3=tp3,
        confluence=score, max_score=combo.theoretical_max_score, signal_grade=grade,
        combos_hit=combos_hit, h4_bias=bias, poi_state=poi.state,
        sweep_atr_ratio=sweep.atr_ratio, displacement_atr_ratio=disp.atr_ratio,
        funding_rate=funding, timestamp=datetime.now(timezone.utc).isoformat(),
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


def format_signal_message(sig: NyxSignal, live_price: float | None = None) -> str:
    arrow = "🟢 LONG" if sig.direction == "long" else "🔴 SHORT"
    grade_emoji = {"A+": "💎", "A": "⭐", "B": "✅"}[sig.signal_grade]
    combos_str = ", ".join(sig.combos_hit)
    funding_line = f"\nFunding: {sig.funding_rate*100:.4f}%/8h" if sig.funding_rate is not None else ""
    price_line = ""
    if live_price is not None:
        dist_pct = (live_price - sig.exact_entry) / sig.exact_entry * 100 if sig.exact_entry else 0.0
        sign = "+" if dist_pct >= 0 else ""
        price_line = f"Live price: {fmt_price(live_price)} ({sign}{dist_pct:.2f}% from entry)\n"

    return (
        f"{grade_emoji} <b>NYX SIGNAL — {sig.symbol}</b> {arrow}  <i>({sig.combo_label})</i>\n"
        f"Grade: <b>{sig.signal_grade}</b>  |  Confluence: {sig.confluence}/{sig.max_score}\n"
        f"HTF Bias: {sig.h4_bias.upper()}  |  HTF POI: {sig.poi_state}\n"
        f"─────────────────────────\n"
        f"{price_line}"
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
# DEDUP / COOLDOWN (per-combo, matching Castellan's per-combo cooldown state)
# ═══════════════════════════════════════════════════════════════════════════════

def signal_key(symbol: str, direction: str, combo_id: str) -> str:
    return f"{combo_id}:{symbol}:{direction}"


def is_duplicate(sig: NyxSignal, combo: Combo) -> bool:
    key = signal_key(sig.symbol, sig.direction, combo.id)
    ts = _fired_signals.get(key)
    if ts is None:
        return False
    return (time.time() - ts) < combo.cooldown_hours * 3600


def mark_fired(sig: NyxSignal) -> None:
    _fired_signals[signal_key(sig.symbol, sig.direction, sig.combo_id)] = time.time()


# ═══════════════════════════════════════════════════════════════════════════════
# SCAN
# ═══════════════════════════════════════════════════════════════════════════════

def scan_symbol(symbol: str, combo: Combo, btc_regime: str) -> NyxSignal | None:
    try:
        sig = compute_signal(symbol, combo, btc_regime)
        if sig is None:
            return None
        if is_duplicate(sig, combo):
            return None
        return sig
    except Exception as e:
        print(f"  [SCAN ERROR] {symbol} [{combo.label}]: {e}")
        return None


def run_scan() -> None:
    global _last_scan_ts

    _atr_cache.clear()
    fetch_all_market_ctx()
    btc_regime = get_btc_regime()
    print(f"  [BTC REGIME] {btc_regime}")

    pairs = [(sym, combo) for combo in COMBOS.values() for sym in WATCHLIST]
    raw_signals: list[NyxSignal] = []
    with ThreadPoolExecutor(max_workers=8) as pool:
        futures = {pool.submit(scan_symbol, sym, combo, btc_regime): (sym, combo) for sym, combo in pairs}
        for fut in as_completed(futures):
            sig = fut.result()
            if sig:
                raw_signals.append(sig)

    print(f"  [SCAN] {len(raw_signals)} candidate(s) across {len(COMBOS)} pipeline(s) before caps")
    raw_signals.sort(key=lambda s: s.confluence, reverse=True)

    # ── Global concurrency brake (ported from Castellan) ──────────────────
    active_count = sum(1 for s in _active_signals.values() if not s.get("resolved"))
    available_slots = max(0, MAX_CONCURRENT_ACTIVE_SIGNALS - active_count)
    if available_slots <= 0:
        print(f"  [CONCURRENCY] {active_count} active signal(s) at/above cap "
              f"({MAX_CONCURRENT_ACTIVE_SIGNALS}) — no new signals this scan")
        _last_scan_ts = time.time()
        return
    n_target = min(TOP_N_SIGNALS, available_slots)

    accepted: list[NyxSignal] = []
    sector_used: dict[str, int] = {}
    direction_used: dict[str, int] = {}
    symbol_used: dict[str, int] = {}

    for sig in raw_signals:
        if len(accepted) >= n_target:
            break
        sector = SECTOR_MAP.get(sig.symbol, "other")
        if sector_used.get(sector, 0) >= MAX_PER_SECTOR:
            continue
        if direction_used.get(sig.direction, 0) >= MAX_SAME_DIRECTION:
            continue
        if symbol_used.get(sig.symbol, 0) >= MAX_PER_SYMBOL:
            continue   # stops both pipelines firing the same symbol in one scan
        accepted.append(sig)
        sector_used[sector] = sector_used.get(sector, 0) + 1
        direction_used[sig.direction] = direction_used.get(sig.direction, 0) + 1
        symbol_used[sig.symbol] = symbol_used.get(sig.symbol, 0) + 1

    print(f"  [SCAN] {len(accepted)} signal(s) accepted after diversification + concurrency caps")

    # ── Live-price staleness re-check right before sending (ported from
    #    Castellan) — refuses to fire on a plan the market has already
    #    moved away from while the rest of the scan/selection ran. ────────
    fresh_mids = fetch_all_mids()
    for sig in accepted:
        coin = hl_coin(sig.symbol)
        live_price = fresh_mids.get(coin)
        if live_price is None:
            print(f"  [SKIP] {sig.symbol} [{sig.combo_label}] — could not confirm live price, "
                  f"refusing to send an unverified entry")
            continue
        risk = abs(sig.exact_entry - sig.stop_loss)
        drift_r = abs(live_price - sig.exact_entry) / risk if risk > 0 else float("inf")
        if drift_r > MAX_ENTRY_DRIFT_R:
            print(f"  [SKIP] {sig.symbol} [{sig.combo_label}] — entry stale: "
                  f"live={fmt_price(live_price)} is {drift_r:.2f}R from entry={fmt_price(sig.exact_entry)}")
            continue

        msg = format_signal_message(sig, live_price)
        msg_id = send_telegram_get_id(msg)
        mark_fired(sig)
        if msg_id:
            track_active_signal(sig, msg_id)
            print(f"  [FIRED] {sig.symbol} {sig.direction.upper()} [{sig.combo_label}] "
                  f"grade={sig.signal_grade} conf={sig.confluence}/{sig.max_score}")
        else:
            print(f"  [TG FAIL] {sig.symbol} [{sig.combo_label}]")

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
    combo = COMBOS.get(sig.combo_id)
    key = f"{sig.symbol}:{sig.combo_id}:{sig.direction}:{int(time.time())}"
    _active_signals[key] = {
        "symbol": sig.symbol, "direction": sig.direction, "message_id": message_id,
        "combo_id": sig.combo_id, "combo_label": sig.combo_label,
        "exact_entry": sig.exact_entry, "backup_entry": sig.backup_entry,
        "stop_loss": sig.stop_loss,
        "tp1": sig.take_profit_1, "tp2": sig.take_profit_2, "tp3": sig.take_profit_3,
        "combos_hit": sig.combos_hit, "signal_grade": sig.signal_grade,
        "filled": False, "primary_filled": False, "backup_filled": False,
        "fill_price": None, "filled_at": None,
        "tp1_hit": False, "tp2_hit": False, "tp3_hit": False,
        "resolved": False, "sent_at": time.time(),
        "ttl_hours": combo.active_signal_ttl_hours if combo else 48.0,
        "fill_timeout_hours": combo.fill_timeout_hours if combo else 6.0,
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
        ttl_s = s.get("ttl_hours", 48.0) * 3600
        fill_timeout_s = s.get("fill_timeout_hours", 6.0) * 3600

        if not s["filled"]:
            if now - s["sent_at"] > fill_timeout_s:
                react_to_message(s["message_id"], "⌛")
                record_outcome(s["symbol"], s.get("combo_id", ""), "expired")
                s["resolved"] = True
                continue

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
            filled_prices = [p for p, hit in
                              ((s["exact_entry"], s["primary_filled"]),
                               (s["backup_entry"], s["backup_filled"])) if hit]
            s["fill_price"] = sum(filled_prices) / len(filled_prices)

        sl_hit = (price <= s["stop_loss"]) if direction == "long" else (price >= s["stop_loss"])
        if sl_hit:
            outcome = "partial_loss" if s["tp1_hit"] else "loss"
            react_to_message(s["message_id"], "❌")
            record_outcome(s["symbol"], s.get("combo_id", ""), outcome)
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
                    record_outcome(s["symbol"], s.get("combo_id", ""), "win")
                    s["resolved"] = True
                    continue

        if s["tp3"] and not s["tp3_hit"]:
            hit = (price >= s["tp3"]) if direction == "long" else (price <= s["tp3"])
            if hit:
                s["tp3_hit"] = True
                react_to_message(s["message_id"], "🏆")
                record_outcome(s["symbol"], s.get("combo_id", ""), "win_full")
                s["resolved"] = True
                continue

        if now - s["sent_at"] > ttl_s:
            outcome = "timeout_win" if s["tp1_hit"] else "timeout"
            record_outcome(s["symbol"], s.get("combo_id", ""), outcome)
            s["resolved"] = True

    for key in [k for k, s in _active_signals.items() if s.get("resolved")]:
        _active_signals.pop(key, None)


# ═══════════════════════════════════════════════════════════════════════════════
# WIN RATE MEMORY (now segmented by pipeline too)
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


def _bump_bucket(bucket: dict, outcome: str) -> None:
    if outcome in ("win", "win_full", "timeout_win", "partial_loss"):
        bucket["wins"] += 1
    elif outcome == "loss":
        bucket["losses"] += 1
    else:
        bucket["other"] += 1


def record_outcome(symbol: str, combo_id: str, outcome: str) -> None:
    global _win_rate_dirty
    _bump_bucket(_win_rate_data.setdefault("overall", {"wins": 0, "losses": 0, "other": 0}), outcome)
    _bump_bucket(_win_rate_data.setdefault(symbol, {"wins": 0, "losses": 0, "other": 0}), outcome)
    if combo_id:
        _bump_bucket(_win_rate_data.setdefault(f"combo:{combo_id}",
                                                {"wins": 0, "losses": 0, "other": 0}), outcome)
    _win_rate_dirty = True


def get_win_rate_summary() -> str:
    overall = _win_rate_data.get("overall", {"wins": 0, "losses": 0, "other": 0})
    total = overall["wins"] + overall["losses"]
    pct = (overall["wins"] / total * 100) if total else 0.0
    lines = [f"[WIN RATE] {overall['wins']}W / {overall['losses']}L "
             f"({pct:.1f}%) — {overall['other']} other outcomes tracked"]
    for combo in COMBOS.values():
        b = _win_rate_data.get(f"combo:{combo.id}")
        if b:
            t = b["wins"] + b["losses"]
            p = (b["wins"] / t * 100) if t else 0.0
            lines.append(f"  [{combo.label}] {b['wins']}W / {b['losses']}L ({p:.1f}%)")
    return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════════════════
# STATE PERSISTENCE (defensive: falls back to .bak, checks schema version —
# ported from Castellan)
# ═══════════════════════════════════════════════════════════════════════════════

def _default_state() -> dict:
    return {"_version": STATE_VERSION, "fired_signals": {}, "active_signals": {}, "last_scan_ts": 0.0}


def load_state() -> None:
    global _fired_signals, _active_signals, _last_scan_ts
    for path in (STATE_FILE, STATE_FILE.with_suffix(".bak")):
        if not path.exists():
            continue
        try:
            data = json.loads(path.read_text())
            if data.get("_version", 1) != STATE_VERSION:
                print(f"  [STATE] Schema version mismatch in {path} — starting fresh")
                continue
            _fired_signals = {k: float(v) for k, v in data.get("fired_signals", {}).items()}
            _active_signals = data.get("active_signals", {})
            _last_scan_ts = float(data.get("last_scan_ts", 0.0))
            if path != STATE_FILE:
                print(f"  [STATE] Loaded from backup {path}")
            print(f"  [STATE] Loaded {len(_fired_signals)} cooldown + {len(_active_signals)} active signals")
            return
        except Exception as e:
            print(f"  [STATE] Failed to load {path}: {e}")
    print("  [STATE] Starting fresh — no valid state file found")
    fresh = _default_state()
    _fired_signals, _active_signals, _last_scan_ts = {}, {}, 0.0


def save_state() -> None:
    if _win_rate_dirty:
        save_win_rate()
    try:
        state_json = json.dumps({
            "_version": STATE_VERSION,
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


def cleanup_state() -> None:
    now = time.time()
    before = len(_fired_signals)
    max_cooldown_s = max(c.cooldown_hours for c in COMBOS.values()) * 3600
    expired = [k for k, ts in _fired_signals.items() if now - ts > max_cooldown_s]
    for k in expired:
        _fired_signals.pop(k, None)

    before_active = len(_active_signals)
    stale = [k for k, s in _active_signals.items()
             if s.get("resolved", False)
             or now - s.get("sent_at", 0) > s.get("ttl_hours", 48.0) * 3600]
    for k in stale:
        _active_signals.pop(k, None)

    print(f"  [CLEANUP] Removed {before - len(_fired_signals)} expired cooldowns, "
          f"{before_active - len(_active_signals)} stale active signals")


# ═══════════════════════════════════════════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════════════════════════════════════════

def _shutdown_handler(signum, frame):
    print(f"\n  [SHUTDOWN] Received signal {signum} — saving state before exit.")
    save_state()
    sys.exit(0)


def main() -> None:
    print("=" * 60)
    print(f"  Nyx Engine v{VERSION}  [dual-pipeline, single-scan mode]")
    print(f"  Pipelines: {', '.join(c.label for c in COMBOS.values())}")
    print(f"  Top {TOP_N_SIGNALS} signals/scan | Sector cap {MAX_PER_SECTOR} | "
          f"Same-dir cap {MAX_SAME_DIRECTION} | Same-symbol cap {MAX_PER_SYMBOL}")
    print(f"  Global concurrency cap: {MAX_CONCURRENT_ACTIVE_SIGNALS} unresolved active signals")
    print(f"  OI floor: ${MIN_OI_USD:,.0f} | Entry drift guard: {MAX_ENTRY_DRIFT_R}R")
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
        run_scan()
    except Exception as e:
        print(f"[MAIN ERROR] {e}")
        send_telegram_get_id(f"⚠️ Nyx Engine error: {e}")

    cleanup_state()
    save_state()
    print("  [DONE] Scan complete. Exiting.")


if __name__ == "__main__":
    main()
