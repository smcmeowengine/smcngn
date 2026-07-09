#!/usr/bin/env python3
"""
Seed / warm-up script for AXIS's candle_cache.json.

Run this ONCE, manually, before the first live cron/loop run (or any time
the cache file has been wiped, or a new symbol has been added to
WATCHLIST). It populates candle_cache.json with a full pull for every
symbol/timeframe, SEQUENTIALLY, so the first real scan afterward only
ever needs small delta-fetches -- avoiding the concurrent full-window
burst that was tripping Hyperliquid's weight limit.

This does not change your normal cadence or add any new endpoints; it's
the same public candleSnapshot/metaAndAssetCtxs calls the engine already
makes, just run once, slowly, ahead of time.

Usage:
    python3 seed_candle_cache.py
"""

from __future__ import annotations

import sys
import time

# Reuse the engine's own config, HTTP layer, and rate limiter so this
# script is governed by the exact same weight budget as the live engine.
import axis_engine_v2_1_0 as axis

# Extra inter-symbol delay on top of the shared weight limiter. The
# limiter alone is enough to stay under budget, but a small pause between
# symbols keeps this one-off pull comfortably polite since it's outside
# the normal 15-min cadence.
INTER_SYMBOL_DELAY_S = 1.5


def main() -> int:
    symbols = ["BTC"] + [s for s in axis.WATCHLIST if s != "BTC"]
    print(f"Seeding candle_cache.json for {len(symbols)} symbols "
          f"({', '.join(symbols)})")
    print(f"Cache path: {axis.CANDLE_CACHE_PATH}")

    candle_cache = axis.load_candle_cache()
    reference_ms = int(time.time() * 1000)

    ok, failed = [], []
    for i, symbol in enumerate(symbols, 1):
        print(f"[{i}/{len(symbols)}] {symbol} ...", end=" ", flush=True)
        bundle = axis.fetch_all_candles(symbol, candle_cache, reference_ms)
        if bundle is None:
            print("FAILED (insufficient candles)")
            failed.append(symbol)
        else:
            print("ok")
            ok.append(symbol)
        # Persist incrementally so a crash partway through doesn't lose
        # everything already fetched.
        axis.save_candle_cache(candle_cache)
        if i < len(symbols):
            time.sleep(INTER_SYMBOL_DELAY_S)

    print(f"\nDone. {len(ok)} succeeded, {len(failed)} failed.")
    if failed:
        print(f"Failed symbols (will full-pull again on next live run): "
              f"{', '.join(failed)}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
