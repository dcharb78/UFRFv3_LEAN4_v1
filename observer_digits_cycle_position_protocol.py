#!/usr/bin/env python3
"""
Observer digits vs cycle positions protocol (finite deterministic bridge).

Purpose:
- keep decimal observer-state dynamics (`0..9`) and mod-13 cycle positions separate,
- verify both update laws concurrently on a finite sample table,
- include a 6-decade return witness on the cycle side.
"""

from __future__ import annotations

import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent
OUT = ROOT / "observer_digits_cycle_position_results.json"

BASE = 10
MOD = 13
MAX_N = 200
DEPTHS = list(range(7))  # 0..6


def digit_at(depth: int, n: int) -> int:
    return (n // (BASE**depth)) % BASE


def cycle_pos(n: int) -> int:
    return n % MOD


def main() -> None:
    samples = list(range(MAX_N))
    shift_table = [pow(BASE, d, MOD) for d in DEPTHS]

    plus_digit_ok = True
    plus_cycle_ok = True
    lower_digit_ok = True

    for d in DEPTHS:
        bump = BASE**d
        for n in samples:
            # Decimal observer update law at selected depth.
            if digit_at(d, n + bump) != (digit_at(d, n) + 1) % BASE:
                plus_digit_ok = False
            # Cycle-position update law.
            if cycle_pos(n + bump) != (cycle_pos(n) + (bump % MOD)) % MOD:
                plus_cycle_ok = False
            # Lower decimal digits remain unchanged under +10^d.
            for i in range(d):
                if digit_at(i, n + bump) != digit_at(i, n):
                    lower_digit_ok = False

    # 6-decade cycle return witness: 10^6 ≡ 1 (mod 13), so n*10^6 preserves residue mod 13.
    cycle_tick10_6_return_ok = all(cycle_pos(n * (BASE**6)) == cycle_pos(n) for n in samples)

    summary = {
        "base": BASE,
        "cycle_modulus": MOD,
        "sample_size": MAX_N,
        "depths": DEPTHS,
        "shift_table_pow10_mod13": shift_table,
        "plus_digit_shift_all_holds": plus_digit_ok,
        "plus_cycle_shift_all_holds": plus_cycle_ok,
        "lower_digit_stability_all_holds": lower_digit_ok,
        "cycle_tick10_6_return_all_holds": cycle_tick10_6_return_ok,
        "expected_shift_table": [1, 10, 9, 12, 3, 4, 1],
    }

    OUT.write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print(f"Saved deterministic observer/cycle shift-table summary: {OUT}")
    print(f"  shift_table={shift_table}")
    print(
        "  checks="
        f"digit:{plus_digit_ok}, cycle:{plus_cycle_ok}, "
        f"lower_digits:{lower_digit_ok}, tick10_6_return:{cycle_tick10_6_return_ok}"
    )


if __name__ == "__main__":
    main()
