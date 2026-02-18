#!/usr/bin/env python3
"""
Observer/cycle periodicity protocol (finite deterministic bridge).

Purpose:
- extend the observer-digit vs mod-13 cycle bridge from finite depths (0..6)
  to a wider finite depth window (0..23),
- certify the period-6 law on the cycle side (`10^d mod 13`),
- keep observer-digit and cycle-position updates as concurrent but distinct axes.
"""

from __future__ import annotations

import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent
OUT = ROOT / "observer_digits_cycle_periodicity_results.json"

BASE = 10
MOD = 13
PERIOD = 6
MAX_DEPTH = 24
MAX_N = 200


def digit_at(depth: int, n: int) -> int:
    return (n // (BASE**depth)) % BASE


def cycle_pos(n: int) -> int:
    return n % MOD


def shift(d: int) -> int:
    return pow(BASE, d, MOD)


def main() -> None:
    samples = list(range(MAX_N))
    depths = list(range(MAX_DEPTH))
    period_depths = list(range(MAX_DEPTH - PERIOD))

    period_shift_table = [shift(d) for d in range(PERIOD)]

    shift_periodicity_ok = all(shift(d + PERIOD) == shift(d) for d in period_depths)
    shift_residue_lookup_ok = all(shift(d) == shift(d % PERIOD) for d in depths)

    plus_digit_ok = True
    plus_cycle_ok = True
    plus_cycle_residue_ok = True
    lower_digit_ok = True

    for d in depths:
        bump = BASE**d
        for n in samples:
            if digit_at(d, n + bump) != (digit_at(d, n) + 1) % BASE:
                plus_digit_ok = False
            if cycle_pos(n + bump) != (cycle_pos(n) + shift(d)) % MOD:
                plus_cycle_ok = False
            if cycle_pos(n + bump) != (cycle_pos(n) + shift(d % PERIOD)) % MOD:
                plus_cycle_residue_ok = False
            for i in range(d):
                if digit_at(i, n + bump) != digit_at(i, n):
                    lower_digit_ok = False

    cycle_add_period_ok = all(
        cycle_pos(n + BASE ** (d + PERIOD)) == cycle_pos(n + BASE**d)
        for d in period_depths
        for n in samples
    )

    cycle_mul_tick10_6_return_ok = all(cycle_pos(n * (BASE**PERIOD)) == cycle_pos(n) for n in samples)

    summary = {
        "base": BASE,
        "cycle_modulus": MOD,
        "period": PERIOD,
        "sample_size": MAX_N,
        "max_depth_exclusive": MAX_DEPTH,
        "period_shift_table_pow10_mod13": period_shift_table,
        "shift_periodicity_all_holds": shift_periodicity_ok,
        "shift_residue_lookup_all_holds": shift_residue_lookup_ok,
        "plus_digit_shift_all_holds": plus_digit_ok,
        "plus_cycle_shift_all_holds": plus_cycle_ok,
        "plus_cycle_shift_residue_lookup_all_holds": plus_cycle_residue_ok,
        "lower_digit_stability_all_holds": lower_digit_ok,
        "cycle_add_pow10_periodicity_all_holds": cycle_add_period_ok,
        "cycle_mul_tick10_6_return_all_holds": cycle_mul_tick10_6_return_ok,
        "expected_period_shift_table": [1, 10, 9, 12, 3, 4],
    }

    OUT.write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print(f"Saved deterministic observer/cycle periodicity summary: {OUT}")
    print(f"  period_shift_table={period_shift_table}")
    print(
        "  checks="
        f"shift_period:{shift_periodicity_ok}, "
        f"shift_lookup:{shift_residue_lookup_ok}, "
        f"digit:{plus_digit_ok}, cycle:{plus_cycle_ok}, "
        f"cycle_lookup:{plus_cycle_residue_ok}, "
        f"lower_digits:{lower_digit_ok}, "
        f"add_period:{cycle_add_period_ok}, "
        f"mul_tick10_6:{cycle_mul_tick10_6_return_ok}"
    )


if __name__ == "__main__":
    main()
