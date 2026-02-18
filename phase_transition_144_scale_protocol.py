"""
Phase-transition 144-scale protocol (deterministic arithmetic bridge).

Bridges Predictions §6.1 from:
  UFRF3.1/08-ufrf-predictions-tests.md

Claim subset encoded here:
  - P = 144 GPa
  - T = 144 K, 1440 K, 14400 K
  - critical points on M = 144 * 10^n
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

BASE = 144
TEMPS = [144, 1440, 14400]
PRESSURE = 144
SCALE_LADDER = [144, 1440, 14400, 144000]

MANTISSA_NUM = 36  # 1.44 = 36/25
MANTISSA_DEN = 25

SEED_STAIR = [4, 14, 144, 144000]


def mantissa_at(k: int) -> Fraction:
    if k >= 0:
        return Fraction(MANTISSA_NUM * (10**k), MANTISSA_DEN)
    return Fraction(MANTISSA_NUM, MANTISSA_DEN * (10 ** (-k)))


def main() -> None:
    fine_ladder = [mantissa_at(k) for k in range(-1, 6)]
    bridge_ok = all(mantissa_at(n + 2) == Fraction(SCALE_LADDER[n], 1) for n in range(4))

    result = {
        "theorem": "phase_transition_144_scale_protocol_v1",
        "claim_subset": {
            "pressure_gpa": PRESSURE,
            "temperatures_k": TEMPS,
            "base_scale": BASE,
        },
        "structural_checks": {
            "pressure_equals_base": PRESSURE == BASE,
            "all_temps_match_144_times_10_pow_n": all(
                t == BASE * (10 ** n) for n, t in enumerate(TEMPS)
            ),
            "temperature_count": len(TEMPS),
            "temperature_ratios_are_10": [
                TEMPS[i + 1] // TEMPS[i] for i in range(len(TEMPS) - 1)
            ],
            "all_temperature_ratios_10": all(
                TEMPS[i + 1] == 10 * TEMPS[i] for i in range(len(TEMPS) - 1)
            ),
            "scale_ladder": SCALE_LADDER,
            "mantissa_bridge_m_n_plus_2_eq_scale_n": bridge_ok,
            "seed_stair_4_to_14_add10": SEED_STAIR[1] == SEED_STAIR[0] + 10,
            "seed_stair_14_to_144_eq_14x10_plus4": SEED_STAIR[2] == SEED_STAIR[1] * 10 + 4,
            "seed_stair_144_to_144000_x1000": SEED_STAIR[3] == SEED_STAIR[2] * 1000,
        },
        "mantissa_ladder_exact": [
            {
                "k": k,
                "numerator": v.numerator,
                "denominator": v.denominator,
                "decimal": float(v),
            }
            for k, v in zip(range(-1, 6), fine_ladder)
        ],
        "mantissa_to_scale_bridge": [
            {
                "n": n,
                "mantissa_k": n + 2,
                "mantissa_value_num": mantissa_at(n + 2).numerator,
                "mantissa_value_den": mantissa_at(n + 2).denominator,
                "scale_value": SCALE_LADDER[n],
                "equal": mantissa_at(n + 2) == Fraction(SCALE_LADDER[n], 1),
            }
            for n in range(4)
        ],
        "seed_stair": {
            "values": SEED_STAIR,
            "interpretation_note": "Seed-to-scale staircase shown as arithmetic anchors; causal geometry is modeled separately.",
        },
    }

    output_path = Path("phase_transition_144_scale_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic phase-transition 144-scale summary:")
    print(f"  {output_path.resolve()}")
    print(f"  temps={TEMPS}, pressure={PRESSURE}, bridge_ok={bridge_ok}")


if __name__ == "__main__":
    main()
