"""
Binding-energy oscillation protocol (deterministic arithmetic bridge).

Bridges Predictions §1.3 from:
  UFRF3.1/08-ufrf-predictions-tests.md

Claim subset encoded here:
  - oscillation phase uses denominator 13,
  - phase argument shifts by exactly one cycle under A -> A + 13,
  - numeric sine periodicity check over a finite window.
"""

from __future__ import annotations

import json
import math
from fractions import Fraction
from pathlib import Path

A_VALUES = list(range(1, 27))
PHASE_FRACS = [Fraction(a, 13) for a in A_VALUES]
PHASE_SHIFTS = [Fraction(a + 13, 13) - Fraction(a, 13) for a in A_VALUES]


def main() -> None:
    sine_periodic_ok = all(
        abs(math.sin(2.0 * math.pi * (a + 13) / 13.0) - math.sin(2.0 * math.pi * a / 13.0)) < 1e-12
        for a in A_VALUES
    )
    damping_ratio = math.exp(-13.0 / 100.0)
    damping_ratio_window = [
        math.exp(-(a + 13) / 100.0) / math.exp(-a / 100.0)
        for a in A_VALUES
    ]
    damping_ratio_constant_ok = all(abs(r - damping_ratio) < 1e-12 for r in damping_ratio_window)

    result = {
        "theorem": "binding_energy_oscillation_protocol_v1",
        "claim_subset": {
            "formula": "A0 * sin(2*pi*A/13) * exp(-A/100)",
            "phase_denominator": 13,
            "window_A_min": 1,
            "window_A_max": 26,
        },
        "structural_checks": {
            "phase_shift_is_one_cycle": all(s == 1 for s in PHASE_SHIFTS),
            "sine_periodic_under_plus13_eps_1e_12": sine_periodic_ok,
            "damping_ratio_constant_under_plus13_eps_1e_12": damping_ratio_constant_ok,
        },
        "derived_values": {
            "phase_at_A1": "1/13",
            "phase_at_A13": "1",
            "phase_at_A26": "2",
            "damping_ratio_exp_minus_13_over_100": damping_ratio,
        },
    }

    output_path = Path("binding_energy_oscillation_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic binding-energy oscillation summary:")
    print(f"  {output_path.resolve()}")
    print(f"  phase shift +13 => +1 cycle: {all(s == 1 for s in PHASE_SHIFTS)}")


if __name__ == "__main__":
    main()
