"""
DNA helix REST-halfstep protocol (deterministic arithmetic bridge).

Bridges Predictions §4.1 from:
  UFRF3.1/08-ufrf-predictions-tests.md

Claim subset encoded here:
  10.5 turns is the half-step just beyond REST=10.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

REST = Fraction(10, 1)
HELIX_TURNS = Fraction(21, 2)  # 10.5
CYCLE = Fraction(13, 1)


def main() -> None:
    delta_from_rest = HELIX_TURNS - REST
    delta_to_cycle = CYCLE - HELIX_TURNS

    result = {
        "theorem": "dna_helix_rest_halfstep_protocol_v1",
        "claim_subset": {
            "rest_position": {"num": REST.numerator, "den": REST.denominator},
            "helical_turns": {"num": HELIX_TURNS.numerator, "den": HELIX_TURNS.denominator},
            "cycle_position": {"num": CYCLE.numerator, "den": CYCLE.denominator},
        },
        "structural_checks": {
            "turns_is_10_5": HELIX_TURNS == Fraction(21, 2),
            "exactly_halfstep_past_rest": delta_from_rest == Fraction(1, 2),
            "distance_to_cycle_end_is_2_5": delta_to_cycle == Fraction(5, 2),
            "ordering_rest_turns_cycle": REST < HELIX_TURNS < CYCLE,
        },
    }

    output_path = Path("dna_helix_rest_halfstep_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic DNA helix REST-halfstep summary:")
    print(f"  {output_path.resolve()}")
    print(
        f"  turns={float(HELIX_TURNS)}, delta_from_rest={float(delta_from_rest)}, delta_to_cycle={float(delta_to_cycle)}"
    )


if __name__ == "__main__":
    main()
