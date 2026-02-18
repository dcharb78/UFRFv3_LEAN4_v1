"""
Protein-folding position protocol (deterministic arithmetic bridge).

Bridges Predictions §4.2 from:
  UFRF3.1/08-ufrf-predictions-tests.md

Claim subset encoded here:
  preferred positions 3.6, 7.2, 10.5 as exact rationals.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

POSITIONS = [Fraction(18, 5), Fraction(36, 5), Fraction(21, 2)]
REST = Fraction(10, 1)
CYCLE = Fraction(13, 1)


def main() -> None:
    result = {
        "theorem": "protein_folding_positions_protocol_v1",
        "claim_subset": {
            "positions": ["3.6", "7.2", "10.5"],
            "exact_rationals": ["18/5", "36/5", "21/2"],
        },
        "structural_checks": {
            "count": len(POSITIONS),
            "ordered": POSITIONS[0] < POSITIONS[1] < POSITIONS[2],
            "second_is_double_first": POSITIONS[1] == 2 * POSITIONS[0],
            "third_is_10p5": POSITIONS[2] == Fraction(21, 2),
            "third_minus_rest_is_half": POSITIONS[2] - REST == Fraction(1, 2),
            "all_inside_cycle_13": all(Fraction(0, 1) < p < CYCLE for p in POSITIONS),
        },
        "table": [
            {"index": i + 1, "numerator": p.numerator, "denominator": p.denominator, "decimal": float(p)}
            for i, p in enumerate(POSITIONS)
        ],
    }

    output_path = Path("protein_folding_positions_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic protein-folding positions summary:")
    print(f"  {output_path.resolve()}")
    print(f"  positions={POSITIONS}")


if __name__ == "__main__":
    main()
