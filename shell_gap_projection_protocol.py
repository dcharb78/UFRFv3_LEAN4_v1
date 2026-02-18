"""
Shell-gap projection protocol (deterministic arithmetic bridge).

Bridges Predictions §1.1 from:
  UFRF3.1/08-ufrf-predictions-tests.md

Claim subset encoded here:
  intrinsic sequence 2.5, 5.5, 8.5, 11.5, 14.5 (step 3.0)
  projected next-shell value: 14.5 - 0.5 = 14.0
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

INTRINSIC = [
    Fraction(5, 2),   # 2.5
    Fraction(11, 2),  # 5.5
    Fraction(17, 2),  # 8.5
    Fraction(23, 2),  # 11.5
    Fraction(29, 2),  # 14.5
]
PROJECTION_SHIFT = Fraction(1, 2)  # 0.5


def main() -> None:
    diffs = [INTRINSIC[i + 1] - INTRINSIC[i] for i in range(len(INTRINSIC) - 1)]
    projected = INTRINSIC[-1] - PROJECTION_SHIFT

    result = {
        "theorem": "shell_gap_projection_protocol_v1",
        "claim_subset": {
            "intrinsic_series": [{"num": x.numerator, "den": x.denominator} for x in INTRINSIC],
            "projection_shift": {"num": PROJECTION_SHIFT.numerator, "den": PROJECTION_SHIFT.denominator},
        },
        "structural_checks": {
            "count": len(INTRINSIC),
            "constant_step_3": all(d == 3 for d in diffs),
            "next_intrinsic_is_14_5": INTRINSIC[-1] == Fraction(29, 2),
            "projected_is_14_0": projected == Fraction(14, 1),
        },
        "projected_value": {
            "numerator": projected.numerator,
            "denominator": projected.denominator,
            "decimal": float(projected),
        },
    }

    output_path = Path("shell_gap_projection_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic shell-gap projection summary:")
    print(f"  {output_path.resolve()}")
    print(f"  intrinsic_last={INTRINSIC[-1]}, projected={projected}")


if __name__ == "__main__":
    main()
