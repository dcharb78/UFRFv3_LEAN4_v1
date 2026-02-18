"""
Projection technique-variation bridge protocol.

Finite deterministic scaffold for Part II / Projection-law falsification logic:
  same intrinsic log-value, different technique couplings alpha -> different
  observed log offsets; difference matches d_M * S * (alpha2 - alpha1).
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path


def main() -> None:
    ln_o_star = Fraction(0, 1)
    d_m = Fraction(2, 1)
    s = Fraction(3, 1)
    alpha1 = Fraction(1, 10)
    alpha2 = Fraction(1, 5)

    delta1 = d_m * alpha1 * s
    delta2 = d_m * alpha2 * s

    ln_o1 = ln_o_star + delta1
    ln_o2 = ln_o_star + delta2

    expected_diff = d_m * s * (alpha2 - alpha1)
    actual_diff = ln_o2 - ln_o1

    result = {
        "theorem": "projection_technique_variation_protocol_v1",
        "claim_subset": {
            "law": "ln O = ln O* + d_M * alpha * S",
            "focus": "technique-dependent alpha variation",
        },
        "parameters": {
            "ln_o_star": {"num": ln_o_star.numerator, "den": ln_o_star.denominator},
            "d_m": {"num": d_m.numerator, "den": d_m.denominator},
            "s": {"num": s.numerator, "den": s.denominator},
            "alpha1": {"num": alpha1.numerator, "den": alpha1.denominator},
            "alpha2": {"num": alpha2.numerator, "den": alpha2.denominator},
        },
        "structural_checks": {
            "alpha1_not_alpha2": alpha1 != alpha2,
            "ln_o1_not_ln_o2": ln_o1 != ln_o2,
            "difference_matches_projection_law": actual_diff == expected_diff,
            "ln_o1": {"num": ln_o1.numerator, "den": ln_o1.denominator},
            "ln_o2": {"num": ln_o2.numerator, "den": ln_o2.denominator},
            "actual_diff": {"num": actual_diff.numerator, "den": actual_diff.denominator},
            "expected_diff": {"num": expected_diff.numerator, "den": expected_diff.denominator},
        },
    }

    output_path = Path("projection_technique_variation_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic projection-technique variation summary:")
    print(f"  {output_path.resolve()}")
    print(f"  ln_o1={ln_o1}, ln_o2={ln_o2}, diff={actual_diff}")


if __name__ == "__main__":
    main()
