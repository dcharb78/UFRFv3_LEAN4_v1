"""
Projection distance-monotonicity bridge protocol.

Finite deterministic scaffold:
  for fixed ln O*, alpha > 0, S > 0, increasing d_M increases ln O.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path


def ln_o(ln_o_star: Fraction, d_m: Fraction, alpha: Fraction, s: Fraction) -> Fraction:
    return ln_o_star + d_m * alpha * s


def main() -> None:
    ln_o_star = Fraction(7, 3)
    alpha = Fraction(1, 10)
    s = Fraction(3, 1)
    dms = [Fraction(0, 1), Fraction(1, 1), Fraction(2, 1), Fraction(5, 1)]

    outputs = [ln_o(ln_o_star, d, alpha, s) for d in dms]
    strictly_increasing = all(outputs[i] < outputs[i + 1] for i in range(len(outputs) - 1))
    step01 = outputs[1] - outputs[0]
    step12 = outputs[2] - outputs[1]

    result = {
        "theorem": "projection_distance_monotonicity_protocol_v1",
        "claim_subset": {
            "law": "ln O = ln O* + d_M * alpha * S",
            "focus": "monotone in d_M for alpha,S > 0",
        },
        "parameters": {
            "ln_o_star": {"num": ln_o_star.numerator, "den": ln_o_star.denominator},
            "alpha": {"num": alpha.numerator, "den": alpha.denominator},
            "s": {"num": s.numerator, "den": s.denominator},
            "dms": [{"num": d.numerator, "den": d.denominator} for d in dms],
        },
        "structural_checks": {
            "strictly_increasing": strictly_increasing,
            "outputs": [{"num": o.numerator, "den": o.denominator} for o in outputs],
            "unit_step_difference_constant": step01 == step12 == alpha * s,
            "step01": {"num": step01.numerator, "den": step01.denominator},
            "step12": {"num": step12.numerator, "den": step12.denominator},
        },
    }

    output_path = Path("projection_distance_monotonicity_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic projection-distance monotonicity summary:")
    print(f"  {output_path.resolve()}")
    print(f"  strictly_increasing={strictly_increasing}, step01={step01}")


if __name__ == "__main__":
    main()
