"""
Projection zero-distance identity bridge protocol.

Finite deterministic scaffold:
  if d_M = 0, then ln O = ln O* regardless of alpha and S.
Includes one non-zero-distance witness to show the condition is substantive.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path


def ln_o(ln_o_star: Fraction, d_m: Fraction, alpha: Fraction, s: Fraction) -> Fraction:
    return ln_o_star + d_m * alpha * s


def main() -> None:
    ln_o_star = Fraction(7, 3)
    d_m_zero = Fraction(0, 1)

    samples = [
        (Fraction(1, 10), Fraction(1, 1)),
        (Fraction(1, 5), Fraction(2, 1)),
        (Fraction(3, 7), Fraction(5, 1)),
    ]

    outputs_zero = [ln_o(ln_o_star, d_m_zero, alpha, s) for alpha, s in samples]
    all_identity = all(v == ln_o_star for v in outputs_zero)

    # Non-zero-distance witness
    witness = ln_o(ln_o_star, Fraction(2, 1), Fraction(1, 10), Fraction(3, 1))

    result = {
        "theorem": "projection_zero_distance_identity_protocol_v1",
        "claim_subset": {
            "identity_case": "d_M = 0 => ln O = ln O*",
            "scope": "independent of alpha, S",
        },
        "parameters": {
            "ln_o_star": {"num": ln_o_star.numerator, "den": ln_o_star.denominator},
            "samples_alpha_s": [
                {"alpha": {"num": a.numerator, "den": a.denominator}, "s": {"num": s.numerator, "den": s.denominator}}
                for a, s in samples
            ],
        },
        "structural_checks": {
            "all_zero_distance_outputs_equal_intrinsic": all_identity,
            "outputs_zero_distance": [{"num": v.numerator, "den": v.denominator} for v in outputs_zero],
            "nonzero_distance_witness_differs": witness != ln_o_star,
            "witness_value": {"num": witness.numerator, "den": witness.denominator},
        },
    }

    output_path = Path("projection_zero_distance_identity_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic projection zero-distance identity summary:")
    print(f"  {output_path.resolve()}")
    print(f"  all_identity={all_identity}, witness={witness}")


if __name__ == "__main__":
    main()
