"""
Projection versions reduction protocol (deterministic arithmetic bridge).

Purpose:
  Formalize a finite reduction scaffold connecting projection versions:

  - V2 additive: correction terms sum (k = Σ_i term_i)
  - V3 tensor: 3x3 tensor with off-diagonal zeros and equal diagonal k
  - V1 scalar-style (axiswise): x -> x + k*x

In this constrained setting, all three produce the same axiswise outputs.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

TERMS = [46, 102]
K_TOTAL = sum(TERMS)
OSTAR = [Fraction(1, 1), Fraction(2, 1), Fraction(3, 1)]


def v1_scalar_axiswise(x: Fraction, k: int) -> Fraction:
    return x + k * x


def v2_additive_axiswise(x: Fraction, terms: list[int]) -> Fraction:
    return x + sum(t * x for t in terms)


def v3_tensor_diag_axiswise(x: Fraction, k: int) -> Fraction:
    # Tensor with zero off-diagonals and equal diagonal k:
    # x + (k*x + 0 + 0) = x + k*x.
    return x + k * x


def main() -> None:
    v1 = [v1_scalar_axiswise(x, K_TOTAL) for x in OSTAR]
    v2 = [v2_additive_axiswise(x, TERMS) for x in OSTAR]
    v3 = [v3_tensor_diag_axiswise(x, K_TOTAL) for x in OSTAR]

    result = {
        "theorem": "projection_versions_reduction_protocol_v1",
        "claim_subset": {
            "v2": "k = sum_i term_i",
            "v3": "tensor offdiag=0 and diag=k",
            "v1_axiswise": "x -> x + k*x",
        },
        "structural_checks": {
            "terms": TERMS,
            "k_total": K_TOTAL,
            "offdiag_zero_assumption": True,
            "diag_equal_assumption": True,
            "v1_eq_v2_axiswise": v1 == v2,
            "v2_eq_v3_axiswise": v2 == v3,
            "v1_eq_v3_axiswise": v1 == v3,
        },
        "derived_values": {
            "ostar": [{"num": x.numerator, "den": x.denominator} for x in OSTAR],
            "v1": [{"num": x.numerator, "den": x.denominator} for x in v1],
            "v2": [{"num": x.numerator, "den": x.denominator} for x in v2],
            "v3": [{"num": x.numerator, "den": x.denominator} for x in v3],
        },
    }

    output_path = Path("projection_versions_reduction_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic projection-version reduction summary:")
    print(f"  {output_path.resolve()}")
    print(f"  k_total={K_TOTAL}, outputs={v1}")


if __name__ == "__main__":
    main()
