"""
Tensor projection law v3 protocol (deterministic arithmetic bridge).

Incorporates the multi-dimensional projection scaffold discussed in-session:

  ln O_d = ln O*_d + Σ_j P_{dj} * O*_j

with a fixed 3x3 rational tensor P (E, B, B' axes) and finite deterministic checks.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

# Rationalized tensor entries from the provided v3 matrix.
P = [
    [Fraction(1727, 500), Fraction(21, 500), Fraction(21, 500)],
    [Fraction(21, 500), Fraction(102, 125), Fraction(9, 200)],
    [Fraction(21, 500), Fraction(9, 200), Fraction(219, 500)],
]

OSTAR_ONES = [Fraction(1, 1), Fraction(1, 1), Fraction(1, 1)]


def project(ostar: list[Fraction]) -> list[Fraction]:
    out: list[Fraction] = []
    for d in range(3):
        correction = sum(P[d][j] * ostar[j] for j in range(3))
        out.append(ostar[d] + correction)
    return out


def main() -> None:
    projected_ones = project(OSTAR_ONES)
    row_sums = [sum(P[d][j] for j in range(3)) for d in range(3)]
    offdiag_symmetric = (
        P[0][1] == P[1][0]
        and P[0][2] == P[2][0]
        and P[1][2] == P[2][1]
    )
    diagonal_dominance = all(
        P[d][d] > (sum(P[d][j] for j in range(3) if j != d))
        for d in range(3)
    )

    result = {
        "theorem": "tensor_projection_law_v3_protocol_v1",
        "claim_subset": {
            "formula": "ln O_d = ln O*_d + sum_j P_dj * O*_j",
            "axes": ["E", "B", "B'"],
        },
        "tensor_entries": [
            [{"num": x.numerator, "den": x.denominator} for x in row] for row in P
        ],
        "structural_checks": {
            "shape_3x3": len(P) == 3 and all(len(r) == 3 for r in P),
            "offdiag_symmetric": offdiag_symmetric,
            "diagonal_dominance_by_row": diagonal_dominance,
            "diag_entries": [
                {"num": P[0][0].numerator, "den": P[0][0].denominator},
                {"num": P[1][1].numerator, "den": P[1][1].denominator},
                {"num": P[2][2].numerator, "den": P[2][2].denominator},
            ],
        },
        "derived_values": {
            "row_sums": [{"num": s.numerator, "den": s.denominator} for s in row_sums],
            "projected_ones": [
                {"num": x.numerator, "den": x.denominator} for x in projected_ones
            ],
        },
    }

    output_path = Path("tensor_projection_law_v3_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic tensor projection v3 summary:")
    print(f"  {output_path.resolve()}")
    print(f"  projected_ones={projected_ones}")


if __name__ == "__main__":
    main()
