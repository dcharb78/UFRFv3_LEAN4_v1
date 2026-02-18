"""
Projection tensor row-sum <-> scalar-gain bridge protocol.

Finite deterministic bridge:
  for O* = [1,1,1], tensor correction per axis equals the corresponding row sum.
This gives a direct axiswise scalar-gain interpretation of the V3 tensor on the
all-ones probe.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

P = [
    [Fraction(1727, 500), Fraction(21, 500), Fraction(21, 500)],
    [Fraction(21, 500), Fraction(102, 125), Fraction(9, 200)],
    [Fraction(21, 500), Fraction(9, 200), Fraction(219, 500)],
]


def main() -> None:
    row_sums = [sum(row) for row in P]
    ostar = [Fraction(1, 1), Fraction(1, 1), Fraction(1, 1)]
    corrections = [sum(P[d][j] * ostar[j] for j in range(3)) for d in range(3)]
    projected = [ostar[d] + corrections[d] for d in range(3)]

    result = {
        "theorem": "projection_tensor_rowsum_scalar_bridge_protocol_v1",
        "claim_subset": {
            "probe": "O* = [1,1,1]",
            "identity": "tensor_correction_d = row_sum_d",
        },
        "structural_checks": {
            "row_sums_match_corrections": corrections == row_sums,
            "projected_equals_one_plus_rowsum": all(projected[d] == 1 + row_sums[d] for d in range(3)),
            "row_sums": [{"num": x.numerator, "den": x.denominator} for x in row_sums],
            "projected": [{"num": x.numerator, "den": x.denominator} for x in projected],
        },
    }

    output_path = Path("projection_tensor_rowsum_scalar_bridge_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic tensor-row-sum scalar bridge summary:")
    print(f"  {output_path.resolve()}")
    print(f"  row_sums={row_sums}")


if __name__ == "__main__":
    main()
