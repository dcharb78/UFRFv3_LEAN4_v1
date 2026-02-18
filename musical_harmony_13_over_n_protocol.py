"""
Musical harmony 13/n protocol (deterministic arithmetic bridge).

Bridges Predictions §7.2 from:
  UFRF3.1/08-ufrf-predictions-tests.md

Claim subset encoded here:
  consonance ratios in the family (13/n), n integer.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

N_VALUES = list(range(1, 14))
RATIOS = [Fraction(13, n) for n in N_VALUES]


def main() -> None:
    result = {
        "theorem": "musical_harmony_13_over_n_protocol_v1",
        "claim_subset": {
            "formula": "ratio_n = 13/n",
            "n_min": 1,
            "n_max": 13,
        },
        "structural_checks": {
            "count": len(RATIOS),
            "all_times_n_equal_13": all(r * n == 13 for r, n in zip(RATIOS, N_VALUES)),
            "strictly_decreasing": all(RATIOS[i] > RATIOS[i + 1] for i in range(len(RATIOS) - 1)),
            "first_is_13": RATIOS[0] == Fraction(13, 1),
            "last_is_1": RATIOS[-1] == Fraction(1, 1),
            "middle_n7_is_13_over_7": RATIOS[6] == Fraction(13, 7),
        },
        "table": [
            {
                "n": n,
                "numerator": r.numerator,
                "denominator": r.denominator,
                "decimal": float(r),
            }
            for n, r in zip(N_VALUES, RATIOS)
        ],
    }

    output_path = Path("musical_harmony_13_over_n_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic musical-harmony 13/n summary:")
    print(f"  {output_path.resolve()}")
    print(f"  first={RATIOS[0]}, middle={RATIOS[6]}, last={RATIOS[-1]}")


if __name__ == "__main__":
    main()
