"""
Quantum Hall n/13 prediction protocol (deterministic discrete bridge).

Bridges Predictions §2.1 from:
  UFRF3.1/08-ufrf-predictions-tests.md

Claim subset encoded here:
  ν = n/13 for n = 1..12, with highlighted position 10/13.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

DEN = 13
N_VALUES = list(range(1, 13))


def main() -> None:
    fracs = [Fraction(n, DEN) for n in N_VALUES]

    result = {
        "theorem": "quantum_hall_n13_prediction_protocol_v1",
        "claim_subset": {
            "formula": "nu_n = n/13",
            "n_min": 1,
            "n_max": 12,
            "denominator": DEN,
            "highlight_fraction": {"n": 10, "value_numerator": 10, "value_denominator": 13},
        },
        "structural_checks": {
            "count": len(fracs),
            "monotone_increasing": all(fracs[i] < fracs[i + 1] for i in range(len(fracs) - 1)),
            "all_between_zero_and_one": all(Fraction(0, 1) < f < Fraction(1, 1) for f in fracs),
            "contains_10_over_13": Fraction(10, 13) in fracs,
            "first_is_1_over_13": fracs[0] == Fraction(1, 13),
            "last_is_12_over_13": fracs[-1] == Fraction(12, 13),
        },
        "table": [
            {
                "n": n,
                "numerator": f.numerator,
                "denominator": f.denominator,
                "decimal": float(f),
            }
            for n, f in zip(N_VALUES, fracs)
        ],
    }

    output_path = Path("quantum_hall_n13_prediction_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic quantum Hall n/13 summary:")
    print(f"  {output_path.resolve()}")
    print(f"  n-range: {N_VALUES[0]}..{N_VALUES[-1]}, contains 10/13: {Fraction(10,13) in fracs}")


if __name__ == "__main__":
    main()
