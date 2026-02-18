"""
Acoustic n/13 prediction protocol (deterministic discrete bridge).

Bridges Predictions §7 from:
  UFRF3.1/08-ufrf-predictions-tests.md

Claim subset encoded here:
  f_n = 432 * (n/13), n = 1..13
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

BASE_FREQ = 432
DEN = 13
N_VALUES = list(range(1, 14))


def main() -> None:
    freqs = [Fraction(BASE_FREQ * n, DEN) for n in N_VALUES]
    diffs = [freqs[i + 1] - freqs[i] for i in range(len(freqs) - 1)]
    step = Fraction(BASE_FREQ, DEN)

    rows = [
        {
            "n": n,
            "numerator": f.numerator,
            "denominator": f.denominator,
            "decimal": float(f),
        }
        for n, f in zip(N_VALUES, freqs)
    ]

    result = {
        "theorem": "acoustic_n13_prediction_protocol_v1",
        "claim_subset": {
            "formula": "f_n = 432 * (n/13)",
            "n_min": 1,
            "n_max": 13,
            "base_frequency_hz": BASE_FREQ,
        },
        "structural_checks": {
            "count": len(freqs),
            "monotone_increasing": all(freqs[i] < freqs[i + 1] for i in range(len(freqs) - 1)),
            "constant_step": all(d == step for d in diffs),
            "step_numerator": step.numerator,
            "step_denominator": step.denominator,
            "f_1_numerator": freqs[0].numerator,
            "f_1_denominator": freqs[0].denominator,
            "f_10_numerator": freqs[9].numerator,
            "f_10_denominator": freqs[9].denominator,
            "f_13_is_432": freqs[12] == Fraction(432, 1),
        },
        "table": rows,
    }

    output_path = Path("acoustic_n13_prediction_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic acoustic n/13 summary:")
    print(f"  {output_path.resolve()}")
    print(
        f"  f1={freqs[0]} Hz, f10={freqs[9]} Hz, f13={freqs[12]} Hz, step={step} Hz"
    )


if __name__ == "__main__":
    main()
