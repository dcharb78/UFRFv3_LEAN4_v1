"""
Acoustic critical-position bridge protocol.

Finite deterministic scaffold for Predictions §7.1:
  frequencies at critical cycle positions n = 2.5, 5.5, 8.5, 10, 11.5
  using f = 432 * (n / 13).
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path


BASE = Fraction(432, 1)
DEN = Fraction(13, 1)
CRITICAL_N = [Fraction(5, 2), Fraction(11, 2), Fraction(17, 2), Fraction(10, 1), Fraction(23, 2)]


def main() -> None:
    freqs = [BASE * (n / DEN) for n in CRITICAL_N]

    result = {
        "theorem": "acoustic_critical_positions_protocol_v1",
        "claim_subset": {
            "formula": "f = 432 * (n/13)",
            "critical_n": [{"num": n.numerator, "den": n.denominator} for n in CRITICAL_N],
        },
        "structural_checks": {
            "count": len(CRITICAL_N),
            "ordered_n": all(CRITICAL_N[i] < CRITICAL_N[i + 1] for i in range(len(CRITICAL_N) - 1)),
            "ordered_freqs": all(freqs[i] < freqs[i + 1] for i in range(len(freqs) - 1)),
            "rest_position_is_n10": CRITICAL_N[3] == 10,
            "rest_frequency_equals_4320_over_13": freqs[3] == Fraction(4320, 13),
            "freqs_exact": [{"num": f.numerator, "den": f.denominator} for f in freqs],
        },
    }

    output_path = Path("acoustic_critical_positions_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic acoustic critical-position summary:")
    print(f"  {output_path.resolve()}")
    print(f"  rest_freq={freqs[3]}")


if __name__ == "__main__":
    main()
