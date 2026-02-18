"""
Neural oscillation 13x protocol (deterministic arithmetic bridge).

Bridges Predictions §4.3 from:
  UFRF3.1/08-ufrf-predictions-tests.md

Claim subset encoded here:
  coherence peaks at 13 Hz, 26 Hz, 39 Hz.
"""

from __future__ import annotations

import json
from pathlib import Path

FREQS = [13, 26, 39]


def main() -> None:
    result = {
        "theorem": "neural_oscillation_13x_protocol_v1",
        "claim_subset": {
            "frequencies_hz": FREQS,
        },
        "structural_checks": {
            "count": len(FREQS),
            "all_multiples_of_13": all(f % 13 == 0 for f in FREQS),
            "ratio_to_13": [f // 13 for f in FREQS],
            "is_13_2x13_3x13": FREQS == [13, 2 * 13, 3 * 13],
            "constant_step_13": all(FREQS[i + 1] - FREQS[i] == 13 for i in range(len(FREQS) - 1)),
        },
    }

    output_path = Path("neural_oscillation_13x_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic neural-oscillation 13x summary:")
    print(f"  {output_path.resolve()}")
    print(f"  freqs={FREQS}")


if __name__ == "__main__":
    main()
