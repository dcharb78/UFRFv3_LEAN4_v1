"""
Galaxy-rotation residual protocol (deterministic arithmetic bridge).

Bridges Predictions §5.2 from:
  UFRF3.1/08-ufrf-predictions-tests.md

Claim subset encoded here:
  - 13-state residual indexing scaffold,
  - invariance under bin shift k -> k + 13,
  - balanced residue coverage over three full cycles (39 bins).
"""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path

BINS = list(range(1, 40))


def state(k: int) -> int:
    return k % 13


def main() -> None:
    periodic_ok = all(state(k + 13) == state(k) for k in range(1, 27))
    counts = Counter(state(k) for k in BINS)
    balanced_three_cycles = all(counts[r] == 3 for r in range(13))

    result = {
        "theorem": "galaxy_rotation_mod13_residual_protocol_v1",
        "claim_subset": {
            "residual_state": "k mod 13",
            "bin_min": 1,
            "bin_max": 39,
        },
        "structural_checks": {
            "periodic_under_plus13": periodic_ok,
            "balanced_three_cycles": balanced_three_cycles,
            "count_per_residue": {str(r): counts[r] for r in range(13)},
        },
        "anchors": {
            "state_1": state(1),
            "state_13": state(13),
            "state_14": state(14),
            "state_26": state(26),
            "state_27": state(27),
        },
    }

    output_path = Path("galaxy_rotation_mod13_residual_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic galaxy-rotation mod13 residual summary:")
    print(f"  {output_path.resolve()}")
    print(f"  periodic={periodic_ok}, balanced_three_cycles={balanced_three_cycles}")


if __name__ == "__main__":
    main()
