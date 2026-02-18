"""
Sub-magic multiples-of-13 prediction protocol (deterministic bridge).

Bridges Predictions §1.2 from:
  UFRF3.1/08-ufrf-predictions-tests.md

Claim subset encoded here:
  N or Z = 26, 39, 52, 65, 78, 91, 104, 117
"""

from __future__ import annotations

import json
from pathlib import Path

VALUES = [26, 39, 52, 65, 78, 91, 104, 117]
STEP = 13


def main() -> None:
    diffs = [VALUES[i + 1] - VALUES[i] for i in range(len(VALUES) - 1)]

    result = {
        "theorem": "submagic_multiples13_prediction_protocol_v1",
        "claim_subset": {
            "values": VALUES,
            "expected_step": STEP,
        },
        "structural_checks": {
            "count": len(VALUES),
            "all_multiples_of_13": all(v % 13 == 0 for v in VALUES),
            "constant_step_13": all(d == STEP for d in diffs),
            "first_is_2x13": VALUES[0] == 2 * 13,
            "last_is_9x13": VALUES[-1] == 9 * 13,
        },
    }

    output_path = Path("submagic_multiples13_prediction_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic sub-magic multiples-of-13 summary:")
    print(f"  {output_path.resolve()}")
    print(f"  count={len(VALUES)}, first={VALUES[0]}, last={VALUES[-1]}, step={STEP}")


if __name__ == "__main__":
    main()
