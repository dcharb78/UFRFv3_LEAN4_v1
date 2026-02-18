"""
28K anomaly protocol (deterministic arithmetic bridge).

Bridges claim subsets for:
  - Graphene anomaly at 28K (Predictions §2.3)
  - Universal 28K anomaly in 2D materials (Predictions §6.2)

Arithmetic decomposition only:
  28 = 13 + 15 = 2 * 14
"""

from __future__ import annotations

import json
from pathlib import Path

ANOMALY = 28


def main() -> None:
    result = {
        "theorem": "anomaly_28k_protocol_v1",
        "claim_subset": {
            "temperature_k": ANOMALY,
        },
        "structural_checks": {
            "is_13_plus_15": ANOMALY == 13 + 15,
            "is_2_times_14": ANOMALY == 2 * 14,
            "offset_from_13": ANOMALY - 13,
            "offset_from_14": ANOMALY - 14,
        },
    }

    output_path = Path("anomaly_28k_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic 28K anomaly summary:")
    print(f"  {output_path.resolve()}")
    print(f"  28=13+15={13+15}, 28=2*14={2*14}")


if __name__ == "__main__":
    main()
