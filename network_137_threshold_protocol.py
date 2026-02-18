"""
Network 137-threshold protocol (deterministic arithmetic bridge).

Bridges Predictions §3.1 from:
  UFRF3.1/08-ufrf-predictions-tests.md

Claim subset encoded here:
  phase-transition threshold at 137 connections.
"""

from __future__ import annotations

import json
from pathlib import Path

THRESHOLD = 137
LOWER = 13 * 10  # 130
UPPER = 13 * 11  # 143
SCALE = 144


def main() -> None:
    result = {
        "theorem": "network_137_threshold_protocol_v1",
        "claim_subset": {
            "threshold": THRESHOLD,
            "scale_anchor": SCALE,
        },
        "structural_checks": {
            "between_adjacent_13_multiples": LOWER < THRESHOLD < UPPER,
            "lower_multiple": LOWER,
            "upper_multiple": UPPER,
            "distance_to_lower": THRESHOLD - LOWER,
            "distance_to_upper": UPPER - THRESHOLD,
            "distance_to_144": SCALE - THRESHOLD,
            "threshold_is_prime": True,  # deterministic fact for 137
        },
    }

    output_path = Path("network_137_threshold_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic network-137 threshold summary:")
    print(f"  {output_path.resolve()}")
    print(f"  130 < 137 < 143, distance_to_144={SCALE-THRESHOLD}")


if __name__ == "__main__":
    main()
