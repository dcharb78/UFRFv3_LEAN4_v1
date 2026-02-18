"""
Network optima prediction protocol (deterministic discrete bridge).

Bridges Predictions §3 from:
  UFRF3.1/08-ufrf-predictions-tests.md

Claim subset encoded here:
  - local optima at 13, 144, 1728 nodes
  - transition threshold at 137 nodes

This script outputs a finite arithmetic summary for Lean mirroring.
"""

from __future__ import annotations

import json
from pathlib import Path

OPTIMA = [13, 144, 1728]
THRESHOLD = 137


def abs_diff(a: int, b: int) -> int:
    return abs(a - b)


def main() -> None:
    distances = {n: abs_diff(n, THRESHOLD) for n in OPTIMA}
    nearest = min(OPTIMA, key=lambda n: distances[n])

    result = {
        "theorem": "network_optima_prediction_protocol_v1",
        "claim_subset": {
            "optima_nodes": OPTIMA,
            "phase_transition_threshold": THRESHOLD,
        },
        "structural_checks": {
            "optima_len": len(OPTIMA),
            "thirteen_is_12_plus_1": OPTIMA[0] == 12 + 1,
            "onefortyfour_is_12_sq": OPTIMA[1] == 12**2,
            "oneseventwentyeight_is_12_cu": OPTIMA[2] == 12**3,
            "ordered": OPTIMA[0] < OPTIMA[1] < OPTIMA[2],
            "threshold_is_7_below_144": THRESHOLD == OPTIMA[1] - 7,
        },
        "distance_to_threshold": {
            "distance_by_optimum": {str(k): v for k, v in distances.items()},
            "nearest_optimum_to_137": nearest,
            "nearest_distance": distances[nearest],
        },
    }

    output_path = Path("network_optima_prediction_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic network-optima summary:")
    print(f"  {output_path.resolve()}")
    print(f"  Nearest optimum to {THRESHOLD}: {nearest} (distance {distances[nearest]})")


if __name__ == "__main__":
    main()
