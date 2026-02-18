"""
Network scale-threshold integration protocol (deterministic bridge).

Finite deterministic scaffold integrating existing network anchors:
  - optima at 13, 144, 1728,
  - threshold at 137,
  - nearest optimum and exact scale relations.
"""

from __future__ import annotations

import json
from pathlib import Path


OPTIMA = [13, 144, 1728]
THRESHOLD = 137


def main() -> None:
    distances = {n: abs(n - THRESHOLD) for n in OPTIMA}
    nearest = min(OPTIMA, key=lambda n: distances[n])

    result = {
        "theorem": "network_scale_threshold_integration_protocol_v1",
        "claim_subset": {
            "optima_nodes": OPTIMA,
            "threshold": THRESHOLD,
        },
        "structural_checks": {
            "thirteen_eq_12_plus_1": OPTIMA[0] == 12 + 1,
            "onefortyfour_eq_12_sq": OPTIMA[1] == 12**2,
            "oneseventwentyeight_eq_12_cu": OPTIMA[2] == 12**3,
            "cube_eq_12_times_square": OPTIMA[2] == 12 * OPTIMA[1],
            "threshold_eq_13_times_10_plus_7": THRESHOLD == 13 * 10 + 7,
            "threshold_is_7_below_144": THRESHOLD == 144 - 7,
            "ordered": OPTIMA[0] < THRESHOLD < OPTIMA[1] < OPTIMA[2],
            "nearest_optimum_to_threshold": nearest == 144,
            "nearest_distance": distances[nearest],
            "distance_map": {str(k): v for k, v in distances.items()},
        },
    }

    output_path = Path("network_scale_threshold_integration_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic network scale-threshold integration summary:")
    print(f"  {output_path.resolve()}")
    print(f"  nearest={nearest}, distance={distances[nearest]}")


if __name__ == "__main__":
    main()
