"""
Critical scale 7-14-28 integration protocol (deterministic synthesis bridge).

Finite deterministic scaffold integrating existing anchors:
  - shell projection gives 14 (from 14.5 - 0.5),
  - anomaly anchor is 28 (= 2 * 14),
  - network threshold gap is 7 (= 144 - 137),
  - therefore 14 = 2*7 and 28 = 4*7.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path


def main() -> None:
    shell_intrinsic_last = Fraction(29, 2)  # 14.5
    shell_shift = Fraction(1, 2)            # 0.5
    shell_projected = shell_intrinsic_last - shell_shift  # 14

    anomaly_28 = 28
    network_threshold = 137
    network_optimum = 144
    network_gap = network_optimum - network_threshold  # 7

    result = {
        "theorem": "critical_scale_7_14_28_integration_protocol_v1",
        "claim_subset": {
            "shell_projected_anchor": 14,
            "anomaly_anchor": 28,
            "network_gap_anchor": 7,
        },
        "structural_checks": {
            "shell_projected_is_14": shell_projected == 14,
            "anomaly_is_2_times_14": anomaly_28 == 2 * 14,
            "network_gap_is_7": network_gap == 7,
            "shell_projected_is_2_times_network_gap": shell_projected == 2 * network_gap,
            "anomaly_is_4_times_network_gap": anomaly_28 == 4 * network_gap,
            "ratio_network_shell_anomaly": [network_gap, int(shell_projected), anomaly_28],
        },
        "derived_values": {
            "shell_intrinsic_last": {"num": shell_intrinsic_last.numerator, "den": shell_intrinsic_last.denominator},
            "shell_shift": {"num": shell_shift.numerator, "den": shell_shift.denominator},
            "shell_projected": {"num": shell_projected.numerator, "den": shell_projected.denominator},
            "network_gap": network_gap,
            "anomaly": anomaly_28,
        },
    }

    output_path = Path("critical_scale_7_14_28_integration_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic critical scale 7-14-28 integration summary:")
    print(f"  {output_path.resolve()}")
    print(f"  gap={network_gap}, shell={shell_projected}, anomaly={anomaly_28}")


if __name__ == "__main__":
    main()
