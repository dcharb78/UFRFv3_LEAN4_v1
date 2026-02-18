"""
Anchor-144 cross-domain integration protocol (deterministic synthesis bridge).

Finite deterministic scaffold integrating existing anchors:
  - network optimum anchor: 144,
  - phase ladder: 144, 1440, 14400,
  - decimal nested anchor: 144000 with per-level digits [0,0,0,4,4,1].
"""

from __future__ import annotations

import json
from pathlib import Path


BASE = 144
PHASE_TEMPS = [144, 1440, 14400]
DECIMAL_ANCHOR = 144000


def digit_at(n: int, level: int) -> int:
    return (n // (10 ** (level - 1))) % 10


def main() -> None:
    digits_1_to_6 = [digit_at(DECIMAL_ANCHOR, k) for k in range(1, 7)]

    result = {
        "theorem": "anchor_144_cross_domain_integration_protocol_v1",
        "claim_subset": {
            "base_anchor": BASE,
            "phase_temps": PHASE_TEMPS,
            "decimal_anchor": DECIMAL_ANCHOR,
        },
        "structural_checks": {
            "phase_is_base_times_powers_of_10": all(
                t == BASE * (10 ** i) for i, t in enumerate(PHASE_TEMPS)
            ),
            "phase_ratios_are_10": [PHASE_TEMPS[i + 1] // PHASE_TEMPS[i] for i in range(len(PHASE_TEMPS) - 1)],
            "decimal_anchor_is_base_times_1000": DECIMAL_ANCHOR == BASE * 1000,
            "decimal_digits_levels_1_to_6": digits_1_to_6,
            "decimal_digits_match_expected": digits_1_to_6 == [0, 0, 0, 4, 4, 1],
            "high_digits_form_144": [digits_1_to_6[5], digits_1_to_6[4], digits_1_to_6[3]] == [1, 4, 4],
        },
    }

    output_path = Path("anchor_144_cross_domain_integration_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic anchor-144 cross-domain integration summary:")
    print(f"  {output_path.resolve()}")
    print(f"  temps={PHASE_TEMPS}, digits={digits_1_to_6}")


if __name__ == "__main__":
    main()
