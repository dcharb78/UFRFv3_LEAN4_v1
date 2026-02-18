"""
Decimal nested-tick projection bridge protocol.

Finite deterministic bridge:
  - each level exposes a state in {0..9},
  - higher-level digit state equals level-1 state on the scaled index,
    capturing concurrent nesting under base-10 projection.
"""

from __future__ import annotations

import json
from pathlib import Path


def digit_at(n: int, level: int) -> int:
    if level < 1:
        raise ValueError("level must be >= 1")
    return (n // (10 ** (level - 1))) % 10


def main() -> None:
    anchors = [1, 14, 144, 1440, 144000, 2197, 13**7, 196884]
    levels = [1, 2, 3, 4, 5, 6]

    table = {
        str(n): {f"L{lvl}": digit_at(n, lvl) for lvl in levels}
        for n in anchors
    }

    sample_pairs = [(2197, 3), (196884, 5), (144000, 6), (13**7, 4), (144, 2)]
    projection_holds = all(
        digit_at(n, lvl) == digit_at(n // (10 ** (lvl - 1)), 1)
        for (n, lvl) in sample_pairs
    )

    range_check = all(
        0 <= digit_at(n, lvl) <= 9
        for n in range(0, 500)
        for lvl in levels
    )

    result = {
        "theorem": "decimal_nested_tick_projection_protocol_v1",
        "claim_subset": {
            "state_space": "0..9 per level",
            "nested_projection": "digit(n, level) = digit(floor(n/10^(level-1)), 1)",
        },
        "structural_checks": {
            "anchor_144000_levels_1_to_6": [digit_at(144000, lvl) for lvl in levels],
            "projection_holds_on_samples": projection_holds,
            "digits_always_in_0_to_9": range_check,
            "table": table,
        },
    }

    output_path = Path("decimal_nested_tick_projection_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic decimal nested-tick projection summary:")
    print(f"  {output_path.resolve()}")
    print(f"  144000 levels 1..6 = {result['structural_checks']['anchor_144000_levels_1_to_6']}")


if __name__ == "__main__":
    main()
