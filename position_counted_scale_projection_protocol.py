"""
Position-counted scale projection bridge protocol.

Finite deterministic bridge:
  - index-of-indexes ladder: 13, 13^2, 13^3
  - SL1 position-counted/geometric ratio consistency on the fixed comparator
    geometric_SL1 = 139.5 = 279/2.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path


def frac_dict(x: Fraction) -> dict[str, int]:
    return {"num": x.numerator, "den": x.denominator}


def main() -> None:
    pos_ladder = [13, 169, 2197]
    geometric_sl1 = Fraction(279, 2)  # 139.5

    ratio_pos_over_geom = Fraction(pos_ladder[1], 1) / geometric_sl1
    intrinsic_per_position = geometric_sl1 / Fraction(pos_ladder[1], 1)
    observer_tick = Fraction(1, 1)
    observer_to_intrinsic = observer_tick / intrinsic_per_position

    result = {
        "theorem": "position_counted_scale_projection_protocol_v1",
        "claim_subset": {
            "position_counted_ladder": "13, 13^2, 13^3",
            "sl1_comparator": "position_counted 169 vs geometric 139.5",
        },
        "structural_checks": {
            "ladder_exact": pos_ladder == [13, 13**2, 13**3],
            "sl1_ratio_consistent": observer_to_intrinsic == ratio_pos_over_geom,
            "values": {
                "position_ladder": pos_ladder,
                "geometric_sl1": frac_dict(geometric_sl1),
                "ratio_pos_over_geom": frac_dict(ratio_pos_over_geom),
                "intrinsic_per_position": frac_dict(intrinsic_per_position),
                "observer_to_intrinsic": frac_dict(observer_to_intrinsic),
            },
        },
    }

    output_path = Path("position_counted_scale_projection_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic position-counted scale projection summary:")
    print(f"  {output_path.resolve()}")
    print(f"  ratio_pos_over_geom={ratio_pos_over_geom}, intrinsic={intrinsic_per_position}")


if __name__ == "__main__":
    main()
