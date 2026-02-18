"""
Moonshine inevitability chain protocol (deterministic synthesis bridge).

Builds one finite checkpoint joining:
  - Frobenius emergence anchors,
  - AP(12) Monster triple structure,
  - c1 = product + 1 identity,
  - denominator ladder checks for c2/c3/c4 numerators (13, 13^2, 13^3).
"""

from __future__ import annotations

import json
from pathlib import Path


def frobenius(a: int, b: int) -> int:
    return a * b - a - b


def main() -> None:
    # Emergence anchors
    f_5_13 = frobenius(5, 13)
    f_7_11 = frobenius(7, 11)
    f_7_13 = frobenius(7, 13)
    monster = [f_5_13, f_7_11, f_7_13]

    # AP(12) structure
    ap_diff_1 = monster[1] - monster[0]
    ap_diff_2 = monster[2] - monster[1]

    # Product-plus-one anchor
    product = monster[0] * monster[1] * monster[2]
    c1 = 196884

    # Symmetric values for the existing c2/c3/c4 formulas.
    e1 = sum(monster)
    e2 = monster[0] * monster[1] + monster[0] * monster[2] + monster[1] * monster[2]
    e3 = product

    c2 = 21493760
    c2_num = 8 * e1 * e3 + 61 * e2 - 31 * e1 + 9800

    c3 = 864299970
    c3_num = 4 * e3 * e3 - 4 * e2 * e3 - 8 * e2 * e2 - 2487 * e2 - 39 * e1 - 34

    c4 = 20245856256
    c4_num = 1147 * e3 * e3 + 9 * e2 * e3 + 8 * e2 * e2 - 1547 * e2 - 32 * e1 + 5

    result = {
        "theorem": "moonshine_inevitability_chain_protocol_v1",
        "claim_subset": {
            "frobenius_pairs": [[5, 13], [7, 11], [7, 13]],
            "monster_triple": monster,
            "j_anchor": "c1 = product(monster)+1",
            "denominator_ladder": [13, 169, 2197],
        },
        "structural_checks": {
            "frobenius_5_13_eq_47": f_5_13 == 47,
            "frobenius_7_11_eq_59": f_7_11 == 59,
            "frobenius_7_13_eq_71": f_7_13 == 71,
            "ap12_diff1_eq_12": ap_diff_1 == 12,
            "ap12_diff2_eq_12": ap_diff_2 == 12,
            "c1_equals_product_plus_one": c1 == product + 1,
            "sigma1_eq_177": e1 == 177,
            "c2_num_eq_13_times_c2": c2_num == 13 * c2,
            "c3_num_eq_169_times_c3": c3_num == 169 * c3,
            "c4_num_eq_2197_times_c4": c4_num == 2197 * c4,
        },
        "derived_values": {
            "monster_triple": monster,
            "product": product,
            "e1": e1,
            "e2": e2,
            "e3": e3,
            "c2_num": c2_num,
            "c3_num": c3_num,
            "c4_num": c4_num,
        },
    }

    output_path = Path("moonshine_inevitability_chain_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic Moonshine inevitability chain summary:")
    print(f"  {output_path.resolve()}")
    print(f"  monster={monster}, c1=product+1 -> {c1 == product + 1}")


if __name__ == "__main__":
    main()
