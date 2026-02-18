"""
Monster mod-1001 order-classes protocol (deterministic synthesis bridge).

Finite deterministic scaffold:
  - certify exact order-60 behavior for Monster anchors 47,59,71 mod 1001,
  - certify product residue class behavior,
  - certify c1 residue class (196884 mod 1001) has exact order 30,
    matching the order class of the source anchor 3.
"""

from __future__ import annotations

import json
import math
from pathlib import Path


M = 1001
MONSTER = [47, 59, 71]
C1 = 196884
PROPER_DIVS_60 = [1, 2, 3, 4, 5, 6, 10, 12, 15, 20, 30]
PROPER_DIVS_30 = [1, 2, 3, 5, 6, 10, 15]


def exact_order(a: int, order: int, proper_divs: list[int], mod: int = M) -> bool:
    return pow(a, order, mod) == 1 and all(pow(a, d, mod) != 1 for d in proper_divs)


def multiplicative_order(a: int, mod: int = M, max_k: int = 2000) -> int | None:
    if math.gcd(a, mod) != 1:
        return None
    x = 1
    for k in range(1, max_k + 1):
        x = (x * a) % mod
        if x == 1:
            return k
    return None


def main() -> None:
    anchor_orders = {a: multiplicative_order(a) for a in MONSTER}
    exact60 = {a: exact_order(a, 60, PROPER_DIVS_60) for a in MONSTER}

    product = MONSTER[0] * MONSTER[1] * MONSTER[2]
    product_residue = product % M
    c1_residue = C1 % M

    product_exact60 = exact_order(product_residue, 60, PROPER_DIVS_60)
    c1_exact30 = exact_order(c1_residue, 30, PROPER_DIVS_30)
    source3_exact30 = exact_order(3, 30, PROPER_DIVS_30)

    result = {
        "theorem": "monster_mod1001_order_classes_protocol_v1",
        "claim_subset": {
            "modulus": M,
            "monster_anchors": MONSTER,
            "c1": C1,
        },
        "structural_checks": {
            "all_anchors_coprime_to_1001": all(math.gcd(a, M) == 1 for a in MONSTER),
            "anchor_orders": anchor_orders,
            "anchors_exact_order_60": exact60,
            "all_anchors_exact_order_60": all(exact60.values()),
            "product": product,
            "product_residue_mod1001": product_residue,
            "product_residue_exact_order_60": product_exact60,
            "c1_residue_mod1001": c1_residue,
            "c1_residue_exact_order_30": c1_exact30,
            "source3_exact_order_30": source3_exact30,
            "c1_and_source3_share_order_class_30": c1_exact30 and source3_exact30,
        },
    }

    output_path = Path("monster_mod1001_order_classes_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic Monster mod1001 order-classes summary:")
    print(f"  {output_path.resolve()}")
    print(
        "  orders="
        f"{anchor_orders}, product_residue={product_residue}, c1_residue={c1_residue}"
    )


if __name__ == "__main__":
    main()
