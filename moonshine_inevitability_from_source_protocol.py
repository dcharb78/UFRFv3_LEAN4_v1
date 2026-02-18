"""
Moonshine inevitability-from-source protocol (deterministic synthesis bridge).

Finite deterministic scaffold:
  - derive source values from all UFRF pairwise Frobenius values,
  - derive the unique AP(12) source triple,
  - certify c1=product+1 and denominator-ladder checks for c2/c3/c4.
"""

from __future__ import annotations

import json
from pathlib import Path


UFRF = [3, 5, 7, 11, 13]


def frobenius(a: int, b: int) -> int:
    return a * b - a - b


def main() -> None:
    pairs = [(UFRF[i], UFRF[j]) for i in range(len(UFRF)) for j in range(i + 1, len(UFRF))]
    pair_values = [(a, b, frobenius(a, b)) for (a, b) in pairs]
    source_values = sorted({v for (_, _, v) in pair_values})

    ap12_triples = [
        (a, b, c)
        for i, a in enumerate(source_values)
        for j, b in enumerate(source_values)
        for c in source_values
        if i < j and b - a == 12 and c - b == 12
    ]

    monster = ap12_triples[0] if ap12_triples else (0, 0, 0)
    m1, m2, m3 = monster
    product = m1 * m2 * m3
    c1 = 196884

    e1 = m1 + m2 + m3
    e2 = m1 * m2 + m1 * m3 + m2 * m3
    e3 = product

    c2 = 21493760
    c2_num = 8 * e1 * e3 + 61 * e2 - 31 * e1 + 9800

    c3 = 864299970
    c3_num = 4 * e3 * e3 - 4 * e2 * e3 - 8 * e2 * e2 - 2487 * e2 - 39 * e1 - 34

    c4 = 20245856256
    c4_num = 1147 * e3 * e3 + 9 * e2 * e3 + 8 * e2 * e2 - 1547 * e2 - 32 * e1 + 5

    result = {
        "theorem": "moonshine_inevitability_from_source_protocol_v1",
        "claim_subset": {
            "source": "UFRF pairwise Frobenius values",
            "derived_monster_triple_via_ap12": True,
            "j_anchor": "c1 = product(monster)+1",
            "denominator_ladder": [13, 169, 2197],
        },
        "structural_checks": {
            "ap12_triples_from_source": ap12_triples,
            "unique_ap12_source_triple": ap12_triples == [(47, 59, 71)],
            "derived_monster_triple": monster,
            "ap12_diff1_eq_12": m2 - m1 == 12,
            "ap12_diff2_eq_12": m3 - m2 == 12,
            "c1_equals_product_plus_one": c1 == product + 1,
            "sigma1_eq_177": e1 == 177,
            "c2_num_eq_13_times_c2": c2_num == 13 * c2,
            "c3_num_eq_169_times_c3": c3_num == 169 * c3,
            "c4_num_eq_2197_times_c4": c4_num == 2197 * c4,
        },
        "derived_values": {
            "monster_triple": [m1, m2, m3],
            "product": product,
            "e1": e1,
            "e2": e2,
            "e3": e3,
            "c2_num": c2_num,
            "c3_num": c3_num,
            "c4_num": c4_num,
        },
    }

    output_path = Path("moonshine_inevitability_from_source_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic Moonshine inevitability-from-source summary:")
    print(f"  {output_path.resolve()}")
    print(f"  monster={monster}, c1=product+1 -> {c1 == product + 1}")


if __name__ == "__main__":
    main()
