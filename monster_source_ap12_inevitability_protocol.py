"""
Monster source-AP12 inevitability protocol (deterministic synthesis bridge).

Finite deterministic scaffold:
  - derive source values from all UFRF pairwise Frobenius values,
  - find all AP(12) triples in those source values,
  - certify uniqueness of the (47,59,71) hit and product+1 = 196884.
"""

from __future__ import annotations

import json
from pathlib import Path


UFRF = [3, 5, 7, 11, 13]
TARGET_C1 = 196884


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

    c1_hits = [t for t in ap12_triples if t[0] * t[1] * t[2] + 1 == TARGET_C1]
    preimages = {
        str(v): [(a, b) for (a, b, w) in pair_values if w == v]
        for v in (47, 59, 71)
    }

    result = {
        "theorem": "monster_source_ap12_inevitability_protocol_v1",
        "claim_subset": {
            "source": "UFRF pairwise Frobenius values",
            "target_c1": TARGET_C1,
        },
        "structural_checks": {
            "pair_values": [{"a": a, "b": b, "frob": v} for (a, b, v) in pair_values],
            "source_values": source_values,
            "ap12_triples_from_source": ap12_triples,
            "triples_with_product_plus_one_196884": c1_hits,
            "unique_ap12_triple_from_source": ap12_triples == [(47, 59, 71)],
            "unique_c1_hit_from_source": c1_hits == [(47, 59, 71)],
            "preimages_47_59_71": preimages,
            "triple_values_have_unique_pair_origins": all(len(preimages[str(v)]) == 1 for v in (47, 59, 71)),
        },
    }

    output_path = Path("monster_source_ap12_inevitability_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic Monster source-AP12 inevitability summary:")
    print(f"  {output_path.resolve()}")
    print(f"  ap12_triples={ap12_triples}")
    print(f"  c1_hits={c1_hits}")


if __name__ == "__main__":
    main()
