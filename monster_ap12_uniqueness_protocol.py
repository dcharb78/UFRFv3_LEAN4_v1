"""
Monster AP12 uniqueness protocol (deterministic synthesis bridge).

Finite deterministic scaffold:
  - build Level-2 Frobenius list from UFRF generators,
  - deduplicate in first-occurrence order,
  - enumerate triples and filter AP(12),
  - certify unique AP(12) triple is (47,59,71),
  - certify product+1 gives 196884.
"""

from __future__ import annotations

import json
from pathlib import Path


UFRF = [3, 5, 7, 11, 13]


def frobenius(a: int, b: int) -> int:
    return a * b - a - b


def dedup_first(xs: list[int]) -> list[int]:
    seen = set()
    out: list[int] = []
    for x in xs:
        if x not in seen:
            seen.add(x)
            out.append(x)
    return out


def all_triples(xs: list[int]) -> list[tuple[int, int, int]]:
    n = len(xs)
    out: list[tuple[int, int, int]] = []
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(j + 1, n):
                out.append((xs[i], xs[j], xs[k]))
    return out


def is_ap12(t: tuple[int, int, int]) -> bool:
    a, b, c = t
    return (b == a + 12) and (c == b + 12)


def main() -> None:
    l2_all = [frobenius(UFRF[i], UFRF[j]) for i in range(len(UFRF)) for j in range(i + 1, len(UFRF))]
    l2_full = dedup_first(l2_all)
    ap12 = [t for t in all_triples(l2_full) if is_ap12(t)]

    monster = (47, 59, 71)
    c1 = monster[0] * monster[1] * monster[2] + 1

    result = {
        "theorem": "monster_ap12_uniqueness_protocol_v1",
        "claim_subset": {
            "l2_from_ufrf": True,
            "ap12_filter": "unique triple",
            "moonshine_anchor": "product+1",
        },
        "structural_checks": {
            "l2_all": l2_all,
            "l2_full": l2_full,
            "ap12_triples": [list(t) for t in ap12],
            "ap12_count_is_one": len(ap12) == 1,
            "ap12_unique_is_monster": ap12 == [monster],
            "c1_equals_196884": c1 == 196884,
        },
    }

    output_path = Path("monster_ap12_uniqueness_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic Monster AP12 uniqueness summary:")
    print(f"  {output_path.resolve()}")
    print(f"  ap12={ap12}, c1={c1}")


if __name__ == "__main__":
    main()
