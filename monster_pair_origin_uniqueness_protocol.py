"""
Monster pair-origin uniqueness protocol (deterministic synthesis bridge).

Finite deterministic scaffold:
  - compute Frobenius values over all UFRF generator pairs,
  - certify unique pair origins for 47, 59, 71,
  - retain AP(12) consistency on the resulting triple.
"""

from __future__ import annotations

import json
from pathlib import Path


UFRF = [3, 5, 7, 11, 13]
TARGETS = [47, 59, 71]


def frobenius(a: int, b: int) -> int:
    return a * b - a - b


def main() -> None:
    pairs = [(UFRF[i], UFRF[j]) for i in range(len(UFRF)) for j in range(i + 1, len(UFRF))]
    pair_values = [(a, b, frobenius(a, b)) for (a, b) in pairs]

    preimages = {
        t: [(a, b) for (a, b, v) in pair_values if v == t]
        for t in TARGETS
    }

    result = {
        "theorem": "monster_pair_origin_uniqueness_protocol_v1",
        "claim_subset": {
            "source": "UFRF pairwise Frobenius values",
            "target_triple": TARGETS,
        },
        "structural_checks": {
            "pair_values": [{"a": a, "b": b, "frob": v} for (a, b, v) in pair_values],
            "preimages": {str(k): v for k, v in preimages.items()},
            "unique_preimage_47": preimages[47] == [(5, 13)],
            "unique_preimage_59": preimages[59] == [(7, 11)],
            "unique_preimage_71": preimages[71] == [(7, 13)],
            "ap12_diff1": TARGETS[1] - TARGETS[0] == 12,
            "ap12_diff2": TARGETS[2] - TARGETS[1] == 12,
            "product_plus_one_is_196884": TARGETS[0] * TARGETS[1] * TARGETS[2] + 1 == 196884,
        },
    }

    output_path = Path("monster_pair_origin_uniqueness_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic Monster pair-origin uniqueness summary:")
    print(f"  {output_path.resolve()}")
    print(f"  preimages={preimages}")


if __name__ == "__main__":
    main()
