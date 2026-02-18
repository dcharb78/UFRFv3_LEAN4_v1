"""
Mod-1001 composite-cycle bridge protocol.

Finite deterministic bridge over concrete anchors:
  - 1001 = 7*11*13
  - 10^3 ≡ -1 (mod 1001)
  - 10^6 ≡ 1  (mod 1001)
  - for anchor n: n*10^3 is the mod-1001 negation and n*10^6 returns.
"""

from __future__ import annotations

import json
from pathlib import Path


M = 1001
ANCHORS = [13, 169, 2197, 196883, 196884, 144000]


def main() -> None:
    pow3 = pow(10, 3, M)
    pow6 = pow(10, 6, M)

    per_anchor = []
    flip_all = True
    return_all = True
    neg_all = True

    for n in ANCHORS:
        r = n % M
        flip_ok = ((n * (10**3)) + n) % M == 0
        ret_ok = (n * (10**6)) % M == r
        neg_ok = ((n * (10**3)) % M) == ((M - r) % M)

        flip_all = flip_all and flip_ok
        return_all = return_all and ret_ok
        neg_all = neg_all and neg_ok

        per_anchor.append(
            {
                "n": n,
                "mod1001": r,
                "mod7": n % 7,
                "mod11": n % 11,
                "mod13": n % 13,
                "flip_ok": flip_ok,
                "return_ok": ret_ok,
                "neg_ok": neg_ok,
            }
        )

    result = {
        "theorem": "mod1001_composite_cycle_protocol_v1",
        "claim_subset": {
            "composite_modulus": "1001 = 7*11*13",
            "cycle_ops": "10^3 flip, 10^6 return",
        },
        "structural_checks": {
            "factorization": M == 7 * 11 * 13,
            "pow3_is_minus1_mod1001": pow3 == M - 1,
            "pow6_is_one_mod1001": pow6 == 1,
            "flip_holds_all_anchors": flip_all,
            "return_holds_all_anchors": return_all,
            "negation_form_holds_all_anchors": neg_all,
        },
        "anchors": per_anchor,
    }

    output_path = Path("mod1001_composite_cycle_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic mod1001 composite-cycle summary:")
    print(f"  {output_path.resolve()}")
    print(f"  pow3={pow3}, pow6={pow6}, anchors={len(ANCHORS)}")


if __name__ == "__main__":
    main()
