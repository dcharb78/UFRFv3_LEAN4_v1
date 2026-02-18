#!/usr/bin/env python3
"""
Protocol: explicit Hodge-star operator on the 4×4 Maxwell field tensor (finite, deterministic).

This repo fixes a specific (E,B) -> F convention in:
  maxwell_field_tensor_duality_protocol.py

Here we define an explicit tensor star-map ⋆F as a pure index permutation/sign map
on the six independent components:
  (F01,F02,F03,F23,F31,F12)  <->  (F23,F31,F12,-F01,-F02,-F03)

We certify, on a small exhaustive integer window of EM states:
1) ⋆F(toF(E,B)) = toF(⋆(E,B)) where ⋆(E,B)=(B,-E)
2) ⋆F⋆F(toF(E,B)) = -toF(E,B)  (order-4 duality rotation on the image)
3) ⋆F output is antisymmetric.

No PDEs; just algebra and sign conventions.
"""

from __future__ import annotations

import json
from itertools import product
from pathlib import Path


ROOT = Path(__file__).resolve().parent
OUT = ROOT / "maxwell_tensor_hodge_star_results.json"


def toF(e: tuple[int, int, int], b: tuple[int, int, int]) -> list[list[int]]:
    ex, ey, ez = e
    bx, by, bz = b
    F = [[0] * 4 for _ in range(4)]

    # Electric components
    F[0][1] = ex
    F[1][0] = -ex
    F[0][2] = ey
    F[2][0] = -ey
    F[0][3] = ez
    F[3][0] = -ez

    # Magnetic bivectors
    F[2][3] = bx
    F[3][2] = -bx
    F[3][1] = by
    F[1][3] = -by
    F[1][2] = bz
    F[2][1] = -bz

    return F


def dual_em(e: tuple[int, int, int], b: tuple[int, int, int]) -> tuple[tuple[int, int, int], tuple[int, int, int]]:
    return b, (-e[0], -e[1], -e[2])


def negF(F: list[list[int]]) -> list[list[int]]:
    return [[-F[i][j] for j in range(4)] for i in range(4)]


def starF(F: list[list[int]]) -> list[list[int]]:
    G = [[0] * 4 for _ in range(4)]

    # Electric -> magnetic
    G[0][1] = F[2][3]
    G[1][0] = -F[2][3]
    G[0][2] = F[3][1]
    G[2][0] = -F[3][1]
    G[0][3] = F[1][2]
    G[3][0] = -F[1][2]

    # Magnetic -> -electric
    G[2][3] = -F[0][1]
    G[3][2] = F[0][1]
    G[3][1] = -F[0][2]
    G[1][3] = F[0][2]
    G[1][2] = -F[0][3]
    G[2][1] = F[0][3]

    return G


def is_antisymm(F: list[list[int]]) -> bool:
    for i in range(4):
        for j in range(4):
            if F[i][j] != -F[j][i]:
                return False
    return True


def mat_eq(A: list[list[int]], B: list[list[int]]) -> bool:
    return all(A[i][j] == B[i][j] for i in range(4) for j in range(4))


def main() -> None:
    vals = list(range(-2, 3))
    cases = 0

    commute_ok = True
    square_ok = True
    antisymm_ok = True
    witness: dict[str, object] | None = None

    for ex, ey, ez, bx, by, bz in product(vals, repeat=6):
        e = (ex, ey, ez)
        b = (bx, by, bz)
        F = toF(e, b)

        if not is_antisymm(F):
            antisymm_ok = False

        ed, bd = dual_em(e, b)
        F_dual = toF(ed, bd)

        SF = starF(F)
        if not mat_eq(SF, F_dual):
            commute_ok = False

        SSF = starF(SF)
        if not mat_eq(SSF, negF(F)):
            square_ok = False

        if not is_antisymm(SF):
            antisymm_ok = False

        cases += 1
        if witness is None and (ex, ey, ez, bx, by, bz) != (0, 0, 0, 0, 0, 0):
            witness = {
                "e": e,
                "b": b,
                "F01": F[0][1],
                "F02": F[0][2],
                "F03": F[0][3],
                "F23": F[2][3],
                "F31": F[3][1],
                "F12": F[1][2],
            }

    ok = commute_ok and square_ok and antisymm_ok
    results = {
        "theorem": "maxwell_tensor_hodge_star_protocol_v1",
        "ok": ok,
        "cases": cases,
        "window": {"min": min(vals), "max": max(vals)},
        "star_commutes_with_toF_and_dual": commute_ok,
        "star_square_is_neg_on_toF_image": square_ok,
        "star_output_is_antisymmetric": antisymm_ok,
        "witness": witness,
        "convention": {
            "toF": "F01=Ex,F02=Ey,F03=Ez; F23=Bx,F31=By,F12=Bz (antisymmetric fill)",
            "dual_em": "⋆(E,B)=(B,-E)",
            "starF": "(F01,F02,F03,F23,F31,F12) -> (F23,F31,F12,-F01,-F02,-F03)",
        },
    }

    OUT.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Saved deterministic Maxwell tensor Hodge-star summary: {OUT}")
    print(f"  ok={ok}, cases={cases}")


if __name__ == "__main__":
    main()
