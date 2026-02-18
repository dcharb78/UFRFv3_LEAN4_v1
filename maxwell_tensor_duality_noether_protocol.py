#!/usr/bin/env python3
"""
Protocol: tensor-side duality invariants under ⋆F (finite, deterministic).

Given the repo's explicit field tensor encoding F = toF(E,B) and the explicit tensor
Hodge-star operator ⋆F (as in maxwell_tensor_hodge_star_protocol.py), define:

  I1_fromF(F) := (F01^2 + F02^2 + F03^2) - (F23^2 + F31^2 + F12^2)
  I2_fromF(F) := F01*F23 + F02*F31 + F03*F12
  Q(F) := I1_fromF(F)^2 + I2_fromF(F)^2

We certify on a small exhaustive integer window that, on the image of toF:
  I1_fromF(⋆F(F)) = -I1_fromF(F)
  I2_fromF(⋆F(F)) = -I2_fromF(F)
  Q(⋆F(F)) = Q(F)
and that Q is invariant under all iterates (⋆F)^[n] for n=0..4.
"""

from __future__ import annotations

import json
from itertools import product
from pathlib import Path


ROOT = Path(__file__).resolve().parent
OUT = ROOT / "maxwell_tensor_duality_noether_results.json"


def toF(e: tuple[int, int, int], b: tuple[int, int, int]) -> list[list[int]]:
    ex, ey, ez = e
    bx, by, bz = b
    F = [[0] * 4 for _ in range(4)]

    F[0][1] = ex
    F[1][0] = -ex
    F[0][2] = ey
    F[2][0] = -ey
    F[0][3] = ez
    F[3][0] = -ez

    F[2][3] = bx
    F[3][2] = -bx
    F[3][1] = by
    F[1][3] = -by
    F[1][2] = bz
    F[2][1] = -bz

    return F


def starF(F: list[list[int]]) -> list[list[int]]:
    G = [[0] * 4 for _ in range(4)]

    G[0][1] = F[2][3]
    G[1][0] = -F[2][3]
    G[0][2] = F[3][1]
    G[2][0] = -F[3][1]
    G[0][3] = F[1][2]
    G[3][0] = -F[1][2]

    G[2][3] = -F[0][1]
    G[3][2] = F[0][1]
    G[3][1] = -F[0][2]
    G[1][3] = F[0][2]
    G[1][2] = -F[0][3]
    G[2][1] = F[0][3]

    return G


def I1_fromF(F: list[list[int]]) -> int:
    f01, f02, f03 = F[0][1], F[0][2], F[0][3]
    f23, f31, f12 = F[2][3], F[3][1], F[1][2]
    return (f01 * f01 + f02 * f02 + f03 * f03) - (f23 * f23 + f31 * f31 + f12 * f12)


def I2_fromF(F: list[list[int]]) -> int:
    f01, f02, f03 = F[0][1], F[0][2], F[0][3]
    f23, f31, f12 = F[2][3], F[3][1], F[1][2]
    return f01 * f23 + f02 * f31 + f03 * f12


def Q(F: list[list[int]]) -> int:
    i1 = I1_fromF(F)
    i2 = I2_fromF(F)
    return i1 * i1 + i2 * i2


def main() -> None:
    vals = list(range(-2, 3))
    cases = 0

    i1_flip = True
    i2_flip = True
    q_invariant = True
    q_iterate_invariant = True

    witness: dict[str, object] | None = None

    for ex, ey, ez, bx, by, bz in product(vals, repeat=6):
        e = (ex, ey, ez)
        b = (bx, by, bz)
        F = toF(e, b)

        i1 = I1_fromF(F)
        i2 = I2_fromF(F)
        q0 = i1 * i1 + i2 * i2

        SF = starF(F)
        i1s = I1_fromF(SF)
        i2s = I2_fromF(SF)
        qs = i1s * i1s + i2s * i2s

        if i1s != -i1:
            i1_flip = False
        if i2s != -i2:
            i2_flip = False
        if qs != q0:
            q_invariant = False

        # Iterate invariance on n=0..4
        G = F
        for _n in range(5):
            if Q(G) != q0:
                q_iterate_invariant = False
                break
            G = starF(G)

        cases += 1
        if witness is None and (ex, ey, ez, bx, by, bz) != (0, 0, 0, 0, 0, 0):
            witness = {
                "e": e,
                "b": b,
                "i1": i1,
                "i2": i2,
                "q": q0,
                "i1_star": i1s,
                "i2_star": i2s,
                "q_star": qs,
            }

    ok = i1_flip and i2_flip and q_invariant and q_iterate_invariant
    results = {
        "theorem": "maxwell_tensor_duality_noether_protocol_v1",
        "ok": ok,
        "cases": cases,
        "window": {"min": min(vals), "max": max(vals)},
        "i1_sign_flip_all": i1_flip,
        "i2_sign_flip_all": i2_flip,
        "q_invariant_one_step_all": q_invariant,
        "q_invariant_iterates_0_to_4_all": q_iterate_invariant,
        "witness": witness,
        "definitions": {
            "I1_fromF": "(F01^2+F02^2+F03^2)-(F23^2+F31^2+F12^2)",
            "I2_fromF": "F01*F23+F02*F31+F03*F12",
            "Q": "I1_fromF^2 + I2_fromF^2",
        },
    }

    OUT.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Saved deterministic Maxwell tensor duality Noether summary: {OUT}")
    print(f"  ok={ok}, cases={cases}")


if __name__ == "__main__":
    main()

