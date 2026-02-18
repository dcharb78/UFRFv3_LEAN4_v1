#!/usr/bin/env python3
"""
Protocol: Maxwell field-tensor (E,B) encoding + Hodge-duality scaffold (finite, exact).

We encode an EM state by 6 components (E,B) in natural units (c=1):
  E = (Ex,Ey,Ez), B = (Bx,By,Bz)

Define the antisymmetric 4×4 field tensor F with components:
  F01=Ex, F02=Ey, F03=Ez
  F23=Bx, F31=By, F12=Bz
  and Fji = -Fij, Fii=0.

Define the dual operation on (E,B):
  *(E,B) := (B, -E)
so that ** = -1 on this 6D space:
  *(* (E,B)) = (-E, -B).

This is a finite algebraic anchor (no PDEs) for the E/B dual-plane structure.
"""

from __future__ import annotations

import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent
OUT = ROOT / "maxwell_field_tensor_duality_results.json"


def dual_em(E: tuple[int, int, int], B: tuple[int, int, int]) -> tuple[tuple[int, int, int], tuple[int, int, int]]:
    return B, (-E[0], -E[1], -E[2])


def to_F(E: tuple[int, int, int], B: tuple[int, int, int]) -> list[list[int]]:
    Ex, Ey, Ez = E
    Bx, By, Bz = B
    F = [[0 for _ in range(4)] for _ in range(4)]
    # Electric components.
    F[0][1] = Ex
    F[0][2] = Ey
    F[0][3] = Ez
    # Magnetic components (spatial bivectors).
    F[2][3] = Bx
    # F31 = By, but we must set the upper-triangular entry first so antisymmetrization
    # doesn't overwrite it.
    F[1][3] = -By
    F[1][2] = Bz
    # Antisymmetrize.
    for i in range(4):
        for j in range(i + 1, 4):
            F[j][i] = -F[i][j]
    return F


def is_antisymmetric(F: list[list[int]]) -> bool:
    for i in range(4):
        if F[i][i] != 0:
            return False
        for j in range(4):
            if F[i][j] != -F[j][i]:
                return False
    return True


def main() -> None:
    # Deterministic anchor example (not a universal claim about physics).
    E = (1, 2, 3)
    B = (4, 5, 6)
    F = to_F(E, B)
    antisym_ok = is_antisymmetric(F)

    E1, B1 = dual_em(E, B)
    E2, B2 = dual_em(E1, B1)
    dual2_ok = (E2, B2) == ((-E[0], -E[1], -E[2]), (-B[0], -B[1], -B[2]))

    results = {
        "theorem": "maxwell_field_tensor_duality_protocol_v1",
        "ok": antisym_ok and dual2_ok,
        "antisymmetric_F_ok": antisym_ok,
        "dual2_is_neg_ok": dual2_ok,
        "example": {"E": E, "B": B, "F": F},
        "dual_rule": "*(E,B)=(B,-E)",
    }

    OUT.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Saved deterministic Maxwell field-tensor duality summary: {OUT}")
    print(f"  ok={results['ok']}")


if __name__ == "__main__":
    main()
