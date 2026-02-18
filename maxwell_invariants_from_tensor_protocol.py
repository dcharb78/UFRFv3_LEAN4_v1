#!/usr/bin/env python3
"""
Protocol: Maxwell invariants as tensor contractions (finite, exact scaffold).

Using the same field-tensor convention as `maxwell_field_tensor_duality_protocol.py`:
  F01=Ex, F02=Ey, F03=Ez
  F23=Bx, F31=By, F12=Bz
  and antisymmetry Fji=-Fij.

Define (natural units c=1):
  I1 := |E|^2 - |B|^2
  I2 := E · B

Define reconstructions from tensor entries:
  I1_F := (F01^2 + F02^2 + F03^2) - (F23^2 + F31^2 + F12^2)
  I2_F := (F01*F23 + F02*F31 + F03*F12)

We certify deterministically on fixed integer anchors that:
  I1_F = I1 and I2_F = I2.
"""

from __future__ import annotations

import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent
OUT = ROOT / "maxwell_invariants_from_tensor_results.json"


def to_F(E: tuple[int, int, int], B: tuple[int, int, int]) -> list[list[int]]:
    Ex, Ey, Ez = E
    Bx, By, Bz = B
    F = [[0 for _ in range(4)] for _ in range(4)]
    F[0][1] = Ex
    F[0][2] = Ey
    F[0][3] = Ez
    F[2][3] = Bx
    # Set upper-triangular entry so antisymmetrization doesn't overwrite it.
    F[1][3] = -By
    F[1][2] = Bz
    for i in range(4):
        for j in range(i + 1, 4):
            F[j][i] = -F[i][j]
    return F


def main() -> None:
    anchors = [
        {"name": "generic", "E": (1, 2, 3), "B": (4, 5, 6)},
        {"name": "null_plane_wave", "E": (1, 0, 0), "B": (0, 1, 0)},
        {"name": "orth_equal", "E": (3, 4, 0), "B": (-4, 3, 0)},
    ]

    checks = []
    for ex in anchors:
        E = ex["E"]
        B = ex["B"]
        Ex, Ey, Ez = E
        Bx, By, Bz = B
        F = to_F(E, B)

        I1 = Ex * Ex + Ey * Ey + Ez * Ez - (Bx * Bx + By * By + Bz * Bz)
        I2 = Ex * Bx + Ey * By + Ez * Bz

        I1_F = (F[0][1] ** 2 + F[0][2] ** 2 + F[0][3] ** 2) - (
            F[2][3] ** 2 + F[3][1] ** 2 + F[1][2] ** 2
        )
        I2_F = F[0][1] * F[2][3] + F[0][2] * F[3][1] + F[0][3] * F[1][2]

        checks.append(
            {
                "name": ex["name"],
                "E": E,
                "B": B,
                "I1": I1,
                "I2": I2,
                "I1_fromF": I1_F,
                "I2_fromF": I2_F,
                "I1_ok": I1_F == I1,
                "I2_ok": I2_F == I2,
            }
        )

    ok = all(c["I1_ok"] and c["I2_ok"] for c in checks)

    results = {
        "theorem": "maxwell_invariants_from_tensor_protocol_v1",
        "ok": ok,
        "checks": checks,
        "I1": "|E|^2-|B|^2 (c=1)",
        "I2": "E·B",
        "I1_fromF": "(F01^2+F02^2+F03^2)-(F23^2+F31^2+F12^2)",
        "I2_fromF": "F01*F23+F02*F31+F03*F12",
    }

    OUT.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Saved deterministic Maxwell invariants-from-tensor summary: {OUT}")
    print(f"  ok={ok}")


if __name__ == "__main__":
    main()
