#!/usr/bin/env python3
"""
Protocol: Dirac square-root factorization (scaled to avoid rationals).

This mirrors the "factorization_test" in the AllGreen package but avoids floating arithmetic
by clearing denominators.

Given the (seeded) 4-vector used in the AllGreen check:
  p = [2.0, 0.3, -0.1, 0.2], m = 1.0

Let d = 10, p' = d*p = [20, 3, -1, 2], and m' = d*m = 10.

Define:
  M := p0' γ0 - p1' γ1 - p2' γ2 - p3' γ3
     = 20 γ0 - 3 γ1 + 1 γ2 - 2 γ3

Then the factorization identity is exactly:
  (M - m' I)(M + m' I) = (p'^2 - m'^2) I

with:
  p'^2 - m'^2 = 20^2 - 3^2 - (-1)^2 - 2^2 - 10^2 = 286.
"""

from __future__ import annotations

import json
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parent
OUT = ROOT / "dirac_factorization_scaled_results.json"


def dirac_gammas() -> list[sp.Matrix]:
    I2 = sp.eye(2)
    Z2 = sp.zeros(2)
    I = sp.I
    sx = sp.Matrix([[0, 1], [1, 0]])
    sy = sp.Matrix([[0, -I], [I, 0]])
    sz = sp.Matrix([[1, 0], [0, -1]])

    g0 = sp.Matrix(sp.BlockMatrix([[I2, Z2], [Z2, -I2]]))
    g1 = sp.Matrix(sp.BlockMatrix([[Z2, sx], [-sx, Z2]]))
    g2 = sp.Matrix(sp.BlockMatrix([[Z2, sy], [-sy, Z2]]))
    g3 = sp.Matrix(sp.BlockMatrix([[Z2, sz], [-sz, Z2]]))
    return [g0, g1, g2, g3]


def main() -> None:
    g0, g1, g2, g3 = dirac_gammas()
    I4 = sp.eye(4)

    M = 20 * g0 - 3 * g1 + 1 * g2 - 2 * g3
    mp = 10
    scalar = 286

    lhs = (M - mp * I4) * (M + mp * I4)
    rhs = scalar * I4
    diff = lhs - rhs
    ok = sp.simplify(diff) == sp.zeros(4)

    results = {
        "theorem": "dirac_factorization_scaled_protocol_v1",
        "ok": ok,
        "d": 10,
        "p_scaled": [20, 3, -1, 2],
        "m_scaled": 10,
        "scalar": scalar,
        "symbolic_simplify_used": True,
    }

    OUT.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Saved deterministic Dirac factorization summary: {OUT}")
    print(f"  ok={ok}")


if __name__ == "__main__":
    main()
