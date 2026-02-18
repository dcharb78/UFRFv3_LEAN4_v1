#!/usr/bin/env python3
"""
Protocol: Dirac gamma matrices satisfy the Clifford anticommutator exactly.

This is a deterministic, finite algebraic bridge from the physics-draft lane
(`RequestedInfo/UFRF_AllGreen_Package_v1.0`) to the canonical protocol pipeline:

  {γ^μ, γ^ν} = γ^μ γ^ν + γ^ν γ^μ = 2 η^{μν} I

We use SymPy matrices with exact entries in ℤ[i] (0, ±1, ±I) to avoid floating error.
"""

from __future__ import annotations

import json
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parent
OUT = ROOT / "dirac_clifford_anticommutator_results.json"


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
    g = dirac_gammas()
    eta = sp.diag(1, -1, -1, -1)
    I4 = sp.eye(4)

    failures: list[dict[str, object]] = []
    ok = True
    for mu in range(4):
        for nu in range(4):
            lhs = g[mu] * g[nu] + g[nu] * g[mu]
            rhs = sp.Integer(2) * eta[mu, nu] * I4
            if lhs != rhs:
                ok = False
                failures.append(
                    {
                        "mu": mu,
                        "nu": nu,
                        "lhs": sp.srepr(lhs),
                        "rhs": sp.srepr(rhs),
                    }
                )

    results = {
        "theorem": "dirac_clifford_anticommutator_protocol_v1",
        "clifford_ok": ok,
        "failures": failures,
        "representation": "Dirac (standard) with Pauli blocks",
        "metric": "diag(1,-1,-1,-1)",
    }

    OUT.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Saved deterministic Dirac Clifford summary: {OUT}")
    print(f"  clifford_ok={ok}")


if __name__ == "__main__":
    main()

