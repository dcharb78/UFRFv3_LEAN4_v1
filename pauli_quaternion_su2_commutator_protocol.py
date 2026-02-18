#!/usr/bin/env python3
"""
Protocol: SU(2) Lie-bracket anchor from the Pauli→Quaternion realization (finite, exact).

Using:
  qi := (-i) σx
  qj := (-i) σy
  qk := (-i) σz

Define the commutator bracket:
  [A,B] := AB - BA

Then (exactly):
  [qi,qj] = 2 qk
  [qj,qk] = 2 qi
  [qk,qi] = 2 qj

and the Jacobi identity holds on (qi,qj,qk):
  [qi,[qj,qk]] + [qj,[qk,qi]] + [qk,[qi,qj]] = 0.

This is the minimal algebraic SU(2) / su(2) scaffold we can later lift into
finite lattice Yang–Mills gauge invariance statements.
"""

from __future__ import annotations

import json
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parent
OUT = ROOT / "pauli_quaternion_su2_commutator_results.json"


def paulis() -> tuple[sp.Matrix, sp.Matrix, sp.Matrix]:
    I = sp.I
    sx = sp.Matrix([[0, 1], [1, 0]])
    sy = sp.Matrix([[0, -I], [I, 0]])
    sz = sp.Matrix([[1, 0], [0, -1]])
    return sx, sy, sz


def mat_eq(a: sp.Matrix, b: sp.Matrix) -> bool:
    return sp.simplify(a - b) == sp.zeros(a.rows, a.cols)


def comm(a: sp.Matrix, b: sp.Matrix) -> sp.Matrix:
    return sp.simplify(a * b - b * a)


def main() -> None:
    sx, sy, sz = paulis()
    I = sp.I

    qi = (-I) * sx
    qj = (-I) * sy
    qk = (-I) * sz

    checks = {
        "comm_qi_qj": mat_eq(comm(qi, qj), 2 * qk),
        "comm_qj_qk": mat_eq(comm(qj, qk), 2 * qi),
        "comm_qk_qi": mat_eq(comm(qk, qi), 2 * qj),
        "jacobi_qi_qj_qk": mat_eq(
            sp.simplify(comm(qi, comm(qj, qk)) + comm(qj, comm(qk, qi)) + comm(qk, comm(qi, qj))),
            sp.zeros(2),
        ),
    }
    ok = all(checks.values())

    results = {
        "theorem": "pauli_quaternion_su2_commutator_protocol_v1",
        "ok": ok,
        "checks": checks,
        "mapping": "qi=(-i)sigma_x, qj=(-i)sigma_y, qk=(-i)sigma_z",
        "bracket": "[A,B]=AB-BA",
    }

    OUT.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Saved deterministic Pauli-Quaternion su2 commutator summary: {OUT}")
    print(f"  ok={ok}")


if __name__ == "__main__":
    main()

