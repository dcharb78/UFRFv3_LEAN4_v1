#!/usr/bin/env python3
"""
Protocol: Pauli matrices realize quaternion units (SU(2) anchor).

We certify (exactly, with SymPy) that the standard Pauli matrices yield the quaternion
multiplication table when mapped as:

  qi := (-i) σx
  qj := (-i) σy
  qk := (-i) σz

Then:
  qi^2 = qj^2 = qk^2 = -I
  qi*qj = qk, qj*qk = qi, qk*qi = qj
  and anti-commutation signs match (e.g. qj*qi = -qk).
"""

from __future__ import annotations

import json
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parent
OUT = ROOT / "pauli_quaternion_bridge_results.json"


def paulis() -> tuple[sp.Matrix, sp.Matrix, sp.Matrix]:
    I = sp.I
    sx = sp.Matrix([[0, 1], [1, 0]])
    sy = sp.Matrix([[0, -I], [I, 0]])
    sz = sp.Matrix([[1, 0], [0, -1]])
    return sx, sy, sz


def main() -> None:
    sx, sy, sz = paulis()
    I2 = sp.eye(2)
    I = sp.I

    qi = (-I) * sx
    qj = (-I) * sy
    qk = (-I) * sz

    checks = {
        "qi2": sp.simplify(qi * qi + I2) == sp.zeros(2),
        "qj2": sp.simplify(qj * qj + I2) == sp.zeros(2),
        "qk2": sp.simplify(qk * qk + I2) == sp.zeros(2),
        "qi_qj": sp.simplify(qi * qj - qk) == sp.zeros(2),
        "qj_qk": sp.simplify(qj * qk - qi) == sp.zeros(2),
        "qk_qi": sp.simplify(qk * qi - qj) == sp.zeros(2),
        "qj_qi": sp.simplify(qj * qi + qk) == sp.zeros(2),
    }
    ok = all(checks.values())

    results = {
        "theorem": "pauli_quaternion_bridge_protocol_v1",
        "ok": ok,
        "checks": checks,
        "mapping": "qi=(-i)sigma_x, qj=(-i)sigma_y, qk=(-i)sigma_z",
    }

    OUT.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Saved deterministic Pauli->Quaternion summary: {OUT}")
    print(f"  ok={ok}")


if __name__ == "__main__":
    main()

