#!/usr/bin/env python3
"""
Protocol: Q8 closure for the Pauli→Quaternion matrix realization (finite, exact).

Given Pauli matrices σx, σy, σz over Gaussian integers via SymPy (entries in {0,±1,±i}),
define quaternion units:

  qi := (-i) σx
  qj := (-i) σy
  qk := (-i) σz

Define the 8-element set:
  Q8 := {±I, ±qi, ±qj, ±qk}

We certify (exactly) that:
  1) all 8 elements are distinct,
  2) Q8 is closed under multiplication (every product lands back in Q8),
  3) qi has a 4-step return (qi^4 = I) and order-2 square (qi^2 = -I),
  4) Q8 is noncommutative (qi*qj != qj*qi).

This is a purely algebraic bridge: no analysis, no floats, no PDE assumptions.
"""

from __future__ import annotations

import json
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parent
OUT = ROOT / "pauli_quaternion_q8_closure_results.json"


def paulis() -> tuple[sp.Matrix, sp.Matrix, sp.Matrix]:
    I = sp.I
    sx = sp.Matrix([[0, 1], [1, 0]])
    sy = sp.Matrix([[0, -I], [I, 0]])
    sz = sp.Matrix([[1, 0], [0, -1]])
    return sx, sy, sz


def mat_eq(a: sp.Matrix, b: sp.Matrix) -> bool:
    return sp.simplify(a - b) == sp.zeros(a.rows, a.cols)


def main() -> None:
    sx, sy, sz = paulis()
    I2 = sp.eye(2)
    I = sp.I

    qi = (-I) * sx
    qj = (-I) * sy
    qk = (-I) * sz

    elems = [I2, -I2, qi, -qi, qj, -qj, qk, -qk]

    # Distinctness (pairwise)
    distinct = True
    for i in range(len(elems)):
        for j in range(i + 1, len(elems)):
            if mat_eq(elems[i], elems[j]):
                distinct = False
                break
        if not distinct:
            break

    # Multiplication closure + table (index in 0..7)
    table: list[list[int]] = []
    closure = True
    for a in elems:
        row: list[int] = []
        for b in elems:
            prod = sp.simplify(a * b)
            hit = None
            for k, e in enumerate(elems):
                if mat_eq(prod, e):
                    hit = k
                    break
            if hit is None:
                closure = False
                hit = -1
            row.append(hit)
        table.append(row)

    # Order / return checks
    qi2_ok = mat_eq(sp.simplify(qi * qi), -I2)
    qi4_ok = mat_eq(sp.simplify(qi**4), I2)

    # Noncommutativity check (canonical witness)
    noncomm = not mat_eq(sp.simplify(qi * qj), sp.simplify(qj * qi))

    ok = all([distinct, closure, qi2_ok, qi4_ok, noncomm])

    results = {
        "theorem": "pauli_quaternion_q8_closure_protocol_v1",
        "ok": ok,
        "distinct": distinct,
        "closed_under_mul": closure,
        "qi2_is_negI": qi2_ok,
        "qi4_is_I": qi4_ok,
        "noncomm_witness_qi_qj": noncomm,
        "mul_table_indices": table,  # 8x8 indices into elems
        "elem_order": ["I", "-I", "qi", "-qi", "qj", "-qj", "qk", "-qk"],
        "mapping": "qi=(-i)sigma_x, qj=(-i)sigma_y, qk=(-i)sigma_z",
    }

    OUT.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Saved deterministic Pauli-Quaternion Q8 closure summary: {OUT}")
    print(f"  ok={ok}")


if __name__ == "__main__":
    main()

