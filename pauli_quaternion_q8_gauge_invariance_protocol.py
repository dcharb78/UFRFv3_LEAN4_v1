#!/usr/bin/env python3
"""
Protocol: Q8 "Wilson loop" gauge-invariance scaffold (finite, exact).

We work in the discrete SU(2) subset Q8 realized by Pauli→Quaternion matrices:
  Q8 := {±I, ±qi, ±qj, ±qk}

Define a 2×2 trace:
  tr2(A) := A00 + A11

Gauge invariance (minimal finite scaffold):
  tr2(g * P * g^{-1}) = tr2(P)

We certify this exactly for all g,P ∈ Q8, using the explicit Q8 inverse map.

This is a discrete, fully algebraic analogue of the trace-invariance behind
Wilson-loop / plaquette observables in lattice Yang–Mills.
"""

from __future__ import annotations

import json
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parent
OUT = ROOT / "pauli_quaternion_q8_gauge_invariance_results.json"


def paulis() -> tuple[sp.Matrix, sp.Matrix, sp.Matrix]:
    I = sp.I
    sx = sp.Matrix([[0, 1], [1, 0]])
    sy = sp.Matrix([[0, -I], [I, 0]])
    sz = sp.Matrix([[1, 0], [0, -1]])
    return sx, sy, sz


def mat_eq(a: sp.Matrix, b: sp.Matrix) -> bool:
    return sp.simplify(a - b) == sp.zeros(a.rows, a.cols)


def tr2(a: sp.Matrix) -> sp.Expr:
    return sp.simplify(a[0, 0] + a[1, 1])


def q8_inv_index(idx: int) -> int:
    # elem_order = ["I", "-I", "qi", "-qi", "qj", "-qj", "qk", "-qk"]
    if idx in (0, 1):
        return idx
    if idx == 2:
        return 3
    if idx == 3:
        return 2
    if idx == 4:
        return 5
    if idx == 5:
        return 4
    if idx == 6:
        return 7
    if idx == 7:
        return 6
    raise ValueError(idx)


def main() -> None:
    sx, sy, sz = paulis()
    I = sp.I
    I2 = sp.eye(2)

    qi = (-I) * sx
    qj = (-I) * sy
    qk = (-I) * sz

    elems = [I2, -I2, qi, -qi, qj, -qj, qk, -qk]

    inv_ok = True
    for i in range(8):
        inv = elems[q8_inv_index(i)]
        if not (mat_eq(sp.simplify(elems[i] * inv), I2) and mat_eq(sp.simplify(inv * elems[i]), I2)):
            inv_ok = False
            break

    trace_invariant = True
    for g in range(8):
        ginv = elems[q8_inv_index(g)]
        for p in range(8):
            lhs = tr2(sp.simplify(elems[g] * elems[p] * ginv))
            rhs = tr2(elems[p])
            if sp.simplify(lhs - rhs) != 0:
                trace_invariant = False
                break
        if not trace_invariant:
            break

    ok = inv_ok and trace_invariant

    results = {
        "theorem": "pauli_quaternion_q8_gauge_invariance_protocol_v1",
        "ok": ok,
        "inverse_ok": inv_ok,
        "trace_conjugation_invariant": trace_invariant,
        "elem_order": ["I", "-I", "qi", "-qi", "qj", "-qj", "qk", "-qk"],
        "trace": "tr2(A)=A00+A11",
        "observable": "tr2(g*P*g^{-1})",
    }

    OUT.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Saved deterministic Pauli-Quaternion Q8 gauge-invariance summary: {OUT}")
    print(f"  ok={ok}")


if __name__ == "__main__":
    main()

