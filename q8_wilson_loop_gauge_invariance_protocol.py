#!/usr/bin/env python3
"""
Protocol: general closed-loop Wilson observable gauge invariance over Q8 (finite, exact).

Goal (discrete lattice Yang–Mills skeleton):
For a closed loop v0→v1→...→vL=v0, with edge variables U_i and vertex gauges g(v),
under the local gauge update
  U(v_i→v_{i+1}) ↦ g(v_i) * U(v_i→v_{i+1}) * g(v_{i+1})^{-1},
the loop holonomy transforms by basepoint conjugation:
  U_loop' = g(v0) * U_loop * g(v0)^{-1}.
Therefore the Wilson observable (trace) is invariant.

This protocol tests the identity on Q8 realized inside SU(2) via Pauli→Quaternion matrices,
but performs checks on indices using the derived Q8 multiplication table for speed.

We deterministically test:
- Loop length L = 6 (strictly beyond single-plaquette length 4).
- All closed gauge sequences g0..g5 with closure g6=g0: 8^6 = 262,144.
- A small fixed set of 4 edge patterns (each edge ∈ Q8), for total cases:
    262,144 * 4 = 1,048,576  (same scale as the plaquette protocol).

This stays fast in the repo-wide verify pipeline while exercising the telescoping
internal cancellations that make Wilson loops gauge-invariant.
"""

from __future__ import annotations

import json
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parent
OUT = ROOT / "q8_wilson_loop_gauge_invariance_results.json"


def paulis() -> tuple[sp.Matrix, sp.Matrix, sp.Matrix]:
    I = sp.I
    sx = sp.Matrix([[0, 1], [1, 0]])
    sy = sp.Matrix([[0, -I], [I, 0]])
    sz = sp.Matrix([[1, 0], [0, -1]])
    return sx, sy, sz


def mat_eq(a: sp.Matrix, b: sp.Matrix) -> bool:
    return sp.simplify(a - b) == sp.zeros(a.rows, a.cols)


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
    inv = [q8_inv_index(i) for i in range(8)]

    # Multiply table in index form: mul[i][j] = k where elems[i]*elems[j] = elems[k].
    mul: list[list[int]] = [[-1] * 8 for _ in range(8)]
    for i in range(8):
        for j in range(8):
            prod = sp.simplify(elems[i] * elems[j])
            k = None
            for t in range(8):
                if mat_eq(prod, elems[t]):
                    k = t
                    break
            if k is None:
                raise RuntimeError(f"Q8 closure lookup failed for i={i}, j={j}")
            mul[i][j] = k

    # Trace map for Q8 in this representation.
    tr_map = {
        0: 2,  # I
        1: -2,  # -I
        2: 0,  # qi
        3: 0,  # -qi
        4: 0,  # qj
        5: 0,  # -qj
        6: 0,  # qk
        7: 0,  # -qk
    }

    def edge_gauge(g_src: int, g_tgt: int, u: int) -> int:
        return mul[mul[g_src][u]][inv[g_tgt]]

    def holonomy(loop_edges: list[int]) -> int:
        acc = 0  # I
        for u in loop_edges:
            acc = mul[acc][u]
        return acc

    loop_len = 6
    gauge_assignments = 8**loop_len
    edge_patterns: list[list[int]] = [
        [0, 0, 0, 0, 0, 0],          # all I
        [2, 4, 6, 3, 5, 7],          # qi,qj,qk,-qi,-qj,-qk
        [4, 6, 2, 5, 7, 3],          # permuted signed units
        [1, 2, 1, 4, 1, 6],          # -I,qi,-I,qj,-I,qk
    ]

    checked = 0
    conj_ok = True
    trace_ok = True

    for t in range(gauge_assignments):
        # Base-8 digits for g0..g5; closure uses g6=g0.
        gs = [(t // (8**i)) % 8 for i in range(loop_len)]
        gs.append(gs[0])
        g0 = gs[0]
        g0inv = inv[g0]

        for edges in edge_patterns:
            up = holonomy(edges)
            gauged_edges = [edge_gauge(gs[i], gs[i + 1], edges[i]) for i in range(loop_len)]
            upp = holonomy(gauged_edges)
            conj = mul[mul[g0][up]][g0inv]

            checked += 1
            if upp != conj:
                conj_ok = False
                break
            if tr_map[upp] != tr_map[up]:
                trace_ok = False
                break
        if not (conj_ok and trace_ok):
            break

    ok = conj_ok and trace_ok
    results = {
        "theorem": "q8_wilson_loop_gauge_invariance_protocol_v1",
        "ok": ok,
        "checked_cases": checked,
        "loop_length": loop_len,
        "gauge_assignments": gauge_assignments,
        "edge_patterns": len(edge_patterns),
        "conjugation_identity_ok": conj_ok,
        "trace_invariant_ok": trace_ok,
        "elem_order": ["I", "-I", "qi", "-qi", "qj", "-qj", "qk", "-qk"],
        "observable": "tr2(U_loop') = tr2(U_loop) for closed loops",
        "note": "Finite protocol exercise; Lean theorem proves a general list-based cancellation lemma.",
    }

    OUT.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Saved Q8 general Wilson-loop gauge-invariance summary: {OUT}")
    print(f"  ok={ok} (checked {checked} cases)")


if __name__ == "__main__":
    main()

