#!/usr/bin/env python3
"""
Protocol: single-plaquette Wilson-loop gauge invariance over Q8 (finite, exact).

This extends the existing Q8 conjugation-invariance protocol by checking the *plaquette*
identity used in lattice Yang–Mills:

Edge gauge update (oriented s→t):
  U(st) ↦ g(s) * U(st) * g(t)^{-1}

Plaquette holonomy:
  U_p := U01 * U12 * U23 * U30

Then for a single square plaquette (0→1→2→3→0),
  U_p' = g0 * U_p * g0^{-1}
so the Wilson-loop observable is invariant:
  tr2(U_p') = tr2(U_p).

We test this deterministically on:
- all 4-vertex gauge assignments g0,g1,g2,g3 ∈ Q8 (8^4 = 4096),
- a small deterministic edge subset (I, qi, qj, qk) on each edge (4^4 = 256).

This stays fast for the repo-wide verify pipeline while still exercising the
nontrivial internal cancellations (g1,g2,g3 disappear from the plaquette).
"""

from __future__ import annotations

import json
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parent
OUT = ROOT / "q8_plaquette_wilson_loop_gauge_invariance_results.json"


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
        0: 2,   # I
        1: -2,  # -I
        2: 0,   # qi
        3: 0,   # -qi
        4: 0,   # qj
        5: 0,   # -qj
        6: 0,   # qk
        7: 0,   # -qk
    }

    def edge_gauge(g_src: int, g_tgt: int, u: int) -> int:
        return mul[mul[g_src][u]][inv[g_tgt]]

    def plaquette(u01: int, u12: int, u23: int, u30: int) -> int:
        return mul[mul[mul[u01][u12]][u23]][u30]

    # Deterministic edge subset: unsigned units only.
    edge_subset = [0, 2, 4, 6]  # I, qi, qj, qk

    checked = 0
    trace_ok = True
    conj_ok = True
    for g0 in range(8):
        for g1 in range(8):
            for g2 in range(8):
                for g3 in range(8):
                    for u01 in edge_subset:
                        for u12 in edge_subset:
                            for u23 in edge_subset:
                                for u30 in edge_subset:
                                    up = plaquette(u01, u12, u23, u30)
                                    u01p = edge_gauge(g0, g1, u01)
                                    u12p = edge_gauge(g1, g2, u12)
                                    u23p = edge_gauge(g2, g3, u23)
                                    u30p = edge_gauge(g3, g0, u30)
                                    upp = plaquette(u01p, u12p, u23p, u30p)
                                    conj = mul[mul[g0][up]][inv[g0]]
                                    checked += 1
                                    if upp != conj:
                                        conj_ok = False
                                        break
                                    if tr_map[upp] != tr_map[up]:
                                        trace_ok = False
                                        break
                                if not (conj_ok and trace_ok):
                                    break
                            if not (conj_ok and trace_ok):
                                break
                        if not (conj_ok and trace_ok):
                            break
                    if not (conj_ok and trace_ok):
                        break
                if not (conj_ok and trace_ok):
                    break
            if not (conj_ok and trace_ok):
                break
        if not (conj_ok and trace_ok):
            break

    ok = conj_ok and trace_ok
    results = {
        "theorem": "q8_plaquette_wilson_loop_gauge_invariance_protocol_v1",
        "ok": ok,
        "checked_cases": checked,
        "gauge_assignments": 8**4,
        "edge_subset_size": len(edge_subset),
        "edge_cases": len(edge_subset) ** 4,
        "conjugation_identity_ok": conj_ok,
        "trace_invariant_ok": trace_ok,
        "edge_subset": ["I", "qi", "qj", "qk"],
        "elem_order": ["I", "-I", "qi", "-qi", "qj", "-qj", "qk", "-qk"],
        "observable": "tr2(plaquette(U')) = tr2(plaquette(U))",
    }

    OUT.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Saved Q8 plaquette Wilson-loop gauge-invariance summary: {OUT}")
    print(f"  ok={ok} (checked {checked} cases)")


if __name__ == "__main__":
    main()

