#!/usr/bin/env python3
"""
Protocol: Maxwell duality (⋆) invariants (finite, deterministic).

We work with an EM state (E,B) in natural units and the discrete duality step:
  ⋆(E,B) := (B, -E)

This protocol checks, on a small exhaustive integer window, that:
1) The standard scalar invariants flip sign under ⋆:
     I1 := |E|^2 - |B|^2     => I1(⋆em) = -I1(em)
     I2 := E·B              => I2(⋆em) = -I2(em)
2) The Poynting proxy vector is invariant:
     S := E×B               => S(⋆em) = S(em)
3) Therefore the squared invariants and combined magnitude are invariant:
     I1^2, I2^2, (I1^2 + I2^2) are conserved under ⋆.

This is the algebraic heart of “duality rotation” conservation in the repo's
finite/discrete setting (no PDEs).
"""

from __future__ import annotations

import json
from itertools import product
from pathlib import Path


ROOT = Path(__file__).resolve().parent
OUT = ROOT / "maxwell_duality_invariants_results.json"


def dot(u: tuple[int, int, int], v: tuple[int, int, int]) -> int:
    return u[0] * v[0] + u[1] * v[1] + u[2] * v[2]


def cross(u: tuple[int, int, int], v: tuple[int, int, int]) -> tuple[int, int, int]:
    return (
        u[1] * v[2] - u[2] * v[1],
        u[2] * v[0] - u[0] * v[2],
        u[0] * v[1] - u[1] * v[0],
    )


def norm2(u: tuple[int, int, int]) -> int:
    return dot(u, u)


def dual(e: tuple[int, int, int], b: tuple[int, int, int]) -> tuple[tuple[int, int, int], tuple[int, int, int]]:
    return b, (-e[0], -e[1], -e[2])


def main() -> None:
    # Exhaustive small window to make this deterministic and auditable.
    vals = list(range(-2, 3))
    cases = 0

    i1_flip = True
    i2_flip = True
    s_invariant = True
    i1sq_invariant = True
    i2sq_invariant = True
    sumsq_invariant = True

    witness: dict[str, object] | None = None

    for ex, ey, ez, bx, by, bz in product(vals, repeat=6):
        e = (ex, ey, ez)
        b = (bx, by, bz)
        e2 = norm2(e)
        b2 = norm2(b)
        i1 = e2 - b2
        i2 = dot(e, b)
        s = cross(e, b)

        ed, bd = dual(e, b)
        i1d = norm2(ed) - norm2(bd)
        i2d = dot(ed, bd)
        sd = cross(ed, bd)

        cases += 1

        if i1d != -i1:
            i1_flip = False
        if i2d != -i2:
            i2_flip = False
        if sd != s:
            s_invariant = False
        if i1d * i1d != i1 * i1:
            i1sq_invariant = False
        if i2d * i2d != i2 * i2:
            i2sq_invariant = False
        if (i1d * i1d + i2d * i2d) != (i1 * i1 + i2 * i2):
            sumsq_invariant = False

        if witness is None and (i1 != 0 or i2 != 0 or s != (0, 0, 0)):
            witness = {
                "e": e,
                "b": b,
                "dual_e": ed,
                "dual_b": bd,
                "i1": i1,
                "i2": i2,
                "s": s,
                "i1_dual": i1d,
                "i2_dual": i2d,
                "s_dual": sd,
            }

        if not (i1_flip and i2_flip and s_invariant and i1sq_invariant and i2sq_invariant and sumsq_invariant):
            # Keep going to get full flags (not early-exit), but this should never trigger.
            pass

    ok = i1_flip and i2_flip and s_invariant and i1sq_invariant and i2sq_invariant and sumsq_invariant

    results = {
        "theorem": "maxwell_duality_invariants_protocol_v1",
        "ok": ok,
        "cases": cases,
        "window": {"min": min(vals), "max": max(vals)},
        "i1_sign_flip_all": i1_flip,
        "i2_sign_flip_all": i2_flip,
        "poynting_cross_invariant_all": s_invariant,
        "i1_squared_invariant_all": i1sq_invariant,
        "i2_squared_invariant_all": i2sq_invariant,
        "i1sq_plus_i2sq_invariant_all": sumsq_invariant,
        "witness": witness,
        "duality": "⋆(E,B)=(B,-E)",
        "invariants": {
            "i1": "|E|^2-|B|^2",
            "i2": "E·B",
            "s": "E×B",
        },
    }

    OUT.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Saved deterministic Maxwell duality invariants summary: {OUT}")
    print(f"  ok={ok}, cases={cases}")


if __name__ == "__main__":
    main()

