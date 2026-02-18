#!/usr/bin/env python3
"""
Protocol: Maxwell invariants vs Poynting (vector identity anchor).

In natural units (c=1), define:
  I1 := |E|^2 - |B|^2
  I2 := E · B
  S  := E × B  (Poynting direction/flux proxy)

Key algebraic identity (Lagrange):
  |E×B|^2 = |E|^2 |B|^2 - (E·B)^2

We certify this deterministically on fixed integer examples (finite anchor),
and record the null-field example where I1=I2=0.
"""

from __future__ import annotations

import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent
OUT = ROOT / "maxwell_poynting_identity_results.json"


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


def main() -> None:
    examples = [
        {"name": "generic", "E": (1, 2, 3), "B": (4, 5, 6)},
        {"name": "null_plane_wave", "E": (1, 0, 0), "B": (0, 1, 0)},
        {"name": "orth_equal", "E": (3, 4, 0), "B": (-4, 3, 0)},
    ]

    checks = []
    for ex in examples:
        E = ex["E"]
        B = ex["B"]
        lhs = norm2(cross(E, B))
        rhs = norm2(E) * norm2(B) - dot(E, B) ** 2
        I1 = norm2(E) - norm2(B)  # c=1
        I2 = dot(E, B)
        checks.append(
            {
                "name": ex["name"],
                "E": E,
                "B": B,
                "lagrange_ok": lhs == rhs,
                "lhs_norm2_cross": lhs,
                "rhs_norm2_formula": rhs,
                "I1": I1,
                "I2": I2,
            }
        )

    ok = all(c["lagrange_ok"] for c in checks)
    null_ok = next(c for c in checks if c["name"] == "null_plane_wave")["I1"] == 0 and next(
        c for c in checks if c["name"] == "null_plane_wave"
    )["I2"] == 0

    results = {
        "theorem": "maxwell_poynting_identity_protocol_v1",
        "ok": ok,
        "null_example_ok": null_ok,
        "checks": checks,
        "identity": "|E×B|^2 = |E|^2|B|^2 - (E·B)^2",
        "invariants": {"I1": "|E|^2-|B|^2 (c=1)", "I2": "E·B"},
    }

    OUT.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Saved deterministic Maxwell Poynting identity summary: {OUT}")
    print(f"  ok={ok}, null_example_ok={null_ok}")


if __name__ == "__main__":
    main()

