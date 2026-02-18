#!/usr/bin/env python3
"""
PRISM projection-compatibility protocol (finite, deterministic).

Purpose:
- certify finite projection-compatibility checks under quotient maps
  `Z/(13^k) -> Z/(13^(k-1))`,
- for a bounded operation set on full finite state spaces at levels `k=2..4`,
- without unbounded claims.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Callable, Dict, List, Optional


ROOT = Path(__file__).resolve().parent
OUT = ROOT / "prism_projection_compatibility_results.json"

BASE = 13
LEVELS = [2, 3, 4]


def digits_le(n: int, k: int) -> List[int]:
    out: List[int] = []
    x = n
    for _ in range(k):
        out.append(x % BASE)
        x //= BASE
    return out


def from_digits_le(ds: List[int]) -> int:
    x = 0
    p = 1
    for d in ds:
        x += d * p
        p *= BASE
    return x


def op_succ(n: int, _k: int, m: int) -> int:
    return (n + 1) % m


def op_pred(n: int, _k: int, m: int) -> int:
    return (n - 1) % m


def op_neg(n: int, _k: int, m: int) -> int:
    return (-n) % m


def op_comp(n: int, k: int, _m: int) -> int:
    ds = digits_le(n, k)
    return from_digits_le([BASE - 1 - d for d in ds])


OPS: Dict[str, Callable[[int, int, int], int]] = {
    "succ": op_succ,
    "pred": op_pred,
    "neg": op_neg,
    "comp": op_comp,
}


def check_level(k: int) -> Dict[str, object]:
    m = BASE ** k
    m_prev = BASE ** (k - 1)
    sample_points = sorted(set([0, 1, BASE - 1, BASE, m_prev - 1, m - 1]))

    per_op: Dict[str, Dict[str, object]] = {}
    for op_name, op in OPS.items():
        fail_count = 0
        first_counterexample: Optional[Dict[str, int]] = None

        for x in range(m):
            lhs = op(x, k, m) % m_prev
            rhs = op(x % m_prev, k - 1, m_prev)
            if lhs != rhs:
                fail_count += 1
                if first_counterexample is None:
                    first_counterexample = {"x": x, "lhs": lhs, "rhs": rhs}

        sample_rows = []
        for x in sample_points:
            lhs = op(x, k, m) % m_prev
            rhs = op(x % m_prev, k - 1, m_prev)
            sample_rows.append({"x": x, "lhs": lhs, "rhs": rhs, "agree": lhs == rhs})

        per_op[op_name] = {
            "compatible": fail_count == 0,
            "fail_count": fail_count,
            "check_count": m,
            "sample_points": sample_points,
            "samples": sample_rows,
            "first_counterexample": first_counterexample,
        }

    return {
        "k": k,
        "modulus": m,
        "projection_modulus": m_prev,
        "total_states": m,
        "operations": per_op,
    }


def main() -> None:
    levels = [check_level(k) for k in LEVELS]

    op_compatible_all: Dict[str, bool] = {}
    op_fail_counts: Dict[str, List[int]] = {}
    for op_name in OPS:
        op_compatible_all[op_name] = all(
            bool(level["operations"][op_name]["compatible"]) for level in levels
        )
        op_fail_counts[op_name] = [
            int(level["operations"][op_name]["fail_count"]) for level in levels
        ]

    all_compatible_all_levels = all(op_compatible_all.values())

    summary = {
        "theorem": "prism_projection_compatibility_protocol_v1",
        "params": {"base": BASE, "levels": LEVELS, "operations": list(OPS.keys())},
        "levels": levels,
        "global": {
            "moduli": [int(level["modulus"]) for level in levels],
            "projection_moduli": [int(level["projection_modulus"]) for level in levels],
            "total_states_by_level": [int(level["total_states"]) for level in levels],
            "op_compatible_all": op_compatible_all,
            "op_fail_counts_by_level": op_fail_counts,
            "all_compatible_all_levels": all_compatible_all_levels,
        },
    }

    OUT.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    print("Saved PRISM projection-compatibility summary:", OUT)
    print("  moduli:", summary["global"]["moduli"])
    print("  projection_moduli:", summary["global"]["projection_moduli"])
    print("  op_compatible_all:", op_compatible_all)
    print("  all_compatible_all_levels:", all_compatible_all_levels)


if __name__ == "__main__":
    main()
