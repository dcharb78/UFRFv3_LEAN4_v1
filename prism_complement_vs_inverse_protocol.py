#!/usr/bin/env python3
"""
PRISM complement-vs-inverse asymmetry protocol (finite, deterministic).

Purpose:
- compare base-13 digit-local complement with additive inverse modulo 13^k,
- quantify carry-coupling asymmetry on finite level sets,
- keep claims bounded (k in a fixed finite range).
"""

from __future__ import annotations

import json
from collections import defaultdict
from pathlib import Path
from typing import Dict, List, Tuple


ROOT = Path(__file__).resolve().parent
OUT = ROOT / "prism_complement_vs_inverse_results.json"

BASE = 13
LEVELS = [2, 3]


def digits_le(n: int, k: int) -> List[int]:
    """Least-significant-first base-13 digits of length k."""
    out = []
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


def complement_digits(ds: List[int]) -> List[int]:
    return [BASE - 1 - d for d in ds]


def group_coupling_count(outputs: List[Tuple[List[int], List[int]]], pos: int) -> int:
    """
    Count groups where output digit at `pos` changes when only lower digits vary,
    while the input suffix (digits[pos:]) is fixed.
    """
    groups: Dict[Tuple[int, ...], set[int]] = defaultdict(set)
    for inp, out in outputs:
        suffix = tuple(inp[pos:])
        groups[suffix].add(out[pos])
    return sum(1 for vals in groups.values() if len(vals) > 1)


def level_summary(k: int) -> Dict[str, object]:
    m = BASE ** k
    all_rows: List[Tuple[List[int], List[int], List[int]]] = []

    comp_digit_local_ok = True
    for n in range(m):
        inp = digits_le(n, k)
        comp = complement_digits(inp)
        neg = digits_le((-n) % m, k)
        all_rows.append((inp, comp, neg))

        if comp != [BASE - 1 - d for d in inp]:
            comp_digit_local_ok = False

    comp_pos_counts: Dict[str, int] = {}
    neg_pos_counts: Dict[str, int] = {}

    for pos in range(1, k):
        comp_rows = [(inp, comp) for (inp, comp, _) in all_rows]
        neg_rows = [(inp, neg) for (inp, _, neg) in all_rows]
        comp_pos_counts[str(pos)] = group_coupling_count(comp_rows, pos)
        neg_pos_counts[str(pos)] = group_coupling_count(neg_rows, pos)

    complement_has_carry_coupling = any(v > 0 for v in comp_pos_counts.values())
    neg_has_carry_coupling = any(v > 0 for v in neg_pos_counts.values())

    if k == 2:
        n0 = 5 * BASE + 0
        n1 = 5 * BASE + 1
    else:
        # same high digits, vary only least-significant digit
        n0 = 7 * BASE * BASE + 5 * BASE + 0
        n1 = 7 * BASE * BASE + 5 * BASE + 1

    inp0 = digits_le(n0, k)
    inp1 = digits_le(n1, k)
    comp0 = complement_digits(inp0)
    comp1 = complement_digits(inp1)
    neg0 = digits_le((-n0) % m, k)
    neg1 = digits_le((-n1) % m, k)

    witness = {
        "n0": n0,
        "n1": n1,
        "inp0": inp0,
        "inp1": inp1,
        "comp0": comp0,
        "comp1": comp1,
        "neg0": neg0,
        "neg1": neg1,
        "comp_high_same": comp0[1:] == comp1[1:],
        "neg_high_same": neg0[1:] == neg1[1:],
    }

    return {
        "k": k,
        "modulus": m,
        "total_states": m,
        "complement_digit_local": comp_digit_local_ok,
        "complement_coupled_groups_by_pos": comp_pos_counts,
        "neg_coupled_groups_by_pos": neg_pos_counts,
        "complement_has_carry_coupling": complement_has_carry_coupling,
        "neg_has_carry_coupling": neg_has_carry_coupling,
        "asymmetry_confirmed": comp_digit_local_ok and (not complement_has_carry_coupling) and neg_has_carry_coupling,
        "witness_same_high_diff_low": witness,
    }


def main() -> None:
    levels = [level_summary(k) for k in LEVELS]

    global_summary = {
        "complement_is_digit_local_all": all(bool(l["complement_digit_local"]) for l in levels),
        "complement_has_no_carry_coupling_all": all(not bool(l["complement_has_carry_coupling"]) for l in levels),
        "neg_is_carry_coupled_all": all(bool(l["neg_has_carry_coupling"]) for l in levels),
        "asymmetry_confirmed_all": all(bool(l["asymmetry_confirmed"]) for l in levels),
    }

    out = {
        "theorem": "prism_complement_vs_inverse_protocol_v1",
        "params": {
            "base": BASE,
            "levels": LEVELS,
        },
        "levels": levels,
        "global": global_summary,
    }

    OUT.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    print("Saved PRISM complement-vs-inverse summary:", OUT)
    for level in levels:
        print(
            "  k=", level["k"],
            "comp_local=", level["complement_digit_local"],
            "comp_carry=", level["complement_has_carry_coupling"],
            "neg_carry=", level["neg_has_carry_coupling"],
            "asym=", level["asymmetry_confirmed"],
        )
    print("  asymmetry_confirmed_all:", global_summary["asymmetry_confirmed_all"])


if __name__ == "__main__":
    main()
