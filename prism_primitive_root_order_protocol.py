#!/usr/bin/env python3
"""
PRISM base-13 primitive-root/order protocol (finite, deterministic).

Purpose:
- certify finite multiplicative-order facts for the witness `2` on `13^k`,
- certify nested projection compatibility under quotient map
  `Z/(13^k) -> Z/(13^(k-1))` on a fixed finite exponent set,
- keep scope bounded (no unbounded theorem claims).
"""

from __future__ import annotations

import json
from math import gcd
from pathlib import Path
from typing import Dict, List


ROOT = Path(__file__).resolve().parent
OUT = ROOT / "prism_primitive_root_order_results.json"

BASE = 13
WITNESS = 2
MAX_K = 4


def phi_prime_power(p: int, k: int) -> int:
    return (p - 1) * (p ** (k - 1))


def divisors(n: int) -> List[int]:
    out: List[int] = []
    i = 1
    while i * i <= n:
        if n % i == 0:
            out.append(i)
            if i * i != n:
                out.append(n // i)
        i += 1
    return sorted(out)


def proper_divisors(n: int) -> List[int]:
    return [d for d in divisors(n) if d < n]


def multiplicative_order(a: int, m: int) -> int:
    if gcd(a, m) != 1:
        raise ValueError(f"a={a} is not a unit modulo {m}")

    x = a % m
    r = 1
    while x != 1:
        x = (x * a) % m
        r += 1
        if r > m:
            raise RuntimeError(f"order search exceeded modulus m={m}")
    return r


def level_summary(k: int) -> Dict[str, object]:
    m = BASE ** k
    phi = phi_prime_power(BASE, k)
    ord_w = multiplicative_order(WITNESS, m)

    proper = proper_divisors(phi)
    minimality_hits = [d for d in proper if pow(WITNESS, d, m) == 1]

    level: Dict[str, object] = {
        "k": k,
        "modulus": m,
        "phi_modulus": phi,
        "order_witness": ord_w,
        "order_equals_phi": ord_w == phi,
        "proper_divisor_count": len(proper),
        "order_minimality_holds": len(minimality_hits) == 0,
        "order_minimality_counterexamples": minimality_hits,
    }

    if k >= 2:
        m_prev = BASE ** (k - 1)
        phi_prev = phi_prime_power(BASE, k - 1)
        exponents_raw = [0, 1, 2, 3, 5, 7, 11, 12, 13, 24, phi_prev, phi]
        exponents = list(dict.fromkeys(exponents_raw))
        checks = [
            ((pow(WITNESS, e, m) % m_prev) == pow(WITNESS, e, m_prev))
            for e in exponents
        ]
        level["projection_exponents"] = exponents
        level["projection_compatibility"] = all(checks)
        level["projection_check_count"] = len(exponents)

    return level


def main() -> None:
    levels = [level_summary(k) for k in range(1, MAX_K + 1)]

    moduli = [int(l["modulus"]) for l in levels]
    phi_values = [int(l["phi_modulus"]) for l in levels]
    orders = [int(l["order_witness"]) for l in levels]

    order_equals_phi_all = all(bool(l["order_equals_phi"]) for l in levels)
    order_minimality_all = all(bool(l["order_minimality_holds"]) for l in levels)
    projection_compatibility_all = all(
        bool(l.get("projection_compatibility", True)) for l in levels
    )

    scale_by_13_from_level2 = all(
        orders[i] == BASE * orders[i - 1] for i in range(1, len(orders))
    )

    summary = {
        "theorem": "prism_primitive_root_order_protocol_v1",
        "params": {
            "base": BASE,
            "witness": WITNESS,
            "max_k": MAX_K,
        },
        "levels": levels,
        "global": {
            "moduli": moduli,
            "phi_moduli": phi_values,
            "order_witness_values": orders,
            "order_equals_phi_all": order_equals_phi_all,
            "order_minimality_all": order_minimality_all,
            "projection_compatibility_all": projection_compatibility_all,
            "scale_by_13_from_level2": scale_by_13_from_level2,
            "primitive_root_witness_all": order_equals_phi_all and order_minimality_all,
        },
    }

    OUT.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    print("Saved PRISM primitive-root/order summary:", OUT)
    print("  moduli:", moduli)
    print("  phi_moduli:", phi_values)
    print("  order_witness_values:", orders)
    print("  order_equals_phi_all:", order_equals_phi_all)
    print("  order_minimality_all:", order_minimality_all)
    print("  projection_compatibility_all:", projection_compatibility_all)
    print("  scale_by_13_from_level2:", scale_by_13_from_level2)


if __name__ == "__main__":
    main()
