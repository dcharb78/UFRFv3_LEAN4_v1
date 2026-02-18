#!/usr/bin/env python3
"""
j(q) q-expansion from classical modular q-series (finite, exact, deterministic).

Goal:
  Provide an *independent* computational derivation of the first few coefficients of the
  classical j-invariant (as a formal q-series) from:

    Δ(q) := q * ∏_{n≥1} (1 - q^n)^24
    E4(q) := 1 + 240 * Σ_{n≥1} σ₃(n) q^n
    j(q)  := E4(q)^3 / Δ(q)

This is an evidence-lane protocol:
  - It does NOT prove modularity in Lean.
  - It computes a finite truncation *exactly* (integer arithmetic, no floats) and writes JSON.

Bridge check to UFRF Moonshine anchor:
  - Compute Monster triple via Frobenius emergence: f(a,b)=ab-a-b from pairs (5,13),(7,11),(7,13).
  - Verify that the computed j coefficient c₁ equals product(triple)+1.
"""

from __future__ import annotations

from dataclasses import dataclass
import json
import math
from pathlib import Path
from typing import List


def frobenius(a: int, b: int) -> int:
    return a * b - a - b


def sigma_k(n: int, k: int) -> int:
    """Sum of k-th powers of divisors of n (k is a nonnegative int)."""
    s = 0
    r = int(math.isqrt(n))
    for d in range(1, r + 1):
        if n % d != 0:
            continue
        e = n // d
        s += d**k
        if e != d:
            s += e**k
    return s


def series_mul(a: List[int], b: List[int], deg: int) -> List[int]:
    """Multiply power series a*b mod q^(deg+1). a[i]=coeff q^i."""
    out = [0] * (deg + 1)
    for i, ai in enumerate(a):
        if ai == 0:
            continue
        if i > deg:
            break
        jmax = deg - i
        for j in range(0, min(len(b) - 1, jmax) + 1):
            bj = b[j]
            if bj:
                out[i + j] += ai * bj
    return out


def series_pow(a: List[int], exp: int, deg: int) -> List[int]:
    """Power a^exp mod q^(deg+1). exp >= 0."""
    assert exp >= 0
    # fast pow, but deg is tiny; keep it simple.
    out = [0] * (deg + 1)
    out[0] = 1
    base = a[:]
    e = exp
    while e > 0:
        if e & 1:
            out = series_mul(out, base, deg)
        e >>= 1
        if e:
            base = series_mul(base, base, deg)
    return out


def series_inv_unit(p: List[int], deg: int) -> List[int]:
    """
    Invert a unit power series p with p[0]=1, returning q such that p*q = 1 mod q^(deg+1).
    """
    assert len(p) >= deg + 1
    assert p[0] == 1
    q = [0] * (deg + 1)
    q[0] = 1
    for n in range(1, deg + 1):
        acc = 0
        for k in range(1, n + 1):
            acc += p[k] * q[n - k]
        q[n] = -acc  # since p[0]=1
    return q


def delta_unit_series(deg: int) -> List[int]:
    """
    Compute P(q) = ∏_{n=1..deg} (1 - q^n)^24 mod q^(deg+1), as coefficients [P0..Pdeg].

    This is the unit part of the discriminant:
      Δ(q) = q * P(q)
    """
    p = [0] * (deg + 1)
    p[0] = 1
    for n in range(1, deg + 1):
        # factor(q) = (1 - q^n)^24 = Σ_{k=0..24} C(24,k) (-1)^k q^(k*n)
        factor = [0] * (deg + 1)
        for k in range(0, 25):
            e = k * n
            if e > deg:
                break
            coeff = math.comb(24, k)
            if k % 2 == 1:
                coeff = -coeff
            factor[e] = coeff
        p = series_mul(p, factor, deg)
    return p


def eisenstein_E4_series(deg: int) -> List[int]:
    """E4(q) = 1 + 240 Σ_{n>=1} σ3(n) q^n."""
    e4 = [0] * (deg + 1)
    e4[0] = 1
    for n in range(1, deg + 1):
        e4[n] = 240 * sigma_k(n, 3)
    return e4


def j_coeffs_from_delta_e4(max_q_power: int) -> dict:
    """
    Compute j coefficients from q^-1 up to q^max_q_power inclusive.

    Returns:
      - unitP: P coefficients up to deg=max_q_power+1
      - invP: 1/P coefficients up to same degree
      - e4, e4^3, H=e4^3*invP
      - j_coeffs: dict with keys "-1","0",... as strings
    """
    # Need degree D = max_q_power+1 for H since j(q)=q^-1 * H(q).
    D = max_q_power + 1

    P = delta_unit_series(D)
    invP = series_inv_unit(P, D)

    E4 = eisenstein_E4_series(D)
    E4_3 = series_pow(E4, 3, D)

    H = series_mul(E4_3, invP, D)

    j_coeffs: dict[str, int] = {}
    j_coeffs["-1"] = H[0]
    for k in range(0, max_q_power + 1):
        j_coeffs[str(k)] = H[k + 1]

    return {
        "max_q_power": max_q_power,
        "deg_internal": D,
        "P_unit_delta": P,
        "invP_unit_delta": invP,
        "E4": E4,
        "E4_cubed": E4_3,
        "H": H,
        "j_coeffs": j_coeffs,
    }


@dataclass(frozen=True)
class ProtocolParams:
    max_q_power: int


def run(params: ProtocolParams) -> dict:
    jdata = j_coeffs_from_delta_e4(params.max_q_power)
    j = jdata["j_coeffs"]

    # UFRF emergence side (Frobenius anchors)
    monster = [
        frobenius(5, 13),
        frobenius(7, 11),
        frobenius(7, 13),
    ]
    product = monster[0] * monster[1] * monster[2]
    product_plus_one = product + 1

    # Extract c1 if present (q^1 coefficient).
    c1 = j.get("1")
    return {
        "theorem": "j_qexp_from_delta_e4_protocol_v1",
        "params": {"max_q_power": params.max_q_power},
        "derived": {
            "monster_triple": monster,
            "monster_product": product,
            "monster_product_plus_one": product_plus_one,
        },
        "j_qexp": {
            "max_q_power": jdata["max_q_power"],
            "deg_internal": jdata["deg_internal"],
            "j_coeffs": j,
        },
        "checks": {
            "monster_triple_eq_47_59_71": monster == [47, 59, 71],
            "j_has_qneg1_term": j.get("-1") == 1,
            "j_has_q0_term": ("0" in j),
            "j_has_q1_term": ("1" in j),
            "c1_equals_monster_product_plus_one": (c1 == product_plus_one) if c1 is not None else False,
            # Optional sanity checks (known classical values; still computed above, not used for computation).
            "c0_is_744": (j.get("0") == 744),
            "c1_is_196884": (j.get("1") == 196884),
            "c2_is_21493760": (j.get("2") == 21493760),
        },
    }


def main() -> None:
    params = ProtocolParams(max_q_power=5)
    out = run(params)

    out_path = Path(__file__).resolve().with_name("j_qexp_from_delta_e4_results.json")
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    c1 = out["j_qexp"]["j_coeffs"].get("1")
    print("Saved deterministic j(q) q-expansion derivation summary:")
    print(f"  {out_path.resolve()}")
    print(f"  c1(q^1)={c1}, monster_product_plus_one={out['derived']['monster_product_plus_one']}")


if __name__ == "__main__":
    main()

