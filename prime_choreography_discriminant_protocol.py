#!/usr/bin/env python3
"""
Prime-choreography discriminant protocol (finite, deterministic).

Purpose:
- reuse the fixed waveform/period construction from
  `prime_choreography_autocorr_protocol.py`,
- compute compact discriminant metrics that separate the known degenerate
  uniform control from multi-period superpositions,
- keep claims finite and auditable.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path
from typing import Dict, List

from prime_choreography_autocorr_protocol import BASE, ProtocolParams, run


ROOT = Path(__file__).resolve().parent
OUT = ROOT / "prime_choreography_discriminant_results.json"


def frac_to_json(x: Fraction) -> Dict[str, int]:
    return {"num": x.numerator, "den": x.denominator}


def strictly_ascending(xs: List[int]) -> bool:
    return all(xs[i] < xs[i + 1] for i in range(len(xs) - 1))


def summarize_group(name: str, group: Dict[str, object]) -> Dict[str, object]:
    lags = [int(v) for v in group["mult13_lags_sorted"]]
    inv = int(group["mult13_inversion_count"])
    n = len(lags)
    max_inv = n * (n - 1) // 2
    asc = strictly_ascending(lags)
    return {
        "name": name,
        "count_mult13_lags": n,
        "max_inversion_count": max_inv,
        "inversion_count": inv,
        "inversion_density": frac_to_json(Fraction(inv, max_inv)),
        "strictly_ascending_mult13": asc,
        "first_mult13_lag": lags[0],
        "last_mult13_lag": lags[-1],
        "lags": lags,
    }


def main() -> None:
    params = ProtocolParams(
        primes_ufrf=[1, 3, 5, 7, 11],
        primes_conventional=[2, 3, 5, 7, 11],
        primes_uniform=[1, 1, 1, 1, 1],
        primes_nonprime_swap=[1, 3, 5, 7, 9],
        n_samples=BASE * 11 * 5,
        max_lag=BASE * 11,
        top_k=15,
        sqrt_phi_approx=Fraction(159, 125),
    )

    out = run(params)
    results = out["results"]

    ufrf = summarize_group("ufrf", results["ufrf"])
    conventional = summarize_group("conventional", results["conventional"])
    uniform = summarize_group("uniform", results["uniform"])
    nonprime = summarize_group("nonprime_swap", results["nonprime_swap"])

    nonuniform = [ufrf, conventional, nonprime]

    summary = {
        "theorem": "prime_choreography_discriminant_protocol_v1",
        "params": {
            "base": BASE,
            "n_samples": params.n_samples,
            "max_lag": params.max_lag,
            "top_k": params.top_k,
            "primes_ufrf": params.primes_ufrf,
            "primes_conventional": params.primes_conventional,
            "primes_uniform": params.primes_uniform,
            "primes_nonprime_swap": params.primes_nonprime_swap,
        },
        "groups": {
            "ufrf": ufrf,
            "conventional": conventional,
            "uniform": uniform,
            "nonprime_swap": nonprime,
        },
        "discriminant": {
            "uniform_is_degenerate": uniform["strictly_ascending_mult13"] and uniform["inversion_count"] == 0,
            "all_nonuniform_are_scrambled": all(
                (not g["strictly_ascending_mult13"]) and g["inversion_count"] > 0 for g in nonuniform
            ),
            "ufrf_uniform_top13_alias": ufrf["first_mult13_lag"] == uniform["first_mult13_lag"] == 13,
            "ufrf_uniform_inversion_gap": int(ufrf["inversion_count"]) - int(uniform["inversion_count"]),
            "conventional_uniform_inversion_gap": int(conventional["inversion_count"]) - int(uniform["inversion_count"]),
            "nonprime_uniform_inversion_gap": int(nonprime["inversion_count"]) - int(uniform["inversion_count"]),
            # Honest scope: this metric family is a degeneracy gate, not yet a UFRF-vs-conventional separator.
            "ufrf_conventional_equal_inversion": int(ufrf["inversion_count"]) == int(conventional["inversion_count"]),
        },
    }

    OUT.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    print("Saved prime choreography discriminant summary:", OUT)
    print("  ufrf inv / asc / first:", ufrf["inversion_count"], ufrf["strictly_ascending_mult13"], ufrf["first_mult13_lag"])
    print(
        "  conventional inv / asc / first:",
        conventional["inversion_count"],
        conventional["strictly_ascending_mult13"],
        conventional["first_mult13_lag"],
    )
    print("  uniform inv / asc / first:", uniform["inversion_count"], uniform["strictly_ascending_mult13"], uniform["first_mult13_lag"])
    print(
        "  nonprime inv / asc / first:",
        nonprime["inversion_count"],
        nonprime["strictly_ascending_mult13"],
        nonprime["first_mult13_lag"],
    )
    print("  uniform_is_degenerate:", summary["discriminant"]["uniform_is_degenerate"])
    print("  all_nonuniform_are_scrambled:", summary["discriminant"]["all_nonuniform_are_scrambled"])
    print("  ufrf_uniform_top13_alias:", summary["discriminant"]["ufrf_uniform_top13_alias"])
    print("  ufrf_uniform_inversion_gap:", summary["discriminant"]["ufrf_uniform_inversion_gap"])


if __name__ == "__main__":
    main()

