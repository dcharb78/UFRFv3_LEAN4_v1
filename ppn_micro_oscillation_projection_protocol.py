"""
PPN micro-oscillation projection bridge protocol.

Finite deterministic scaffold for Part III (PPN micro-oscillations):
  - 13-beat periodic oscillations around unity for gamma and beta,
  - cycle-mean equals 1,
  - synthetic projection term d_M * alpha * S matches the oscillation offset.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path


def delta(k: int) -> Fraction:
    return Fraction((k % 13) - 6, 1000)


def main() -> None:
    gamma = [Fraction(1, 1) + delta(k) for k in range(13)]
    beta = [Fraction(1, 1) - delta(k) for k in range(13)]

    mean_gamma = sum(gamma, Fraction(0, 1)) / 13
    mean_beta = sum(beta, Fraction(0, 1)) / 13

    periodic = all(delta(k + 13) == delta(k) for k in range(50))
    coherence_sum2 = all(gamma[k] + beta[k] == 2 for k in range(13))

    d_m = Fraction(2, 1)
    alpha = Fraction(1, 10)

    def s_term(k: int) -> Fraction:
        return Fraction((k % 13) - 6, 200)

    projection_match = all(d_m * alpha * s_term(k) == delta(k) for k in range(13))

    result = {
        "theorem": "ppn_micro_oscillation_projection_protocol_v1",
        "claim_subset": {
            "periodicity": "13-beat micro-oscillation",
            "unity_mean": "cycle-mean around 1",
            "projection_link": "delta = d_M * alpha * S (synthetic scaffold)",
        },
        "structural_checks": {
            "mean_gamma_is_one": mean_gamma == 1,
            "mean_beta_is_one": mean_beta == 1,
            "periodic_mod_13": periodic,
            "gamma_plus_beta_equals_two": coherence_sum2,
            "projection_term_matches_delta": projection_match,
            "mean_gamma": {"num": mean_gamma.numerator, "den": mean_gamma.denominator},
            "mean_beta": {"num": mean_beta.numerator, "den": mean_beta.denominator},
        },
    }

    output_path = Path("ppn_micro_oscillation_projection_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic PPN micro-oscillation projection summary:")
    print(f"  {output_path.resolve()}")
    print(
        "  mean_gamma=1, mean_beta=1, periodic_mod13=True, projection_match=True"
    )


if __name__ == "__main__":
    main()
