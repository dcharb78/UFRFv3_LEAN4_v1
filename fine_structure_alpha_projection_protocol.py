#!/usr/bin/env python3
"""
Protocol: Fine-structure projection correction scaffold (ratio-first).

This protocol turns the "fine structure with projection" falsification test
from `UFRF3.1/08-ufrf-predictions-tests.md` into a deterministic compute(JSON) artifact.

Inputs (explicit, finite):
- Intrinsic candidate: α⁻¹_candidate := 4π^3 + π^2 + π
- π is bracketed using mathlib's proven `d20` bounds:
    piLo < π < piHi
- √φ is represented (ratio-first) by the existing repo anchor:
    sqrtPhiApprox := 159/125  (used in Tc sqrt(phi) protocol)
- Correction-factor candidate (document literal):
    c := (9*311)/(312 * 13^2 * sqrtPhiApprox * 137^2)
- Projected candidate:
    α⁻¹_proj := α⁻¹_candidate * (1 - c)
- Fixed measured reference (same literal as in Lean internal-consistency layer):
    α⁻¹_measured := 137.035999084

We report the induced projected interval from the `d20` π-bracket and certify that
the mid-point error is < 1e-8.
"""

from __future__ import annotations

import json
from decimal import Decimal, getcontext
from pathlib import Path


ROOT = Path(__file__).resolve().parent
OUT = ROOT / "fine_structure_alpha_projection_results.json"


def f(x: Decimal) -> Decimal:
    return Decimal(4) * (x**3) + (x**2) + x


def main() -> None:
    getcontext().prec = 90

    # mathlib d20 bounds:
    pi_lo = Decimal("3.14159265358979323846")
    pi_hi = Decimal("3.14159265358979323847")

    alpha_lo = f(pi_lo)
    alpha_hi = f(pi_hi)

    sqrtphi_approx = Decimal(159) / Decimal(125)
    correction = (Decimal(9) * Decimal(311)) / (
        Decimal(312) * (Decimal(13) ** 2) * sqrtphi_approx * (Decimal(137) ** 2)
    )
    k = Decimal(1) - correction

    proj_lo = alpha_lo * k
    proj_hi = alpha_hi * k
    proj_width = proj_hi - proj_lo
    proj_mid = (proj_lo + proj_hi) / 2

    measured_ref = Decimal("137.035999084")
    err_mid = proj_mid - measured_ref
    eps = Decimal("1e-8")

    results = {
        "theorem": "fine_structure_alpha_projection_protocol_v1",
        "inputs": {
            "sqrtphi_approx": "159/125",
            "correction_factor": str(correction),
            "k": str(k),
            "measured_ref": str(measured_ref),
            "eps": str(eps),
        },
        "intrinsic_from_pi_d20": {
            "pi_lo": str(pi_lo),
            "pi_hi": str(pi_hi),
            "alpha_lo": str(alpha_lo),
            "alpha_hi": str(alpha_hi),
        },
        "projected_interval": {
            "proj_lo": str(proj_lo),
            "proj_hi": str(proj_hi),
            "width": str(proj_width),
            "proj_mid": str(proj_mid),
        },
        "comparison": {
            "err_mid": str(err_mid),
            "abs_err_mid": str(abs(err_mid)),
            "mid_within_eps": abs(err_mid) < eps,
            "measured_within_eps_of_interval": (
                (measured_ref - eps) < proj_lo and proj_hi < (measured_ref + eps)
            ),
        },
    }

    OUT.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Saved deterministic fine-structure projection summary: {OUT}")
    print(f"  abs_err_mid={results['comparison']['abs_err_mid']}")
    print(f"  mid_within_eps={results['comparison']['mid_within_eps']}")


if __name__ == "__main__":
    main()

