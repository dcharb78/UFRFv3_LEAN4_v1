#!/usr/bin/env python3
"""
Protocol: Fine-structure inverse candidate from the UFRF π-polynomial.

Scope (deterministic, finite):
  α⁻¹_candidate := 4π^3 + π^2 + π

We certify, using the same π bounds available in Lean/mathlib (Real.pi_gt_d20 / Real.pi_lt_d20):
  piLo < π < piHi
  => f(piLo) < f(π) < f(piHi), where f(t)=4t^3+t^2+t

and that this implies a stable 9-decimal rounding anchor:
  round_9(α⁻¹_candidate) = 137.036303776

We also report the offset to a fixed measured reference value used elsewhere in the repo.

Important: this is an anchor/example protocol (compute(JSON) <-> Lean finite-summary),
not a first-principles physical derivation in Lean.
"""

from __future__ import annotations

import json
from decimal import Decimal, getcontext
from pathlib import Path


ROOT = Path(__file__).resolve().parent
OUT = ROOT / "fine_structure_alpha_intrinsic_results.json"


def f(x: Decimal) -> Decimal:
    return Decimal(4) * (x**3) + (x**2) + x


def round_half_up(x: Decimal, places: int) -> Decimal:
    q = Decimal(10) ** places
    return (x * q).to_integral_value(rounding="ROUND_HALF_UP") / q


def main() -> None:
    # High precision: we only need enough to keep the d20-derived interval stable.
    getcontext().prec = 90

    # These bounds match mathlib's theorems:
    #   Real.pi_gt_d20 : 3.14159265358979323846 < π
    #   Real.pi_lt_d20 : π < 3.14159265358979323847
    pi_lo = Decimal("3.14159265358979323846")
    pi_hi = Decimal("3.14159265358979323847")

    alpha_lo = f(pi_lo)
    alpha_hi = f(pi_hi)
    width = alpha_hi - alpha_lo
    alpha_mid = (alpha_lo + alpha_hi) / 2

    # 9-decimal rounding anchor used throughout the UFRF docs.
    alpha_round9_anchor = Decimal("137.036303776")
    alpha_mid_round9 = round_half_up(alpha_mid, 9)

    # Half-ulp for 9-decimal rounding (0.5e-9).
    eps_round9 = Decimal(1) / Decimal(2_000_000_000)

    # Fixed measured reference value (same literal as in Lean internal-consistency layer).
    alpha_measured_ref = Decimal("137.035999084")
    offset_mid_minus_measured = alpha_mid - alpha_measured_ref

    results = {
        "theorem": "fine_structure_alpha_intrinsic_protocol_v1",
        "pi_bounds_mathlib_d20": {
            "pi_lo": str(pi_lo),
            "pi_hi": str(pi_hi),
            "width": str(pi_hi - pi_lo),
        },
        "alpha_inv_candidate_bounds_from_pi_d20": {
            "alpha_lo": str(alpha_lo),
            "alpha_hi": str(alpha_hi),
            "width": str(width),
            "alpha_mid": str(alpha_mid),
        },
        "rounding_anchor_9dp": {
            "anchor": str(alpha_round9_anchor),
            "mid_round9": str(alpha_mid_round9),
            "anchor_matches_mid_round9": alpha_mid_round9 == alpha_round9_anchor,
            "eps_round9": str(eps_round9),
            "interval_within_eps_of_anchor": (
                (alpha_round9_anchor - eps_round9) < alpha_lo
                and alpha_hi < (alpha_round9_anchor + eps_round9)
            ),
        },
        "measured_reference": {
            "alpha_measured_ref": str(alpha_measured_ref),
            "offset_mid_minus_measured": str(offset_mid_minus_measured),
        },
    }

    OUT.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Saved deterministic fine-structure intrinsic summary: {OUT}")
    print(f"  mid_round9={results['rounding_anchor_9dp']['mid_round9']}")
    print(
        "  within_eps="
        + str(results["rounding_anchor_9dp"]["interval_within_eps_of_anchor"])
    )


if __name__ == "__main__":
    main()

