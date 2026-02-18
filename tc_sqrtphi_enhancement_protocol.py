"""
Tc sqrt(phi)-enhancement protocol (deterministic arithmetic bridge).

Bridges Predictions §2.2 from:
  UFRF3.1/08-ufrf-predictions-tests.md

Claim subset encoded here:
  Tc_optimal = Tc_base * sqrt(phi) ≈ Tc_base * 1.272

Discrete protocol uses the exact rational proxy:
  1.272 = 159/125
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

ENHANCEMENT = Fraction(159, 125)  # 1.272 exactly as ratio
BASELINE_TCS = [50, 100, 125, 200, 250, 300]


def main() -> None:
    enhanced = [Fraction(b, 1) * ENHANCEMENT for b in BASELINE_TCS]

    rows = [
        {
            "tc_base": b,
            "tc_opt_num": t.numerator,
            "tc_opt_den": t.denominator,
            "tc_opt_decimal": float(t),
        }
        for b, t in zip(BASELINE_TCS, enhanced)
    ]

    result = {
        "theorem": "tc_sqrtphi_enhancement_protocol_v1",
        "claim_subset": {
            "formula": "Tc_optimal = Tc_base * 1.272",
            "enhancement_ratio_num": ENHANCEMENT.numerator,
            "enhancement_ratio_den": ENHANCEMENT.denominator,
        },
        "structural_checks": {
            "count": len(BASELINE_TCS),
            "all_scaled_by_same_ratio": all(
                enhanced[i] * BASELINE_TCS[0] == enhanced[0] * BASELINE_TCS[i]
                for i in range(1, len(BASELINE_TCS))
            ),
            "all_enhanced_above_base": all(e > Fraction(b, 1) for b, e in zip(BASELINE_TCS, enhanced)),
            "anchor_125_to_159": Fraction(125, 1) * ENHANCEMENT == Fraction(159, 1),
            "anchor_250_to_318": Fraction(250, 1) * ENHANCEMENT == Fraction(318, 1),
        },
        "table": rows,
    }

    output_path = Path("tc_sqrtphi_enhancement_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic Tc sqrt(phi)-enhancement summary:")
    print(f"  {output_path.resolve()}")
    print(
        f"  ratio={ENHANCEMENT.numerator}/{ENHANCEMENT.denominator}, anchor 125->{int(125*ENHANCEMENT)}"
    )


if __name__ == "__main__":
    main()
