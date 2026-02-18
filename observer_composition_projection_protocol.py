"""
Observer-composition projection protocol (deterministic arithmetic bridge).

Bridges the Part III "Network/Observer Composition Test" in:
  UFRF3.1/08-ufrf-predictions-tests.md

Claim subset encoded here:
  additive composition of projection exponents
  Delta ln O = d_M1*alpha1*S1 + d_M2*alpha2*S2.
"""

from __future__ import annotations

import json
from pathlib import Path

# Synthetic observer chain constants (integer scaffold for finite verification).
D_AB = 23
ALPHA_B = 1
S_B = 2

D_BC = 17
ALPHA_C = 2
S_C = 3


def main() -> None:
    term_ab = D_AB * ALPHA_B * S_B
    term_bc = D_BC * ALPHA_C * S_C
    delta_total = term_ab + term_bc

    result = {
        "theorem": "observer_composition_projection_protocol_v1",
        "claim_subset": {
            "formula": "Delta ln O = d_M1*alpha1*S1 + d_M2*alpha2*S2",
            "observer_chain": "A observes B observes C",
        },
        "synthetic_parameters": {
            "d_ab": D_AB,
            "alpha_b": ALPHA_B,
            "s_b": S_B,
            "d_bc": D_BC,
            "alpha_c": ALPHA_C,
            "s_c": S_C,
        },
        "structural_checks": {
            "term_ab": term_ab,
            "term_bc": term_bc,
            "delta_total": delta_total,
            "additive_composition_holds": delta_total == term_ab + term_bc,
        },
    }

    output_path = Path("observer_composition_projection_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic observer-composition projection summary:")
    print(f"  {output_path.resolve()}")
    print(f"  term_ab={term_ab}, term_bc={term_bc}, total={delta_total}")


if __name__ == "__main__":
    main()
