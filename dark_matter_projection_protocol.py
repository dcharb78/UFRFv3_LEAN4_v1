"""
Dark-matter projection protocol (deterministic arithmetic bridge).

Bridges Predictions §5.1 from:
  UFRF3.1/08-ufrf-predictions-tests.md

Claim subset encoded here:
  - projection scale ratio uses 10^28 and 10^5,
  - exact exponent gap is 23,
  - exact ratio is 10^23,
  - d_M uses equivalent log forms:
      ln(10^28 / 10^5) = ln(10^23) = 23 * ln(10).
"""

from __future__ import annotations

import json
import math
from pathlib import Path

SCALE_OBS_EXP = 28
SCALE_REF_EXP = 5
GAP_EXP = SCALE_OBS_EXP - SCALE_REF_EXP
RATIO_INT = 10**GAP_EXP


def main() -> None:
    ratio_from_scales = (10**SCALE_OBS_EXP) // (10**SCALE_REF_EXP)
    d_m_log_ratio = math.log(RATIO_INT)
    d_m_gap_form = GAP_EXP * math.log(10.0)

    result = {
        "theorem": "dark_matter_projection_protocol_v1",
        "claim_subset": {
            "observer_scale": "10^28",
            "reference_scale": "10^5",
            "projection_distance_symbol": "d_M",
        },
        "structural_checks": {
            "gap_is_23": GAP_EXP == 23,
            "ratio_is_10_pow_23": RATIO_INT == 10**23,
            "ratio_from_scales_matches": ratio_from_scales == RATIO_INT,
            "log_forms_match_eps_1e_12": abs(d_m_log_ratio - d_m_gap_form) < 1e-12,
            "dm_close_to_53_within_0_1": abs(d_m_log_ratio - 53.0) < 0.1,
        },
        "derived_values": {
            "gap_exp": GAP_EXP,
            "ratio_int": RATIO_INT,
            "d_m_log_ratio": d_m_log_ratio,
            "d_m_gap_form": d_m_gap_form,
            "distance_to_53": abs(d_m_log_ratio - 53.0),
        },
    }

    output_path = Path("dark_matter_projection_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic dark-matter projection summary:")
    print(f"  {output_path.resolve()}")
    print(f"  gap={GAP_EXP}, ratio=10^{GAP_EXP}, d_M={d_m_log_ratio:.12f}")


if __name__ == "__main__":
    main()
