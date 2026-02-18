"""
Mod-1001 inevitability scaffold protocol.

Finite deterministic bridge for the "why mod-1001?" question:
  - decimal cube-flip modulus condition: m | (10^3 + 1),
  - 13-axis inclusion condition: 13 | m,
  - full concurrent odd-axis closure: 7 | m, 11 | m, 13 | m.

Under these constraints in base-10, m = 1001 is the unique full closure modulus.
"""

from __future__ import annotations

import json
from pathlib import Path


TARGET = 10**3 + 1  # 1001


def divisors(n: int) -> list[int]:
    return [d for d in range(1, n + 1) if n % d == 0]


def main() -> None:
    divs = divisors(TARGET)
    with13 = [d for d in divs if d % 13 == 0]
    full_axes = [d for d in divs if d % 7 == 0 and d % 11 == 0 and d % 13 == 0]

    result = {
        "theorem": "mod1001_inevitability_protocol_v1",
        "claim_subset": {
            "decimal_constraint": "m divides 10^3 + 1",
            "axis_constraint": "13 divides m",
            "full_closure_constraint": "7,11,13 all divide m",
        },
        "structural_checks": {
            "target_is_1001": TARGET == 1001,
            "target_factorization": (TARGET == 7 * 11 * 13),
            "divisors_of_1001": divs,
            "divisors_with_13_axis": with13,
            "full_axis_closure_candidates": full_axes,
            "max_with_13_axis_is_1001": max(with13) == 1001,
            "unique_full_axis_closure_modulus": full_axes == [1001],
        },
    }

    output_path = Path("mod1001_inevitability_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic mod1001 inevitability summary:")
    print(f"  {output_path.resolve()}")
    print(f"  with13={with13}, full_axes={full_axes}")


if __name__ == "__main__":
    main()
