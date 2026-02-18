"""
Mod-1001 order decomposition bridge protocol.

Finite deterministic scaffold:
  - per-axis return periods for base-10 on {7,11,13},
  - simultaneous axis return first occurs at 6,
  - combined modulus return: 10^6 ≡ 1 (mod 1001),
  - no smaller positive exponent returns mod 1001.
"""

from __future__ import annotations

import json
import math
from pathlib import Path


AXES = [7, 11, 13]
M = 1001


def first_return(modulus: int, max_k: int = 200) -> int:
    for k in range(1, max_k + 1):
        if pow(10, k, modulus) == 1:
            return k
    raise RuntimeError(f"no return <= {max_k} for modulus {modulus}")


def all_axes_return(k: int) -> bool:
    return all(pow(10, k, m) == 1 for m in AXES)


def main() -> None:
    axis_orders = {m: first_return(m) for m in AXES}
    lcm_order = math.lcm(*(axis_orders[m] for m in AXES))

    first_simul = first_return(M)
    no_small_mod1001 = all(pow(10, k, M) != 1 for k in range(1, first_simul))

    small_axis_fail = all(not all_axes_return(k) for k in range(1, lcm_order))

    result = {
        "theorem": "mod1001_order_decomposition_protocol_v1",
        "claim_subset": {
            "axes": AXES,
            "composite_modulus": M,
            "return_condition": "10^k ≡ 1",
        },
        "structural_checks": {
            "axis_orders": axis_orders,          # expected {7:6, 11:2, 13:6}
            "lcm_axis_order": lcm_order,         # expected 6
            "first_mod1001_return": first_simul, # expected 6
            "mod1001_return_at_6": pow(10, 6, M) == 1,
            "no_smaller_mod1001_return": no_small_mod1001,
            "no_smaller_simultaneous_axis_return": small_axis_fail,
        },
    }

    output_path = Path("mod1001_order_decomposition_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic mod1001 order-decomposition summary:")
    print(f"  {output_path.resolve()}")
    print(
        f"  axis_orders={axis_orders}, lcm={lcm_order}, first_mod1001_return={first_simul}"
    )


if __name__ == "__main__":
    main()
