"""
Critical-positions alignment protocol (deterministic synthesis bridge).

Finite deterministic scaffold integrating existing position ladders:
  - shell intrinsic half-integer anchors: 2.5, 5.5, 8.5, 11.5, 14.5
  - acoustic critical anchors: 2.5, 5.5, 8.5, 10, 11.5
  - shared set is exactly: 2.5, 5.5, 8.5, 11.5
  - REST distinction: 10 appears in acoustic set, not shell intrinsic set.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path


SHELL = [Fraction(5, 2), Fraction(11, 2), Fraction(17, 2), Fraction(23, 2), Fraction(29, 2)]
ACOUSTIC = [Fraction(5, 2), Fraction(11, 2), Fraction(17, 2), Fraction(10, 1), Fraction(23, 2)]


def as_key(x: Fraction) -> tuple[int, int]:
    return (x.numerator, x.denominator)


def main() -> None:
    shell_set = set(SHELL)
    acoustic_set = set(ACOUSTIC)
    shared = sorted(shell_set.intersection(acoustic_set), key=as_key)

    result = {
        "theorem": "critical_positions_alignment_protocol_v1",
        "claim_subset": {
            "shell_positions": [{"num": x.numerator, "den": x.denominator} for x in SHELL],
            "acoustic_positions": [{"num": x.numerator, "den": x.denominator} for x in ACOUSTIC],
        },
        "structural_checks": {
            "shared_positions": [{"num": x.numerator, "den": x.denominator} for x in shared],
            "shared_exactly_2_5_5_5_8_5_11_5": shared == [Fraction(5, 2), Fraction(11, 2), Fraction(17, 2), Fraction(23, 2)],
            "rest10_in_acoustic": Fraction(10, 1) in acoustic_set,
            "rest10_not_in_shell": Fraction(10, 1) not in shell_set,
            "shell_forward_anchor_14_5_present": Fraction(29, 2) in shell_set,
            "shell_step_3_constant": all(SHELL[i + 1] - SHELL[i] == 3 for i in range(len(SHELL) - 1)),
            "acoustic_contains_rest_and_prepost_halfsteps": (
                Fraction(17, 2) in acoustic_set and Fraction(10, 1) in acoustic_set and Fraction(23, 2) in acoustic_set
            ),
        },
    }

    output_path = Path("critical_positions_alignment_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic critical-positions alignment summary:")
    print(f"  {output_path.resolve()}")
    print(f"  shared={[str(x) for x in shared]}, rest10_in_acoustic={Fraction(10,1) in acoustic_set}")


if __name__ == "__main__":
    main()
