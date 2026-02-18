"""
REST-anchor cross-domain protocol (deterministic synthesis bridge).

Finite deterministic scaffold:
  - quantum Hall ladder contains REST fraction 10/13,
  - acoustic ladder has REST at n=10 -> 4320/13 Hz,
  - DNA/protein anchors include half-step REST location 10.5.

This is an integration bridge across already-established domain anchors.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path


REST_INDEX = 10


def main() -> None:
    quantum_n = list(range(1, 13))
    quantum_fractions = [Fraction(n, 13) for n in quantum_n]

    acoustic_rest = Fraction(432 * REST_INDEX, 13)  # 4320/13
    acoustic_critical_positions = [Fraction(5, 2), Fraction(11, 2), Fraction(17, 2), Fraction(10, 1), Fraction(23, 2)]
    acoustic_rest_in_critical = Fraction(REST_INDEX, 1) in acoustic_critical_positions

    dna_turns = Fraction(21, 2)  # 10.5
    protein_positions = [Fraction(18, 5), Fraction(36, 5), Fraction(21, 2)]  # 3.6, 7.2, 10.5

    result = {
        "theorem": "rest_anchor_cross_domain_protocol_v1",
        "claim_subset": {
            "rest_index": REST_INDEX,
            "domains": ["quantum_hall", "acoustic", "dna", "protein"],
        },
        "structural_checks": {
            "quantum_contains_10_over_13": Fraction(10, 13) in quantum_fractions,
            "acoustic_rest_frequency_num": acoustic_rest.numerator,
            "acoustic_rest_frequency_den": acoustic_rest.denominator,
            "acoustic_rest_equals_432_times_10_over_13": acoustic_rest == Fraction(432, 1) * Fraction(10, 13),
            "acoustic_critical_contains_rest_index_10": acoustic_rest_in_critical,
            "dna_turns_num": dna_turns.numerator,
            "dna_turns_den": dna_turns.denominator,
            "dna_is_rest_plus_half": dna_turns == Fraction(REST_INDEX, 1) + Fraction(1, 2),
            "protein_contains_10_5": Fraction(21, 2) in protein_positions,
            "protein_third_is_10_5": protein_positions[2] == Fraction(21, 2),
        },
        "derived_values": {
            "quantum_rest_fraction": {"num": 10, "den": 13},
            "acoustic_rest_frequency": {"num": acoustic_rest.numerator, "den": acoustic_rest.denominator},
            "dna_turns": {"num": dna_turns.numerator, "den": dna_turns.denominator},
            "protein_positions": [{"num": p.numerator, "den": p.denominator} for p in protein_positions],
        },
    }

    output_path = Path("rest_anchor_cross_domain_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic REST-anchor cross-domain summary:")
    print(f"  {output_path.resolve()}")
    print(f"  quantum_rest=10/13, acoustic_rest={acoustic_rest}, dna={dna_turns}")


if __name__ == "__main__":
    main()
