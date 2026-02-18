#!/usr/bin/env python3
"""
Twin-prime occupancy boundary protocol (finite, deterministic).

Purpose:
- keep architecture-vs-occupancy split explicit,
- provide finite witness data for the canonical 1001 bundle (7*11*13),
- avoid any occupancy-by-primes overclaim.
"""

from __future__ import annotations

import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent
OUT = ROOT / "twinprime_occupancy_boundary_results.json"

MODULUS = 1001
CAPACITY = 495  # (7-2)*(11-2)*(13-2) = 5*9*11


def allowed_residue(n: int) -> bool:
    return (
        (n % 7) not in (0, 5)
        and (n % 11) not in (0, 9)
        and (n % 13) not in (0, 11)
    )


def occupied_classes(values: list[int], modulus: int) -> int:
    return len({v % modulus for v in values})


def main() -> None:
    universe = list(range(MODULUS))
    allowed = [n for n in universe if allowed_residue(n)]
    forbidden = [n for n in universe if not allowed_residue(n)]

    # Deterministic admissible subset witness:
    # exactly 60 admissible residues in [0, 122].
    subset60 = [n for n in range(123) if allowed_residue(n)]

    summary = {
        "modulus": MODULUS,
        "capacity": CAPACITY,
        "allowed_count_scan_0_1000": len(allowed),
        "forbidden_count_scan_0_1000": len(forbidden),
        "partition_ok": len(allowed) + len(forbidden) == MODULUS,
        "allowed_first10": allowed[:10],
        "allowed_subset_range_end_exclusive": 123,
        "allowed_subset_count": len(subset60),
        "allowed_subset_all_admissible": all(allowed_residue(n) for n in subset60),
        "allowed_subset_occupied_classes": occupied_classes(subset60, MODULUS),
        "allowed_subset_within_capacity": occupied_classes(subset60, MODULUS) <= CAPACITY,
        "full_allowed_occupied_classes": occupied_classes(allowed, MODULUS),
        "full_allowed_hits_capacity": occupied_classes(allowed, MODULUS) == CAPACITY,
        "forbidden_occupied_classes": occupied_classes(forbidden, MODULUS),
        "forbidden_exceeds_capacity_without_guard": occupied_classes(forbidden, MODULUS) > CAPACITY,
        "forbidden_all_admissible": all(allowed_residue(n) for n in forbidden),
    }

    OUT.write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print(f"Saved deterministic twin-prime occupancy-boundary summary: {OUT}")
    print(f"  allowed={summary['allowed_count_scan_0_1000']}, forbidden={summary['forbidden_count_scan_0_1000']}")
    print(
        "  subset_occ="
        f"{summary['allowed_subset_occupied_classes']}, "
        f"full_allowed_occ={summary['full_allowed_occupied_classes']}, "
        f"forbidden_occ={summary['forbidden_occupied_classes']}"
    )


if __name__ == "__main__":
    main()
