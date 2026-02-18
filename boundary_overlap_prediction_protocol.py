"""
Boundary overlap prediction protocol (deterministic discrete model).

This script computes a finite, reproducible summary for Prediction §0 in:
  UFRF3.1/08-ufrf-predictions-tests.md

Model used (matches Lean seam core):
  cycle = 14
  rest = 10
  birth(g) = g * 10
  seamTick(g, r) = birth(g) + rest + r
  state(g, t) = (t - birth(g)) % cycle

Boundary window offsets are r in {1,2,3}.
Control window offsets are r in {4,5,6,7,8,9,10,11,12,13}.
"""

from __future__ import annotations

import json
from pathlib import Path

CYCLE = 14
REST = 10
MAX_GENERATION = 10  # g = 0..9
BOUNDARY_OFFSETS = [1, 2, 3]
CONTROL_OFFSETS = [4, 5, 6, 7, 8, 9, 10, 11, 12, 13]


def birth(g: int) -> int:
    return g * REST


def seam_tick(g: int, r: int) -> int:
    return birth(g) + REST + r


def state(g: int, t: int) -> int:
    return (t - birth(g)) % CYCLE


def is_parent_complete(s: int) -> bool:
    return s in (11, 12, 13)


def is_child_seed(s: int) -> bool:
    return s in (1, 2, 3)


def event(g: int, r: int) -> dict[str, int | bool]:
    t = seam_tick(g, r)
    parent_state = state(g, t)
    child_state = state(g + 1, t)
    return {
        "generation": g,
        "offset": r,
        "tick": t,
        "parent_state": parent_state,
        "child_state": child_state,
        "parent_complete": is_parent_complete(parent_state),
        "child_seed": is_child_seed(child_state),
        "overlap": is_parent_complete(parent_state) and is_child_seed(child_state),
        "exact_pair": (parent_state == REST + r) and (child_state == r),
    }


def summarize(offsets: list[int]) -> dict[str, object]:
    events = [event(g, r) for g in range(MAX_GENERATION) for r in offsets]
    n = len(events)
    parent_complete_count = sum(1 for e in events if e["parent_complete"])
    child_seed_count = sum(1 for e in events if e["child_seed"])
    overlap_count = sum(1 for e in events if e["overlap"])
    exact_pair_count = sum(1 for e in events if e["exact_pair"])
    return {
        "events": n,
        "parent_complete_count": parent_complete_count,
        "child_seed_count": child_seed_count,
        "overlap_count": overlap_count,
        "exact_pair_count": exact_pair_count,
        "overlap_rate": (overlap_count / n) if n else 0.0,
        "first_five": events[:5],
    }


def main() -> None:
    boundary_summary = summarize(BOUNDARY_OFFSETS)
    control_summary = summarize(CONTROL_OFFSETS)

    result = {
        "theorem": "boundary_overlap_prediction_protocol_v1",
        "model": {
            "cycle": CYCLE,
            "rest": REST,
            "max_generation": MAX_GENERATION,
            "boundary_offsets": BOUNDARY_OFFSETS,
            "control_offsets": CONTROL_OFFSETS,
        },
        "boundary_window": boundary_summary,
        "control_window": control_summary,
    }

    output_path = Path("boundary_overlap_prediction_results.json")
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    print("Saved deterministic boundary-overlap summary:")
    print(f"  {output_path.resolve()}")
    print(
        f"  Boundary overlap: {boundary_summary['overlap_count']}/{boundary_summary['events']}"
    )
    print(f"  Control overlap: {control_summary['overlap_count']}/{control_summary['events']}")


if __name__ == "__main__":
    main()
