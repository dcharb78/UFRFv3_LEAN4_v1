#!/usr/bin/env python3
"""Build prioritized routing table from canonical claims."""

from __future__ import annotations

import csv
from pathlib import Path


def route_action(route: str) -> str:
    if route == "Lean-now":
        return "lean_first"
    if route == "Compute-first":
        return "compute_then_lean_anchor"
    return "spec_and_prerequisites"


def formalizability(route: str, lane: str, conf: float) -> float:
    base = {"Lean-now": 0.95, "Compute-first": 0.65, "Conjecture": 0.25}.get(route, 0.5)
    lane_adj = {"Kernel": 0.10, "Bridge": 0.00, "Evidence": -0.05, "Physics bridge": -0.10, "Anchor": -0.05}.get(lane, 0)
    return max(0.0, min(1.0, base + lane_adj + 0.15 * (conf - 0.5)))


def cross_view(lane: str, member_count: int) -> float:
    lane_base = {"Kernel": 0.70, "Bridge": 0.85, "Evidence": 0.65, "Physics bridge": 0.80, "Anchor": 0.75}.get(lane, 0.6)
    merge_boost = min(0.15, 0.05 * max(0, member_count - 1))
    return max(0.0, min(1.0, lane_base + merge_boost))


def axiom_cost(route: str, lane: str) -> float:
    # Higher means lower axiom burden (better for priority).
    base = {"Lean-now": 0.85, "Compute-first": 0.70, "Conjecture": 0.35}.get(route, 0.6)
    lane_adj = {"Kernel": 0.10, "Bridge": 0.00, "Evidence": 0.00, "Physics bridge": -0.10, "Anchor": -0.05}.get(lane, 0)
    return max(0.0, min(1.0, base + lane_adj))


def novelty(notes: str, member_count: int) -> float:
    if notes == "merged":
        return max(0.3, 0.55 - 0.05 * (member_count - 2))
    return 0.65


def priority(sf: float, sc: float, sa: float, sn: float, conf: float) -> float:
    # Weighted toward formalizability and axiom efficiency.
    return 0.38 * sf + 0.22 * sc + 0.28 * sa + 0.07 * sn + 0.05 * conf


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    in_csv = root / "RequestedInfo/review_state/CANONICAL_CLAIMS.csv"
    out_csv = root / "RequestedInfo/review_state/CLAIM_ROUTING.csv"

    with in_csv.open(newline="", encoding="utf-8") as f:
        rows = list(csv.DictReader(f))

    enriched = []
    for r in rows:
        conf = float(r["confidence_max"])
        mcount = int(r["member_count"])
        sf = formalizability(r["preferred_route"], r["lane"], conf)
        sc = cross_view(r["lane"], mcount)
        sa = axiom_cost(r["preferred_route"], r["lane"])
        sn = novelty(r["notes"], mcount)
        pr = priority(sf, sc, sa, sn, conf)
        enriched.append(
            {
                "canonical_id": r["canonical_id"],
                "preferred_route": r["preferred_route"],
                "lane": r["lane"],
                "confidence_max": r["confidence_max"],
                "score_formalizability": f"{sf:.3f}",
                "score_cross_view": f"{sc:.3f}",
                "score_axiom_efficiency": f"{sa:.3f}",
                "score_novelty": f"{sn:.3f}",
                "priority_score": f"{pr:.3f}",
                "action_path": route_action(r["preferred_route"]),
                "status": "queued",
                "notes": r["notes"],
            }
        )

    enriched.sort(key=lambda x: float(x["priority_score"]), reverse=True)

    fieldnames = [
        "canonical_id",
        "preferred_route",
        "lane",
        "confidence_max",
        "score_formalizability",
        "score_cross_view",
        "score_axiom_efficiency",
        "score_novelty",
        "priority_score",
        "action_path",
        "status",
        "notes",
    ]

    with out_csv.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        w.writerows(enriched)

    print(f"Wrote {len(enriched)} rows to {out_csv}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
