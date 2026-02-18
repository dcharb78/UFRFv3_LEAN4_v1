#!/usr/bin/env python3
"""Build canonical claim table from claim atoms with explicit dedup merges."""

from __future__ import annotations

import csv
from collections import defaultdict
from pathlib import Path


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    atoms_csv = root / "RequestedInfo/review_state/CLAIM_ATOMS.csv"
    out_csv = root / "RequestedInfo/review_state/CANONICAL_CLAIMS.csv"

    with atoms_csv.open(newline="", encoding="utf-8") as f:
        atoms = list(csv.DictReader(f))

    by_id = {r["claim_id"]: r for r in atoms}

    # Explicit high-confidence merges to prevent duplicated work across near-identical claims.
    merge_groups = [
        ["CA-0007", "CA-0024"],  # constant->interval mapping proposals
        ["CA-0022", "CA-0034"],  # triad balance near-phi observations
        ["CA-0023", "CA-0032", "CA-0044"],  # interface-polynomial/root family
        ["CA-0031", "CA-0052"],  # unifying constants taxonomy narrative
    ]

    canonical_of: dict[str, str] = {}
    canon_members: dict[str, list[str]] = {}

    # Initialize with each claim as its own canonical representative.
    for cid in by_id:
        canonical_of[cid] = cid
        canon_members[cid] = [cid]

    # Apply explicit merges using the first id as representative.
    for grp in merge_groups:
        rep = grp[0]
        if rep not in by_id:
            continue
        merged = []
        for cid in grp:
            if cid in by_id:
                merged.append(cid)
                canonical_of[cid] = rep
        if merged:
            canon_members[rep] = sorted(set(canon_members.get(rep, []) + merged))
            for cid in merged[1:]:
                canon_members.pop(cid, None)

    # Recompute member lists from canonical_of to avoid drift.
    regroup: dict[str, list[str]] = defaultdict(list)
    for cid, rep in canonical_of.items():
        regroup[rep].append(cid)

    fieldnames = [
        "canonical_id",
        "canonical_text",
        "lane",
        "preferred_route",
        "confidence_max",
        "member_claim_ids",
        "member_count",
        "sources",
        "notes",
    ]

    rows = []
    for rep in sorted(regroup):
        members = sorted(regroup[rep])
        member_rows = [by_id[m] for m in members]

        route_priority = {"Lean-now": 0, "Compute-first": 1, "Conjecture": 2}
        best_route = sorted(
            (r["route"] for r in member_rows),
            key=lambda x: route_priority.get(x, 99),
        )[0]

        lane_priority = {"Kernel": 0, "Bridge": 1, "Evidence": 2, "Physics bridge": 3, "Anchor": 4}
        best_lane = sorted(
            (r["lane"] for r in member_rows),
            key=lambda x: lane_priority.get(x, 99),
        )[0]

        confidence_max = max(float(r["confidence"]) for r in member_rows)
        sources = sorted(set(r["source_path"] for r in member_rows))

        note = "merged" if len(members) > 1 else "singleton"
        rows.append(
            {
                "canonical_id": f"CC-{int(rep.split('-')[1]):04d}",
                "canonical_text": by_id[rep]["claim_text"],
                "lane": best_lane,
                "preferred_route": best_route,
                "confidence_max": f"{confidence_max:.2f}",
                "member_claim_ids": "|".join(members),
                "member_count": str(len(members)),
                "sources": "|".join(sources),
                "notes": note,
            }
        )

    with out_csv.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        w.writerows(rows)

    print(f"Wrote {len(rows)} canonical claims to {out_csv}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
