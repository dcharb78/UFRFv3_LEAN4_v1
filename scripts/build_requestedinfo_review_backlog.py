#!/usr/bin/env python3
"""Build deterministic review backlog for RequestedInfo corpus.

Outputs CSV:
  RequestedInfo/review_state/REVIEW_BACKLOG.csv
"""

from __future__ import annotations

import csv
import hashlib
from pathlib import Path
from datetime import datetime, timezone


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def family_for(rel: Path) -> str:
    s = rel.as_posix()
    if s.startswith("RequestedInfo/Constants/"):
        return "constants"
    if s.startswith("RequestedInfo/ReallyOldbutRelevant/"):
        return "legacy"
    if (
        s == "RequestedInfo/10-ufrf-fourier-connection.md"
        or s == "RequestedInfo/UFRF_YangMills_Restored.md"
        or s.startswith("RequestedInfo/UFRF_AllGreen_Package_v1.0/")
        or s == "RequestedInfo/UFRF_Maxwell_Dirac_YM_AllGreen_v1.0.zip"
    ):
        return "physics_bridge"
    return "other"


def trust_tier_for(family: str, suffix: str) -> str:
    # Initial defaults only; later phases will refine this.
    if family == "legacy":
        return "T0"
    if family == "constants":
        return "T0"
    if family == "physics_bridge" and suffix in {".md", ".pdf"}:
        return "T1"
    return "T0"


def load_existing_state(path: Path) -> dict[str, dict[str, str]]:
    """Load prior backlog so status/route/notes survive refresh runs."""
    if not path.exists():
        return {}
    with path.open(newline="", encoding="utf-8") as f:
        rows = list(csv.DictReader(f))
    return {r["path"]: r for r in rows if r.get("path")}


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    req = root / "RequestedInfo"
    out_dir = req / "review_state"
    out_dir.mkdir(parents=True, exist_ok=True)
    out_csv = out_dir / "REVIEW_BACKLOG.csv"

    existing = load_existing_state(out_csv)
    rows: list[dict[str, str]] = []
    files = sorted(
        p
        for p in req.rglob("*")
        if p.is_file()
        and not p.name.startswith("._")
        and p.name != "REVIEW_BACKLOG.csv"
    )

    for p in files:
        rel = p.relative_to(root)
        stat = p.stat()
        mtime = datetime.fromtimestamp(stat.st_mtime, tz=timezone.utc).isoformat()
        suffix = p.suffix.lower()
        family = family_for(rel)
        default_tier = trust_tier_for(family, suffix)
        prev = existing.get(rel.as_posix(), {})
        row = {
            "path": rel.as_posix(),
            "family": family,
            "type": suffix[1:] if suffix else "(noext)",
            "size_bytes": str(stat.st_size),
            "mtime_utc": mtime,
            "sha256": sha256_file(p),
            "status": prev.get("status", "pending") or "pending",
            "trust_tier": prev.get("trust_tier", default_tier) or default_tier,
            "route": prev.get("route", ""),
            "notes": prev.get("notes", ""),
        }
        rows.append(row)

    fieldnames = [
        "path",
        "family",
        "type",
        "size_bytes",
        "mtime_utc",
        "sha256",
        "status",
        "trust_tier",
        "route",
        "notes",
    ]
    with out_csv.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        w.writerows(rows)

    print(f"Wrote {len(rows)} rows to {out_csv}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
