#!/usr/bin/env python3
"""Pipeline gate: ensure all required dimensional views remain represented.

Checks:
1. Every required path in context/MULTIVIEW_MANIFEST.json exists.
2. Every required Lean file is transitively reachable from lean/Main.lean imports.
"""

from __future__ import annotations

import csv
import hashlib
import json
import re
import sys
from collections import deque
from pathlib import Path


def import_deps(module_file: Path) -> list[str]:
    deps: list[str] = []
    for line in module_file.read_text(encoding="utf-8").splitlines():
        m = re.match(r"^\s*import\s+([A-Za-z0-9_'.]+)\s*$", line)
        if m:
            deps.append(m.group(1))
    return deps


def reachable_lean_modules(root: Path) -> set[str]:
    lean_dir = root / "lean"
    seen: set[str] = set()
    q: deque[str] = deque(["Main"])
    seen.add("Main")
    while q:
        mod = q.popleft()
        mod_file = lean_dir / f"{mod}.lean"
        if not mod_file.exists():
            continue
        for dep in import_deps(mod_file):
            dep_file = lean_dir / f"{dep}.lean"
            if dep_file.exists() and dep not in seen:
                seen.add(dep)
                q.append(dep)
    return seen


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def validate_requestedinfo_backlog(root: Path) -> list[str]:
    errs: list[str] = []
    req = root / "RequestedInfo"
    backlog = req / "review_state" / "REVIEW_BACKLOG.csv"
    if not backlog.exists():
        errs.append(f"Missing RequestedInfo backlog: {backlog}")
        return errs

    current_files = sorted(
        p.relative_to(root).as_posix()
        for p in req.rglob("*")
        if p.is_file()
        and not p.name.startswith("._")
        and p.relative_to(root).as_posix() != "RequestedInfo/review_state/REVIEW_BACKLOG.csv"
    )

    rows: dict[str, dict[str, str]] = {}
    with backlog.open("r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            path = (row.get("path") or "").strip()
            if path:
                rows[path] = row

    backlog_paths = sorted(
        p for p in rows.keys() if p != "RequestedInfo/review_state/REVIEW_BACKLOG.csv"
    )
    if backlog_paths != current_files:
        missing_in_backlog = sorted(set(current_files) - set(backlog_paths))
        stale_in_backlog = sorted(set(backlog_paths) - set(current_files))
        if missing_in_backlog:
            errs.append(
                "RequestedInfo backlog missing paths: "
                + ", ".join(missing_in_backlog[:8])
                + (" ..." if len(missing_in_backlog) > 8 else "")
            )
        if stale_in_backlog:
            errs.append(
                "RequestedInfo backlog has stale paths: "
                + ", ".join(stale_in_backlog[:8])
                + (" ..." if len(stale_in_backlog) > 8 else "")
            )
        return errs

    # Hash spot-check: require exact hash match for all listed files.
    for rel in current_files:
        row = rows.get(rel, {})
        expected = (row.get("sha256") or "").strip().lower()
        p = root / rel
        actual = sha256_file(p)
        if expected != actual:
            errs.append(f"RequestedInfo backlog hash mismatch: {rel}")
            if len(errs) >= 10:
                errs.append("Too many hash mismatches; stop listing.")
                break
    return errs


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    manifest_path = root / "context" / "MULTIVIEW_MANIFEST.json"
    if not manifest_path.exists():
        print(f"Missing manifest: {manifest_path}")
        return 1

    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    views = manifest.get("views", [])
    if not isinstance(views, list) or not views:
        print("Manifest has no views.")
        return 1

    reachable = reachable_lean_modules(root)
    errors: list[str] = []

    print("Multi-view coverage:")
    for view in views:
        name = view.get("name", "<unnamed>")
        paths = view.get("required_paths", [])
        if not isinstance(paths, list) or not paths:
            errors.append(f"[{name}] required_paths missing or empty")
            continue
        view_missing = 0
        for rel in paths:
            rel_path = Path(rel)
            p = root / rel_path
            if not p.exists():
                errors.append(f"[{name}] Missing path: {rel}")
                view_missing += 1
                continue
            # Lean file reachability check from Main.
            if rel_path.parts and rel_path.parts[0] == "lean" and rel_path.suffix == ".lean":
                mod = rel_path.stem
                if mod != "Main" and mod not in reachable:
                    errors.append(f"[{name}] Lean module not reachable from Main imports: {rel}")
                    view_missing += 1
        status = "OK" if view_missing == 0 else f"FAIL({view_missing})"
        print(f"  - {name}: {status}")

    if errors:
        print("\nMulti-view gate failures:")
        for e in errors:
            print(f"  * {e}")
        return 1

    backlog_errors = validate_requestedinfo_backlog(root)
    if backlog_errors:
        print("\nRequestedInfo backlog check failures:")
        for e in backlog_errors:
            print(f"  * {e}")
        print(
            "  * Run: ./.venv/bin/python scripts/build_requestedinfo_review_backlog.py"
        )
        return 1

    print("Multi-view gate passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
