#!/usr/bin/env python3
"""
Pipeline gate: prevent protocol drift.

Checks (for `*_protocol.py` files in repo root):
1. Every protocol script is executed by `scripts/verify.sh`.
2. Every protocol script has a sibling deterministic output JSON:
   `name_protocol.py` -> `name_results.json`.
3. Every protocol script has a Lean finite-summary theorem module:
   `name_protocol.py` -> `lean/*_Protocol_Theorem.lean`,
   and it is explicitly imported by `lean/Layer3_Anchors.lean`.

Rationale:
These checks make it hard to "forget" to wire a new bridge step into the
canonical pipeline and anchor layer.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
VERIFY = ROOT / "scripts" / "verify.sh"
LAYER3 = ROOT / "lean" / "Layer3_Anchors.lean"


def main() -> int:
    if not VERIFY.exists():
        print(f"Missing verify script: {VERIFY}")
        return 1
    if not LAYER3.exists():
        print(f"Missing Layer3 anchors file: {LAYER3}")
        return 1

    root_protocols = sorted(p.name for p in ROOT.glob("*_protocol.py"))
    verify_text = VERIFY.read_text(encoding="utf-8")
    layer3_text = LAYER3.read_text(encoding="utf-8")

    # Collect all Lean protocol-theorem modules (case-insensitive) and Layer3 imports.
    lean_protocol_stems = {
        p.stem.lower()
        for p in (ROOT / "lean").glob("*_Protocol_Theorem.lean")
    }
    layer3_imports = set()
    for line in layer3_text.splitlines():
        m = re.match("^\\s*import\\s+([A-Za-z0-9_'.]+)\\s*$", line)
        if m:
            layer3_imports.add(m.group(1).strip().lower())

    # Parse verify invocations: `.venv/bin/python "$ROOT/foo_protocol.py"`
    invoked: set[str] = set()
    for line in verify_text.splitlines():
        m = re.search(r'"[^"]+/([A-Za-z0-9_]+_protocol\.py)"', line)
        if m:
            invoked.add(m.group(1))

    errors: list[str] = []

    missing_in_verify = sorted(set(root_protocols) - invoked)
    if missing_in_verify:
        errors.append("verify.sh is missing protocol scripts: " + ", ".join(missing_in_verify))

    # 2) results JSON + 3) Lean theorem module wired into Layer3.
    for script in root_protocols:
        stem = script[:-3]  # drop `.py`
        if not stem.endswith("_protocol"):
            continue
        base = stem[: -len("_protocol")]
        results = ROOT / f"{base}_results.json"
        if not results.exists():
            errors.append(f"Missing results JSON for {script}: {results.name}")

        expected_lean = f"{stem}_theorem".lower()
        if expected_lean not in lean_protocol_stems:
            errors.append(f"Missing Lean protocol theorem for {script}: expected lean/* stem `{expected_lean}`")
        if expected_lean not in layer3_imports:
            errors.append(f"Layer3_Anchors missing import for {script}: expected module `{expected_lean}` (case-insensitive)")

    if errors:
        print("Protocol coverage gate failures:")
        for e in errors:
            print(f"  * {e}")
        return 1

    print(f"Protocol coverage gate passed ({len(root_protocols)} protocol scripts).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
