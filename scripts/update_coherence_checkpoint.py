#!/usr/bin/env python3
"""
Write a compact machine-oriented coherence checkpoint for low-token recovery.

Output:
  context/.coherence_state.min.json

Design goals:
  - minimal keys / compact structure,
  - deterministic ordering,
  - rewrite only when content changes.
"""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
LEDGER = ROOT / "LEAN_PROOFS_THEORY_AND_NEXT_STEPS.md"
VERIFY = ROOT / "scripts" / "verify.sh"
OUT = ROOT / "context" / ".coherence_state.min.json"


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    h.update(path.read_bytes())
    return h.hexdigest()[:16]


def parse_step_state() -> tuple[int, int]:
    done = -1
    nxt = -1
    for raw in LEDGER.read_text(encoding="utf-8").splitlines():
        s = raw.strip()
        m_done = re.match(r"^(\d+)\. DONE:", s)
        if m_done:
            done = max(done, int(m_done.group(1)))
        m_next = re.match(r"^(\d+)\. NEXT:", s)
        if m_next:
            nxt = max(nxt, int(m_next.group(1)))
    return done, nxt


def parse_tail_protocols(k: int = 10) -> list[str]:
    protos: list[str] = []
    for raw in VERIFY.read_text(encoding="utf-8").splitlines():
        raw = raw.strip()
        m = re.search(r'"[^"]+/([a-zA-Z0-9_]+_protocol\.py)"', raw)
        if m:
            protos.append(m.group(1))
    return protos[-k:]


def build_payload() -> dict[str, object]:
    done, nxt = parse_step_state()
    return {
        "v": 1,
        "s": {"d": done, "n": nxt},
        "h": {
            "a": sha256(ROOT / "AGENTS.md"),
            "l": sha256(ROOT / "LEAN_PROOFS_THEORY_AND_NEXT_STEPS.md"),
            "p": sha256(ROOT / "PROOF_CONTINUATION_PLAN.md"),
            "m": sha256(ROOT / "MULTI_AGENT_WORKFLOW.md"),
            "i": sha256(ROOT / "context" / "ANCHOR_INDEX.md"),
            "z": sha256(ROOT / "scripts" / "verify.sh"),
            "c": sha256(ROOT / "scripts" / "certify.sh"),
            "x": sha256(ROOT / "lean" / "Layer3_Anchors.lean"),
        },
        "k": parse_tail_protocols(),
        "g": {"vf": 1, "ns": 1, "mv": 1},
    }


def main() -> None:
    payload = build_payload()
    rendered = json.dumps(payload, separators=(",", ":"), sort_keys=True) + "\n"

    if OUT.exists() and OUT.read_text(encoding="utf-8") == rendered:
        print(f"Checkpoint unchanged: {OUT}")
        return

    OUT.write_text(rendered, encoding="utf-8")
    print(f"Wrote checkpoint: {OUT}")
    print(rendered.strip())


if __name__ == "__main__":
    main()
