#!/usr/bin/env python3
"""
Write a small human-readable "where are we?" snapshot for fast recovery.

Output:
  context/SESSION_STATE.md

This complements `context/.coherence_state.min.json`:
- `.coherence_state.min.json` is machine-oriented and stable for low-token recovery.
- `SESSION_STATE.md` is human-oriented and answers: what is DONE/NEXT, and what were the last certs.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
COHERENCE = ROOT / "context" / ".coherence_state.min.json"
OUT = ROOT / "context" / "SESSION_STATE.md"
CERT_DIR = ROOT / "context" / "cert"


@dataclass(frozen=True)
class CertLog:
    path: Path
    status: str  # PASS/FAIL/UNKNOWN


def newest(glob: str) -> Path | None:
    paths = sorted(CERT_DIR.glob(glob))
    return paths[-1] if paths else None


def cert_status(path: Path | None) -> str:
    if path is None or not path.exists():
        return "MISSING"
    try:
        tail = "\n".join(path.read_text(encoding="utf-8", errors="replace").splitlines()[-40:])
    except Exception:
        return "UNKNOWN"
    if "CERT_STATUS=PASS" in tail:
        return "PASS"
    if "CERT_STATUS=FAIL" in tail:
        return "FAIL"
    return "UNKNOWN"


def fmt_cert(label: str, path: Path | None) -> str:
    if path is None:
        return f"- {label}: (missing)"
    rel = path.relative_to(ROOT).as_posix()
    return f"- {label}: `{rel}` ({cert_status(path)})"


def main() -> None:
    if not COHERENCE.exists():
        raise SystemExit(f"Missing coherence state: {COHERENCE}")

    state = json.loads(COHERENCE.read_text(encoding="utf-8"))
    done = int(state.get("s", {}).get("d", -1))
    nxt = int(state.get("s", {}).get("n", -1))
    hashes = state.get("h", {})

    inc = newest("certify_incremental_*.log")
    clean = newest("certify_clean_*.log")

    lines: list[str] = []
    lines.append("# Session State")
    lines.append("")
    lines.append("Authoritative status lives in the certify logs; this file is a quick pointer.")
    lines.append("")
    lines.append(f"- Ledger: `{done} DONE / {nxt} NEXT`")
    lines.append(f"- Coherence: `context/.coherence_state.min.json` (v={state.get('v')})")
    lines.append("- Anchors: `context/ANCHOR_INDEX.md` (quick map of certified examples -> exact artifacts)")
    lines.append("")
    lines.append("## Latest Certs")
    lines.append(fmt_cert("incremental", inc))
    lines.append(fmt_cert("clean", clean))
    lines.append("")
    lines.append("## Key Hashes (short)")
    for k in ["a", "l", "p", "m", "i", "z", "c", "x"]:
        v = hashes.get(k, "")
        if v:
            lines.append(f"- `{k}`: `{v}`")
    lines.append("")

    rendered = "\n".join(lines) + "\n"
    if OUT.exists() and OUT.read_text(encoding="utf-8") == rendered:
        return
    OUT.write_text(rendered, encoding="utf-8")


if __name__ == "__main__":
    main()
