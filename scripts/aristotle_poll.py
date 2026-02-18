"""
Poll an Aristotle project until completion and download the solution.

Usage:
  ARISTOTLE_API_KEY=... .venv311/bin/python scripts/aristotle_poll.py <project_id> [output_path]
"""

from __future__ import annotations

import asyncio
import sys
from pathlib import Path

from aristotlelib.project import Project, ProjectStatus


async def main() -> int:
    if len(sys.argv) < 2:
        print("usage: scripts/aristotle_poll.py <project_id> [output_path]", file=sys.stderr)
        return 2

    project_id = sys.argv[1]
    output_path = Path(sys.argv[2]) if len(sys.argv) >= 3 else None

    p = await Project.from_id(project_id)
    print(p)

    # Keep polling until terminal state.
    while p.status not in (ProjectStatus.COMPLETE, ProjectStatus.FAILED, ProjectStatus.CANCELED):
        await asyncio.sleep(30)
        await p.refresh()
        print(p)

    if p.status != ProjectStatus.COMPLETE:
        print(f"project ended with status={p.status.name}", file=sys.stderr)
        return 1

    out = output_path or Path(f"{project_id}_aristotle_solution.lean")
    saved = await p.get_solution(output_path=out)
    print(f"saved: {saved}")
    return 0


if __name__ == "__main__":
    raise SystemExit(asyncio.run(main()))

