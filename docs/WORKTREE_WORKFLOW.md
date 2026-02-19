# Worktree Workflow (codex/* branches)

This repo uses one branch/worktree per task to reduce drift and make validation repeatable.

## 1) Create a task branch + worktree

```bash
# from repo root on main
git fetch origin
git switch main
git pull --ff-only

TASK="codex/<short-task-name>"
WT="../wt-<short-task-name>"

git branch "$TASK"
git worktree add "$WT" "$TASK"
```

## 2) Execute inside the worktree

```bash
cd "$WT"
```

- If non-trivial task: create a PRD using `docs/PRD_TEMPLATE.md`.
- Use `docs/CHANGE_CHECKLIST.md` as the execution gate.

## 3) Validate before merge

Always run:

```bash
./scripts/verify.sh
```

Run additionally when applicable:

```bash
./scripts/certify.sh
./scripts/certify.sh --clean
```

Use `--clean` after global build wiring changes (toolchain/lake/global scripts).

## 4) Commit and push

```bash
git add -A
git commit -m "<task summary>"
git push -u origin "$TASK"
```

## 5) Merge and clean up

After merge (or fast-forward into `main`):

```bash
cd <repo-root>
git switch main
git pull --ff-only

git worktree remove "$WT"
git branch -d "$TASK"
git push origin --delete "$TASK"   # only if remote branch no longer needed
```

## Notes

- Keep one concern per branch.
- If a task grows too broad, split into additional branches/worktrees.
- Never skip validation gates to “just get green”; preserve proof integrity.
