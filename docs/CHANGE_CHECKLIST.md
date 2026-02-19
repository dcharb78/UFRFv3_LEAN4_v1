# Change Checklist (Execution Gate)

Use this checklist before declaring task complete.

## A) Pre-Change

- [ ] Goal and scope are explicit.
- [ ] Existing coverage checked (no duplicate theorem/protocol).
- [ ] Anchor vs necessity scope identified.
- [ ] PRD created if task is non-trivial (`docs/PRD_TEMPLATE.md`).

## B) Implementation

- [ ] Changes are minimal and scoped to task.
- [ ] No `sorry`/`admit` introduced in `lean/` or `context/`.
- [ ] No placeholder proofs (`True := by trivial`) added to formal surface.
- [ ] Comments/docs updated where behavior or workflow changed.

## C) Validation

- [ ] `./scripts/verify.sh` passed.
- [ ] `./scripts/certify.sh` passed (if milestone/hardening state changed).
- [ ] `./scripts/certify.sh --clean` passed (if global build wiring changed).

## D) Finalization

- [ ] `git status` is clean or intentionally staged.
- [ ] Commit message matches actual change.
- [ ] Ledger/session pointers updated (if step changed).
- [ ] Supermemory saved: durable decisions, what changed, next step.
