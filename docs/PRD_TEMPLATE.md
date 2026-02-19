# PRD Template (Lean + Protocol Tasks)

Use this for non-trivial tasks (cross-lane, multi-file, or global wiring changes).

## 1) Problem Statement

- What is missing/broken?
- Why does it matter now?

## 2) Scope

- In scope:
- Out of scope:

## 3) Target Outcome

- Concrete success condition(s):
- Required artifact(s) (Lean theorem, protocol script, docs, etc.):

## 4) Existing Coverage (No-Rework Gate)

- Relevant existing Lean files:
- Relevant protocols/results:
- Canonical ledger references:

## 5) Design

- Core approach:
- Proof/mechanism strategy:
- Anchor vs necessity boundary (if relevant):

## 6) Files To Touch

- `path/file1`
- `path/file2`

## 7) Validation Plan

- Required:
  - `./scripts/verify.sh`
- Conditional:
  - `./scripts/certify.sh`
  - `./scripts/certify.sh --clean` (when global wiring changes)

## 8) Risks / Rollback

- Main risks:
- How to rollback safely:

## 9) Done Criteria

- [ ] Implementation complete
- [ ] Validation passes
- [ ] Ledger/session pointers updated (if step advanced)
- [ ] Supermemory summary saved (durable decisions + next step)
