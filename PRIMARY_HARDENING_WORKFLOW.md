# Primary Hardening Workflow (No New Theorem Surface)

Status: Reference workflow (hardening gates currently PASS; re-enter if pipeline regresses)  
Scope: clean, organize, certify, and truth-check existing work before further proof expansion.

## Goal
Make the current Lean/Python proof stack auditable and resilient:
- no false-green claims,
- no hidden placeholder assumptions,
- no transitive import drift,
- no unclear certification status.

## Non-Negotiable Rules
1. No new theorem topics while hardening mode is active.
2. Fixes may only be:
   - proof repairs,
   - import/wiring repairs,
   - verification/certification pipeline repairs,
   - documentation/traceability repairs.
3. Every "pass" claim must cite a concrete log in `context/cert/`.
4. If any gate fails, status is FAIL even if `lake build` alone passes.

## One Command Certification
- Incremental cert:
  - `./scripts/certify.sh`
- Clean cert:
  - `./scripts/certify.sh --clean`

Both commands produce a timestamped log in `context/cert/` and print:
- `CERT_STATUS=PASS|FAIL`
- `CERT_LOG=...`

## Required Gates (in order)
1. Python protocol execution (`scripts/verify.sh`).
2. Lean full build.
3. `lean/Main.lean` transitive reachability for all `lean/*.lean`.
4. Multi-view manifest gate.
   - If RequestedInfo files changed, refresh backlog first:
     - `./.venv/bin/python scripts/build_requestedinfo_review_backlog.py`
5. Unified context typecheck.
6. No `sorry`/`admit` in canonical surfaces (`lean/`, `context/`).
7. Hardening snapshot: `native_decide` usage count/top files (honesty signal).

## Honesty Boundaries
Use these labels exactly:
- `Formally proved`: theorem is machine-checked in Lean without `sorry/admit`.
- `Computationally validated`: finite computation/protocol result (Python and/or `native_decide`).
- `Open`: not yet proved/validated.

Never present `Computationally validated` as `Formally proved`.

## Drift Prevention
1. Keep `lean/Main.lean` reachable set complete (no orphan root files).
2. Keep `LEAN_PROOFS_THEORY_AND_NEXT_STEPS.md` as canonical ledger.
3. Keep `PROOF_CONTINUATION_PLAN.md` concise and current-state only.
4. Archive stale planning docs; keep only one active workflow narrative.

## Exit Criteria (to resume expansion)
All must hold:
1. Clean cert passes (`./scripts/certify.sh --clean`).
2. Incremental cert passes (`./scripts/certify.sh`).
3. No orphan Lean roots from Main-transitive check.
4. Hard blockers list is empty or explicitly accepted.
5. Next theorem target selected from canonical ledger (non-duplicate scope).
