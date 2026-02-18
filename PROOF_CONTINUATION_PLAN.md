# UFRF Active Plan (Concise)

Status: Active
Last-updated: 2026-02-18

## Current Checkpoint

- Canonical ledger: `LEAN_PROOFS_THEORY_AND_NEXT_STEPS.md`
- Session pointer: `context/SESSION_STATE.md`
- Current step: `300 DONE / 301 NEXT`
- Latest certs:
  - incremental: `context/cert/certify_incremental_20260218T042054Z.log` (PASS)
  - clean: `context/cert/certify_clean_20260218T003859Z.log` (PASS)

## Scope Rule (Non-negotiable)

- Anchor examples (Monster/mod-1001/etc.) are not necessity theorems.
- New work must be mechanism-first:
  - Lean theorem for the discrete mechanism.
  - Python protocol only for deterministic finite evidence.
- No `sorry`/`admit` in `lean/` or `context/`.

## Immediate Next Step (301)

Step 301: warning debt burn-down (mechanism-preserving).

Goal:
- reduce linter warnings in `lean/Multi_Axis_Phase_Lift_Theorem.lean` without semantic changes:
  replace unnecessary `simpa`, remove unused simp args, and remove unused variables.

Acceptance:
- one compact bounded statement theorem + Start-Here pointer,
- no mechanism churn or theorem-surface sprawl,
- `./scripts/verify.sh` PASS,
- `./scripts/certify.sh` PASS,
- ledger advanced to `301 DONE / 302 NEXT`.

## Short Horizon

Step 252:
- completed: complement-vs-additive-inverse finite protocol/theorem pair (digit-local vs carry-coupled).

Step 253:
- completed: compact API wrappers/entry points for discriminant + PRISM summaries.

Step 254:
- completed: bounded projection-compatibility protocol/theorem + PRISM API entrypoint.

Step 255:
- completed: bounded PRISM-to-observer bridge packaging (no unbounded claims).

Step 256:
- completed: bounded PRISM-observer worked-class wrappers (no unbounded claims).

Step 257:
- completed: bounded PRISM-observer seam-class bridge wrappers (no unbounded claims).

Step 258:
- completed: bounded PRISM-observer class-seam index consolidation (no unbounded claims).

Step 259:
- completed: bounded PRISM-observer index adoption wrapper (no unbounded claims).

Step 260:
- completed: bounded PRISM discoverability compression wrapper (no unbounded claims).

Step 261:
- completed: bounded PRISM Start-Here adoption pointer (no unbounded claims).

Step 262:
- completed: bounded PRISM discoverability smoke-bundle pointer (no unbounded claims).

Step 263:
- completed: bounded PRISM Start-Here canonical entry retarget (no unbounded claims).

Step 264:
- completed: bounded PRISM Start-Here naming alias consolidation (no unbounded claims).

Step 265:
- completed: bounded Start-Here onboarding pointer bundle (no unbounded claims).

Step 266:
- completed: bounded Start-Here onboarding alias in canonical API surface (no unbounded claims).

Step 267:
- completed: bounded Start-Here unified entry bundle (no unbounded claims).

Step 268:
- completed: bounded Start-Here unified entry alias consolidation (no unbounded claims).

Step 269:
- completed: bounded Start-Here unified API smoke bundle (no unbounded claims).

Step 270:
- completed: bounded Start-Here master entry alias (no unbounded claims).

Step 271:
- completed: bounded Start-Here master entry smoke alias (no unbounded claims).

Step 272:
- completed: bounded Start-Here root discoverability alias (no unbounded claims).

Step 273:
- completed: bounded Start-Here root entry smoke endpoint (no unbounded claims).

Step 274:
- completed: bounded Start-Here canonical root entry alias (no unbounded claims).

Step 275:
- completed: bounded Start-Here root entry final smoke alias (no unbounded claims).

Step 276:
- completed: bounded Start-Here canonical endpoint alias (no unbounded claims).

Step 277:
- completed: bounded Start-Here canonical endpoint smoke-package alias (no unbounded claims).

Step 278:
- completed: bounded Start-Here endpoint minimal kernel alias (no unbounded claims).

Step 279:
- completed: bounded trinitarian spine alignment (truth-boundary preserving, no new axioms).

Step 280:
- completed: bounded trinitarian kernel proxy package theorem (no new axioms).

Step 281:
- completed: Start-Here pointer to the trinitarian kernel proxy package (wiring + pointer, no new axioms).

## Keep / Drop

Keep:
- `LEAN_PROOFS_THEORY_AND_NEXT_STEPS.md` as canonical long ledger.
- `context/SESSION_STATE.md` as quick pointer.
- `context/ANCHOR_INDEX.md` as artifact map.

Drop from this plan file:
- Historical phase replay.
- Legacy “Phase 0/1/2” narratives already completed.
- Duplicated theorem inventories better maintained in source files and anchor index.

## Execution Gates (Every Step)

1. Duplicate-scope check before adding theorem/protocol:
   - ledger
   - existing `*_protocol.py`
   - existing Lean theorem modules
2. Wiring check:
   - protocol in `scripts/verify.sh`
   - theorem import in `lean/Layer3_Anchors.lean` (if anchor/protocol theorem)
3. Validation:
   - `./scripts/verify.sh`
   - then `./scripts/certify.sh`
4. Run `./scripts/certify.sh --clean` when global wiring/toolchain changes, or
   before repo-level “fully green” claims.

Backlog ideas remain in canonical ledger and supporting notes. Only active execution
items stay in this file.

## Archive

Older plan snapshots live under `_archive/2026-02-11_plan_cleanup/`.
