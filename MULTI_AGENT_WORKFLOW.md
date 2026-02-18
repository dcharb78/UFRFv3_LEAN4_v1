# Multi-Agent Workflow (Anti-Tunnel Design)

## Why This Exists
UFRF work spans multiple equivalent views of one recursive/concurrent structure.
To avoid tunnel vision, every work cycle must include cross-view checks and handoffs.

## Lanes
- `Kernel/Lean`: discrete cycle, closure, recursion, and semigroup core.
- `Bridge`: equivalence maps between arithmetic/harmonic/geometric views.
- `Anchor`: Moonshine, Tn, Frobenius/Monster, log/mod coordinates.
- `Physics bridge`: Maxwell/Dirac/Yang-Mills/Fourier drafts and formalization candidates.
- `Evidence`: reproducible Python tests and statistical checks.

## Required Cycle Outputs
For each substantial iteration:
1. `What changed` (formal, computational, or conjectural).
2. `What assumptions were used`.
3. `What cross-view links were checked`.
4. `What remains open`.

## Core Invariants Checklist (Must Stay In Scope)
- `13 SL` finite index invariant is explicit (`SL0..SL12`).
- Prime self-perspective invariant is explicit (`p % p = 0`).
- Trinity-plus-source decomposition is explicit (`4+4+4+1 = 13` and `12+1 = 13`).
- Base-10 and base-12+source views are treated as concurrent charts, not competing truths.
- "System of systems" recursion is represented by repeated 13-closure, not ad-hoc constants.

Recommended locations:
- `LEAN_PROOFS_THEORY_AND_NEXT_STEPS.md` for canonical step ledger (`N DONE / N+1 NEXT`).
- `PROOF_CONTINUATION_PLAN.md` for concise active execution/gate state.

## Merge/Completion Gates
Run:

```bash
./scripts/verify.sh
```

This now checks:
- Python validation scripts.
- Lean build.
- Main transitive Lean dependency coverage.
- Multi-view manifest coverage (`context/MULTIVIEW_MANIFEST.json`).
- Unified context typecheck.
- No `sorry`/`admit`.

## Compaction Guard
- Before long tool runs or when context is getting dense, run:
  - `./scripts/update_coherence_checkpoint.py`
- This writes a compact machine checkpoint:
  - `context/.coherence_state.min.json`
- Pair it with a supermemory summary save so both local and remote continuity are preserved.

## Source Trust Levels
- **Formal truth:** `lean/`, `context/`
- **Computational evidence:** `*.py` + generated JSON
- **Hypothesis sources:** `RequestedInfo/`, `_archive/`, external repos/docs

Hypothesis-source content is not considered proved until translated into Lean theorem statements
or reproducible computational checks.
