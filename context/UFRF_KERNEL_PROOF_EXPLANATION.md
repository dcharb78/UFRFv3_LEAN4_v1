# UFRF Kernel Proof Explanation

This document explains what is *actually certified in Lean* in the kernel-first entry points:

- `context/UFRF_KERNEL_PROOF.lean`
- `context/UFRF_START_HERE.lean`

It is intentionally mechanism-focused: it maps each “story sentence” to a concrete lemma/theorem name
and file path.

## What The Kernel Proves (High Level)

The kernel is the repo’s “0→1 discrete refinement” core:

- **Exact base-13 refinement addressing** (`addrQ` join/split).
- **A deterministic bin selector** `floorBin` for any rational `q ∈ [0,1)`.
- **A resolution operator** `resolveQ` and residual `residualQ` giving an exact decomposition
  `q = resolveQ + residualQ`, plus monotone refinement across scales.
- **A representative multi-axis concurrency invariant** for decimal ticks (`tick10` at `φ(m)`).

The kernel is *not* a Monster/Moonshine proof; those live downstream as anchor layers.

## Resolution Triad (0→1 Kernel)

At a fixed depth `k`, the kernel gives three *equivalent views* of the same discrete fact
for any `q ∈ [0,1)` and any bin index `x : Fin (SL k)`:

1. **Interval view**: `q ∈ coarseInterval k x`
2. **Address view**: `resolveQ k q = addrQ k x`
3. **Selector view**: `floorBin k q = x`

In Lean, these are certified via the following mechanism lemmas (all in
`lean/Index_Of_Indexes_Subintervals_Theorem.lean`):

- Bin membership:
  - `IndexOfIndexesSubintervals.floorBin_mem_coarseInterval`
- Coarse-bin membership implies resolved-prefix equality:
  - `IndexOfIndexesSubintervals.resolveQ_eq_addrQ_of_mem_coarseInterval`
- Resolved-prefix equality recovers the bin (no ambiguity):
  - `IndexOfIndexesSubintervals.floorBin_eq_of_resolveQ_eq_addrQ`

And the repo also provides packaged iff forms (useful as a stable API surface):

- `IndexOfIndexesSubintervals.mem_coarseInterval_iff_resolveQ_eq_addrQ`
- `IndexOfIndexesSubintervals.resolveQ_eq_addrQ_iff_floorBin_eq`
- `IndexOfIndexesSubintervals.mem_coarseInterval_iff_floorBin_eq`

The kernel entry points include a *minimal directional basis* of these, so the iff forms remain
derivable without bloating the kernel statement.

## Ordering + Seam Crossing (Tick Ordering Invariants)

Once the resolution triad is in place, there are two additional kernel invariants that we treat as
“tick ordering” facts (all in `lean/Index_Of_Indexes_Subintervals_Theorem.lean`):

- **Monotonicity** (order preservation on `[0,1)`):
  - `IndexOfIndexesSubintervals.floorBin_mono`
  - `IndexOfIndexesSubintervals.resolveQ_mono`
- **Seam crossing witness** (a bin change forces crossing a depth-`k` gridpoint):
  - `IndexOfIndexesSubintervals.floorBin_lt_imp_exists_gridpoint_between`
  - `IndexOfIndexesSubintervals.resolveQ_lt_imp_exists_gridpoint_between`

These are the discrete versions of:

- “the observer’s coarse bin index is order-consistent,” and
- “you cannot change bins without crossing an exact grid boundary.”

## Where To Look (Navigation)

Start here (smallest entry point):

- `context/UFRF_START_HERE.lean`

Full kernel synthesis bundle (large conjunction, intended for downstream imports):

- `context/UFRF_KERNEL_PROOF.lean`

Core definitions + lemmas for the 0→1 refinement:

- `lean/Index_Of_Indexes_Subintervals_Theorem.lean`

Repo’s canonical “what is Lean-certified” ledger:

- `LEAN_PROOFS_THEORY_AND_NEXT_STEPS.md`

## How To Validate

One-command full validation (Python protocols + Lean build + gates):

```bash
./scripts/verify.sh
```

Auditable certification (timestamped PASS/FAIL logs):

```bash
./scripts/certify.sh
./scripts/certify.sh --clean
```
