# Proofpoints Review (2026-02-12)

## Scope

Reviewed all files under `proofpoints/` and evaluated:

1. Conceptual fit with current UFRF Lean program.
2. Computational reproducibility in current repo.
3. Non-breaking integration path.

## Inventory

Files found:

- `proofpoints/Dirac_from_UFRF_Complete.md`
- `proofpoints/Maxwell_from_UFRF_Green.md`
- `proofpoints/YM_from_UFRF_Complete.md`

## Deduplication Result

All three files are byte-identical duplicates of canonical docs in:

- `RequestedInfo/UFRF_AllGreen_Package_v1.0/docs/Dirac_from_UFRF_Complete.md`
- `RequestedInfo/UFRF_AllGreen_Package_v1.0/docs/Maxwell_from_UFRF_Green.md`
- `RequestedInfo/UFRF_AllGreen_Package_v1.0/docs/YM_from_UFRF_Complete.md`

Integration decision:

- Keep canonical source in `RequestedInfo/UFRF_AllGreen_Package_v1.0/docs/`.
- Treat `proofpoints/` as intake pointers only (avoid edit drift).

## Conceptual Assessment

Helpful:

- Strengthens the existing UFRF narrative bridge from trinity/13/26 structure to:
  - Maxwell form/invariants,
  - Dirac square-root structure and spinor checks,
  - Yang-Mills lattice observables and scale-proxy behavior.

Not yet Lean-ready as first-principles PDE proofs:

- Current statements are high-level and rely on external physics formalism not currently encoded in Lean here.
- Best current use is as computational protocol inputs and finite arithmetic/invariant anchors.

## Computational Validation (Executed)

Ran from repo root:

```bash
.venv/bin/python RequestedInfo/UFRF_AllGreen_Package_v1.0/code/run_all.py
```

Observed key outputs:

- Maxwell checks:
  - `<E^2 - c^2 H^2> = 1.3118846287074603e-19`
  - `<E·H> = 1.1536901089475027e-05`
- Dirac checks:
  - max Clifford anticommutator error = `0.0`
  - factorization error = `5.551115123125783e-17`
- YM SU(2):
  - `avg_plaquette_mean = 0.29053482399625`
  - `mass_proxy = 0.37587294127125614`
- YM SU(3):
  - `avg_plaquette_mean = 0.021079391984087092`

Outputs are written under:

- `RequestedInfo/UFRF_AllGreen_Package_v1.0/results/`

## Non-Breaking Integration Applied

1. Hardened package runner:
   - Updated `RequestedInfo/UFRF_AllGreen_Package_v1.0/code/run_all.py` to use `sys.executable` and absolute paths.
   - This allows execution from any working directory and avoids reliance on `python` shell alias.
2. Added intake guidance:
   - `proofpoints/README.md` documenting canonical source and reproducible command.
3. Added planning lane:
   - `PROOF_CONTINUATION_PLAN.md` now includes a dedicated physics-bridge lane for controlled integration.

No Lean theorem files were changed in this review step.

## Recommended Next Integration Steps

1. Add finite protocol bridges (Lean + Python JSON) for three stable checks:
   - Maxwell invariant near-null bounds.
   - Dirac anticommutator/factorization error bounds.
   - YM coarse observable bounds (plaquette ranges, positive finite mass proxy).
2. Keep these in the empirical/protocol lane (not first-principles PDE derivations).
3. Gate them behind existing `./scripts/verify.sh` style only after duplicate-check to prevent overlap.
