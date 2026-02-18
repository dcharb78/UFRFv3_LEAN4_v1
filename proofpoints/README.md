# Proofpoints Intake Notes

This folder currently mirrors three physics-bridge summary docs that already exist in:

- `RequestedInfo/UFRF_AllGreen_Package_v1.0/docs/Dirac_from_UFRF_Complete.md`
- `RequestedInfo/UFRF_AllGreen_Package_v1.0/docs/Maxwell_from_UFRF_Green.md`
- `RequestedInfo/UFRF_AllGreen_Package_v1.0/docs/YM_from_UFRF_Complete.md`

The files in this folder are byte-identical duplicates of those canonical docs.

## Policy

1. Treat `RequestedInfo/UFRF_AllGreen_Package_v1.0/docs/` as canonical.
2. If content changes, update canonical docs first.
3. Keep this folder as an intake pointer to avoid plan drift and duplicate edits.

## Quick Repro (computational checks only)

From repo root:

```bash
.venv/bin/python RequestedInfo/UFRF_AllGreen_Package_v1.0/code/run_all.py
```

Expected outputs are JSON files under:

- `RequestedInfo/UFRF_AllGreen_Package_v1.0/results/`

Notes:

- This is computational validation scaffolding (Maxwell FDTD invariants, Dirac algebra checks, SU(2)/SU(3) lattice health checks).
- It is not yet a first-principles Lean derivation of full Maxwell/Dirac/Yang-Mills PDE systems.
