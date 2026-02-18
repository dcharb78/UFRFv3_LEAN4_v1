# Riemann Lattice Distance Analysis (Portable)

This folder is a portable package of the Riemann lattice-distance analysis used in the UFRF workspace.

## Files
- `riemann_zero_exclusion_corrected.py`
  - finite-sample analysis on first 100 built-in zeta zeros.
- `riemann_distance_streaming.py`
  - streaming analyzer for very large zero datasets (LMFDB-scale files).
- `riemann_zero_exclusion_results.json`
  - sample output from the corrected finite-sample run.
- `LMFDB_100B_DISTANCE_FACTS_PORTING.md`
  - notes for scaling/porting to very large datasets.
- `requirements.txt`
  - minimal Python deps for these scripts.

## Setup
```bash
python3 -m venv .venv
.venv/bin/pip install -r requirements.txt
```

## Quick run (finite built-in 100 zeros)
```bash
.venv/bin/python riemann_zero_exclusion_corrected.py
```

## Quick run (streaming mode)
Builtin first 100:
```bash
.venv/bin/python riemann_distance_streaming.py run --builtin-first100 --out first100_stream.json
```

Large file (one gamma per line or tokenized rows):
```bash
.venv/bin/python riemann_distance_streaming.py run \
  --zeros /path/to/zeros.txt \
  --token-index 0 \
  --out shard_01.json
```

Merge multiple shard outputs:
```bash
.venv/bin/python riemann_distance_streaming.py merge \
  --inputs shard_01.json shard_02.json \
  --out merged.json
```

## Notes
- Distance definition matches the Lean model used in `lean/Riemann_Zero_Exclusion_Theorem.lean`.
- The corrected finite script reflects density-consistent behavior (denser lattice -> smaller nearest distance on average).
