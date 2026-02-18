# LMFDB 100B Zeros: Portable Deterministic Distance-Facts Workflow

This note shows how to reuse the current finite/deterministic nearest-lattice analysis in another project at very large scale (including ~100B precomputed zeros).

## 1) Keep the exact metric definitions

Use the same definitions as in:

- `lean/Riemann_Zero_Exclusion_Theorem.lean`
- `lean/Lattice_Distance_Monotonicity_Theorem.lean`

Definitions:

- For generator `d`, lattice points are:
  - `gamma = 2 * n * pi / d`, `n >= 1`.
- For family `G` of generators, nearest distance at zero `z` is:
  - `dist_G(z) = min_{d in G} min_{n>=1} |z - 2*n*pi/d|`.

Current families:

- UFRF: `[3, 5, 7, 11, 13]`
- Monster: `[47, 59, 71]`

## 2) Use the streaming runner (no lattice materialization)

Added script:

- `scripts/riemann_distance_streaming.py`

It computes distances in constant memory using the nearest-positive-multiple formula per generator, so it scales to very large datasets.

### Smoke test (matches current first-100 check)

```bash
.venv/bin/python scripts/riemann_distance_streaming.py run \
  --builtin-first100 \
  --threshold 0.05 \
  --output /tmp/riemann_stream_first100.json
```

### Run on external zero file

Assume one row per line; by default it reads token index `0`.

```bash
.venv/bin/python scripts/riemann_distance_streaming.py run \
  --zeros /path/to/zeros.txt.gz \
  --token-index 0 \
  --threshold 0.01 --threshold 0.05 --threshold 0.1 \
  --output /path/to/results/run_part_001.json
```

If your file has an index and the zero in column 2, use `--token-index 1`.

## 3) Shard/parallelize for 100B

For 100B, split into shards and run one output per shard:

```bash
.venv/bin/python scripts/riemann_distance_streaming.py run --zeros shard_000.txt.gz --output out_000.json
.venv/bin/python scripts/riemann_distance_streaming.py run --zeros shard_001.txt.gz --output out_001.json
...
```

Merge deterministic accumulators:

```bash
.venv/bin/python scripts/riemann_distance_streaming.py merge \
  --inputs out_000.json out_001.json out_002.json \
  --output merged_100b.json
```

## 4) What to report as finite deterministic facts

For each family (UFRF / Monster), report:

- `count` of zeros processed
- `mean` nearest distance
- `std_population`
- threshold counts (e.g. `<0.05`)

Cross-family report:

- `monster_mean_over_ufrf_mean` (current first-100 baseline is ~`0.2024`)

These are finite, deterministic data facts for the exact dataset and parser configuration used.

## 5) Density comparison (finite structural fact)

The script also reports exact `points_per_2pi` for each family via inclusion-exclusion on generator gcds.

For current families:

- UFRF: `35` points per `2π`
- Monster: `175` points per `2π`
- Exact ratio: `5.0`

This is a structural density witness independent of zero sample size.

## 6) How to integrate with Lean in a new project

Recommended split:

1. External compute layer (Python/Rust): generate result JSON + file hash metadata.
2. Lean layer:
   - prove generic lemmas (distance monotonicity, threshold implications),
   - certify small canonical finite datasets directly in Lean (`native_decide`),
   - treat 100B output as deterministic empirical evidence unless importing a formal certificate mechanism.

This preserves the current no-`sorry` style while allowing exploration at 100B scale.

