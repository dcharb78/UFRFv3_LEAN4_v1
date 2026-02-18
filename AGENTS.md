# UFRF / Fel / Moonshine: Working Agreement (For Codex + Humans)

This repo contains:
- Theory docs: `UFRF3.1/` (UFRF v0.5.2 markdown package)
- Lean formalization: `lean/`
- Python verification / analysis: `*.py` + `*.json` outputs

## One Command Validation

Run both the Python checks and the Lean build:

```bash
./scripts/verify.sh
```

For auditable hardening certification (timestamped logs + explicit pass/fail marker):

```bash
./scripts/certify.sh
./scripts/certify.sh --clean
```

## Python Environment

This repo uses a local venv in `.venv/`.

```bash
python3 -m venv .venv
.venv/bin/pip install -r requirements.txt
```

All Python scripts write their JSON outputs to the repo root (next to the scripts).

## Lean Environment

Lean is pinned via `lean-toolchain` (currently `leanprover/lean4:v4.26.0-rc2`).
Mathlib is pinned in `lakefile.lean` to the matching tag.

```bash
~/.elan/bin/lake update
~/.elan/bin/lake exe cache get   # optional but recommended for speed
~/.elan/bin/lake build
```

## Current Lean Status (Honesty Check)

Lean files compile with `lake build` and contain **no** `sorry`/`admit` (and no placeholder `True := by trivial` theorems).

For the canonical, maintained inventory of what is Lean-validated (and how it fits the overall proof spine),
see:
- `LEAN_PROOFS_THEORY_AND_NEXT_STEPS.md`

High-level summary of what is currently *fully formal / computably validated* in Lean (often via `native_decide`):
- Emergence anchors (Frobenius → Monster triple, AP(12) filter, σ₁ center identity).
- Semigroup semantics + global gap set (`{1,2,4}`) for the UFRF generators.
- Concurrency / recursion skeletons:
  - modular orbit closure (`m/gcd(m,s)`),
  - multi-axis synchronization (LCM/CRT),
  - base-10/base-13 digit recursion (“index of indexes” carry/return).
- Moonshine anchors (e.g. `47*59*71 + 1 = 196884`) and exact log/mod coordinates.
- Bounded computational checks (Riemann-zero lattice distance statistics, gap-prime stats).

Notes:
- The corrected Riemann lattice-distance computation shows the Monster lattice is denser and mean nearest-lattice distances are smaller (density-consistent). The older "40x" claim was caused by lattice truncation.

What is currently *formal for `Tₙ`*:
- Low-order and higher-order closed forms derived from the generating-function product (currently through degree 10).
- An exact (all-`n`) definition and exact algebraic laws (scale invariance and multiset concurrency) in:
  - `lean/Tn_Exact_Definition.lean` and related files.

## Reference Repo

There is a known-good Lean proof project used as a reference:
- `_archive/2026-02-11_repo_cleanup_phase1/legacy_repos/_refs/UFRF-MonsterMoonshinev1/`
  (cloned from `dcharb78/UFRF-MonsterMoonshinev1`)

Use it for patterns on project structure, Mathlib pinning, and proof style.

## Rules For Changes

- Keep `lake build` green.
- Do not introduce `sorry`/`admit` in `lean/`.
- Do not introduce “placeholder theorems” (e.g. `True := by trivial`) in `lean/` or `context/`.
- If a claim is empirical/computational, encode it as:
  - Python: compute it and write JSON results.
  - Lean: prove the *discrete mechanism* behind the computation (counts, equalities, invariants),
    and keep the empirical claim scoped to the protocol output.
- Prefer small, named lemmas over monolithic proofs.

## Anchor vs Necessity (Critical Scope Boundary)

This repo distinguishes:
- **Anchor examples:** finite, certified identities/statistics (Monster, mod-1001, etc.).
- **Necessity theorems:** general statements explaining *why* an entire class of tools/structures must exist
  (e.g. Fourier on cycles, character orthogonality, symmetry→conservation via Noether lens).

Rule: expand anchor coverage only when it is tied to a stated mechanism theorem, otherwise it becomes curve fitting.

Scope note (j-function):
- `lean/J_Function_Coefficient_Theorem.lean` treats `jCoefficient` as a pinned data table (OEIS values) and proves exact
  arithmetic identities against it. This is an anchor layer, not a proof of modularity/Hauptmodul theory.

## Planning And Tracking Hygiene

- Keep `LEAN_PROOFS_THEORY_AND_NEXT_STEPS.md` as the canonical step ledger (`N DONE / N+1 NEXT`).
- Keep `PROOF_CONTINUATION_PLAN.md` concise and active-only (current gates, next step, no long historical replay).
- Archive historical plan snapshots under `_archive/2026-02-11_plan_cleanup/` before large plan rewrites.
- Do not maintain duplicate long-form step histories across multiple docs.
- When hardening mode is active, treat `PRIMARY_HARDENING_WORKFLOW.md` as the primary execution workflow and pause theorem-surface expansion.

## Pre-Proof Drift Gate (Run Before New Bridge Claims)

1. Duplicate-scope check:
   - search `LEAN_PROOFS_THEORY_AND_NEXT_STEPS.md`,
   - search existing `*_protocol.py`,
   - search existing `lean/*Protocol_Theorem.lean`.
2. Wiring check:
   - protocol script is listed in `scripts/verify.sh`,
   - theorem is imported by `lean/Layer3_Anchors.lean`.
3. Pipeline check:
   - run `./scripts/verify.sh`,
   - require no `sorry`/`admit`.

If any gate fails, resolve before creating another theorem/script pair.

## Supermemory Operational Notes

- Use supermemory recall/save each session for context continuity.
- Supermemory is **not** an automatic full-transcript recorder; it stores **curated** durable facts/decisions.
  - Pipeline truth is in-repo (`LEAN_PROOFS_THEORY_AND_NEXT_STEPS.md`, `context/cert/*.log`, Lean sources).
  - Use Supermemory to remember the *index* of that truth (what changed, why, and where it lives).
- If strict project tags are unsupported by the MCP schema, use `sm_project_default`
  and include project identity in the memory text/query itself.
- Before long runs or expected context compaction, refresh local compact state:
  - `./scripts/update_coherence_checkpoint.py`
  - output: `context/.coherence_state.min.json`
- After any ledger step increment (`N DONE / N+1 NEXT`), save a Supermemory note with:
  - step number, one-sentence claim, and the primary file paths touched.
  - do **not** store secrets/tokens/keys.

### Supermemory Troubleshooting (When Tools Time Out)

Common failure modes:
- `timed out awaiting tools/call after 60s`: the MCP transport is up but the backend is wedged/unresponsive.
- `Transport closed`: the MCP server process died or the app session lost the transport (usually requires session/app restart).

This repo is configured to use `mcp-remote` (stdio proxy) because `https://mcp.supermemory.ai/mcp`
is not currently compatible with Codex's `streamable_http` transport.

**Check config:**
```bash
codex mcp get supermemory
```

Expected (working) shape:
- `transport: stdio`
- `command: sh`
- `args: -lc KEY=...; npx -y mcp-remote@latest https://mcp.supermemory.ai/mcp --header "Authorization: Bearer $KEY"`

**Hard reset (safe, but requires restarting the Codex chat/app to re-bind tools):**
```bash
codex mcp remove supermemory
codex mcp add supermemory -- sh -lc 'KEY=$(tr -d '\'''\\r\\n '\''' < $HOME/.codex/supermemory_api_key); npx -y mcp-remote@latest https://mcp.supermemory.ai/mcp --header "Authorization: Bearer $KEY"'
```

**Optional: kill stale proxy processes** (only do this if you're about to restart the Codex chat/app,
because it will break the current session transport):
```bash
ps aux | rg -n "mcp-remote https://mcp\\.supermemory\\.ai/mcp" | head
kill <pid> ...
```

**CLI health-check (spawns its own session):**
```bash
cd "<repo>"
codex exec --skip-git-repo-check "Use the supermemory tool whoAmI. Reply with exactly: OK if it succeeds, otherwise FAIL."
```

Local recovery aids (always updated by `./scripts/verify.sh`):
- `context/.coherence_state.min.json` (machine-oriented, low-token)
- `context/SESSION_STATE.md` (human-oriented pointer: DONE/NEXT + latest cert logs)
- `context/ANCHOR_INDEX.md` (human-oriented map: anchor examples -> exact Lean/Python artifacts)

## Multi-Agent Anti-Tunnel Protocol

This repo is intentionally multi-view (arithmetic, harmonic, geometric, modular, physics-bridge).
Single-thread reasoning is a known risk. Use a lane-based workflow:

- `Kernel/Lean lane`: formal discrete core (`lean/Layer0_*`, `lean/Layer1_*`).
- `Bridge lane`: representation equivalences and cross-view mappings (`lean/Layer2_*`).
- `Anchor lane`: Monster/Moonshine/Tn/fine-structure anchors (`lean/Layer3_*`).
- `Physics bridge lane`: Maxwell/Dirac/Yang-Mills draft mapping in `RequestedInfo/` and theory docs.
- `Evidence lane`: computational checks (`*.py` + JSON outputs).

Canonical process:

1. Read `MULTI_AGENT_WORKFLOW.md`.
2. Keep every lane connected to current work via `context/MULTIVIEW_MANIFEST.json`.
3. Run `./scripts/verify.sh` (includes a multi-view context gate).
4. If any lane loses required artifacts or Lean linkage, treat as pipeline failure.

Trust boundaries:

- `lean/` + `context/` are the formal truth surface.
- `*.py` + JSON are empirical/computational evidence.
- `RequestedInfo/`, `_archive/`, and external repos are hypothesis/input sources until translated into formal or computational artifacts.
