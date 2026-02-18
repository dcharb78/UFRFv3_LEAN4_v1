# UFRFv3_LEAN4_v1

Lean4 + Python protocol repo: a kernel-first attempt to formalize **UFRF-style discrete mechanisms**
in Lean, with **computational protocols** (Python scripts + JSON outputs) used as evidence for
finite/empirical claims.

This is intentionally structured around:
- `lean/` and `context/`: the formal “truth surface” (no `sorry`/`admit`).
- `*_protocol.py` + `*_results.json`: bounded computational checks (reproducible).
- `UFRF3.1/`, `RequestedInfo/`: hypothesis / source-material until translated into the above.

## Quick Start (Validation)

1. Python venv:

```bash
python3 -m venv .venv
.venv/bin/pip install -r requirements.txt
```

2. One command (Python protocols + Lean build + repo gates):

```bash
./scripts/verify.sh
```

3. Auditable certification (timestamped logs under `context/cert/`):

```bash
./scripts/certify.sh
./scripts/certify.sh --clean
```

## Where To Start Reading

1. Current status pointer (ledger + latest cert logs):
   - `context/SESSION_STATE.md`
2. Canonical “what is certified / what is next” ledger:
   - `LEAN_PROOFS_THEORY_AND_NEXT_STEPS.md`
3. Kernel-first Lean entry point (smallest “0→1” bundle):
   - `context/UFRF_START_HERE.lean`
4. Kernel explanation (mechanism map + “resolution triad”):
   - `context/UFRF_KERNEL_PROOF_EXPLANATION.md`
5. Full canonical spine explanation (kernel + bridges + anchors):
   - `context/UFRF_UNIFIED_PROOF_EXPLANATION.md`
6. Minimal axiom spine (discrete-first scope boundary):
   - `UFRF_MINIMAL_AXIOM_SPINE.md`
7. Trinitarian narrative spine (theory text mapped to certified artifacts):
   - `context/UFRF_Trinitarian_Spine_v3.md`

## Truth Surface / Scope Boundaries

- `lean/` and `context/` are the formal truth surface.
  - no `sorry`/`admit` are allowed.
- `*_protocol.py` + `*_results.json` are computational evidence (finite checks).
- Theory docs (`UFRF3.1/`, `RequestedInfo/`, etc.) are hypothesis sources until translated into
  certified Lean theorems and/or protocol outputs.

## Multi-Agent Workflow

This project is intentionally multi-view (kernel, bridges, anchors, physics drafts, evidence).
See:

- `MULTI_AGENT_WORKFLOW.md`
- `PRIMARY_HARDENING_WORKFLOW.md`
