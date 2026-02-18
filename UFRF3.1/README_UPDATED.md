# UFRF Updated Package (2025-12-14)

This zip contains the UFRF markdown documents updated to **Version 0.5.2** with *surgical* clarity upgrades (no breaking changes to the 13-position cycle):

- Explicit **Positions vs States** distinction (13 manifest positions + optional 14-state seam chart for recursion/boundary tracking)
- Formal **REST↔VOID** duality and the **Bridge→Seed overlap lemma** (parent COMPLETE 11–13 overlaps child SEED 1–3 under REST-anchored births)
- Removal of informal “log₁” notation (replaced by **Linear chart** `Lin(x)=x`)
- Explicit labeling of **Hypothesis MetaMerge14** as an optional 3→1 merge operator
- **Contextual Birth Rules (REST-anchored gates)**: births occur at REST crossings, optionally filtered by a gate congruence `t mod G in A` (Mathematical Framework §10.8)
- New **Boundary Overlap Test** protocol in Predictions (Bridge→Seed superposition)
- Stronger **anti-numerology guardrails**: charts vs claims, CRT caveats, explicit note on 28

See `CHANGELOG.md` for details.

## Included helper scripts (optional)
- `ufrf_infinite_pattern_validate.py` (brute-force validator; sandbox-safe to 100,000+)
- `ufrf_infinite_pattern_largeN.py` (analytic large-N counts + spot checks for 1e9–1e11+)
- `ufrf_contextual_moduli.py` (CRT/bookkeeping demos)
- `ufrf_contextual_birth_rule.py` (contextual gate family; verifies overlap invariants)

These scripts validate the bookkeeping layer used for recursion/context tracking. They do not by themselves validate the physical claims; they ensure the chart-based formalism is internally consistent and testable.
