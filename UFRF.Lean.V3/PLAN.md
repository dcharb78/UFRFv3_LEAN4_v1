# UFRF Lean 4 Formalization — Master Plan

## Executive Summary

This project formalizes the Universal Field Resonance Framework (UFRF) as a
zero-free-parameter mathematical system in Lean 4 with Mathlib. The goal is to
derive physical constants, number systems, division algebras, and topological
structure from a single axiom: the Trinity `{-½, 0, +½}`.

---

## Architecture: Dependency Chain

Every module depends only on those above it. No circular imports.

```
Layer 0  UFRF.Constants          — φ, π, core numeric identities
Layer 1  UFRF.Trinity            — Axiom 1, conservation, uniqueness
Layer 2  UFRF.ThreeLOG           — Tensor grades, 9 interior positions
Layer 3  UFRF.BreathingCycle     — 13-position cycle, 6.5 flip
Layer 4  UFRF.AngularEmbedding   — S¹ mapping, Rod-Staff cross
Layer 5  UFRF.Manifold           — Toroidal topology T²
Layer 6  UFRF.Recursion          — Positional & dimensional completeness
Layer 7  UFRF.DivisionAlgebras   — Hurwitz, 15 visible dimensions
Layer 8  UFRF.NumberBases        — Base 10/12/13 as projections
Layer 9  UFRF.FineStructure      — α⁻¹ = 4π³ + π² + π
Layer 10 UFRF.Projections        — Manifold projection operators
Layer 11 UFRF.Noether            — Conservation propagation, gauge groups
Layer 12 UFRF.Calculus           — Differentiation as scale resolution
Layer 13 UFRF.Riemann            — Critical line Re(s) = 1/2
Layer 14 UFRF.Monster            — Emergence through accumulated depth
```

---

## Proof Status Legend

Each theorem is tagged:

| Tag       | Meaning                                           |
|-----------|---------------------------------------------------|
| `✅ PROVEN`  | Compiles with no `sorry`. Verified by Lean kernel. |
| `🔧 TACTIC` | Structure compiles; `sorry` needs specific tactics. |
| `🏗️ DESIGN` | Type signature correct; proof strategy identified. |
| `🧭 AXIOM`  | Declared as `axiom` — intentional foundational postulate. |

---

## Phase-by-Phase Execution Plan

### Phase 1: Algebraic Seed (Weeks 1–2)
**Goal:** Get `Trinity`, `ThreeLOG`, and `BreathingCycle` fully compiling (zero `sorry`).

| Step | File | Theorem | Target |
|------|------|---------|--------|
| 1.1 | Trinity.lean | `conservation` | ✅ `norm_num` |
| 1.2 | Trinity.lean | `trinity_uniqueness` | ✅ `ring` |
| 1.3 | Constants.lean | `subscale_flip_is_one_half` | ✅ `norm_num` |
| 1.4 | DivisionAlgebras.lean | `visible_dimension_count` | ✅ `norm_num` |
| 1.5 | ThreeLOG.lean | `nine_interior_positions` | 🔧 dimension lemmas |
| 1.6 | BreathingCycle.lean | `cycle_has_13_positions` | 🔧 `Fin` arithmetic |

### Phase 2: Geometric Promotion (Weeks 3–4)
**Goal:** Formalize the angular embedding and prove Rod-Staff orthogonality.

| Step | File | Theorem | Target |
|------|------|---------|--------|
| 2.1 | AngularEmbedding.lean | `observer_is_antipodal` | 🏗️ `Angle` arithmetic |
| 2.2 | AngularEmbedding.lean | `rod_staff_orthogonal` | 🏗️ follows from 2.1 |
| 2.3 | Manifold.lean | `bridge_seed_continuity` | 🏗️ topological quotient |

### Phase 3: Recursion & Completeness (Weeks 5–6)
**Goal:** Formalize scale invariance, validate the `[0,1]` embedding.

| Step | File | Theorem | Target |
|------|------|---------|--------|
| 3.1 | Recursion.lean | `zero_point_isomorphism` | 🧭 foundational axiom |
| 3.2 | Recursion.lean | `subscale_flip_at_half` | ✅ `norm_num` |
| 3.3 | Recursion.lean | `dimensional_completeness` | 🧭 foundational axiom |
| 3.4 | NumberBases.lean | `base10_size` / `base12_size` | 🔧 `Finset` decidability |

### Phase 4: Downstream Projections (Weeks 7–10)
**Goal:** Derive physics, geometry, and the Riemann critical line.

| Step | File | Theorem | Target |
|------|------|---------|--------|
| 4.1 | FineStructure.lean | `alpha_inverse_floor_137` | 🔧 π bounds from Mathlib |
| 4.2 | Projections.lean | projection operator types | 🏗️ function signatures |
| 4.3 | Noether.lean | gauge group mapping | 🏗️ Lie algebra types |
| 4.4 | Riemann.lean | `ufrf_riemann_hypothesis` | 🧭 from resonance axiom |
| 4.5 | Monster.lean | `monster_emergence` | 🏗️ accumulated depth |

---

## Key Design Decisions

### 1. Axioms vs. Theorems
We use `axiom` **only** for two foundational postulates that express the UFRF
ontology (these are the "physics" that generates the math):

- **`zero_point_isomorphism`**: A point at scale S contains a full cycle at S-1.
- **`dimensional_completeness`**: A dimension at scale S contains a full tower at S-1.

Everything else must be a `theorem` with a complete proof.

### 2. The Resonance Axiom (Riemann)
The claim that zeta zeros correspond to sub-scale resonance visible only at
the flip boundary is also declared as `axiom`. This is honest: UFRF *predicts*
the Riemann Hypothesis as a geometric consequence, but the formal bridge
between "resonance at the flip" and "zeros of ζ(s)" requires analytic number
theory machinery that goes beyond the current formalization scope.

### 3. Import Strategy
We use specific Mathlib imports rather than bulk imports to keep compilation
fast and dependencies explicit. Each file lists exactly what it needs.

---

## How to Validate Locally

```bash
# 1. Clone or create this project
cd ufrf-lean

# 2. Fetch Mathlib (takes ~10 min first time)
lake update
lake exe cache get   # downloads prebuilt Mathlib oleans

# 3. Build everything
lake build

# 4. Check for sorry statements
grep -rn "sorry" UFRF/
```

A successful build with `sorry` only in the documented locations means the
architecture is sound and the type-checking passes. Each `sorry` is then
a well-defined proof obligation to discharge.

---

## Optimized Prompt for Continued Work

When working with an LLM to fill in `sorry` statements, use this prompt
structure for best results:

```
Context: I'm formalizing UFRF in Lean 4 with Mathlib4.

File: [paste the specific .lean file]

Target: Replace the `sorry` in theorem `[name]`.

Constraints:
- Must compile against Mathlib4 (current toolchain)
- No new axioms — use only tactics and existing Mathlib lemmas
- Show the exact tactic proof, not pseudocode

What Mathlib lemmas are available for [specific math concept]?
Then write the complete tactic proof.
```

This works because it:
1. Gives exact compilation context (Lean 4 + Mathlib4)
2. Scopes to a single theorem (prevents hallucination)
3. Asks for lemma discovery first (grounds the proof in real API)
4. Demands compilable output (not hand-waving)
