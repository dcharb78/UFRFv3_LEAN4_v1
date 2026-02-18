# UFRF Unified Proof (Canonical Spine)

## What Is Actually “Lean-Validated” In This Repo

The repo’s validated Lean proofs live under:

- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/` (the Lean library)
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/context/` (stitching / narrative wrappers)

This file explains the *current canonical spine*: which parts are proven, where they live, and how they compose.

Interpretation boundary (important):
- The **kernel** is the certified discrete “0→1 refinement” story (base-13 nesting + rational addressing) together with
  certified multi-axis closure / chart-invariance (concurrency).
- For the kernel-first entry points and the “resolution triad” (`coarseInterval` ↔ `resolveQ` ↔ `floorBin`), see:
  `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/context/UFRF_KERNEL_PROOF_EXPLANATION.md`.
- Monster/Moonshine/mod-1001 are **finite anchor examples** downstream of this kernel (useful stress-tests, not the spine itself).
- These remain anchors until we prove stronger necessity/uniqueness theorems from a minimal seed.
- For the trinitarian narrative spine (theory doc, mapped to certified artifacts), see:
  `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/context/UFRF_Trinitarian_Spine_v3.md`.

The single unified bundle theorem is:

- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/context/UFRF_UNIFIED_PROOF.lean`
  - `UFRFUnified.UFRF_Canonical_Synthesis`

## Proof Spine (Files and Theorems)

### 0. Kernel (0→1 Refinement + Concurrent Charts)

Files:
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Index_Of_Indexes_Theorem.lean`
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Index_Of_Indexes_Subcycle_Fiber_Theorem.lean`
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Index_Of_Indexes_Subintervals_Theorem.lean`
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Multidimensional_Ticks_Theorem.lean`
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Observer_Tick_Axis_Choice_Theorem.lean`
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Observer_Tick_Axis_Family_Theorem.lean`

Kernel entry points (smallest-to-largest):
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/context/UFRF_START_HERE.lean`
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/context/UFRF_KERNEL_PROOF.lean`

What is proven (finite, exact):
- **13-way refinement is structural:** every coarse state has exactly 13 refinements at the next scale
  (`fiber_card_base`), and the refinement fiber’s rational-address image is an explicit 13-point offset set
  (`fiberAddrImage_eq_offsetAddrImage`).
- **0→1 refinement is literal in `[0,1)` addressing:** the join/split equations (`addrQ_join`, `addrQ_split`) and the interval
  bound (`addrQ_join_bounds`) formalize “every interval refines into 13 sub-intervals,” i.e. the `13, 13^2, 13^3, ...` tower as
  refinement depth.
- **The resolution triad is exact:** for any `q ∈ [0,1)`, bin membership, resolved prefix, and the deterministic bin selector are
  equivalent (all in `Index_Of_Indexes_Subintervals_Theorem.lean`):
  - `q ∈ coarseInterval k x ↔ resolveQ k q = addrQ k x`
  - `resolveQ k q = addrQ k x ↔ floorBin k q = x`
  - `q ∈ coarseInterval k x ↔ floorBin k q = x`
- **Concurrency is chart-invariant:** multi-axis closure / orbit invariance depends only on the orbit profile (LCM/gcd laws), not on
  a particular chart choice (`Observer_Tick_*`, `Multidimensional_Ticks_Theorem`).

### 1. Emergence (Concrete Frobenius Equalities)

File:
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Frobenius_Emergence_Theorem.lean`

What is proven (computationally, no placeholders):
- `FrobeniusEmergence.frobenius_5_13 : frobeniusNumber 5 13 = 47`
- `FrobeniusEmergence.frobenius_7_11 : frobeniusNumber 7 11 = 59`
- `FrobeniusEmergence.frobenius_7_13 : frobeniusNumber 7 13 = 71`
- full Level-2 enumeration from the UFRF generators:
  - `FrobeniusEmergence.ufrfGenerators = [3,5,7,11,13]`
  - `FrobeniusEmergence.frobeniusAll ufrfGenerators = [7,11,19,23,23,39,47,59,71,119]`
  - `FrobeniusEmergence.L2Full = [7,11,19,23,39,47,59,71,119]`
  - `FrobeniusEmergence.monsterGenerators ⊆ L2Full`

This is the “Level 1 → Level 2” emergence hook used everywhere else.

### 1b. Monster Selection Rule (Unique AP With Step 12 Inside L2Full)

File:
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Monster_AP12_Filter_Theorem.lean`

What is proven:
- enumerate all triples from `L2Full`,
- filter those that are 3-term arithmetic progressions with common difference 12,
- the unique surviving triple is `[(47,59,71)]`.

### 2. Center Resonance (σ₁ Pattern)

File:
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Sigma1_Pattern_Theorem.lean`

What is proven:
- `MonsterSigma1.sigma1_is_three_times_middle : sigma1 [47,59,71] = 3 * 59`

This is the algebraic “center is distinguished” statement.

### 3. Pattern-of-Patterns Layer (Concurrency + Scale Invariance + Universality)

File:
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Tn_Recurrence_Universality_Theorem.lean`

What is proven:

- **Universality of low-order `Tₙ` closed forms** (depend only on low power sums `σ₁,σ₂,σ₄`).
  - `TnRecurrence.coeff1_formula`, `coeff2_formula`, `coeff3_formula`, `coeff4_formula`
  - `TnRecurrence.T2_formula`, `T3_formula`, `T4_formula`
  - specialized “same formulas for both systems” anchors used in the unified spine:
    - `TnRecurrence.T2_universal_for_ufrf_and_monster`
    - `TnRecurrence.T3_universal_for_ufrf_and_monster`
    - `TnRecurrence.T4_universal_for_ufrf_and_monster`

- **Concurrency / commutativity** (order-invariance).
  - `TnRecurrence.aCoeffs_perm : List.Perm xs ys → aCoeffs xs = aCoeffs ys`

- **Concurrency as an algebraic law on multisets** (independent “sources” compose by multiplication).
  - `TnRecurrence.aCoeffsMS_add : aCoeffsMS (s + t) = mulCoeffs (aCoeffsMS s) (aCoeffsMS t)`

- **Scale invariance / renormalization-style homogeneity**.
  - `TnRecurrence.TnFromGen_scale :
      TnFromGen (map (k*·) gens) n = (k:ℚ)^n * TnFromGen gens n`

These are the strongest “pattern-of-patterns” results currently in Lean: they are not narrative claims, they are explicit algebraic invariants.

### 3b. Exact `Tₙ` (All `n`) + Truncation Coherence

Files:
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Tn_Truncated_Engine.lean`
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Tn_Exact_Definition.lean`
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Tn_Truncation_Coherence.lean`
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Tn_Singleton_ClosedForm.lean`
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Tn_Pair_ClosedForm.lean`

What is proven:
- `TnExact.TnFromMS`: exact `Tₙ` for any multiset of generators and any `n` (no degree-4 cutoff).
- `TnExact.TnFromMS_add`: exact binomial-convolution law under multiset union (formal concurrency law at the `Tₙ` level).
- `TnExact.TnFromGen_scale` / `TnExact.TnFromMS_scale`: exact scale invariance `Tₙ(k·gens) = kⁿ·Tₙ(gens)`.
- `TnExact.TnFromMS_singleton`: closed form for a single generator: `Tₙ({d}) = dⁿ/(n+1)`.
- `TnExact.TnFromMS_pair_singletons`: derived closed form for `{a,b}` as the exact binomial convolution of the singleton law.

### 3c. Fourier Inevitability on the 13-Cycle (Characters Diagonalize Shift + Convolution)

Files:
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Fourier_ZMod_DFT_Translation_Theorem.lean`
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Fourier_ZMod_DFT_Convolution_Theorem.lean`
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Fourier_ZMod_DFT_Inversion_Theorem.lean`
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Fourier_ZMod13_Packaging_Theorem.lean`

What is proven (exact, Mathlib-based):
- On any finite cycle `ZMod N`, for the canonical discrete Fourier transform `ZMod.dft` (`𝓕`) and standard additive character
  `ZMod.stdAddChar`, translation is diagonalized:
  - `FourierZMod.dft_translate : 𝓕 (τ_t Φ) k = stdAddChar (t*k) • 𝓕 Φ k`.
- On any finite cycle `ZMod N`, defining circular convolution `(f ⋆ g)(j) := Σ i, f i * g (j - i)`, convolution is diagonalized:
  - `FourierZMod.dft_conv : 𝓕 (f ⋆ g) k = (𝓕 f k) * (𝓕 g k)`.
- The transform is invertible and has an explicit inverse-transform formula:
  - `FourierZMod.invDFT_apply : 𝓕⁻ Ψ k = (N:ℂ)⁻¹ • Σ j, stdAddChar (j*k) • Ψ j`
  - `FourierZMod.dft_dft : 𝓕 (𝓕 Φ) = fun j => (N:ℂ) • Φ (-j)` (finite-cycle inversion form)
- These are then packaged with stable names for the canonical first-cycle instance `N = 13`:
- `FourierZMod13.dft_translate_13`, `FourierZMod13.dft_conv_13`,
- `FourierZMod13.invDFT_apply_13`, `FourierZMod13.dft_dft_13`.
- These hooks are now explicitly included as conjuncts inside the unified bundle theorem
  `context/UFRF_UNIFIED_PROOF.lean` (`UFRF_Canonical_Synthesis`), so “Fourier inevitability” is part of the certified spine.

Interpretation boundary (important):
- This is not a claim about “the universe must do Fourier”. It is the exact algebraic fact that on a cycle,
  translation symmetry forces the character basis and diagonalizes circular convolution.
  In UFRF terms: if the *state space* is a finite cycle (e.g. the first full 13-position system), then the harmonic/character view
  is not arbitrary; it is the canonical eigenbasis of the shift operator on that cycle.

### 4. Gap-Prime Depletion (Computable Semigroup Gaps)

File:
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Gap_Set_Prime_Theorem.lean`

What is proven:
- UFRF gap set and its prime content (`ufrf_gap_set`, `ufrf_gap_primes`, `ufrf_gap_prime_position`)
- Monster gap-prime residue computation up to a pinned bound
  - `GapSetPrime.position_zero_depleted : count 0 = 1 ∧ total_primes = 143`

This is a concrete “mod 13 residue bias” computation inside Lean.

Seed inevitability add-on (semigroup lens):
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Seed_Inevitability_GapSignature_Theorem.lean`
- If a generator list has **positive gaps** exactly `{1,2,4}`, then the resulting semigroup is forced:
  it coincides with the UFRF seed semigroup generated by `[3,5,7]` (and `[3,5,7]` is minimal in the list sense).
  This is one of the “pattern of patterns” levers: a tiny discrete gap signature uniquely determines the whole closure.

Seed → Frobenius emergence add-on (selection-lens nonredundancy):
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Seed_To_Frobenius_Emergence_Bridge_Theorem.lean`
- In the semigroup lens, `11` and `13` are redundant because `[3,5,7]` already reaches them.
  In the *Frobenius/AP(12) emergence* lens, they are nonredundant: removing either destroys the unique AP(12) triple.
  Concretely:
  - seed-only `[3,5,7]` yields `ap12Triples = []`,
  - adding only one of `{11,13}` still yields `ap12Triples = []`,
  - only the full list `[3,5,7,11,13]` yields `ap12Triples = [(47,59,71)]`.

Discrete angular-embedding quotient add-on (antipodal observer identification ⇒ 3 classes):
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Angular_Embedding_Discrete_Quotient_Theorem.lean`
- What is proven (finite, exact):
  - model 4 quadrants as `Fin 4`,
  - identify the antipodal observer positions by kernel-equating `0` and `2`,
  - the induced quotient has exactly 3 equivalence classes:
    `AngularEmbeddingDiscreteQuotient.angular_embedding_discrete_summary`.

### 5. Riemann Zeros vs A-Zero Lattices (Computable Distance Check)

File:
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Riemann_Zero_Exclusion_Theorem.lean`

What is proven:
- `RiemannZeroExclusion.computed_stats` (lattice sizes, mean distances, “within 0.05” counts)
- Stability checks against lattice truncation (`lattice_truncation_stable`)
- A truncation-effect witness (too-small lattices inflate mean nearest-lattice distances):
  - `RiemannZeroExclusion.lattice_truncation_inflates_mean`

### 6. Moonshine Anchor (j-Function Coefficient)

File:
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/J_Function_Coefficient_Theorem.lean`

What is proven:
- `JFunctionCoefficient.j_coefficient_c1_equals_product_plus_one`
- `JFunctionCoefficient.synthesis_complete` (bundle around `c₁ = 196884`, product `= 196883`, and `+1`)

Interpretation boundary (important):
- This is an **anchor example**: an exact arithmetic identity tying one canonical modular-object
  coefficient (`j`’s `c₁`) to the Monster triple product-plus-one.
- This repo does **not** claim “Moonshine is the rule forever” from this hook alone. The goal is to
  formalize the *shared discrete mechanisms* (closure, recursion, modular coordinates) so that
  inevitability-style claims can be stated precisely and tested on additional instances.

### 7. Screenshot Anchors (Cube Identities)

File:
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Unity_Cube_Identities.lean`

What is proven:
- `(3^3) % 13 = 1` (mod-13 “return to source” anchor)
- `2^3 - 1 = 7` (the “flip” value)
- `φ^3 = 2φ + 1` in `Real` using Mathlib's `Real.goldenRatio`

### 7b. Screenshot Anchors (Catalan 42)

File:
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Catalan_42_Theorem.lean`

What is proven:
- `catalan 5 = 42` (Mathlib Catalan number; “42 valid architectures” anchor)
- the Catalan self-similar recurrence in antidiagonal form:
  - `UnityCatalan.catalan_fractal_recurrence : catalan (n+1) = ∑_{i+j=n} catalan i * catalan j`

### 7c. Screenshot / Idea Anchors (Universal Ticks)

File:
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Universal_Ticks_Theorem.lean`

What is proven:
- base-10 decade shift:
  - `UniversalTicks.decade_mul10 : decade (n*10) = decade n + 1` (for `n ≠ 0`)
- scale invariance under powers of 10:
  - `UniversalTicks.leadingBlock_mul_pow10 : leadingBlock (n*10^k) = leadingBlock n` (for `n ≠ 0`)

### 7d. Screenshot / Idea Anchors (Fibonacci Seed Identities)

File:
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Fibonacci_Seed_Monster_Theorem.lean`

What is proven:
- exact (non-interpretive) equalities tying Monster numbers to Fibonacci-derived factors:
  - `(F4+F2)*(F7-F2)-1 = 47`
  - `(F5+F2)*(F6+F3)-1 = 59`
  - `(F5+F2)*(F7-F2)-1 = 71`

### 7e. Screenshot / Idea Anchors (Decimal / Mod-13 Concurrency)

File:
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Decimal_Mod13_Concurrency_Theorem.lean`

What is proven:
- `10^6 % 13 = 1`
- `∀ n, (n * 10^6) % 13 = n % 13`
- half-period “flip” facts:
  - `10^3 % 13 = 12` (i.e. `10^3 ≡ -1 (mod 13)`)
  - `∀ n, ((n * 10^3) + n) % 13 = 0`  (equivalently: `n*10^3 ≡ -n (mod 13)`)

Interpretation:
- multiplying by `10^6` is a concrete “return to the same 13-cycle position” operation in base-10 scaling.
- multiplying by `10^3` is a concrete “flip” (order-2) operation on the mod-13 coordinate, and applying it twice
  gives the 6-decade return.

### 7e'. Screenshot / Idea Anchors (Decimal / Mod-1001 Concurrency)

File:
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Decimal_Mod1001_Concurrency_Theorem.lean`

What is proven:
- exact arithmetic skeleton (no empirical claims):
  - `10^3 + 1 = 1001` and therefore `∀ n, (n*10^3 + n) % 1001 = 0`,
  - `10^6 ≡ 1 (mod 1001)` and therefore `∀ n, (n*10^6) % 1001 = n % 1001`,
  - an explicit “emergent concurrency” derivation of the return from the coprime prime axes `7,11,13`.

Interpretation boundary (important):
- `1001` is treated as an **anchor example** of coprime-axis composition (systems become nodes of other systems),
  not as a universal modulus.

### 7f. Idea Anchors (Multidimensional Ticks: Base-10 + Multiple Mod Axes)

File:
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Multidimensional_Ticks_Theorem.lean`

What is proven:
- A single exact update law for base-10 ticks: `(n * 10^k) % m` evolves by multiplication with `10^k % m`.
- General periodicity when `gcd(10,m)=1` (Euler totient):
  - `10^φ(m) % m = 1` and hence `(n * 10^φ(m)) % m = n % m` (for `1 < m` and `10.Coprime m`)
- Observer-scale view (internal perspective):
  - for any `m` with `gcd(10,m)=1` and any tick-length `k`, multiplication by `10^k` is a **permutation** of `ZMod m`
    (`tick10_zmod_bijective`).
  - This is the discrete “no information loss on an invertible axis” statement; exact *return* is the special case when the
    permutation is the identity (e.g. at `k = φ(m)` or the true multiplicative order).
- Combined-coordinate return (log-axis + modular axis):
  - at tick `φ(m)`, `leadingBlock` is unchanged and the residue mod `m` returns together
    (`tick10_totient_invariant_leadingBlock_and_mod`)
- Multi-axis concurrency:
  - at tick `lcm(φ(m₁), φ(m₂))`, residues return simultaneously mod `m₁` and mod `m₂`
    (`tick10_mod_invariant_lcm_totients`)
- Finite-family concurrency (concurrent nesting):
  - define `totientLCM ms = lcm_{m∈ms} φ(m)`
  - at tick `totientLCM ms`, residues return simultaneously on every axis `mod m` for all `m ∈ ms`
    (`tick10_totientLCM_invariant_leadingBlock_and_mods`)
- System-node packaging:
  - define `systemCoord ms n = (leadingBlock n, ms.map (fun m => n % m))`
  - at tick `totientLCM ms`, the entire packaged coordinate is invariant
    (`systemCoord_invariant_at_totientLCM`)
- System composition:
  - `totientLCM (ms₁ ++ ms₂) = lcm (totientLCM ms₁) (totientLCM ms₂)` (`totientLCM_append`)
  - `systemCoord` respects append (`systemCoord_append`)
  - combined systems can be proven invariant at the combined tick
    (`systemCoord_invariant_at_lcm_subsystems`)
- Concrete axis examples (all as exact theorems, no placeholders):
  - mod 3 returns every decade: `(n*10) % 3 = n % 3`
  - mod 2 absorbs after 1 decade: `(n*10) % 2 = 0`
  - mod 5 absorbs after 1 decade: `(n*10) % 5 = 0`
  - mod 11 returns every 2 decades: `(n*10^2) % 11 = n % 11`
  - mod 13 returns every 6 decades: `(n*10^6) % 13 = n % 13`
  - mod 4 absorbs after 2 decades: `(n*10^2) % 4 = 0`
- General absorption thresholds (base-10 carries 2/5 factors):
  - mod `2^a` absorbs after `a` decades:
    - `tick10_mod_pow2_absorbs : (tick10 k n) % (2^a) = 0` whenever `a ≤ k`
  - mod `5^a` absorbs after `a` decades:
    - `tick10_mod_pow5_absorbs : (tick10 k n) % (5^a) = 0` whenever `a ≤ k`
- One global tick that does **both** return and absorption (concurrent “cycle + convergence”):
  - define `globalTick ms a₂ a₅ := totientLCM ms * (max a₂ a₅ + 1)`
  - at tick `globalTick ms a₂ a₅` (for `n ≠ 0` and axes `m ∈ ms` with `1 < m` and `gcd(10,m)=1`):
    - `leadingBlock` is invariant,
    - every residue mod `m ∈ ms` returns,
    - and the absorption axes collapse: mod `2^a₂ = 0` and mod `5^a₅ = 0`.
    (`tick10_globalTick_return_and_absorb`)
- Mixed observer-state packaging:
  - define `systemCoordMixed ms a₂ a₅ n = (leadingBlock n, residues(ms,n), n % 2^a₂, n % 5^a₅)`
  - at tick `globalTick ms a₂ a₅`, this collapses to `(leadingBlock n, residues(ms,n), 0, 0)`
    (`systemCoordMixed_invariant_at_globalTick`)
- Period alignment tools:
  - “return every k ticks implies return every multiple of k”
  - `lcm`-based alignment lemmas (shared return ticks across axes)

### 7g. Idea Anchors (Spherical Harmonic Counting Skeleton)

File:
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Spherical_Harmonic_Breathing_Theorem.lean`

What is proven (exact arithmetic):
- The standard mode-counting identities:
  - modes at degree `ℓ` are `2ℓ+1`
  - total modes through degree `ℓ` are `(ℓ+1)^2`
- UFRF `13` anchors as specializations of the counting skeleton:
  - flip row at `ℓ=6` has `13` modes
  - through `ℓ=12` (13 rows) total modes are `13^2 = 169`
  - through `ℓ=168` (169 rows) total modes are `13^4 = 28561`
- A two-axis “conserved complexity” bookkeeping identity:
  - for `m ≤ ℓ`, `(ℓ-m) + m = ℓ`

Important scope note:
- This module does **not** formalize analytic spherical harmonics as functions; it formalizes the counting skeleton and its
  exact numerical consequences used as UFRF “anchors”.

### 7h. Idea Anchors (Index-Of-Indexes: Discrete Nesting for 13, 169, 2197, ...)

File:
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Index_Of_Indexes_Theorem.lean`

What is proven:
- define the structural node counts as powers: `SL k := 13^k`
  - `SL 2 = 169`
  - `SL 3 = 2197`
- the key structural nesting equivalence:
  - `Fin (13^(k+1)) ≃ Fin (13^k) × Fin 13` (`splitEquiv`)
  - plus the inverse laws `join_split` / `split_join`

Interpretation:
- the “index of indexes” structure is discrete and exact.
- it gives a canonical way to treat `SL1=169` as `13×13` (and higher scales similarly), independent of any geometric-time
  embedding or sampling scheme.

## Noether Lens (Symmetry = Conservation, Discrete)

This repo currently encodes “Noether” in the *discrete* sense:

- **Symmetry** is an update/transform on state (tick advance, chart change, conjugation, flip).
- **Conservation** is an observation/quantity that is invariant under that transform.
- The key formal move: *one-step invariance implies invariance at every iterate*.

Core lemma (generic, reusable):
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Noether_Symmetry_Conservation_Lens_Theorem.lean`
  - `NoetherDiscrete.conserved_iterate`

Concrete instantiations already in the proof surface:
- Observer/tick invariance kernels (closure events don’t depend on chart choice):
  - `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Observer_Tick_Axis_Choice_Theorem.lean`
  - `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Aspect_Projection_Kernel_Theorem.lean`
- Discrete gauge invariance (finite Wilson-loop analogue: trace invariant under conjugation):
  - `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Pauli_Quaternion_Q8_Gauge_Invariance_Protocol_Theorem.lean`
    - strengthened to all `2×2` matrices as `q8_tr2_conj_invariant_all`
    - iterate conservation as `q8_tr2_conj_conserved_iterate`

Interpretation boundary:
- These are exact invariance/conservation statements in a finite algebraic setting.
- Mapping them to continuum physics Noether statements is a *bridge task* (not assumed in Lean).

## Unified Bundle

File:
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/context/UFRF_UNIFIED_PROOF.lean`

What it does:
- Imports the canonical proof modules above.
- States one conjunction theorem:
  - `UFRFUnified.UFRF_Canonical_Synthesis`
- Proves it by *only* referencing already-proved theorems (no new axioms).

## Deprecated: Aristotle Outputs (What They Are)

Folder:
- `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/aristotle/`

Those files are useful as idea sketches, but many encode desired properties as assumptions.
They are intentionally not imported by the Lean library.

## How To Validate

Run the full end-to-end check:

```bash
cd "/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine"
./scripts/verify.sh
```
