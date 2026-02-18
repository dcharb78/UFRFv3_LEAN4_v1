# Anchor Index (Certified Examples, Not Universal Claims)

Purpose: one place to find the exact artifacts (Lean + Python + JSON) behind the key **anchor examples** we reference in UFRF discussions.

Interpretation boundary:
- These are **certified, finite, deterministic** examples.
- They are **not** claimed as “the rule forever” without additional theory+proof work.
- For the unified proof spine and how anchors fit the multi-view story, see `context/UFRF_UNIFIED_PROOF_EXPLANATION.md`.

Recommended reading order (to stay kernel-first):
- Start with the **Nested Tick / Index-of-Indexes** anchors (0→1 refinement, `13^k` nesting).
- Then read the **multiaxis / concurrency** anchors (systems-as-nodes composition).
- Treat Monster/Moonshine/mod-1001 as downstream anchors that exercise the kernel.

## How To Validate

- Fast validation (Python protocols + Lean build):
  - `./scripts/verify.sh`
- Auditable validation (timestamped logs):
  - `./scripts/certify.sh`
  - `./scripts/certify.sh --clean`

## Monster / Moonshine Anchor

Claim shape (finite): the Monster triple `{47,59,71}` (as a UFRF-emergent AP(12) triple) deterministically yields:
- `47 * 59 * 71 + 1 = 196884` (the classical moonshine “c₁” anchor)

Artifacts:
- Python:
  - `monster_pair_origin_uniqueness_protocol.py` -> `monster_pair_origin_uniqueness_results.json`
  - `monster_ap12_uniqueness_protocol.py` -> `monster_ap12_uniqueness_results.json`
  - `monster_source_ap12_inevitability_protocol.py` -> `monster_source_ap12_inevitability_results.json`
  - `moonshine_inevitability_chain_protocol.py` -> `moonshine_inevitability_chain_results.json`
  - `moonshine_inevitability_from_source_protocol.py` -> `moonshine_inevitability_from_source_results.json`
  - `j_qexp_from_delta_e4_protocol.py` -> `j_qexp_from_delta_e4_results.json`
  - `j_function_coefficient_theorem.py` -> `j_function_coefficient_results.json`
- Lean (imported by `lean/Layer3_Anchors.lean`):
  - `lean/Monster_Pair_Origin_Uniqueness_Protocol_Theorem.lean`
  - `lean/Monster_AP12_Uniqueness_Protocol_Theorem.lean`
  - `lean/Monster_Source_AP12_Inevitability_Protocol_Theorem.lean`
  - `lean/Moonshine_Inevitability_Chain_Protocol_Theorem.lean`
  - `lean/Moonshine_Inevitability_From_Source_Protocol_Theorem.lean`
  - `lean/Moonshine_Inevitability_From_UFRF_Theorem.lean` (∃! inevitability statement inside the discrete pipeline)
  - `lean/J_Function_Coefficient_Theorem.lean`
  - `lean/J_Qexp_From_Delta_E4_Protocol_Theorem.lean`

## mod-1001 Anchor (Decimal Cube Flip / Return)

Claim shape (finite): `1001 = 7 * 11 * 13` is the unique “full concurrent axis closure” modulus among the decimal cube-flip divisors under our stated constraints, and it exhibits:
- `10^3 ≡ -1 (mod 1001)`
- `10^6 ≡  1 (mod 1001)`

Artifacts:
- Python:
  - `mod1001_composite_cycle_protocol.py` -> `mod1001_composite_cycle_results.json`
  - `mod1001_inevitability_protocol.py` -> `mod1001_inevitability_results.json`
  - `mod1001_order_decomposition_protocol.py` -> `mod1001_order_decomposition_results.json`
  - `monster_mod1001_order_classes_protocol.py` -> `monster_mod1001_order_classes_results.json`
- Lean (imported by `lean/Layer3_Anchors.lean`):
  - `lean/Mod1001_Composite_Cycle_Protocol_Theorem.lean`
  - `lean/Mod1001_Inevitability_Protocol_Theorem.lean`
  - `lean/Mod1001_Order_Decomposition_Protocol_Theorem.lean`
  - `lean/Monster_Mod1001_Order_Classes_Protocol_Theorem.lean`
  - `lean/Decimal_Mod1001_Concurrency_Theorem.lean`

## Fine Structure (π-Polynomial Intrinsic Anchor)

Claim shape (finite, math-only anchor):
- Define the candidate intrinsic value `α⁻¹_candidate := 4π^3 + π^2 + π`.
- Using mathlib-certified `π` bounds, prove stable numeric anchoring (e.g. 9-decimal rounding) and the integer floor anchor `⌊α⁻¹_candidate⌋ = 137`.

Artifacts:
- Python:
  - `fine_structure_alpha_intrinsic_protocol.py` -> `fine_structure_alpha_intrinsic_results.json`
  - `fine_structure_alpha_projection_protocol.py` -> `fine_structure_alpha_projection_results.json`
- Lean (imported by `lean/Layer3_Anchors.lean`):
  - `lean/Fine_Structure_Internal_Consistency_Theorem.lean` (math-only bracket + floor anchor, measured-ref comparison)
  - `lean/UFRF_Core_DualTrinity_FineStructure_Theorem.lean` (discrete dual-trinity -> candidate bridge)
  - `lean/Fine_Structure_Alpha_Intrinsic_Protocol_Theorem.lean` (tight `d20` π-bracket -> 9-decimal rounding stability)
  - `lean/Fine_Structure_Alpha_Projection_Protocol_Theorem.lean` (ratio-first correction scaffold -> `α⁻¹_proj` within `1e-8` of measured reference)

## Riemann Zero Lattice Distance (Finite Evidence)

Claim shape (finite): in the corrected computation, the Monster lattice is denser and produces smaller mean nearest-lattice distances (density-consistent) on the chosen finite window.

Artifacts:
- Python:
  - `riemann_zero_exclusion_corrected.py` -> `riemann_zero_exclusion_results.json`
- Lean (imported by `lean/Layer3_Anchors.lean`):
  - `lean/Riemann_Zero_Exclusion_Theorem.lean`

## Projection Law (v3 Tensor Form, Finite Check)

Claim shape (finite): consistency checks on a specific numeric instance of the tensor projection law v3 scaffold.

Artifacts:
- Python:
  - `tensor_projection_law_v3_protocol.py` -> `tensor_projection_law_v3_results.json`
  - `projection_versions_reduction_protocol.py` -> `projection_versions_reduction_results.json`
  - `projection_tensor_rowsum_scalar_bridge_protocol.py` -> `projection_tensor_rowsum_scalar_bridge_results.json`
- Lean:
  - `lean/Tensor_Projection_Law_V3_Protocol_Theorem.lean`
  - `lean/Projection_Versions_Reduction_Protocol_Theorem.lean`
  - `lean/Projection_Tensor_Rowsum_Scalar_Bridge_Protocol_Theorem.lean`

## Nested Tick / Index-of-Indexes (Finite Bridge)

Claim shape (finite): discrete “index-of-indexes” carry/return and decimal-nesting closures under explicit assumptions.

Artifacts:
- Python:
  - `decimal_nested_tick_projection_protocol.py` -> `decimal_nested_tick_projection_results.json`
- Lean:
  - `lean/Decimal_Nested_Tick_Projection_Protocol_Theorem.lean`
  - `lean/RecursiveGrid_IndexOfIndexes_Bridge_Theorem.lean`

## Observer/Cycle Residue-Class Bridge (Mechanism Discoverability)

Claim shape (finite mechanism bridge): decimal observer rendering (`0..9`) and mod-13 cycle position
remain concurrent but distinct lenses; for tick-based composed entry points, cycle shifts normalize by
`d mod 6` via the observer/cycle API.

Breathing-cycle phase partition (mechanism-only):
- A bounded discrete partition of `Fin 13` into:
  - LOG blocks (`1..3`, `4..6`, `7..9`),
  - REST (`10`),
  - bridge/return tail (`11,12,0`),
  plus a 26-cycle half-step witness of the midpoint between `6` and `7`.
- Also available: a 4-block overlap-window decomposition
  (`{1,2,3,4}`, `{4,5,6,7}`, `{7,8,9,10}`, `{10,11,12,0}`) with shared checkpoints `{4,7,10}`.
- Also available: a digit→phase lens `Fin 13 → Phase` that is total + deterministic
  (every digit belongs to exactly one of `LOG1/LOG2/LOG3/REST/BRIDGE`).
- Also available: phase successor dynamics (`succ13`) showing `phaseOf` is constant off a small
  boundary set, with an explicit boundary transition table.
- Also available: a multi-axis phase lift to `Digits k` coordinates (`13^k` states),
  with per-axis counting independence (mechanism-only).
- Also available: the same phase-counting statement transported back to the canonical
  `Fin (13^k)` view via `digitsEquiv` (mechanism-only).
- Also available: a phase lens ↔ recursive-grid digit bridge showing the canonical
  `phaseAtFin` lens equals `phaseOf` applied to `RecursiveGridBase13.digit` (mechanism-only).
- Also available: phase lens projection compatibility showing the natural prefix projection
  `Fin (13^(k+1)) → Fin (13^k)` (via `digitsEquiv`) commutes with `phaseAtFin` (mechanism-only).
- Also available: phase successor lift with carry: under global successor `succSL` on `Fin (13^k)`,
  depth-0 evolves by `succ13` and the prefix projection updates iff the carry boundary `x % 13 = 12`
  (mechanism-only).
- Also available: general carry-chain successor lift on prefixes: dropping `d` least-significant digits
  via `prefixFinPow : Fin (13^(k+d)) → Fin (13^k)` updates under successor exactly at the carry-chain
  boundary `13^d ∣ t + 1` (equivalently `t % 13^d = 13^d - 1`) (mechanism-only).

Refinement→phase lens (mechanism-only):
- For every scale level `k` and every coarse node `x : Fin (13^k)`, the refinement fiber over `x`
  sees the same phase census (`3,3,3,1,3`) under the digit→phase lens.

REST seam bookkeeping collapse (mechanism-only):
- Collapse `state ∈ {0..13}` (seam bookkeeping, `mod 14`) to `state mod 13`, so `13 ↦ 0`.
- Under the REST seam overlap, parent COMPLETE `{11,12,13}` collapses to `{11,12,0}`.

Artifacts:
- Python:
  - `observer_digits_cycle_position_protocol.py` -> `observer_digits_cycle_position_results.json`
  - `observer_digits_cycle_periodicity_protocol.py` -> `observer_digits_cycle_periodicity_results.json`
- Lean:
  - `lean/Index_Of_Indexes_Subcycle_Fiber_Theorem.lean`
    - `IndexOfIndexesSubcycle.RefinementPhaseLens.refinement_phase_lens`
  - `lean/Breathing_Cycle_LOG_Partition_Theorem.lean`
    - `BreathingCycleLOGPartition.breathing_cycle_log_checkpoint_partition`
    - `BreathingCycleLOGPartition.overlap_window_decomposition`
    - `BreathingCycleLOGPartition.digit_phase_lens`
    - `BreathingCycleLOGPartition.phase_successor_dynamics`
  - `lean/REST_Seam_Overlap_Theorem.lean`
    - `RESTSeamOverlap.collapse13_parentComplete_in_bridge`
  - `lean/Multi_Axis_Phase_Lift_Theorem.lean`
    - `MultiAxisPhaseLift.multi_axis_phase_lift`
    - `MultiAxisPhaseLift.multi_axis_phase_lift_fin`
    - `MultiAxisPhaseLift.phaseAtFin_recursive_digit_bridge`
    - `MultiAxisPhaseLift.phaseAtFin_projection_compat`
    - `MultiAxisPhaseLift.phase_successor_lift_with_carry`
    - `MultiAxisPhaseLift.prefixFinPow_succSL_eq_ite_dvd`
    - `MultiAxisPhaseLift.prefixFinPow_succSL_eq_ite_dvd_all`
    - `MultiAxisPhaseLift.basePow_dvd_succ_iff_mod_eq_pred`
    - `MultiAxisPhaseLift.prefixFinPow_succSL_eq_ite_mod`
    - `MultiAxisPhaseLift.prefixFinPow_succSL_eq_ite_mod_all`
    - `MultiAxisPhaseLift.basePow_mod_eq_pred_iff_tailReturn`
    - `MultiAxisPhaseLift.basePow_mod_eq_pred_iff_tailReturn_all`
    - `MultiAxisPhaseLift.basePow_mod_eq_pred_iff_tailReturnDigits`
    - `MultiAxisPhaseLift.basePow_mod_eq_pred_iff_tailReturnDigits_all`
    - `MultiAxisPhaseLift.prefixFinPow_succSL_eq_ite_tailReturnDigits`
    - `MultiAxisPhaseLift.prefixFinPow_succSL_eq_ite_tailReturnDigits_all`
  - `lean/Observer_Digits_CyclePosition_Bridge_Theorem.lean`
  - `lean/Observer_Digits_Cycle_Position_Protocol_Theorem.lean`
  - `lean/Observer_Digits_Cycle_Periodicity_Protocol_Theorem.lean`
  - `lean/Observer_Digits_Cycle_Periodicity_Bridge_Theorem.lean`
  - `lean/Observer_Cycle_Bridge_API_Theorem.lean`
  - `lean/Composed_Tick_API_Theorem.lean`
  - `lean/Kernel_Observer_Cycle_Stitch_Theorem.lean`
    - stitched canonical wrappers:
      - `KernelObserverCycleStitch.kernel_refinement_zero_canonical`
      - `KernelObserverCycleStitch.kernel_cycle_class_0_6`
      - `KernelObserverCycleStitch.kernel_observer_cycle_package_0_6`
      - `KernelObserverCycleStitch.kernel_observer_cycle_smoke_1`
  - `lean/Trinitarian_Kernel_Proxy_Package_Theorem.lean`
    - packaged kernel proxy:
      - `TrinitarianKernelProxyPackage.trinitarian_kernel_proxy_package`
  - `context/UFRF_START_HERE.lean`
    - pointer hook:
      - `UFRFStartHere.UFRF_Start_Here_observer_cycle_pointer`
      - `UFRFStartHere.UFRF_Start_Here_kernel_only_entry`
      - `UFRFStartHere.UFRF_Start_Here_trinitarian_kernel_proxy_pointer`
      - `UFRFStartHere.UFRF_Start_Here_breathing_cycle_partition_pointer`
      - `UFRFStartHere.UFRF_Start_Here_overlap_window_decomposition_pointer`
      - `UFRFStartHere.UFRF_Start_Here_digit_phase_lens_pointer`
      - `UFRFStartHere.UFRF_Start_Here_refinement_phase_lens_pointer`
      - `UFRFStartHere.UFRF_Start_Here_phase_successor_dynamics_pointer`
      - `UFRFStartHere.UFRF_Start_Here_multi_axis_phase_lift_pointer`
      - `UFRFStartHere.UFRF_Start_Here_multi_axis_phase_lift_fin_pointer`
      - `UFRFStartHere.UFRF_Start_Here_phaseAtFin_recursive_digit_bridge_pointer`
      - `UFRFStartHere.UFRF_Start_Here_phaseAtFin_projection_compat_pointer`
      - `UFRFStartHere.UFRF_Start_Here_phase_successor_lift_with_carry_pointer`
      - `UFRFStartHere.UFRF_Start_Here_prefixFinPow_succSL_carry_chain_pointer`
      - `UFRFStartHere.UFRF_Start_Here_prefixFinPow_succSL_carry_chain_mod_pointer`
      - `UFRFStartHere.UFRF_Start_Here_carry_chain_boundary_digit_tail_pointer`
      - `UFRFStartHere.UFRF_Start_Here_carry_chain_boundary_digitsEquiv_tail_pointer`
      - `UFRFStartHere.UFRF_Start_Here_prefixFinPow_succSL_carry_chain_tailDigits_pointer`
      - `UFRFStartHere.UFRF_Start_Here_seam_collapse_bridge_pointer`
      - `UFRFStartHere.UFRF_Start_Here_prism_compression_pointer`
      - `UFRFStartHere.UFRF_Start_Here_prism_smoke_bundle_pointer`
      - `UFRFStartHere.UFRF_Start_Here_onboarding_pointer_bundle`
      - `UFRFStartHere.UFRF_Start_Here_onboarding_api_entry`
      - `UFRFStartHere.UFRF_Start_Here_unified_entry_bundle`
      - `UFRFStartHere.UFRF_Start_Here_unified_entry_api`
      - `UFRFStartHere.UFRF_Start_Here_unified_api_smoke_bundle`
      - `UFRFStartHere.UFRF_Start_Here_master_entry_alias`
      - `UFRFStartHere.UFRF_Start_Here_master_entry_smoke_alias`
      - `UFRFStartHere.UFRF_Start_Here_root_discoverability_alias`
      - `UFRFStartHere.UFRF_Start_Here_root_entry_smoke_endpoint`
      - `UFRFStartHere.UFRF_Start_Here_canonical_root_entry_alias`
      - `UFRFStartHere.UFRF_Start_Here_root_entry_final_smoke_alias`
      - `UFRFStartHere.UFRF_Start_Here_canonical_endpoint_alias`
      - `UFRFStartHere.UFRF_Start_Here_canonical_endpoint_smoke_package_alias`

## Prime-Choreography Autocorrelation (Finite Evidence)

Claim shape (finite, toy model): in a deterministic prime-period superposition model (single piecewise waveform on the
13-cycle, period = `13·p` per oscillator), the *relative dominance* of multiples-of-13 autocorrelation lags differs
between the prime set that includes the “fundamental” `p=1` and a nearby conventional set using `p=2` instead.

This is evidence-only: it is not yet a theorem about primes; it is a repeatable finite check that can drive future
formalization choices (e.g. waveform definition, what “carrier” should mean in discrete terms).

Artifacts:
- Python:
  - `prime_choreography_autocorr_protocol.py` -> `prime_choreography_autocorr_results.json`
- Lean:
  - `lean/Prime_Choreography_Autocorr_Protocol_Theorem.lean`

## PRISM Mechanism Summaries (Finite, Bounded)

Claim shape (finite): bounded mechanism checks now include:
- prime-choreography discriminant separation (degenerate uniform vs scrambled non-uniform),
- witness-order behavior for `2` on `13^k` for fixed `k=1..4`,
- complement-vs-inverse asymmetry (digit-local complement vs carry-coupled additive inverse) for fixed `k=2,3`,
- bounded projection compatibility across quotient maps `Z/(13^k) -> Z/(13^(k-1))`
  for operations `{succ, pred, neg, comp}` on fixed `k=2,3,4`.

Artifacts:
- Python:
  - `prime_choreography_discriminant_protocol.py` -> `prime_choreography_discriminant_results.json`
  - `prism_primitive_root_order_protocol.py` -> `prism_primitive_root_order_results.json`
  - `prism_complement_vs_inverse_protocol.py` -> `prism_complement_vs_inverse_results.json`
  - `prism_projection_compatibility_protocol.py` -> `prism_projection_compatibility_results.json`
- Lean:
  - `lean/Prime_Choreography_Discriminant_Protocol_Theorem.lean`
  - `lean/Prism_Primitive_Root_Order_Protocol_Theorem.lean`
  - `lean/Prism_Complement_Vs_Inverse_Protocol_Theorem.lean`
  - `lean/Prism_Projection_Compatibility_Protocol_Theorem.lean`
  - `lean/Prism_Observer_Bridge_API_Theorem.lean` (bounded PRISM↔observer packaging)
  - `lean/Prism_Observer_WorkedClass_API_Theorem.lean` (bounded `d mod 6` worked-class wrappers)
  - `lean/Prism_Observer_SeamClass_Bridge_Theorem.lean` (bounded worked-class ↔ seam/global-tick composition)
  - `lean/Prism_Observer_ClassSeam_Index_API_Theorem.lean` (single-entry index wrapper over class+seam packages)
  - `lean/Prism_Observer_Index_Adoption_API_Theorem.lean` (bounded adoption wrapper linking class-seam index to composed-tick smoke entrypoints)
  - `lean/Prism_Observer_Discoverability_Compression_API_Theorem.lean` (single compact smoke-pointer wrapper over worked/seam/index/adoption PRISM packages, including canonical entry `PrismObserverDiscoverabilityCompressionAPI.prism_observer_discoverability_smoke_bundle_entry`)
  - `lean/Prism_Summary_API_Theorem.lean` (discoverability wrappers/bundle only)

## Dirac Clifford (Physics Bridge, Finite Algebra)

Claim shape (finite, exact): the standard Dirac gamma matrices satisfy the Clifford anticommutator exactly:
`{γ^μ, γ^ν} = 2 η^{μν} I` with metric `diag(1,-1,-1,-1)`.

Artifacts:
- Python:
  - `dirac_clifford_anticommutator_protocol.py` -> `dirac_clifford_anticommutator_results.json`
  - `dirac_factorization_scaled_protocol.py` -> `dirac_factorization_scaled_results.json`
  - `pauli_quaternion_bridge_protocol.py` -> `pauli_quaternion_bridge_results.json`
  - `pauli_quaternion_q8_closure_protocol.py` -> `pauli_quaternion_q8_closure_results.json`
  - `pauli_quaternion_su2_commutator_protocol.py` -> `pauli_quaternion_su2_commutator_results.json`
  - `pauli_quaternion_q8_gauge_invariance_protocol.py` -> `pauli_quaternion_q8_gauge_invariance_results.json`
- Lean (imported by `lean/Layer3_Anchors.lean`):
  - `lean/Dirac_Clifford_Anticommutator_Protocol_Theorem.lean`
  - `lean/Dirac_Factorization_Scaled_Protocol_Theorem.lean`
  - `lean/Pauli_Quaternion_Bridge_Protocol_Theorem.lean`
  - `lean/Pauli_Quaternion_Q8_Closure_Protocol_Theorem.lean`
  - `lean/Pauli_Quaternion_SU2_Commutator_Protocol_Theorem.lean`
  - `lean/Pauli_Quaternion_Q8_Gauge_Invariance_Protocol_Theorem.lean`

## Lattice Yang–Mills (Q8 Single-Plaquette Wilson Loop)

Claim shape (finite, algebraic scaffold): for a single square plaquette with edge variables
in `Mat2(ℤ[i])`, and vertex gauge elements in the discrete subgroup `Q8`, the plaquette holonomy
transforms by basepoint conjugation, hence the Wilson-loop observable (trace) is gauge-invariant.

Artifacts:
- Python:
  - `q8_plaquette_wilson_loop_gauge_invariance_protocol.py`
    -> `q8_plaquette_wilson_loop_gauge_invariance_results.json`
- Lean (imported by `lean/Layer3_Anchors.lean`):
  - `lean/Q8_Plaquette_Wilson_Loop_Gauge_Invariance_Protocol_Theorem.lean`

## Lattice Yang–Mills (Q8 Closed-Loop Wilson Observable, General)

Claim shape (general theorem + finite protocol): for an arbitrary closed loop encoded as a list
of edge variables with a matching list of vertex gauges in `Q8`, the loop holonomy transforms by
basepoint conjugation, hence `tr2` is gauge-invariant.

Artifacts:
- Python:
  - `q8_wilson_loop_gauge_invariance_protocol.py`
    -> `q8_wilson_loop_gauge_invariance_results.json`
- Lean (imported by `lean/Layer3_Anchors.lean`):
  - `lean/Q8_Wilson_Loop_Gauge_Invariance_Protocol_Theorem.lean`

## Maxwell (E×B Invariants / Poynting Identity)

Claim shape (algebraic anchor + finite example): the Poynting proxy `S := E×B` and invariants
`I1 := ‖E‖²-‖B‖²`, `I2 := E⋅B` are linked by the exact identity:
`‖E×B‖² = ‖E‖²‖B‖² - (E⋅B)²`, and a fixed null-field example has `I1=I2=0`.

Artifacts:
- Python:
  - `maxwell_poynting_identity_protocol.py` -> `maxwell_poynting_identity_results.json`
  - `maxwell_field_tensor_duality_protocol.py` -> `maxwell_field_tensor_duality_results.json`
  - `maxwell_invariants_from_tensor_protocol.py` -> `maxwell_invariants_from_tensor_results.json`
  - `maxwell_duality_invariants_protocol.py` -> `maxwell_duality_invariants_results.json`
  - `maxwell_tensor_hodge_star_protocol.py` -> `maxwell_tensor_hodge_star_results.json`
  - `maxwell_tensor_duality_noether_protocol.py` -> `maxwell_tensor_duality_noether_results.json`
- Lean (imported by `lean/Layer3_Anchors.lean`):
  - `lean/Maxwell_Poynting_Identity_Protocol_Theorem.lean`
  - `lean/Maxwell_Field_Tensor_Duality_Protocol_Theorem.lean`
  - `lean/Maxwell_Invariants_From_Tensor_Protocol_Theorem.lean`
  - `lean/Maxwell_Duality_Invariants_Protocol_Theorem.lean`
  - `lean/Maxwell_Tensor_Hodge_Star_Protocol_Theorem.lean`
  - `lean/Maxwell_Tensor_Duality_Noether_Protocol_Theorem.lean`

## Maxwell Duality (⋆) Invariants (Finite Conservation Lens)

Claim shape (finite, algebraic): under the discrete EM duality step `⋆(E,B)=(B,-E)`,
the scalar invariants `I1=|E|^2-|B|^2` and `I2=E⋅B` flip sign, while the Poynting proxy
`S=E×B` is invariant. Therefore `I1^2`, `I2^2`, and `I1^2+I2^2` are conserved; and by the
Noether discrete lens, this conservation lifts to every iterate `⋆^[n]`.

Artifacts:
- Python:
  - `maxwell_duality_invariants_protocol.py` -> `maxwell_duality_invariants_results.json`
- Lean (imported by `lean/Layer3_Anchors.lean`):
  - `lean/Maxwell_Duality_Invariants_Protocol_Theorem.lean`

## Maxwell Tensor Hodge-Star (⋆F) (Finite Convention Anchor)

Claim shape (finite, algebraic): define an explicit tensor-side duality operator `⋆F` as a pure
index permutation/sign map on the six independent components:
`(F01,F02,F03,F23,F31,F12) ↦ (F23,F31,F12,-F01,-F02,-F03)`.
Then `⋆F(toF(E,B)) = toF(⋆(E,B))` and `⋆F⋆F(toF(E,B)) = -toF(E,B)` (order-4 law on the image).

Artifacts:
- Python:
  - `maxwell_tensor_hodge_star_protocol.py` -> `maxwell_tensor_hodge_star_results.json`
- Lean (imported by `lean/Layer3_Anchors.lean`):
  - `lean/Maxwell_Tensor_Hodge_Star_Protocol_Theorem.lean`

## Maxwell Tensor Duality Noether Packaging (Finite)

Claim shape (finite, algebraic): on the tensor image `F = toF(E,B)`, the scalar contractions
`I1_fromF(F)` and `I2_fromF(F)` flip sign under `⋆F`, so the quadratic quantity
`Q(F) := I1_fromF(F)^2 + I2_fromF(F)^2` is conserved. The Lean theorem packages invariance across
all iterates `(⋆F)^[n]` on the image using the commutation law with EM duality.

Artifacts:
- Python:
  - `maxwell_tensor_duality_noether_protocol.py` -> `maxwell_tensor_duality_noether_results.json`
- Lean (imported by `lean/Layer3_Anchors.lean`):
  - `lean/Maxwell_Tensor_Duality_Noether_Protocol_Theorem.lean`
