import REST_Seam_Unified_Interface_Theorem
import Observer_Cycle_Bridge_API_Theorem

/-!
# Composed Tick API

Discoverability layer for composed-tick theorems, without relocating existing proofs.
This file only packages already-proved statements into concise, high-level interfaces.
-/

namespace ComposedTickAPI

open MultidimensionalTicks
open AspectProjectionKernel
open RESTSeamOverlap
open ObserverCycleBridgeAPI
open ObserverDigitsCyclePeriodicityBridge

abbrev cyclePos : Nat → Nat :=
  ObserverDigitsCyclePeriodicityBridge.cyclePos

theorem cyclePos_tick10_normal_form (n d : Nat) :
    cyclePos (tick10 d n) =
      (cyclePos n * ((10 ^ cycleShiftClass d) % 13)) % 13 := by
  unfold cyclePos
  calc
    (tick10 d n) % 13 = ((n % 13) * ((10 ^ d) % 13)) % 13 := by
      simpa using (tick10_mod n d 13)
    _ = ((n % 13) * ((10 ^ cycleShiftClass d) % 13)) % 13 := by
      rw [pow10_mod13_normal_form d]
    _ = (n % 13 * (10 ^ cycleShiftClass d % 13)) % 13 := by rfl

theorem cyclePos_tick10_eq_of_same_shift_class
    (n d e : Nat) (h : cycleShiftClass d = cycleShiftClass e) :
    cyclePos (tick10 d n) = cyclePos (tick10 e n) := by
  rw [cyclePos_tick10_normal_form, cyclePos_tick10_normal_form]
  simp [h]

theorem cyclePos_tick10_6_return_api (n : Nat) :
    cyclePos (tick10 6 n) = cyclePos n := by
  unfold cyclePos tick10
  simpa using ObserverCycleBridgeAPI.cyclePos_tick10_6_return n

theorem kernel_globalTick_add_package
    (n : Nat) (ms : List Nat) (a₂ a₅ b₂ b₅ : Nat) (hn : n ≠ 0)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    (systemCoord ms (tick10 (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) n) =
      systemCoord ms n)
    ∧ (systemCoordMixed ms a₂ a₅ (tick10 (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) n) =
      (UniversalTicks.leadingBlock n, ms.map (fun m => n % m), 0, 0))
    ∧ (projectView scaleView ms (tick10 (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) n) =
      projectView scaleView ms n)
    ∧ (projectView residueView ms (tick10 (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) n) =
      projectView residueView ms n) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact systemCoord_invariant_at_globalTick_add n ms a₂ a₅ b₂ b₅ hn hgt hcop
  · exact systemCoordMixed_invariant_at_globalTick_add n ms a₂ a₅ b₂ b₅ hn hgt hcop
  · exact scaleView_invariant_at_globalTick_add n ms a₂ a₅ b₂ b₅ hn hgt hcop
  · exact residueView_invariant_at_globalTick_add n ms a₂ a₅ b₂ b₅ hn hgt hcop

theorem seam_globalTick_add_package
    (g r : Nat) (hr : r ≤ 3)
    (hnode : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    (ms : List Nat) (a₂ a₅ b₂ b₅ : Nat)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    (state (g + 1) (seamTick g r) = 0)
    ∧ (CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    ∧ (systemCoord ms (tick10 (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) (seamTick g r)) =
      (UniversalTicks.leadingBlock (seamTick g 0), ms.map (fun m => (seamTick g 0) % m)))
    ∧ (systemCoordMixed ms a₂ a₅
      (tick10 (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) (seamTick g r)) =
      (UniversalTicks.leadingBlock (seamTick g 0), ms.map (fun m => (seamTick g 0) % m), 0, 0))
    ∧ (projectView scaleView ms
      (tick10 (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) (seamTick g r)) =
      projectView scaleView ms (seamTick g 0))
    ∧ (projectView residueView ms
      (tick10 (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) (seamTick g r)) =
      projectView residueView ms (seamTick g 0)) := by
  have hScale :=
    seamClosure_unified_interface_globalTick_add_scaleView
      g r hr hnode ms a₂ a₅ b₂ b₅ hgt hcop
  have hResid :=
    seamClosure_unified_interface_globalTick_add_residueView
      g r hr hnode ms a₂ a₅ b₂ b₅ hgt hcop
  have hMix :=
    seamClosure_unified_interface_globalTick_add_mixed_scaleView
      g r hr hnode ms a₂ a₅ b₂ b₅ hgt hcop
  exact ⟨hScale.1, hScale.2.1, hScale.2.2.1, hMix.2.2.1, hScale.2.2.2, hResid.2.2.2⟩

theorem seam_totientLCM_package
    (g r : Nat) (hr : r ≤ 3)
    (hnode : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    (ms : List Nat)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    (state (g + 1) (seamTick g r) = 0)
    ∧ (CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    ∧ (systemCoord ms (tick10 (totientLCM ms) (seamTick g r)) =
      (UniversalTicks.leadingBlock (seamTick g 0), ms.map (fun m => (seamTick g 0) % m)))
    ∧ (projectView scaleView ms (tick10 (totientLCM ms) (seamTick g r)) =
      projectView scaleView ms (seamTick g 0))
    ∧ (projectView residueView ms (tick10 (totientLCM ms) (seamTick g r)) =
      projectView residueView ms (seamTick g 0)) := by
  have hScale :=
    seamClosure_unified_interface_totientLCM_scaleView g r hr hnode ms hgt hcop
  have hResid :=
    seamClosure_unified_interface_totientLCM_residueView g r hr hnode ms hgt hcop
  exact ⟨hScale.1, hScale.2.1, hScale.2.2.1, hScale.2.2.2, hResid.2.2.2⟩

theorem seam_lcm_subsystems_package
    (g r : Nat) (hr : r ≤ 3)
    (hnode : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    (ms₁ ms₂ : List Nat)
    (hgt₁ : ∀ m ∈ ms₁, 1 < m) (hgt₂ : ∀ m ∈ ms₂, 1 < m)
    (hcop₁ : ∀ m ∈ ms₁, (10 : Nat).Coprime m) (hcop₂ : ∀ m ∈ ms₂, (10 : Nat).Coprime m) :
    (state (g + 1) (seamTick g r) = 0)
    ∧ (CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    ∧ (systemCoord (ms₁ ++ ms₂)
        (tick10 (Nat.lcm (totientLCM ms₁) (totientLCM ms₂)) (seamTick g r)) =
      (UniversalTicks.leadingBlock (seamTick g 0), (ms₁ ++ ms₂).map (fun m => (seamTick g 0) % m)))
    ∧ (projectView scaleView (ms₁ ++ ms₂)
        (tick10 (Nat.lcm (totientLCM ms₁) (totientLCM ms₂)) (seamTick g r)) =
      projectView scaleView (ms₁ ++ ms₂) (seamTick g 0))
    ∧ (projectView residueView (ms₁ ++ ms₂)
        (tick10 (Nat.lcm (totientLCM ms₁) (totientLCM ms₂)) (seamTick g r)) =
      projectView residueView (ms₁ ++ ms₂) (seamTick g 0)) := by
  have hScale :=
    seamClosure_unified_interface_lcm_subsystems_scaleView
      g r hr hnode ms₁ ms₂ hgt₁ hgt₂ hcop₁ hcop₂
  have hResid :=
    seamClosure_unified_interface_lcm_subsystems_residueView
      g r hr hnode ms₁ ms₂ hgt₁ hgt₂ hcop₁ hcop₂
  exact ⟨hScale.1, hScale.2.1, hScale.2.2.1, hScale.2.2.2, hResid.2.2.2⟩

theorem nodeClosure14_r0 : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 0 := by
  exact (nodeClosure_singleton14_step1_iff 0).2 (by simp)

theorem hgt_pair_of_components (a b : Nat) (ha : 1 < a) (hb : 1 < b) :
    ∀ m ∈ ([a, b] : List Nat), 1 < m := by
  intro m hm
  simp at hm
  rcases hm with rfl | rfl <;> assumption

theorem hgt_triple_of_components (a b c : Nat) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) :
    ∀ m ∈ ([a, b, c] : List Nat), 1 < m := by
  intro m hm
  simp at hm
  rcases hm with rfl | rfl | rfl <;> assumption

theorem hgt_singleton_of_component (a : Nat) (ha : 1 < a) :
    ∀ m ∈ ([a] : List Nat), 1 < m := by
  intro m hm
  simp at hm
  rcases hm with rfl
  exact ha

theorem hcop10_pair_of_components (a b : Nat)
    (ha : (10 : Nat).Coprime a) (hb : (10 : Nat).Coprime b) :
    ∀ m ∈ ([a, b] : List Nat), (10 : Nat).Coprime m := by
  intro m hm
  simp at hm
  rcases hm with rfl | rfl <;> assumption

theorem hcop10_triple_of_components (a b c : Nat)
    (ha : (10 : Nat).Coprime a) (hb : (10 : Nat).Coprime b) (hc : (10 : Nat).Coprime c) :
    ∀ m ∈ ([a, b, c] : List Nat), (10 : Nat).Coprime m := by
  intro m hm
  simp at hm
  rcases hm with rfl | rfl | rfl <;> assumption

theorem hcop10_singleton_of_component (a : Nat) (ha : (10 : Nat).Coprime a) :
    ∀ m ∈ ([a] : List Nat), (10 : Nat).Coprime m := by
  intro m hm
  simp at hm
  rcases hm with rfl
  exact ha

theorem hgt_3_11_13 : ∀ m ∈ ([3, 11, 13] : List Nat), 1 < m := by
  exact hgt_triple_of_components 3 11 13 (by decide) (by decide) (by decide)

theorem hcop_3_11_13 : ∀ m ∈ ([3, 11, 13] : List Nat), (10 : Nat).Coprime m := by
  exact hcop10_triple_of_components 3 11 13 (by decide) (by decide) (by decide)

theorem hgt_3_11 : ∀ m ∈ ([3, 11] : List Nat), 1 < m := by
  exact hgt_pair_of_components 3 11 (by decide) (by decide)

theorem hcop_3_11 : ∀ m ∈ ([3, 11] : List Nat), (10 : Nat).Coprime m := by
  exact hcop10_pair_of_components 3 11 (by decide) (by decide)

theorem hgt_13_singleton : ∀ m ∈ ([13] : List Nat), 1 < m := by
  exact hgt_singleton_of_component 13 (by decide)

theorem hcop_13_singleton : ∀ m ∈ ([13] : List Nat), (10 : Nat).Coprime m := by
  exact hcop10_singleton_of_component 13 (by decide)

theorem hgt_7_11_13 : ∀ m ∈ ([7, 11, 13] : List Nat), 1 < m := by
  exact hgt_triple_of_components 7 11 13 (by decide) (by decide) (by decide)

theorem hcop_7_11_13 : ∀ m ∈ ([7, 11, 13] : List Nat), (10 : Nat).Coprime m := by
  exact hcop10_triple_of_components 7 11 13 (by decide) (by decide) (by decide)

theorem hgt_7_11 : ∀ m ∈ ([7, 11] : List Nat), 1 < m := by
  exact hgt_pair_of_components 7 11 (by decide) (by decide)

theorem hcop_7_11 : ∀ m ∈ ([7, 11] : List Nat), (10 : Nat).Coprime m := by
  exact hcop10_pair_of_components 7 11 (by decide) (by decide)

theorem hgt_3_7_13 : ∀ m ∈ ([3, 7, 13] : List Nat), 1 < m := by
  exact hgt_triple_of_components 3 7 13 (by decide) (by decide) (by decide)

theorem hcop_3_7_13 : ∀ m ∈ ([3, 7, 13] : List Nat), (10 : Nat).Coprime m := by
  exact hcop10_triple_of_components 3 7 13 (by decide) (by decide) (by decide)

theorem hgt_3_7 : ∀ m ∈ ([3, 7] : List Nat), 1 < m := by
  exact hgt_pair_of_components 3 7 (by decide) (by decide)

theorem hcop_3_7 : ∀ m ∈ ([3, 7] : List Nat), (10 : Nat).Coprime m := by
  exact hcop10_pair_of_components 3 7 (by decide) (by decide)

theorem hgt_append_of_parts
    (ms₁ ms₂ : List Nat)
    (hgt₁ : ∀ m ∈ ms₁, 1 < m) (hgt₂ : ∀ m ∈ ms₂, 1 < m) :
    ∀ m ∈ (ms₁ ++ ms₂), 1 < m := by
  intro m hm
  rcases List.mem_append.mp hm with hm₁ | hm₂
  · exact hgt₁ m hm₁
  · exact hgt₂ m hm₂

theorem hcop_append_of_parts
    (ms₁ ms₂ : List Nat)
    (hcop₁ : ∀ m ∈ ms₁, (10 : Nat).Coprime m)
    (hcop₂ : ∀ m ∈ ms₂, (10 : Nat).Coprime m) :
    ∀ m ∈ (ms₁ ++ ms₂), (10 : Nat).Coprime m := by
  intro m hm
  rcases List.mem_append.mp hm with hm₁ | hm₂
  · exact hcop₁ m hm₁
  · exact hcop₂ m hm₂

theorem globalTick_3_11_13_1_1 : globalTick ([3, 11, 13] : List Nat) 1 1 = 120 := by
  -- `totientLCM [3,11,13] = 60`, then multiply by `(max 1 1 + 1) = 2`.
  simp [globalTick, totientLCM_3_11_13]

theorem kernel_globalTick_add_package_3_11_13
    (n : Nat) (hn : n ≠ 0) :
    (systemCoord ([3, 11, 13] : List Nat) (tick10 240 n) =
      systemCoord ([3, 11, 13] : List Nat) n)
    ∧ (systemCoordMixed ([3, 11, 13] : List Nat) 1 1 (tick10 240 n) =
      (UniversalTicks.leadingBlock n, ([3, 11, 13] : List Nat).map (fun m => n % m), 0, 0))
    ∧ (projectView scaleView ([3, 11, 13] : List Nat) (tick10 240 n) =
      projectView scaleView ([3, 11, 13] : List Nat) n)
    ∧ (projectView residueView ([3, 11, 13] : List Nat) (tick10 240 n) =
      projectView residueView ([3, 11, 13] : List Nat) n) := by
  have hpkg :=
    kernel_globalTick_add_package
      (n := n) (ms := ([3, 11, 13] : List Nat))
      (a₂ := 1) (a₅ := 1) (b₂ := 1) (b₅ := 1) hn hgt_3_11_13 hcop_3_11_13
  have hK : globalTick ([3, 11, 13] : List Nat) 1 1 = 120 := globalTick_3_11_13_1_1
  have h240 : globalTick ([3, 11, 13] : List Nat) 1 1 + globalTick ([3, 11, 13] : List Nat) 1 1 = 240 := by
    simp [hK]
  simpa [hK, h240] using hpkg

theorem seam_globalTick_add_package_3_11_13_r0
    (g : Nat) :
    (state (g + 1) (seamTick g 0) = 0)
    ∧ (CycleStepOrbit.nodeClosure ([14] : List Nat) 1 0)
    ∧ (systemCoord ([3, 11, 13] : List Nat) (tick10 240 (seamTick g 0)) =
      (UniversalTicks.leadingBlock (seamTick g 0),
        ([3, 11, 13] : List Nat).map (fun m => (seamTick g 0) % m)))
    ∧ (systemCoordMixed ([3, 11, 13] : List Nat) 1 1 (tick10 240 (seamTick g 0)) =
      (UniversalTicks.leadingBlock (seamTick g 0),
        ([3, 11, 13] : List Nat).map (fun m => (seamTick g 0) % m), 0, 0))
    ∧ (projectView scaleView ([3, 11, 13] : List Nat) (tick10 240 (seamTick g 0)) =
      projectView scaleView ([3, 11, 13] : List Nat) (seamTick g 0))
    ∧ (projectView residueView ([3, 11, 13] : List Nat) (tick10 240 (seamTick g 0)) =
      projectView residueView ([3, 11, 13] : List Nat) (seamTick g 0)) := by
  have hr : (0 : Nat) ≤ 3 := by decide
  have hpkg :=
    seam_globalTick_add_package
      g 0 hr nodeClosure14_r0 ([3, 11, 13] : List Nat) 1 1 1 1 hgt_3_11_13 hcop_3_11_13
  have hK : globalTick ([3, 11, 13] : List Nat) 1 1 = 120 := globalTick_3_11_13_1_1
  have h240 : globalTick ([3, 11, 13] : List Nat) 1 1 + globalTick ([3, 11, 13] : List Nat) 1 1 = 240 := by
    simp [hK]
  simpa [hK, h240] using hpkg

theorem seam_lcm_subsystems_package_3_11_13_r0
    (g : Nat) :
    (state (g + 1) (seamTick g 0) = 0)
    ∧ (CycleStepOrbit.nodeClosure ([14] : List Nat) 1 0)
    ∧ (systemCoord (([3, 11] : List Nat) ++ ([13] : List Nat)) (tick10 60 (seamTick g 0)) =
      (UniversalTicks.leadingBlock (seamTick g 0),
        (([3, 11] : List Nat) ++ ([13] : List Nat)).map (fun m => (seamTick g 0) % m)))
    ∧ (projectView scaleView (([3, 11] : List Nat) ++ ([13] : List Nat)) (tick10 60 (seamTick g 0)) =
      projectView scaleView (([3, 11] : List Nat) ++ ([13] : List Nat)) (seamTick g 0))
    ∧ (projectView residueView (([3, 11] : List Nat) ++ ([13] : List Nat)) (tick10 60 (seamTick g 0)) =
      projectView residueView (([3, 11] : List Nat) ++ ([13] : List Nat)) (seamTick g 0)) := by
  have hr : (0 : Nat) ≤ 3 := by decide
  have hpkg :=
    seam_lcm_subsystems_package
      g 0 hr nodeClosure14_r0 ([3, 11] : List Nat) ([13] : List Nat)
      hgt_3_11 hgt_13_singleton hcop_3_11 hcop_13_singleton
  have h60_num : Nat.lcm 10 12 = 60 := by native_decide
  have h60 : Nat.lcm (totientLCM ([3, 11] : List Nat)) (totientLCM ([13] : List Nat)) = 60 := by
    simpa [totientLCM_3_11, totientLCM_13] using h60_num
  simpa [h60] using hpkg

theorem seam_totientLCM_package_3_11_13_r0
    (g : Nat) :
    (state (g + 1) (seamTick g 0) = 0)
    ∧ (CycleStepOrbit.nodeClosure ([14] : List Nat) 1 0)
    ∧ (systemCoord ([3, 11, 13] : List Nat) (tick10 60 (seamTick g 0)) =
      (UniversalTicks.leadingBlock (seamTick g 0),
        ([3, 11, 13] : List Nat).map (fun m => (seamTick g 0) % m)))
    ∧ (projectView scaleView ([3, 11, 13] : List Nat) (tick10 60 (seamTick g 0)) =
      projectView scaleView ([3, 11, 13] : List Nat) (seamTick g 0))
    ∧ (projectView residueView ([3, 11, 13] : List Nat) (tick10 60 (seamTick g 0)) =
      projectView residueView ([3, 11, 13] : List Nat) (seamTick g 0)) := by
  have hr : (0 : Nat) ≤ 3 := by decide
  have hpkg :=
    seam_totientLCM_package
      g 0 hr nodeClosure14_r0 ([3, 11, 13] : List Nat) hgt_3_11_13 hcop_3_11_13
  have h60 : totientLCM ([3, 11, 13] : List Nat) = 60 := totientLCM_3_11_13
  simpa [h60] using hpkg

abbrev KernelPkg31113 (n : Nat) : Prop :=
  (systemCoord ([3, 11, 13] : List Nat) (tick10 240 n) =
    systemCoord ([3, 11, 13] : List Nat) n)
  ∧ (systemCoordMixed ([3, 11, 13] : List Nat) 1 1 (tick10 240 n) =
    (UniversalTicks.leadingBlock n, ([3, 11, 13] : List Nat).map (fun m => n % m), 0, 0))
  ∧ (projectView scaleView ([3, 11, 13] : List Nat) (tick10 240 n) =
    projectView scaleView ([3, 11, 13] : List Nat) n)
  ∧ (projectView residueView ([3, 11, 13] : List Nat) (tick10 240 n) =
    projectView residueView ([3, 11, 13] : List Nat) n)

abbrev SeamGlobalPkg31113 (g : Nat) : Prop :=
  (state (g + 1) (seamTick g 0) = 0)
  ∧ (CycleStepOrbit.nodeClosure ([14] : List Nat) 1 0)
  ∧ (systemCoord ([3, 11, 13] : List Nat) (tick10 240 (seamTick g 0)) =
    (UniversalTicks.leadingBlock (seamTick g 0),
      ([3, 11, 13] : List Nat).map (fun m => (seamTick g 0) % m)))
  ∧ (systemCoordMixed ([3, 11, 13] : List Nat) 1 1 (tick10 240 (seamTick g 0)) =
    (UniversalTicks.leadingBlock (seamTick g 0),
      ([3, 11, 13] : List Nat).map (fun m => (seamTick g 0) % m), 0, 0))
  ∧ (projectView scaleView ([3, 11, 13] : List Nat) (tick10 240 (seamTick g 0)) =
    projectView scaleView ([3, 11, 13] : List Nat) (seamTick g 0))
  ∧ (projectView residueView ([3, 11, 13] : List Nat) (tick10 240 (seamTick g 0)) =
    projectView residueView ([3, 11, 13] : List Nat) (seamTick g 0))

abbrev SeamTotientPkg31113 (g : Nat) : Prop :=
  (state (g + 1) (seamTick g 0) = 0)
  ∧ (CycleStepOrbit.nodeClosure ([14] : List Nat) 1 0)
  ∧ (systemCoord ([3, 11, 13] : List Nat) (tick10 60 (seamTick g 0)) =
    (UniversalTicks.leadingBlock (seamTick g 0),
      ([3, 11, 13] : List Nat).map (fun m => (seamTick g 0) % m)))
  ∧ (projectView scaleView ([3, 11, 13] : List Nat) (tick10 60 (seamTick g 0)) =
    projectView scaleView ([3, 11, 13] : List Nat) (seamTick g 0))
  ∧ (projectView residueView ([3, 11, 13] : List Nat) (tick10 60 (seamTick g 0)) =
    projectView residueView ([3, 11, 13] : List Nat) (seamTick g 0))

abbrev SeamLCMPkg31113 (g : Nat) : Prop :=
  (state (g + 1) (seamTick g 0) = 0)
  ∧ (CycleStepOrbit.nodeClosure ([14] : List Nat) 1 0)
  ∧ (systemCoord (([3, 11] : List Nat) ++ ([13] : List Nat)) (tick10 60 (seamTick g 0)) =
    (UniversalTicks.leadingBlock (seamTick g 0),
      (([3, 11] : List Nat) ++ ([13] : List Nat)).map (fun m => (seamTick g 0) % m)))
  ∧ (projectView scaleView (([3, 11] : List Nat) ++ ([13] : List Nat)) (tick10 60 (seamTick g 0)) =
    projectView scaleView (([3, 11] : List Nat) ++ ([13] : List Nat)) (seamTick g 0))
  ∧ (projectView residueView
      (([3, 11] : List Nat) ++ ([13] : List Nat)) (tick10 60 (seamTick g 0)) =
    projectView residueView (([3, 11] : List Nat) ++ ([13] : List Nat)) (seamTick g 0))

theorem canonical_composed_trilogy_package
    (g n : Nat) (hn : n ≠ 0) :
    KernelPkg31113 n
    ∧ SeamGlobalPkg31113 g
    ∧ SeamTotientPkg31113 g
    ∧ SeamLCMPkg31113 g := by
  exact ⟨
    kernel_globalTick_add_package_3_11_13 n hn,
    seam_globalTick_add_package_3_11_13_r0 g,
    seam_totientLCM_package_3_11_13_r0 g,
    seam_lcm_subsystems_package_3_11_13_r0 g
  ⟩

theorem canonical_composed_trilogy_smoke :
    KernelPkg31113 1
    ∧ SeamGlobalPkg31113 0
    ∧ SeamTotientPkg31113 0
    ∧ SeamLCMPkg31113 0 := by
  exact canonical_composed_trilogy_package 0 1 (by decide)

theorem default_smoke_suite :
    KernelPkg31113 1
    ∧ SeamGlobalPkg31113 0
    ∧ SeamTotientPkg31113 0
    ∧ SeamLCMPkg31113 0 := by
  exact canonical_composed_trilogy_smoke

end ComposedTickAPI
