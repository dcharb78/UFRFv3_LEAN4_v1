import REST_Seam_Unified_Interface_Core_Theorem
import REST_Seam_AspectProjection_Bridge_Theorem
import REST_Seam_SystemCoordMixed_Bridge_Theorem

/-!
# REST Seam Unified Interface

Single packaged theorem schema combining:
- seam-window closure witness,
- node-closure bridge,
- mixed-coordinate global-tick closure,
- aspect-projection global-tick closure.
-/

namespace RESTSeamOverlap

open MultidimensionalTicks
open AspectProjectionKernel

theorem seamClosure_unified_interface
    {α : Type} (f : KernelState → α)
    (g r : Nat) (hr : r ≤ 3)
    (hnode : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    (ms : List Nat) (a₂ a₅ : Nat)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    (state (g + 1) (seamTick g r) = 0)
      ∧ (CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
      ∧ (systemCoordMixed ms a₂ a₅ (tick10 (globalTick ms a₂ a₅) (seamTick g r)) =
            (UniversalTicks.leadingBlock (seamTick g 0), ms.map (fun m => (seamTick g 0) % m), 0, 0))
      ∧ (projectView f ms (tick10 (globalTick ms a₂ a₅) (seamTick g r)) =
            projectView f ms (seamTick g 0)) := by
  have hchild : state (g + 1) (seamTick g r) = 0 :=
    (childVoid_iff_nodeClosure14_at_seamTick g r hr).2 hnode
  refine ⟨hchild, hnode, ?_, ?_⟩
  · exact
      systemCoordMixed_globalTick_from_seamNodeClosure14_general
        g r hr hnode ms a₂ a₅ hgt hcop
  · exact
      projectView_globalTick_from_seamNodeClosure14
        (f := f) g r hr hnode ms a₂ a₅ hgt hcop

theorem seamClosure_unified_interface_scaleView
    (g r : Nat) (hr : r ≤ 3)
    (hnode : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    (ms : List Nat) (a₂ a₅ : Nat)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    (state (g + 1) (seamTick g r) = 0)
      ∧ (CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
      ∧ (systemCoordMixed ms a₂ a₅ (tick10 (globalTick ms a₂ a₅) (seamTick g r)) =
            (UniversalTicks.leadingBlock (seamTick g 0), ms.map (fun m => (seamTick g 0) % m), 0, 0))
      ∧ (projectView scaleView ms (tick10 (globalTick ms a₂ a₅) (seamTick g r)) =
            projectView scaleView ms (seamTick g 0)) := by
  exact seamClosure_unified_interface (f := scaleView) g r hr hnode ms a₂ a₅ hgt hcop

theorem seamClosure_unified_interface_residueView
    (g r : Nat) (hr : r ≤ 3)
    (hnode : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    (ms : List Nat) (a₂ a₅ : Nat)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    (state (g + 1) (seamTick g r) = 0)
      ∧ (CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
      ∧ (systemCoordMixed ms a₂ a₅ (tick10 (globalTick ms a₂ a₅) (seamTick g r)) =
            (UniversalTicks.leadingBlock (seamTick g 0), ms.map (fun m => (seamTick g 0) % m), 0, 0))
      ∧ (projectView residueView ms (tick10 (globalTick ms a₂ a₅) (seamTick g r)) =
            projectView residueView ms (seamTick g 0)) := by
  exact seamClosure_unified_interface (f := residueView) g r hr hnode ms a₂ a₅ hgt hcop

theorem seamClosure_unified_interface_totientLCM
    {α : Type} (f : KernelState → α)
    (g r : Nat) (hr : r ≤ 3)
    (hnode : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    (ms : List Nat)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    (state (g + 1) (seamTick g r) = 0)
      ∧ (CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
      ∧ (systemCoord ms (tick10 (totientLCM ms) (seamTick g r)) =
            (UniversalTicks.leadingBlock (seamTick g 0), ms.map (fun m => (seamTick g 0) % m)))
      ∧ (projectView f ms (tick10 (totientLCM ms) (seamTick g r)) =
            projectView f ms (seamTick g 0)) := by
  have hr0 : r = 0 := (nodeClosure_singleton14_step1_iff_zero_of_le3 r hr).1 hnode
  have hseam : seamTick g r = seamTick g 0 := by simp [hr0]
  have hsysInv :=
    systemCoord_invariant_at_totientLCM
      (n := seamTick g r) (ms := ms)
      (hn := seamTick_ne_zero g r) (hgt := hgt) (hcop := hcop)
  have hsys :
      systemCoord ms (tick10 (totientLCM ms) (seamTick g r)) =
        (UniversalTicks.leadingBlock (seamTick g 0), ms.map (fun m => (seamTick g 0) % m)) := by
    simpa [systemCoord, hseam] using hsysInv
  have hproj :=
    projectView_totientLCM_from_seamNodeClosure14
      (f := f) g r hr hnode ms hgt hcop
  exact
    seamClosure_unified_interface_systemCoord_of_transports
      (f := f) g r hr hnode ms (totientLCM ms) hsys hproj

theorem seamClosure_unified_interface_totientLCM_scaleView
    (g r : Nat) (hr : r ≤ 3)
    (hnode : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    (ms : List Nat)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    (state (g + 1) (seamTick g r) = 0)
      ∧ (CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
      ∧ (systemCoord ms (tick10 (totientLCM ms) (seamTick g r)) =
            (UniversalTicks.leadingBlock (seamTick g 0), ms.map (fun m => (seamTick g 0) % m)))
      ∧ (projectView scaleView ms (tick10 (totientLCM ms) (seamTick g r)) =
            projectView scaleView ms (seamTick g 0)) := by
  exact seamClosure_unified_interface_totientLCM (f := scaleView) g r hr hnode ms hgt hcop

theorem seamClosure_unified_interface_totientLCM_residueView
    (g r : Nat) (hr : r ≤ 3)
    (hnode : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    (ms : List Nat)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    (state (g + 1) (seamTick g r) = 0)
      ∧ (CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
      ∧ (systemCoord ms (tick10 (totientLCM ms) (seamTick g r)) =
            (UniversalTicks.leadingBlock (seamTick g 0), ms.map (fun m => (seamTick g 0) % m)))
      ∧ (projectView residueView ms (tick10 (totientLCM ms) (seamTick g r)) =
            projectView residueView ms (seamTick g 0)) := by
  exact seamClosure_unified_interface_totientLCM (f := residueView) g r hr hnode ms hgt hcop

theorem seamClosure_unified_interface_globalTick_add
    {α : Type} (f : KernelState → α)
    (g r : Nat) (hr : r ≤ 3)
    (hnode : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    (ms : List Nat) (a₂ a₅ b₂ b₅ : Nat)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    (state (g + 1) (seamTick g r) = 0)
      ∧ (CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
      ∧ (systemCoord ms (tick10 (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) (seamTick g r)) =
            (UniversalTicks.leadingBlock (seamTick g 0), ms.map (fun m => (seamTick g 0) % m)))
      ∧ (projectView f ms (tick10 (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) (seamTick g r)) =
            projectView f ms (seamTick g 0)) := by
  have hr0 : r = 0 := (nodeClosure_singleton14_step1_iff_zero_of_le3 r hr).1 hnode
  have hseam : seamTick g r = seamTick g 0 := by simp [hr0]
  have hsysInv :=
    systemCoord_invariant_at_globalTick_add
      (n := seamTick g r) (ms := ms)
      (a₂ := a₂) (a₅ := a₅) (b₂ := b₂) (b₅ := b₅)
      (hn := seamTick_ne_zero g r) (hgt := hgt) (hcop := hcop)
  have hsys :
      systemCoord ms (tick10 (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) (seamTick g r)) =
        (UniversalTicks.leadingBlock (seamTick g 0), ms.map (fun m => (seamTick g 0) % m)) := by
    simpa [systemCoord, hseam] using hsysInv
  have hproj :=
    projectView_globalTick_add_from_seamNodeClosure14
      (f := f) g r hr hnode ms a₂ a₅ b₂ b₅ hgt hcop
  exact
    seamClosure_unified_interface_systemCoord_of_transports
      (f := f) g r hr hnode ms
      (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) hsys hproj

theorem seamClosure_unified_interface_globalTick_add_scaleView
    (g r : Nat) (hr : r ≤ 3)
    (hnode : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    (ms : List Nat) (a₂ a₅ b₂ b₅ : Nat)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    (state (g + 1) (seamTick g r) = 0)
      ∧ (CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
      ∧ (systemCoord ms (tick10 (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) (seamTick g r)) =
            (UniversalTicks.leadingBlock (seamTick g 0), ms.map (fun m => (seamTick g 0) % m)))
      ∧ (projectView scaleView ms (tick10 (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) (seamTick g r)) =
            projectView scaleView ms (seamTick g 0)) := by
  exact
    seamClosure_unified_interface_globalTick_add
      (f := scaleView) g r hr hnode ms a₂ a₅ b₂ b₅ hgt hcop

theorem seamClosure_unified_interface_globalTick_add_residueView
    (g r : Nat) (hr : r ≤ 3)
    (hnode : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    (ms : List Nat) (a₂ a₅ b₂ b₅ : Nat)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    (state (g + 1) (seamTick g r) = 0)
      ∧ (CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
      ∧ (systemCoord ms (tick10 (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) (seamTick g r)) =
            (UniversalTicks.leadingBlock (seamTick g 0), ms.map (fun m => (seamTick g 0) % m)))
      ∧ (projectView residueView ms (tick10 (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) (seamTick g r)) =
            projectView residueView ms (seamTick g 0)) := by
  exact
    seamClosure_unified_interface_globalTick_add
      (f := residueView) g r hr hnode ms a₂ a₅ b₂ b₅ hgt hcop

theorem seamClosure_unified_interface_globalTick_add_mixed
    {α : Type} (f : KernelState → α)
    (g r : Nat) (hr : r ≤ 3)
    (hnode : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    (ms : List Nat) (a₂ a₅ b₂ b₅ : Nat)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    (state (g + 1) (seamTick g r) = 0)
      ∧ (CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
      ∧ (systemCoordMixed ms a₂ a₅
            (tick10 (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) (seamTick g r)) =
            (UniversalTicks.leadingBlock (seamTick g 0), ms.map (fun m => (seamTick g 0) % m), 0, 0))
      ∧ (projectView f ms
            (tick10 (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) (seamTick g r)) =
            projectView f ms (seamTick g 0)) := by
  have hchild : state (g + 1) (seamTick g r) = 0 :=
    (childVoid_iff_nodeClosure14_at_seamTick g r hr).2 hnode
  refine ⟨hchild, hnode, ?_, ?_⟩
  · exact
      systemCoordMixed_globalTick_add_from_seamNodeClosure14_general
        g r hr hnode ms a₂ a₅ b₂ b₅ hgt hcop
  · exact
      projectView_globalTick_add_from_seamNodeClosure14
        (f := f) g r hr hnode ms a₂ a₅ b₂ b₅ hgt hcop

theorem seamClosure_unified_interface_globalTick_add_mixed_scaleView
    (g r : Nat) (hr : r ≤ 3)
    (hnode : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    (ms : List Nat) (a₂ a₅ b₂ b₅ : Nat)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    (state (g + 1) (seamTick g r) = 0)
      ∧ (CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
      ∧ (systemCoordMixed ms a₂ a₅
            (tick10 (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) (seamTick g r)) =
            (UniversalTicks.leadingBlock (seamTick g 0), ms.map (fun m => (seamTick g 0) % m), 0, 0))
      ∧ (projectView scaleView ms
            (tick10 (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) (seamTick g r)) =
            projectView scaleView ms (seamTick g 0)) := by
  exact
    seamClosure_unified_interface_globalTick_add_mixed
      (f := scaleView) g r hr hnode ms a₂ a₅ b₂ b₅ hgt hcop

theorem seamClosure_unified_interface_globalTick_add_mixed_residueView
    (g r : Nat) (hr : r ≤ 3)
    (hnode : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    (ms : List Nat) (a₂ a₅ b₂ b₅ : Nat)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    (state (g + 1) (seamTick g r) = 0)
      ∧ (CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
      ∧ (systemCoordMixed ms a₂ a₅
            (tick10 (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) (seamTick g r)) =
            (UniversalTicks.leadingBlock (seamTick g 0), ms.map (fun m => (seamTick g 0) % m), 0, 0))
      ∧ (projectView residueView ms
            (tick10 (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) (seamTick g r)) =
            projectView residueView ms (seamTick g 0)) := by
  exact
    seamClosure_unified_interface_globalTick_add_mixed
      (f := residueView) g r hr hnode ms a₂ a₅ b₂ b₅ hgt hcop

theorem seamClosure_unified_interface_lcm_subsystems
    {α : Type} (f : KernelState → α)
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
      ∧ (projectView f (ms₁ ++ ms₂)
            (tick10 (Nat.lcm (totientLCM ms₁) (totientLCM ms₂)) (seamTick g r)) =
            projectView f (ms₁ ++ ms₂) (seamTick g 0)) := by
  have hr0 : r = 0 := (nodeClosure_singleton14_step1_iff_zero_of_le3 r hr).1 hnode
  have hseam : seamTick g r = seamTick g 0 := by simp [hr0]
  have hsysInv :=
    systemCoord_invariant_at_lcm_subsystems
      (n := seamTick g r) (ms₁ := ms₁) (ms₂ := ms₂)
      (hn := seamTick_ne_zero g r)
      (hgt₁ := hgt₁) (hgt₂ := hgt₂) (hcop₁ := hcop₁) (hcop₂ := hcop₂)
  have hsys :
      systemCoord (ms₁ ++ ms₂)
        (tick10 (Nat.lcm (totientLCM ms₁) (totientLCM ms₂)) (seamTick g r)) =
        (UniversalTicks.leadingBlock (seamTick g 0), (ms₁ ++ ms₂).map (fun m => (seamTick g 0) % m)) := by
    simpa [systemCoord, hseam] using hsysInv
  have hproj :=
    projectView_lcm_subsystems_from_seamNodeClosure14
      (f := f) g r hr hnode ms₁ ms₂ hgt₁ hgt₂ hcop₁ hcop₂
  exact
    seamClosure_unified_interface_systemCoord_of_transports
      (f := f) g r hr hnode (ms₁ ++ ms₂)
      (Nat.lcm (totientLCM ms₁) (totientLCM ms₂)) hsys hproj

theorem seamClosure_unified_interface_lcm_subsystems_scaleView
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
            projectView scaleView (ms₁ ++ ms₂) (seamTick g 0)) := by
  exact
    seamClosure_unified_interface_lcm_subsystems
      (f := scaleView) g r hr hnode ms₁ ms₂ hgt₁ hgt₂ hcop₁ hcop₂

theorem seamClosure_unified_interface_lcm_subsystems_residueView
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
      ∧ (projectView residueView (ms₁ ++ ms₂)
            (tick10 (Nat.lcm (totientLCM ms₁) (totientLCM ms₂)) (seamTick g r)) =
            projectView residueView (ms₁ ++ ms₂) (seamTick g 0)) := by
  exact
    seamClosure_unified_interface_lcm_subsystems
      (f := residueView) g r hr hnode ms₁ ms₂ hgt₁ hgt₂ hcop₁ hcop₂

end RESTSeamOverlap
