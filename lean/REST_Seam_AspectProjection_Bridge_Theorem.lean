import REST_Seam_Core_Theorem
import REST_Seam_NodeClosure_Bridge_Theorem
import Aspect_Projection_Kernel_Theorem

/-!
# REST Seam ↔ Aspect Projection Bridge

End-to-end bridge:
seam-window closure (`nodeClosure [14] 1 r`) transports through the projection kernel,
so any projected aspect is invariant at the composed `globalTick`.
-/

namespace RESTSeamOverlap

open MultidimensionalTicks
open AspectProjectionKernel

theorem projectView_globalTick_from_seamNodeClosure14
    {α : Type} (f : KernelState → α)
    (g r : Nat) (hr : r ≤ 3)
    (hnode : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    (ms : List Nat) (a₂ a₅ : Nat)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    projectView f ms (tick10 (globalTick ms a₂ a₅) (seamTick g r)) =
      projectView f ms (seamTick g 0) := by
  have hr0 : r = 0 := (nodeClosure_singleton14_step1_iff_zero_of_le3 r hr).1 hnode
  have hseam : seamTick g r = seamTick g 0 := by simp [hr0]
  have hproj :=
    projectView_invariant_at_globalTick
      (f := f) (n := seamTick g r) (ms := ms) (a₂ := a₂) (a₅ := a₅)
      (hn := seamTick_ne_zero g r) (hgt := hgt) (hcop := hcop)
  simpa [hseam] using hproj

theorem scaleView_globalTick_from_seamNodeClosure14
    (g r : Nat) (hr : r ≤ 3)
    (hnode : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    (ms : List Nat) (a₂ a₅ : Nat)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    projectView scaleView ms (tick10 (globalTick ms a₂ a₅) (seamTick g r)) =
      projectView scaleView ms (seamTick g 0) := by
  exact
    projectView_globalTick_from_seamNodeClosure14
      (f := scaleView) g r hr hnode ms a₂ a₅ hgt hcop

theorem residueView_globalTick_from_seamNodeClosure14
    (g r : Nat) (hr : r ≤ 3)
    (hnode : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    (ms : List Nat) (a₂ a₅ : Nat)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    projectView residueView ms (tick10 (globalTick ms a₂ a₅) (seamTick g r)) =
      projectView residueView ms (seamTick g 0) := by
  exact
    projectView_globalTick_from_seamNodeClosure14
      (f := residueView) g r hr hnode ms a₂ a₅ hgt hcop

theorem projectView_globalTick_add_from_seamNodeClosure14
    {α : Type} (f : KernelState → α)
    (g r : Nat) (hr : r ≤ 3)
    (hnode : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    (ms : List Nat) (a₂ a₅ b₂ b₅ : Nat)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    projectView f ms (tick10 (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) (seamTick g r)) =
      projectView f ms (seamTick g 0) := by
  have hr0 : r = 0 := (nodeClosure_singleton14_step1_iff_zero_of_le3 r hr).1 hnode
  have hseam : seamTick g r = seamTick g 0 := by simp [hr0]
  have hproj :=
    projectView_invariant_at_globalTick_add
      (f := f) (n := seamTick g r) (ms := ms)
      (a₂ := a₂) (a₅ := a₅) (b₂ := b₂) (b₅ := b₅)
      (hn := seamTick_ne_zero g r) (hgt := hgt) (hcop := hcop)
  simpa [hseam] using hproj

theorem scaleView_globalTick_add_from_seamNodeClosure14
    (g r : Nat) (hr : r ≤ 3)
    (hnode : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    (ms : List Nat) (a₂ a₅ b₂ b₅ : Nat)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    projectView scaleView ms (tick10 (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) (seamTick g r)) =
      projectView scaleView ms (seamTick g 0) := by
  exact
    projectView_globalTick_add_from_seamNodeClosure14
      (f := scaleView) g r hr hnode ms a₂ a₅ b₂ b₅ hgt hcop

theorem residueView_globalTick_add_from_seamNodeClosure14
    (g r : Nat) (hr : r ≤ 3)
    (hnode : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    (ms : List Nat) (a₂ a₅ b₂ b₅ : Nat)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    projectView residueView ms (tick10 (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) (seamTick g r)) =
      projectView residueView ms (seamTick g 0) := by
  exact
    projectView_globalTick_add_from_seamNodeClosure14
      (f := residueView) g r hr hnode ms a₂ a₅ b₂ b₅ hgt hcop

theorem projectView_totientLCM_from_seamNodeClosure14
    {α : Type} (f : KernelState → α)
    (g r : Nat) (hr : r ≤ 3)
    (hnode : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    (ms : List Nat)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    projectView f ms (tick10 (totientLCM ms) (seamTick g r)) =
      projectView f ms (seamTick g 0) := by
  have hr0 : r = 0 := (nodeClosure_singleton14_step1_iff_zero_of_le3 r hr).1 hnode
  have hseam : seamTick g r = seamTick g 0 := by simp [hr0]
  have hproj :=
    projectView_invariant_at_totientLCM
      (f := f) (n := seamTick g r) (ms := ms)
      (hn := seamTick_ne_zero g r) (hgt := hgt) (hcop := hcop)
  simpa [hseam] using hproj

theorem scaleView_totientLCM_from_seamNodeClosure14
    (g r : Nat) (hr : r ≤ 3)
    (hnode : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    (ms : List Nat)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    projectView scaleView ms (tick10 (totientLCM ms) (seamTick g r)) =
      projectView scaleView ms (seamTick g 0) := by
  exact
    projectView_totientLCM_from_seamNodeClosure14
      (f := scaleView) g r hr hnode ms hgt hcop

theorem residueView_totientLCM_from_seamNodeClosure14
    (g r : Nat) (hr : r ≤ 3)
    (hnode : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    (ms : List Nat)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    projectView residueView ms (tick10 (totientLCM ms) (seamTick g r)) =
      projectView residueView ms (seamTick g 0) := by
  exact
    projectView_totientLCM_from_seamNodeClosure14
      (f := residueView) g r hr hnode ms hgt hcop

theorem projectView_lcm_subsystems_from_seamNodeClosure14
    {α : Type} (f : KernelState → α)
    (g r : Nat) (hr : r ≤ 3)
    (hnode : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    (ms₁ ms₂ : List Nat)
    (hgt₁ : ∀ m ∈ ms₁, 1 < m) (hgt₂ : ∀ m ∈ ms₂, 1 < m)
    (hcop₁ : ∀ m ∈ ms₁, (10 : Nat).Coprime m) (hcop₂ : ∀ m ∈ ms₂, (10 : Nat).Coprime m) :
    projectView f (ms₁ ++ ms₂)
      (tick10 (Nat.lcm (totientLCM ms₁) (totientLCM ms₂)) (seamTick g r)) =
      projectView f (ms₁ ++ ms₂) (seamTick g 0) := by
  have hr0 : r = 0 := (nodeClosure_singleton14_step1_iff_zero_of_le3 r hr).1 hnode
  have hseam : seamTick g r = seamTick g 0 := by simp [hr0]
  have hproj :=
    projectView_invariant_at_lcm_subsystems
      (f := f) (n := seamTick g r) (ms₁ := ms₁) (ms₂ := ms₂)
      (hn := seamTick_ne_zero g r)
      (hgt₁ := hgt₁) (hgt₂ := hgt₂) (hcop₁ := hcop₁) (hcop₂ := hcop₂)
  simpa [hseam] using hproj

theorem scaleView_lcm_subsystems_from_seamNodeClosure14
    (g r : Nat) (hr : r ≤ 3)
    (hnode : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    (ms₁ ms₂ : List Nat)
    (hgt₁ : ∀ m ∈ ms₁, 1 < m) (hgt₂ : ∀ m ∈ ms₂, 1 < m)
    (hcop₁ : ∀ m ∈ ms₁, (10 : Nat).Coprime m) (hcop₂ : ∀ m ∈ ms₂, (10 : Nat).Coprime m) :
    projectView scaleView (ms₁ ++ ms₂)
      (tick10 (Nat.lcm (totientLCM ms₁) (totientLCM ms₂)) (seamTick g r)) =
      projectView scaleView (ms₁ ++ ms₂) (seamTick g 0) := by
  exact
    projectView_lcm_subsystems_from_seamNodeClosure14
      (f := scaleView) g r hr hnode ms₁ ms₂ hgt₁ hgt₂ hcop₁ hcop₂

theorem residueView_lcm_subsystems_from_seamNodeClosure14
    (g r : Nat) (hr : r ≤ 3)
    (hnode : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    (ms₁ ms₂ : List Nat)
    (hgt₁ : ∀ m ∈ ms₁, 1 < m) (hgt₂ : ∀ m ∈ ms₂, 1 < m)
    (hcop₁ : ∀ m ∈ ms₁, (10 : Nat).Coprime m) (hcop₂ : ∀ m ∈ ms₂, (10 : Nat).Coprime m) :
    projectView residueView (ms₁ ++ ms₂)
      (tick10 (Nat.lcm (totientLCM ms₁) (totientLCM ms₂)) (seamTick g r)) =
      projectView residueView (ms₁ ++ ms₂) (seamTick g 0) := by
  exact
    projectView_lcm_subsystems_from_seamNodeClosure14
      (f := residueView) g r hr hnode ms₁ ms₂ hgt₁ hgt₂ hcop₁ hcop₂

/-- One-call seam/aspect package for composed-globalTick invariance (scale + residue). -/
theorem seam_aspect_projection_package_globalTick_add
    (g r : Nat) (hr : r ≤ 3)
    (hnode : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    (ms : List Nat) (a₂ a₅ b₂ b₅ : Nat)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    (projectView scaleView ms (tick10 (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) (seamTick g r)) =
      projectView scaleView ms (seamTick g 0))
    ∧ (projectView residueView ms (tick10 (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) (seamTick g r)) =
      projectView residueView ms (seamTick g 0)) := by
  exact ⟨
    scaleView_globalTick_add_from_seamNodeClosure14 g r hr hnode ms a₂ a₅ b₂ b₅ hgt hcop,
    residueView_globalTick_add_from_seamNodeClosure14 g r hr hnode ms a₂ a₅ b₂ b₅ hgt hcop
  ⟩

/-- One-call seam/aspect package for totientLCM invariance (scale + residue). -/
theorem seam_aspect_projection_package_totientLCM
    (g r : Nat) (hr : r ≤ 3)
    (hnode : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    (ms : List Nat)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    (projectView scaleView ms (tick10 (totientLCM ms) (seamTick g r)) =
      projectView scaleView ms (seamTick g 0))
    ∧ (projectView residueView ms (tick10 (totientLCM ms) (seamTick g r)) =
      projectView residueView ms (seamTick g 0)) := by
  exact ⟨
    scaleView_totientLCM_from_seamNodeClosure14 g r hr hnode ms hgt hcop,
    residueView_totientLCM_from_seamNodeClosure14 g r hr hnode ms hgt hcop
  ⟩

/-- Fixed-parameter smoke theorem for seam/aspect composed-globalTick package on `[3,11,13]`. -/
theorem seam_aspect_projection_package_globalTick_add_smoke_3_11_13 :
    (projectView scaleView ([3, 11, 13] : List Nat)
      (tick10
        (globalTick ([3, 11, 13] : List Nat) 1 1 + globalTick ([3, 11, 13] : List Nat) 1 1)
        (seamTick 0 0))
      = projectView scaleView ([3, 11, 13] : List Nat) (seamTick 0 0))
    ∧
    (projectView residueView ([3, 11, 13] : List Nat)
      (tick10
        (globalTick ([3, 11, 13] : List Nat) 1 1 + globalTick ([3, 11, 13] : List Nat) 1 1)
        (seamTick 0 0))
      = projectView residueView ([3, 11, 13] : List Nat) (seamTick 0 0)) := by
  exact seam_aspect_projection_package_globalTick_add
    0 0 (by decide)
    ((nodeClosure_singleton14_step1_iff 0).2 (by simp))
    ([3, 11, 13] : List Nat) 1 1 1 1
    (by
      intro m hm
      simp at hm
      rcases hm with rfl | rfl | rfl <;> decide)
    (by
      intro m hm
      simp at hm
      rcases hm with rfl | rfl | rfl <;> decide)

end RESTSeamOverlap
