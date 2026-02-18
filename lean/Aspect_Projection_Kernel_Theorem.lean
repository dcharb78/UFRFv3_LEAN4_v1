import Multidimensional_Ticks_Theorem

/-!
# Aspect = Projection (Discrete Kernel Package)

This module packages a single closure kernel (`systemCoord`) and proves that any
derived aspect/view is invariant whenever the kernel is invariant.

This is the formal bridge for:
- "many aspects" (music/modular/geometric chart choices),
- one underlying closure object.
-/

namespace AspectProjectionKernel

open MultidimensionalTicks

/-- Shared closure kernel state for finite-axis systems. -/
abbrev KernelState := Nat × List Nat

/-- Canonical kernel state extracted from a system/number pair. -/
def kernelState (ms : List Nat) (n : Nat) : KernelState :=
  systemCoord ms n

/-- Generic aspect projection from kernel state. -/
def projectView {α : Type} (f : KernelState → α) (ms : List Nat) (n : Nat) : α :=
  f (kernelState ms n)

/-- Scale-axis projection (leading block chart). -/
def scaleView (st : KernelState) : Nat := st.1

/-- Cycle-axis projection (residue vector chart). -/
def residueView (st : KernelState) : List Nat := st.2

theorem kernelState_invariant_of_nodeClosure
    (n k : Nat) (ms : List Nat) (hn : n ≠ 0)
    (hcop : ms.Pairwise Nat.Coprime)
    (hnode : CycleStepOrbit.nodeClosure ms (10 ^ k - 1) n) :
    kernelState ms (tick10 k n) = kernelState ms n := by
  exact systemCoord_invariant_of_nodeClosure n k ms hn hcop hnode

theorem projectView_invariant_of_nodeClosure
    {α : Type} (f : KernelState → α)
    (n k : Nat) (ms : List Nat) (hn : n ≠ 0)
    (hcop : ms.Pairwise Nat.Coprime)
    (hnode : CycleStepOrbit.nodeClosure ms (10 ^ k - 1) n) :
    projectView f ms (tick10 k n) = projectView f ms n := by
  unfold projectView kernelState
  exact congrArg f (kernelState_invariant_of_nodeClosure n k ms hn hcop hnode)

theorem scaleView_invariant_of_nodeClosure
    (n k : Nat) (ms : List Nat) (hn : n ≠ 0)
    (hcop : ms.Pairwise Nat.Coprime)
    (hnode : CycleStepOrbit.nodeClosure ms (10 ^ k - 1) n) :
    projectView scaleView ms (tick10 k n) = projectView scaleView ms n := by
  exact projectView_invariant_of_nodeClosure scaleView n k ms hn hcop hnode

theorem residueView_invariant_of_nodeClosure
    (n k : Nat) (ms : List Nat) (hn : n ≠ 0)
    (hcop : ms.Pairwise Nat.Coprime)
    (hnode : CycleStepOrbit.nodeClosure ms (10 ^ k - 1) n) :
    projectView residueView ms (tick10 k n) = projectView residueView ms n := by
  exact projectView_invariant_of_nodeClosure residueView n k ms hn hcop hnode

theorem projectView_invariant_at_globalTick
    {α : Type} (f : KernelState → α)
    (n : Nat) (ms : List Nat) (a₂ a₅ : Nat) (hn : n ≠ 0)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    projectView f ms (tick10 (globalTick ms a₂ a₅) n) = projectView f ms n := by
  unfold projectView kernelState
  exact congrArg f (systemCoord_invariant_at_globalTick n ms a₂ a₅ hn hgt hcop)

theorem projectView_invariant_at_totientLCM
    {α : Type} (f : KernelState → α)
    (n : Nat) (ms : List Nat) (hn : n ≠ 0)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    projectView f ms (tick10 (totientLCM ms) n) = projectView f ms n := by
  unfold projectView kernelState
  exact congrArg f (systemCoord_invariant_at_totientLCM n ms hn hgt hcop)

theorem projectView_invariant_at_globalTick_add
    {α : Type} (f : KernelState → α)
    (n : Nat) (ms : List Nat) (a₂ a₅ b₂ b₅ : Nat) (hn : n ≠ 0)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    projectView f ms (tick10 (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) n) =
      projectView f ms n := by
  have hB :=
    projectView_invariant_at_globalTick
      (f := f) (n := n) (ms := ms) (a₂ := b₂) (a₅ := b₅) hn hgt hcop
  have hnB : tick10 (globalTick ms b₂ b₅) n ≠ 0 :=
    tick10_ne_zero (globalTick ms b₂ b₅) n hn
  have hA :=
    projectView_invariant_at_globalTick
      (f := f) (n := tick10 (globalTick ms b₂ b₅) n)
      (ms := ms) (a₂ := a₂) (a₅ := a₅) hnB hgt hcop
  rw [← tick10_add (globalTick ms a₂ a₅) (globalTick ms b₂ b₅) n]
  exact hA.trans hB

theorem scaleView_invariant_at_globalTick
    (n : Nat) (ms : List Nat) (a₂ a₅ : Nat) (hn : n ≠ 0)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    projectView scaleView ms (tick10 (globalTick ms a₂ a₅) n) = projectView scaleView ms n := by
  exact projectView_invariant_at_globalTick scaleView n ms a₂ a₅ hn hgt hcop

theorem scaleView_invariant_at_totientLCM
    (n : Nat) (ms : List Nat) (hn : n ≠ 0)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    projectView scaleView ms (tick10 (totientLCM ms) n) = projectView scaleView ms n := by
  exact projectView_invariant_at_totientLCM scaleView n ms hn hgt hcop

theorem residueView_invariant_at_globalTick
    (n : Nat) (ms : List Nat) (a₂ a₅ : Nat) (hn : n ≠ 0)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    projectView residueView ms (tick10 (globalTick ms a₂ a₅) n) = projectView residueView ms n := by
  exact projectView_invariant_at_globalTick residueView n ms a₂ a₅ hn hgt hcop

theorem residueView_invariant_at_totientLCM
    (n : Nat) (ms : List Nat) (hn : n ≠ 0)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    projectView residueView ms (tick10 (totientLCM ms) n) = projectView residueView ms n := by
  exact projectView_invariant_at_totientLCM residueView n ms hn hgt hcop

theorem scaleView_invariant_at_globalTick_add
    (n : Nat) (ms : List Nat) (a₂ a₅ b₂ b₅ : Nat) (hn : n ≠ 0)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    projectView scaleView ms (tick10 (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) n) =
      projectView scaleView ms n := by
  exact projectView_invariant_at_globalTick_add scaleView n ms a₂ a₅ b₂ b₅ hn hgt hcop

theorem residueView_invariant_at_globalTick_add
    (n : Nat) (ms : List Nat) (a₂ a₅ b₂ b₅ : Nat) (hn : n ≠ 0)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    projectView residueView ms (tick10 (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) n) =
      projectView residueView ms n := by
  exact projectView_invariant_at_globalTick_add residueView n ms a₂ a₅ b₂ b₅ hn hgt hcop

theorem projectView_invariant_at_lcm_subsystems
    {α : Type} (f : KernelState → α)
    (n : Nat) (ms₁ ms₂ : List Nat) (hn : n ≠ 0)
    (hgt₁ : ∀ m ∈ ms₁, 1 < m) (hgt₂ : ∀ m ∈ ms₂, 1 < m)
    (hcop₁ : ∀ m ∈ ms₁, (10 : Nat).Coprime m) (hcop₂ : ∀ m ∈ ms₂, (10 : Nat).Coprime m) :
    projectView f (ms₁ ++ ms₂) (tick10 (Nat.lcm (totientLCM ms₁) (totientLCM ms₂)) n) =
      projectView f (ms₁ ++ ms₂) n := by
  unfold projectView kernelState
  exact congrArg f (systemCoord_invariant_at_lcm_subsystems n ms₁ ms₂ hn hgt₁ hgt₂ hcop₁ hcop₂)

theorem scaleView_invariant_at_lcm_subsystems
    (n : Nat) (ms₁ ms₂ : List Nat) (hn : n ≠ 0)
    (hgt₁ : ∀ m ∈ ms₁, 1 < m) (hgt₂ : ∀ m ∈ ms₂, 1 < m)
    (hcop₁ : ∀ m ∈ ms₁, (10 : Nat).Coprime m) (hcop₂ : ∀ m ∈ ms₂, (10 : Nat).Coprime m) :
    projectView scaleView (ms₁ ++ ms₂) (tick10 (Nat.lcm (totientLCM ms₁) (totientLCM ms₂)) n) =
      projectView scaleView (ms₁ ++ ms₂) n := by
  exact
    projectView_invariant_at_lcm_subsystems
      scaleView n ms₁ ms₂ hn hgt₁ hgt₂ hcop₁ hcop₂

theorem residueView_invariant_at_lcm_subsystems
    (n : Nat) (ms₁ ms₂ : List Nat) (hn : n ≠ 0)
    (hgt₁ : ∀ m ∈ ms₁, 1 < m) (hgt₂ : ∀ m ∈ ms₂, 1 < m)
    (hcop₁ : ∀ m ∈ ms₁, (10 : Nat).Coprime m) (hcop₂ : ∀ m ∈ ms₂, (10 : Nat).Coprime m) :
    projectView residueView (ms₁ ++ ms₂) (tick10 (Nat.lcm (totientLCM ms₁) (totientLCM ms₂)) n) =
      projectView residueView (ms₁ ++ ms₂) n := by
  exact
    projectView_invariant_at_lcm_subsystems
      residueView n ms₁ ms₂ hn hgt₁ hgt₂ hcop₁ hcop₂

theorem projectView_invariant_of_chart_change_ratio
    {α : Type} (f : KernelState → α)
    (n k : Nat) (ms : List Nat) (hn : n ≠ 0)
    (hcop : ms.Pairwise Nat.Coprime) (hpos : ∀ m ∈ ms, 0 < m)
    {s : Nat}
    (hRatio : ∀ m ∈ ms, m / Nat.gcd m s = m / Nat.gcd m (10 ^ k - 1))
    (hnode : CycleStepOrbit.nodeClosure ms s n) :
    projectView f ms (tick10 k n) = projectView f ms n := by
  unfold projectView kernelState
  exact congrArg f
    (systemCoord_invariant_of_nodeClosure_chart_change_ratio
      n k ms hn hcop hpos hRatio hnode)

theorem projectView_invariant_of_chart_change_coprime
    {α : Type} (f : KernelState → α)
    (n k : Nat) (ms : List Nat) (hn : n ≠ 0)
    (hcop : ms.Pairwise Nat.Coprime) (hpos : ∀ m ∈ ms, 0 < m)
    {s : Nat}
    (hcopS : ∀ m ∈ ms, Nat.Coprime m s)
    (hcopTick : ∀ m ∈ ms, Nat.Coprime m (10 ^ k - 1))
    (hnode : CycleStepOrbit.nodeClosure ms s n) :
    projectView f ms (tick10 k n) = projectView f ms n := by
  unfold projectView kernelState
  exact congrArg f
    (systemCoord_invariant_of_nodeClosure_chart_change_coprime
      n k ms hn hcop hpos hcopS hcopTick hnode)

theorem projectView_invariant_of_chart_change_append_of_parts_ratio
    {α : Type} (f : KernelState → α)
    (n k : Nat) (ms₁ ms₂ : List Nat) (hn : n ≠ 0)
    (hcop : (ms₁ ++ ms₂).Pairwise Nat.Coprime) (hpos : ∀ m ∈ ms₁ ++ ms₂, 0 < m)
    {s : Nat}
    (hRatio₁ : ∀ m ∈ ms₁, m / Nat.gcd m s = m / Nat.gcd m (10 ^ k - 1))
    (hRatio₂ : ∀ m ∈ ms₂, m / Nat.gcd m s = m / Nat.gcd m (10 ^ k - 1))
    (h₁ : CycleStepOrbit.nodeClosure ms₁ s n)
    (h₂ : CycleStepOrbit.nodeClosure ms₂ s n) :
    projectView f (ms₁ ++ ms₂) (tick10 k n) = projectView f (ms₁ ++ ms₂) n := by
  unfold projectView kernelState
  exact congrArg f
    (systemCoord_invariant_of_nodeClosure_chart_change_append_of_parts_ratio
      n k ms₁ ms₂ hn hcop hpos hRatio₁ hRatio₂ h₁ h₂)

theorem projectView_invariant_of_chart_change_append_of_parts_coprime
    {α : Type} (f : KernelState → α)
    (n k : Nat) (ms₁ ms₂ : List Nat) (hn : n ≠ 0)
    (hcop : (ms₁ ++ ms₂).Pairwise Nat.Coprime) (hpos : ∀ m ∈ ms₁ ++ ms₂, 0 < m)
    {s : Nat}
    (hcopS₁ : ∀ m ∈ ms₁, Nat.Coprime m s)
    (hcopS₂ : ∀ m ∈ ms₂, Nat.Coprime m s)
    (hcopTick₁ : ∀ m ∈ ms₁, Nat.Coprime m (10 ^ k - 1))
    (hcopTick₂ : ∀ m ∈ ms₂, Nat.Coprime m (10 ^ k - 1))
    (h₁ : CycleStepOrbit.nodeClosure ms₁ s n)
    (h₂ : CycleStepOrbit.nodeClosure ms₂ s n) :
    projectView f (ms₁ ++ ms₂) (tick10 k n) = projectView f (ms₁ ++ ms₂) n := by
  unfold projectView kernelState
  exact congrArg f
    (systemCoord_invariant_of_nodeClosure_chart_change_append_of_parts_coprime
      n k ms₁ ms₂ hn hcop hpos hcopS₁ hcopS₂ hcopTick₁ hcopTick₂ h₁ h₂)

/-- One-call package for globalTick+globalTick aspect invariance (scale + residue). -/
theorem aspect_projection_package_globalTick_add
    (n : Nat) (ms : List Nat) (a₂ a₅ b₂ b₅ : Nat) (hn : n ≠ 0)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    (projectView scaleView ms (tick10 (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) n) =
      projectView scaleView ms n)
    ∧ (projectView residueView ms (tick10 (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) n) =
      projectView residueView ms n) := by
  exact ⟨
    scaleView_invariant_at_globalTick_add n ms a₂ a₅ b₂ b₅ hn hgt hcop,
    residueView_invariant_at_globalTick_add n ms a₂ a₅ b₂ b₅ hn hgt hcop
  ⟩

/-- One-call package for totientLCM aspect invariance (scale + residue). -/
theorem aspect_projection_package_totientLCM
    (n : Nat) (ms : List Nat) (hn : n ≠ 0)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    (projectView scaleView ms (tick10 (totientLCM ms) n) = projectView scaleView ms n)
    ∧ (projectView residueView ms (tick10 (totientLCM ms) n) = projectView residueView ms n) := by
  exact ⟨
    scaleView_invariant_at_totientLCM n ms hn hgt hcop,
    residueView_invariant_at_totientLCM n ms hn hgt hcop
  ⟩

/-- One-call package for subsystem-lcm aspect invariance (scale + residue). -/
theorem aspect_projection_package_lcm_subsystems
    (n : Nat) (ms₁ ms₂ : List Nat) (hn : n ≠ 0)
    (hgt₁ : ∀ m ∈ ms₁, 1 < m) (hgt₂ : ∀ m ∈ ms₂, 1 < m)
    (hcop₁ : ∀ m ∈ ms₁, (10 : Nat).Coprime m) (hcop₂ : ∀ m ∈ ms₂, (10 : Nat).Coprime m) :
    (projectView scaleView (ms₁ ++ ms₂) (tick10 (Nat.lcm (totientLCM ms₁) (totientLCM ms₂)) n) =
      projectView scaleView (ms₁ ++ ms₂) n)
    ∧ (projectView residueView (ms₁ ++ ms₂) (tick10 (Nat.lcm (totientLCM ms₁) (totientLCM ms₂)) n) =
      projectView residueView (ms₁ ++ ms₂) n) := by
  exact ⟨
    scaleView_invariant_at_lcm_subsystems n ms₁ ms₂ hn hgt₁ hgt₂ hcop₁ hcop₂,
    residueView_invariant_at_lcm_subsystems n ms₁ ms₂ hn hgt₁ hgt₂ hcop₁ hcop₂
  ⟩

/-- Fixed-parameter smoke theorem for canonical axes `[3,11,13]`. -/
theorem aspect_projection_package_globalTick_add_smoke_3_11_13 :
    (projectView scaleView ([3, 11, 13] : List Nat)
        (tick10
          (globalTick ([3, 11, 13] : List Nat) 1 1 + globalTick ([3, 11, 13] : List Nat) 1 1)
          1)
        =
      projectView scaleView ([3, 11, 13] : List Nat) 1)
    ∧
    (projectView residueView ([3, 11, 13] : List Nat)
        (tick10
          (globalTick ([3, 11, 13] : List Nat) 1 1 + globalTick ([3, 11, 13] : List Nat) 1 1)
          1)
        =
      projectView residueView ([3, 11, 13] : List Nat) 1) := by
  exact aspect_projection_package_globalTick_add
    1 ([3, 11, 13] : List Nat) 1 1 1 1 (by decide)
    (by
      intro m hm
      simp at hm
      rcases hm with rfl | rfl | rfl <;> decide)
    (by
      intro m hm
      simp at hm
      rcases hm with rfl | rfl | rfl <;> decide)

end AspectProjectionKernel
