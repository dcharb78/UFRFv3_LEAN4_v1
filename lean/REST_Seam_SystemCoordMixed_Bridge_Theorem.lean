import REST_Seam_Core_Theorem
import REST_Seam_NodeClosure_Bridge_Theorem
import Multidimensional_Ticks_Theorem

/-!
# REST Seam ↔ `systemCoordMixed` Bridge

Packages seam-window closure into the mixed-coordinate observer container.
-/

namespace RESTSeamOverlap

open MultidimensionalTicks

theorem systemCoordMixed_empty_1_1_at_seamTick (g r : Nat) :
    systemCoordMixed ([] : List Nat) 1 1 (seamTick g r) =
      (UniversalTicks.leadingBlock (seamTick g r), [], (seamTick g r) % 2, (seamTick g r) % 5) := by
  simp [systemCoordMixed]

theorem systemCoordMixed_empty_1_1_at_seamTick_of_nodeClosure14
    (g r : Nat) (hr : r ≤ 3)
    (hnode : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r) :
    systemCoordMixed ([] : List Nat) 1 1 (seamTick g r) =
      (UniversalTicks.leadingBlock (seamTick g r), [], 0, 0) := by
  have hr0 : r = 0 := (nodeClosure_singleton14_step1_iff_zero_of_le3 r hr).1 hnode
  rw [hr0]
  have hmod2 : (g * 10 + 10) % 2 = 0 := by
    simpa [Nat.add_comm] using (show (10 + g * 10) % 2 = 0 by simp [Nat.add_mod, Nat.mul_mod])
  have hmod5 : (g * 10 + 10) % 5 = 0 := by
    simpa [Nat.add_comm] using (show (10 + g * 10) % 5 = 0 by simp [Nat.add_mod, Nat.mul_mod])
  simp [systemCoordMixed, seamTick, birth, rest, hmod2, hmod5]

theorem systemCoordMixed_globalTick_from_seamNodeClosure14
    (g r : Nat) (hr : r ≤ 3)
    (hnode : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    (ms : List Nat)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    systemCoordMixed ms 1 1 (tick10 (globalTick ms 1 1) (seamTick g r)) =
      (UniversalTicks.leadingBlock (seamTick g 0),
        ms.map (fun m => (seamTick g 0) % m), 0, 0) := by
  have hr0 : r = 0 := (nodeClosure_singleton14_step1_iff_zero_of_le3 r hr).1 hnode
  have hseam : seamTick g r = seamTick g 0 := by simp [hr0]
  have hglob :=
    systemCoordMixed_invariant_at_globalTick
      (n := seamTick g r) (ms := ms) (a₂ := 1) (a₅ := 1)
      (hn := seamTick_ne_zero g r) (hgt := hgt) (hcop := hcop)
  simpa [hseam] using hglob

theorem systemCoordMixed_globalTick_from_seamNodeClosure14_general
    (g r : Nat) (hr : r ≤ 3)
    (hnode : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    (ms : List Nat) (a₂ a₅ : Nat)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    systemCoordMixed ms a₂ a₅ (tick10 (globalTick ms a₂ a₅) (seamTick g r)) =
      (UniversalTicks.leadingBlock (seamTick g 0),
        ms.map (fun m => (seamTick g 0) % m), 0, 0) := by
  have hr0 : r = 0 := (nodeClosure_singleton14_step1_iff_zero_of_le3 r hr).1 hnode
  have hseam : seamTick g r = seamTick g 0 := by simp [hr0]
  have hglob :=
    systemCoordMixed_invariant_at_globalTick
      (n := seamTick g r) (ms := ms) (a₂ := a₂) (a₅ := a₅)
      (hn := seamTick_ne_zero g r) (hgt := hgt) (hcop := hcop)
  simpa [hseam] using hglob

theorem systemCoordMixed_globalTick_add_from_seamNodeClosure14_general
    (g r : Nat) (hr : r ≤ 3)
    (hnode : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    (ms : List Nat) (a₂ a₅ b₂ b₅ : Nat)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    systemCoordMixed ms a₂ a₅
      (tick10 (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) (seamTick g r)) =
      (UniversalTicks.leadingBlock (seamTick g 0),
        ms.map (fun m => (seamTick g 0) % m), 0, 0) := by
  have hr0 : r = 0 := (nodeClosure_singleton14_step1_iff_zero_of_le3 r hr).1 hnode
  have hseam : seamTick g r = seamTick g 0 := by simp [hr0]
  have hglob :=
    systemCoordMixed_invariant_at_globalTick_add
      (n := seamTick g r) (ms := ms)
      (a₂ := a₂) (a₅ := a₅) (b₂ := b₂) (b₅ := b₅)
      (hn := seamTick_ne_zero g r) (hgt := hgt) (hcop := hcop)
  simpa [hseam] using hglob

end RESTSeamOverlap
