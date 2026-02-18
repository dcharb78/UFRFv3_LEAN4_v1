import REST_Seam_Core_Theorem
import Breathing_Cycle_LOG_Partition_Theorem

/-!
# REST-Anchored Seam Overlap (Discrete 14-State Bookkeeping)

This file formalizes the bookkeeping convention used in the UFRF docs:

- local cycle state is tracked on `0..13` (`mod 14`),
- new contexts are born every `10` ticks (REST-anchored births),
- parent COMPLETE (`11,12,13`) overlaps child SEED (`1,2,3`).

No physics assumptions are used here; this is a pure `Nat`/`mod` statement.
-/

namespace RESTSeamOverlap

/-!
## 14→13 collapse (bookkeeping)

The seam bookkeeping tracks local states on `0..13` (`mod 14`) to represent the overlap window.
To compare with the intrinsic 13-cycle view, we collapse a seam state `n` to `n mod 13`,
so that `13 ↦ 0`.
-/

def collapse13 (n : Nat) : Fin 13 := ⟨n % 13, Nat.mod_lt n (by decide)⟩

theorem collapse13_13 : collapse13 13 = (0 : Fin 13) := by
  apply Fin.ext
  simp [collapse13]

theorem collapse13_11 : collapse13 11 = (11 : Fin 13) := by
  apply Fin.ext
  simp [collapse13]

theorem collapse13_12 : collapse13 12 = (12 : Fin 13) := by
  apply Fin.ext
  simp [collapse13]

theorem collapse13_10 : collapse13 10 = (10 : Fin 13) := by
  apply Fin.ext
  simp [collapse13]

/--
REST-anchored birth:
- parent reaches REST (`10`)
- child is at seam/VOID (`0`)
at the same global tick.
-/
theorem parent_rest_child_void (g : Nat) :
    state g (birth g + rest) = rest ∧ state (g + 1) (birth g + rest) = 0 := by
  have hb : birth (g + 1) = birth g + 10 := birth_succ g
  constructor
  · rw [state, stateFrom_shift]
    simp [rest, cycle]
  · have ht : birth g + rest = birth (g + 1) := by
      simpa [rest] using hb.symm
    rw [state, ht, stateFrom_at_birth]

theorem parent11_child1 (g : Nat) :
    state g (birth g + 11) = 11 ∧ state (g + 1) (birth g + 11) = 1 := by
  have hb : birth (g + 1) = birth g + 10 := birth_succ g
  have ht : birth g + 11 = birth (g + 1) + 1 := by
    rw [hb]
  constructor
  · rw [state, stateFrom_shift]
    simp [cycle]
  · rw [state, ht, stateFrom_shift]
    simp [cycle]

theorem parent12_child2 (g : Nat) :
    state g (birth g + 12) = 12 ∧ state (g + 1) (birth g + 12) = 2 := by
  have hb : birth (g + 1) = birth g + 10 := birth_succ g
  have ht : birth g + 12 = birth (g + 1) + 2 := by
    rw [hb]
  constructor
  · rw [state, stateFrom_shift]
    simp [cycle]
  · rw [state, ht, stateFrom_shift]
    simp [cycle]

theorem parent13_child3 (g : Nat) :
    state g (birth g + 13) = 13 ∧ state (g + 1) (birth g + 13) = 3 := by
  have hb : birth (g + 1) = birth g + 10 := birth_succ g
  have ht : birth g + 13 = birth (g + 1) + 3 := by
    rw [hb]
  constructor
  · rw [state, stateFrom_shift]
    simp [cycle]
  · rw [state, ht, stateFrom_shift]
    simp [cycle]

/--
Packaged overlap law:
parent COMPLETE (`11..13`) overlaps child SEED (`1..3`) under REST-anchored births.
-/
def parentComplete_childSeed_stmt (g : Nat) : Prop :=
    (state g (birth g + 11) = 11 ∧ state (g + 1) (birth g + 11) = 1)
  ∧ (state g (birth g + 12) = 12 ∧ state (g + 1) (birth g + 12) = 2)
  ∧ (state g (birth g + 13) = 13 ∧ state (g + 1) (birth g + 13) = 3)

theorem parentComplete_childSeed (g : Nat) : parentComplete_childSeed_stmt g := by
  exact ⟨parent11_child1 g, parent12_child2 g, parent13_child3 g⟩

theorem collapse13_parentRest (g : Nat) :
    collapse13 (state g (birth g + rest)) = (10 : Fin 13) := by
  have h : state g (birth g + rest) = rest := (parent_rest_child_void g).1
  calc
    collapse13 (state g (birth g + rest)) = collapse13 rest := by
      simp [h]
    _ = (10 : Fin 13) := by
      simpa [rest] using collapse13_10

def collapse13_parentComplete_in_bridge_stmt (g : Nat) : Prop :=
    collapse13 (state g (birth g + 11)) ∈ BreathingCycleLOGPartition.bridge
    ∧ collapse13 (state g (birth g + 12)) ∈ BreathingCycleLOGPartition.bridge
    ∧ collapse13 (state g (birth g + 13)) ∈ BreathingCycleLOGPartition.bridge

theorem collapse13_parentComplete_in_bridge (g : Nat) :
    collapse13_parentComplete_in_bridge_stmt g := by
  have h11 : state g (birth g + 11) = 11 := (parent11_child1 g).1
  have h12 : state g (birth g + 12) = 12 := (parent12_child2 g).1
  have h13 : state g (birth g + 13) = 13 := (parent13_child3 g).1
  refine ⟨?_, ?_, ?_⟩
  · -- `11` is in the bridge tail `{11,12,0}`.
    have : collapse13 (state g (birth g + 11)) = (11 : Fin 13) := by
      simpa [h11] using collapse13_11
    simp [this, BreathingCycleLOGPartition.bridge]
  · -- `12` is in the bridge tail `{11,12,0}`.
    have : collapse13 (state g (birth g + 12)) = (12 : Fin 13) := by
      simpa [h12] using collapse13_12
    simp [this, BreathingCycleLOGPartition.bridge]
  · -- `13` collapses to `0`, which is also in the bridge tail.
    have : collapse13 (state g (birth g + 13)) = (0 : Fin 13) := by
      simpa [h13] using collapse13_13
    simp [this, BreathingCycleLOGPartition.bridge]

end RESTSeamOverlap
