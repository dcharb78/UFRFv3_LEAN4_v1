import Mathlib

/-!
# Seam Generic API

Parameterized seam bookkeeping (`cycle`, `stride`) independent of a fixed UFRF instantiation.
-/

namespace SeamGeneric

structure Params where
  cycle : Nat
  stride : Nat
  cycle_pos : 0 < cycle

def birth (P : Params) (g : Nat) : Nat := g * P.stride

def stateFrom (P : Params) (b t : Nat) : Nat := (t - b) % P.cycle

def state (P : Params) (g t : Nat) : Nat := stateFrom P (birth P g) t

def seamTick (P : Params) (g r : Nat) : Nat := birth P g + P.stride + r

def seamTickN (P : Params) (g j r : Nat) : Nat := birth P g + j * P.stride + r

@[simp] theorem stateFrom_at_birth (P : Params) (b : Nat) : stateFrom P b b = 0 := by
  simp [stateFrom]

@[simp] theorem stateFrom_shift (P : Params) (b r : Nat) : stateFrom P b (b + r) = r % P.cycle := by
  simp [stateFrom]

theorem seamTick_as_child_birth_plus (P : Params) (g r : Nat) :
    seamTick P g r = birth P (g + 1) + r := by
  unfold seamTick birth
  change g * P.stride + P.stride + r = (Nat.succ g) * P.stride + r
  rw [Nat.succ_mul]

theorem seamTickN_as_descendant_birth_plus (P : Params) (g j r : Nat) :
    seamTickN P g j r = birth P (g + j) + r := by
  unfold seamTickN birth
  calc
    g * P.stride + j * P.stride + r = (g + j) * P.stride + r := by
      rw [Nat.add_mul]
    _ = birth P (g + j) + r := by simp [birth]

theorem state_parent_at_seamTick_mod (P : Params) (g r : Nat) :
    state P g (seamTick P g r) = (P.stride + r) % P.cycle := by
  calc
    state P g (seamTick P g r)
        = stateFrom P (birth P g) (birth P g + (P.stride + r)) := by
            simp [state, seamTick, Nat.add_assoc]
    _ = (P.stride + r) % P.cycle := by
          exact stateFrom_shift P (birth P g) (P.stride + r)

theorem state_child_at_seamTick_mod (P : Params) (g r : Nat) :
    state P (g + 1) (seamTick P g r) = r % P.cycle := by
  calc
    state P (g + 1) (seamTick P g r)
        = stateFrom P (birth P (g + 1)) (birth P (g + 1) + r) := by
            rw [seamTick_as_child_birth_plus]
            simp [state]
    _ = r % P.cycle := by
          exact stateFrom_shift P (birth P (g + 1)) r

theorem state_child_at_seamTick_of_lt (P : Params) (g r : Nat) (hr : r < P.cycle) :
    state P (g + 1) (seamTick P g r) = r := by
  simpa [Nat.mod_eq_of_lt hr] using state_child_at_seamTick_mod P g r

theorem state_descendant_at_seamTickN_mod (P : Params) (g j r : Nat) :
    state P (g + j) (seamTickN P g j r) = r % P.cycle := by
  calc
    state P (g + j) (seamTickN P g j r)
        = stateFrom P (birth P (g + j)) (birth P (g + j) + r) := by
            rw [seamTickN_as_descendant_birth_plus]
            simp [state]
    _ = r % P.cycle := by
          exact stateFrom_shift P (birth P (g + j)) r

theorem state_descendant_at_seamTickN_of_lt (P : Params) (g j r : Nat) (hr : r < P.cycle) :
    state P (g + j) (seamTickN P g j r) = r := by
  simpa [Nat.mod_eq_of_lt hr] using state_descendant_at_seamTickN_mod P g j r

theorem seamTick_ne_zero (P : Params) (hstride : 0 < P.stride) (g r : Nat) :
    seamTick P g r ≠ 0 := by
  have hpos : 0 < seamTick P g r := by
    unfold seamTick birth
    omega
  exact Nat.ne_of_gt hpos

end SeamGeneric
