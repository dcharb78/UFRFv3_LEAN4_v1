import Mathlib

/-!
# REST Seam Core (Canonical)

Canonical fixed-parameter seam definitions for UFRF:
- `cycle = 14`
- `rest = 10`
- births/states and basic shift lemmas.
-/

namespace RESTSeamOverlap

def cycle : Nat := 14
def rest : Nat := 10

def birth (g : Nat) : Nat := g * 10

/-- Seam tick family for parent context `g`: REST crossing plus local offset `r`. -/
def seamTick (g r : Nat) : Nat := birth g + rest + r

/-- Multi-level seam tick family (`j` nested REST shifts from parent `g`). -/
def seamTickN (g j r : Nat) : Nat := birth g + j * rest + r

/-- Local state of a context with birth-time `b`, tracked in the 14-state seam chart. -/
def stateFrom (b t : Nat) : Nat := (t - b) % cycle

/-- Local state of phase-group `g` at global tick `t`. -/
def state (g t : Nat) : Nat := stateFrom (birth g) t

theorem seamTick_pos (g r : Nat) : 0 < seamTick g r := by
  unfold seamTick birth rest
  omega

theorem seamTick_ne_zero (g r : Nat) : seamTick g r ≠ 0 := by
  exact Nat.ne_of_gt (seamTick_pos g r)

@[simp] theorem stateFrom_at_birth (b : Nat) : stateFrom b b = 0 := by
  simp [stateFrom, cycle]

@[simp] theorem stateFrom_shift (b r : Nat) : stateFrom b (b + r) = r % cycle := by
  simp [stateFrom, cycle]

theorem birth_succ (g : Nat) : birth (g + 1) = birth g + 10 := by
  simp [birth, Nat.succ_mul]

theorem seamTick_as_child_birth_plus (g r : Nat) :
    seamTick g r = birth (g + 1) + r := by
  simp [seamTick, rest, birth_succ]

theorem seamTickN_as_descendant_birth_plus (g j r : Nat) :
    seamTickN g j r = birth (g + j) + r := by
  unfold seamTickN birth rest
  calc
    g * 10 + j * 10 + r = (g + j) * 10 + r := by
      rw [Nat.add_mul]
    _ = birth (g + j) + r := by simp [birth]

end RESTSeamOverlap
