import Mathlib

/-!
# Seam Generic Classification

Small generic window predicates for seam-style classification.
-/

namespace SeamGeneric

def isWindow123 (x : Nat) : Prop := x = 1 ∨ x = 2 ∨ x = 3

def isShiftedWindow123 (k x : Nat) : Prop := x = k + 1 ∨ x = k + 2 ∨ x = k + 3

theorem isShiftedWindow123_at_add_iff_window123 (k r : Nat) (hr : r ≤ 3) :
    isShiftedWindow123 k (k + r) ↔ isWindow123 r := by
  interval_cases r <;> simp [isShiftedWindow123, isWindow123]

end SeamGeneric
