import Mathlib

/-!
# Triad Balance Definition Theorem

Formal kernel definition for `CC-0021`:

`B(a,b,c) = (a*b*c)/(a+b+c)` (with denominator nonzero for evaluated identities).
-/

namespace UFRF

/-- Triad balance functional on rational triples. -/
def triadBalance (a b c : ℚ) : ℚ :=
  (a * b * c) / (a + b + c)

theorem triadBalance_def (a b c : ℚ) :
    triadBalance a b c = (a * b * c) / (a + b + c) := by
  rfl

theorem triadBalance_swap_ab (a b c : ℚ) :
    triadBalance a b c = triadBalance b a c := by
  unfold triadBalance
  ring

theorem triadBalance_swap_bc (a b c : ℚ) :
    triadBalance a b c = triadBalance a c b := by
  unfold triadBalance
  ring

theorem triadBalance_cyclic (a b c : ℚ) :
    triadBalance a b c = triadBalance b c a := by
  unfold triadBalance
  ring

/--
If `a+b+c ≠ 0`, triad balance recovers the defining cross-multiplied identity.
-/
theorem triadBalance_mul_sum (a b c : ℚ) (h : a + b + c ≠ 0) :
    triadBalance a b c * (a + b + c) = a * b * c := by
  unfold triadBalance
  field_simp [h]

end UFRF
