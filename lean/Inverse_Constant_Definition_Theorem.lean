import Mathlib

/-!
# Inverse Constant Definition Theorem

Kernel algebra identity for `CC-0013`:
for a nonzero constant `c`, the inverse is `1 / c`.
-/

namespace UFRF

theorem inverse_eq_one_div (c : ℚ) : c⁻¹ = 1 / c := by
  simp [one_div]

theorem inverse_eq_one_div_of_ne_zero {c : ℚ} (_hc : c ≠ 0) : c⁻¹ = 1 / c := by
  simp [one_div]

theorem inverse_mul_cancel_of_ne_zero {c : ℚ} (hc : c ≠ 0) : c⁻¹ * c = 1 := by
  exact inv_mul_cancel₀ hc

end UFRF
