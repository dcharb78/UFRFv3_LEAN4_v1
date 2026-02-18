import Mathlib

/-!
# C-Transform Identity Theorem

Kernel formalization for `CC-0002`:

`C_transform = |-(1/√10)| = 1/√10`.
-/

namespace UFRF

/-- `C_transform` in the constants track. -/
noncomputable def cTransform : ℝ := abs (-((1 : ℝ) / Real.sqrt 10))

theorem cTransform_eq_inv_sqrt10 :
    cTransform = (1 : ℝ) / Real.sqrt 10 := by
  unfold cTransform
  have hsqrt_pos : 0 < Real.sqrt 10 := by
    exact Real.sqrt_pos.2 (by norm_num)
  have hfrac_pos : 0 < (1 : ℝ) / Real.sqrt 10 := by
    exact div_pos (by norm_num) hsqrt_pos
  -- `simp` uses `abs_neg` and `abs_of_pos` with `hfrac_pos`.
  simp

theorem cTransform_pos : 0 < cTransform := by
  rw [cTransform_eq_inv_sqrt10]
  have hsqrt_pos : 0 < Real.sqrt 10 := by
    exact Real.sqrt_pos.2 (by norm_num)
  exact div_pos (by norm_num) hsqrt_pos

end UFRF
