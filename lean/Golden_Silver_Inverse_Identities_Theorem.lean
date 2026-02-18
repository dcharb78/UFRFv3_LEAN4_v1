import Mathlib
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# Golden/Silver Inverse Identities Theorem

Kernel inverse identities used in `CC-0015` and `CC-0016`:

* `1 / φ = φ - 1`
* `1 / (1 + √2) = √2 - 1`
-/

namespace UFRF

open scoped goldenRatio

theorem goldenRatio_inverse_identity :
    (1 : ℝ) / (φ : ℝ) = (φ : ℝ) - 1 := by
  apply (div_eq_iff Real.goldenRatio_ne_zero).2
  calc
    (1 : ℝ) = ((φ : ℝ) + 1) - (φ : ℝ) := by ring
    _ = (φ : ℝ) ^ 2 - (φ : ℝ) := by simp [Real.goldenRatio_sq]
    _ = ((φ : ℝ) - 1) * (φ : ℝ) := by ring

theorem silverRatio_inverse_identity :
    (1 : ℝ) / (1 + Real.sqrt 2) = Real.sqrt 2 - 1 := by
  have hden : (1 + Real.sqrt 2 : ℝ) ≠ 0 := by
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  apply (div_eq_iff hden).2
  calc
    (1 : ℝ) = (2 : ℝ) - 1 := by norm_num
    _ = (Real.sqrt 2) ^ 2 - 1 := by
      have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      simp [hs]
    _ = (Real.sqrt 2 - 1) * (1 + Real.sqrt 2) := by ring

end UFRF
