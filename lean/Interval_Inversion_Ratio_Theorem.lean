import Mathlib

/-!
# Interval Inversion Ratio Theorem

Formalizes the ratio-level music-interval inversion rule:
swapping `(a:b)` to `(b:a)` is involutive, preserves positivity (under `a,b > 0`),
and yields a multiplicative reciprocal relation.
-/

namespace UFRF

/-- Swap an ordered ratio pair `(a,b)` to `(b,a)`. -/
def invertInterval (a b : ℚ) : ℚ × ℚ := (b, a)

/-- Numeric value of an interval ratio `(a:b)` as `a / b`. -/
def intervalRatio (a b : ℚ) : ℚ := a / b

/-- Inversion is involutive at the pair level. -/
theorem invertInterval_involutive (a b : ℚ) :
    invertInterval (invertInterval a b).1 (invertInterval a b).2 = (a, b) := by
  rfl

/-- Positive interval ratios stay positive after inversion (assuming positive terms). -/
theorem intervalRatio_pos_of_pos {a b : ℚ} (ha : 0 < a) (hb : 0 < b) :
    0 < intervalRatio a b := by
  simpa [intervalRatio] using div_pos ha hb

/-- Product of a ratio and its inversion is exactly `1` (nonzero assumptions). -/
theorem intervalRatio_mul_inversion_eq_one {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) :
    intervalRatio a b * intervalRatio b a = 1 := by
  unfold intervalRatio
  field_simp [ha, hb]

/-- Inverted ratio equals multiplicative inverse of the original (nonzero assumptions). -/
theorem intervalRatio_inversion_eq_inv {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) :
    intervalRatio b a = (intervalRatio a b)⁻¹ := by
  unfold intervalRatio
  field_simp [ha, hb]

end UFRF
