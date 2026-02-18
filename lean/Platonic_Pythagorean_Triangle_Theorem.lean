import Mathlib

/-!
# Platonic/Pythagorean Triangle Theorem

Discrete + exact-real triangle anchors:

- Pythagorean integer triples (`3,4,5`, `5,12,13`, `8,15,17`)
- Plato/Timaeus right-triangle forms (`1,1,√2` and `1,√3,2`)

These are encoded as exact identities (no floating approximations).
-/

namespace UFRF

/-- Integer Pythagorean-triple predicate. -/
def isPythagoreanTriple (a b c : Nat) : Prop :=
  a ^ 2 + b ^ 2 = c ^ 2

theorem pythagorean_3_4_5 : isPythagoreanTriple 3 4 5 := by
  change ((3 : Nat) ^ 2 + (4 : Nat) ^ 2 = (5 : Nat) ^ 2)
  native_decide

theorem pythagorean_5_12_13 : isPythagoreanTriple 5 12 13 := by
  change ((5 : Nat) ^ 2 + (12 : Nat) ^ 2 = (13 : Nat) ^ 2)
  native_decide

theorem pythagorean_8_15_17 : isPythagoreanTriple 8 15 17 := by
  change ((8 : Nat) ^ 2 + (15 : Nat) ^ 2 = (17 : Nat) ^ 2)
  native_decide

theorem pythagorean_5_12_13_with_source_link :
    isPythagoreanTriple 5 12 13 ∧ (12 + 1 = 13) := by
  exact ⟨pythagorean_5_12_13, by native_decide⟩

/--
Plato/Timaeus isosceles right-triangle identity:
`1² + 1² = (√2)²`.
-/
theorem plato_isosceles_1_1_sqrt2 :
    (1 : ℝ) ^ 2 + (1 : ℝ) ^ 2 = (Real.sqrt 2) ^ 2 := by
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  nlinarith [hs]

/--
Plato/Timaeus scalene right-triangle identity:
`1² + (√3)² = 2²`.
-/
theorem plato_scalene_1_sqrt3_2 :
    (1 : ℝ) ^ 2 + (Real.sqrt 3) ^ 2 = (2 : ℝ) ^ 2 := by
  have hs : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  nlinarith [hs]

end UFRF
