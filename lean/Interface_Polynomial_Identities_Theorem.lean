import Mathlib
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# Interface Polynomial Identities Theorem

Kernel-level polynomial identities for the three interface constants used by
`CC-0023`:

* Golden ratio: `φ^2 = φ + 1`
* Silver ratio: `(1 + √2)^2 = 2(1 + √2) + 1`
* Plastic ratio: choose a real root `ρ > 1` of `ρ^3 = ρ + 1`
-/

namespace UFRF

open scoped goldenRatio

/-- Silver ratio in the classical quadratic-radical form. -/
noncomputable def silverRatio : ℝ := 1 + Real.sqrt 2

/-- Golden ratio polynomial identity. -/
theorem goldenRatio_polynomial :
    (φ : ℝ) ^ 2 = (φ : ℝ) + 1 := by
  simp [Real.goldenRatio_sq]

/-- Silver ratio polynomial identity. -/
theorem silverRatio_polynomial :
    silverRatio ^ 2 = 2 * silverRatio + 1 := by
  unfold silverRatio
  calc
    (1 + Real.sqrt 2) ^ 2 = 1 + 2 * Real.sqrt 2 + (Real.sqrt 2) ^ 2 := by ring
    _ = 1 + 2 * Real.sqrt 2 + 2 := by
      have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      simp [hs]
    _ = 2 * (1 + Real.sqrt 2) + 1 := by ring

/-- There exists a real root `ρ > 1` to `ρ^3 = ρ + 1` (plastic-ratio equation). -/
theorem exists_plasticRatio :
    ∃ ρ : ℝ, 1 < ρ ∧ ρ ^ 3 = ρ + 1 := by
  let f : ℝ → ℝ := fun x => x ^ 3 - x - 1
  have hcont : Continuous f := by
    simpa [f] using (((continuous_id.pow 3).sub continuous_id).sub continuous_const)
  have hsurj : Set.SurjOn f (Set.Icc (1 : ℝ) 2) (Set.Icc (f 1) (f 2)) := by
    simpa using
      (intermediate_value_Icc
        (f := f)
        (a := (1 : ℝ))
        (b := (2 : ℝ))
        (by norm_num)
        hcont.continuousOn)
  have hzero : (0 : ℝ) ∈ Set.Icc (f 1) (f 2) := by
    have h1 : f 1 = (-1 : ℝ) := by
      simp [f]
    have h2 : f 2 = (5 : ℝ) := by
      norm_num [f]
    simp [h1, h2]
  rcases hsurj hzero with ⟨ρ, hρIcc, hρroot⟩
  have hρeq : ρ ^ 3 = ρ + 1 := by
    have : ρ ^ 3 - ρ - 1 = 0 := by simpa [f] using hρroot
    linarith
  have hρne1 : ρ ≠ 1 := by
    intro h1
    have hρroot' := hρroot
    -- Rewrite the root equation at `ρ = 1`, then finish by numeric normalization.
    simp [f, h1] at hρroot'
  have hne : (1 : ℝ) ≠ ρ := by exact fun h => hρne1 h.symm
  exact ⟨ρ, lt_of_le_of_ne hρIcc.1 hne, hρeq⟩

/-- A canonical chosen real plastic ratio (`ρ > 1`, `ρ^3 = ρ + 1`). -/
noncomputable def plasticRatio : ℝ := Classical.choose exists_plasticRatio

/-- Chosen plastic ratio is strictly above `1`. -/
theorem plasticRatio_gt_one : 1 < plasticRatio :=
  (Classical.choose_spec exists_plasticRatio).1

/-- Chosen plastic ratio satisfies the cubic interface polynomial. -/
theorem plasticRatio_polynomial : plasticRatio ^ 3 = plasticRatio + 1 :=
  (Classical.choose_spec exists_plasticRatio).2

/-- Bundled `CC-0023` interface-constant polynomial identities. -/
theorem interfacePolynomialIdentities :
    ((φ : ℝ) ^ 2 = (φ : ℝ) + 1) ∧
      (silverRatio ^ 2 = 2 * silverRatio + 1) ∧
      (plasticRatio ^ 3 = plasticRatio + 1) := by
  exact ⟨goldenRatio_polynomial, silverRatio_polynomial, plasticRatio_polynomial⟩

end UFRF
