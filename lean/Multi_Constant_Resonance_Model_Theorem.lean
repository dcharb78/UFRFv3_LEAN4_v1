import Mathlib

/-!
# Multi-Constant Resonance Model Theorem

Kernel formalization for `CC-0030`:

`Resonance = Σᵢ wᵢ * Rᵢ`

This file provides the finite-index weighted-sum skeleton and core linearity
laws needed by later compute/bridge layers.
-/

namespace UFRF

/-- Finite weighted resonance model over `n` channels. -/
def resonanceModel {n : Nat} (w r : Fin n → ℚ) : ℚ :=
  ∑ i : Fin n, w i * r i

theorem resonanceModel_def {n : Nat} (w r : Fin n → ℚ) :
    resonanceModel w r = ∑ i : Fin n, w i * r i := by
  rfl

theorem resonanceModel_zero_right {n : Nat} (w : Fin n → ℚ) :
    resonanceModel w (fun _ => 0) = 0 := by
  unfold resonanceModel
  simp

theorem resonanceModel_zero_left {n : Nat} (r : Fin n → ℚ) :
    resonanceModel (fun _ => 0) r = 0 := by
  unfold resonanceModel
  simp

theorem resonanceModel_add_right {n : Nat} (w r₁ r₂ : Fin n → ℚ) :
    resonanceModel w (fun i => r₁ i + r₂ i)
      = resonanceModel w r₁ + resonanceModel w r₂ := by
  unfold resonanceModel
  simp [mul_add, Finset.sum_add_distrib]

theorem resonanceModel_add_left {n : Nat} (w₁ w₂ r : Fin n → ℚ) :
    resonanceModel (fun i => w₁ i + w₂ i) r
      = resonanceModel w₁ r + resonanceModel w₂ r := by
  unfold resonanceModel
  simp [add_mul, Finset.sum_add_distrib]

theorem resonanceModel_smul_right {n : Nat} (w r : Fin n → ℚ) (a : ℚ) :
    resonanceModel w (fun i => a * r i) = a * resonanceModel w r := by
  unfold resonanceModel
  calc
    (∑ i : Fin n, w i * (a * r i))
        = ∑ i : Fin n, a * (w i * r i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = a * ∑ i : Fin n, w i * r i := by
          symm
          simpa using
            (Finset.mul_sum (s := (Finset.univ : Finset (Fin n)))
              (f := fun i : Fin n => w i * r i) (a := a))
    _ = a * resonanceModel w r := by rfl

theorem resonanceModel_smul_left {n : Nat} (w r : Fin n → ℚ) (a : ℚ) :
    resonanceModel (fun i => a * w i) r = a * resonanceModel w r := by
  unfold resonanceModel
  calc
    (∑ i : Fin n, (a * w i) * r i)
        = ∑ i : Fin n, a * (w i * r i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = a * ∑ i : Fin n, w i * r i := by
          symm
          simpa using
            (Finset.mul_sum (s := (Finset.univ : Finset (Fin n)))
              (f := fun i : Fin n => w i * r i) (a := a))
    _ = a * resonanceModel w r := by rfl

end UFRF
