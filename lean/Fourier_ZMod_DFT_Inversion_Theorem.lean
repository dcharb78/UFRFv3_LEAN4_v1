import Mathlib.Analysis.Fourier.ZMod

/-!
# Discrete Fourier on `ZMod N`: inversion and explicit inverse transform

Mathlib defines the discrete Fourier transform on the finite cycle `ZMod N` as a `LinearEquiv`
(`ZMod.dft`, notation `𝓕` scoped in namespace `ZMod`). This file restates the core inversion
facts as small bridge lemmas we can reference from the UFRF proof spine:

* `𝓕` is invertible (by construction as a linear equivalence).
* applying `𝓕` twice yields a reflection, scaled by `N` (a common finite-cycle inversion form).
* the inverse transform has an explicit finite-sum formula.

All statements are exact (no floating numerics).
-/

open scoped BigOperators
open scoped ZMod

namespace FourierZMod

open ZMod AddChar

variable {N : ℕ} [NeZero N]
variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- Explicit inverse-transform formula (as a finite sum). -/
theorem invDFT_apply (Ψ : ZMod N → E) (k : ZMod N) :
    𝓕⁻ Ψ k = (N : ℂ)⁻¹ • ∑ j : ZMod N, stdAddChar (j * k) • Ψ j := by
  simpa using (ZMod.invDFT_apply (N := N) (E := E) Ψ k)

/-- `𝓕⁻` is a left inverse of `𝓕` (packaged for narrative use). -/
theorem inv_dft (Φ : ZMod N → E) : 𝓕⁻ (𝓕 Φ) = Φ := by
  simp

/-- `𝓕⁻` is a right inverse of `𝓕` (packaged for narrative use). -/
theorem dft_inv (Ψ : ZMod N → E) : 𝓕 (𝓕⁻ Ψ) = Ψ := by
  simp

/--
**Discrete inversion (double DFT) formula:**

`𝓕 (𝓕 Φ)(j) = (N : ℂ) • Φ(-j)`.
-/
theorem dft_dft (Φ : ZMod N → E) :
    𝓕 (𝓕 Φ) = fun j : ZMod N => (N : ℂ) • Φ (-j) := by
  simpa using (ZMod.dft_dft (N := N) (E := E) Φ)

end FourierZMod
