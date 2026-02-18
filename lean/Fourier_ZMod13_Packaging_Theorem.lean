import Fourier_ZMod_DFT_Translation_Theorem
import Fourier_ZMod_DFT_Convolution_Theorem
import Fourier_ZMod_DFT_Inversion_Theorem

/-!
# Fourier inevitability on the UFRF first cycle (`ZMod 13`)

The general bridge theorems live in:
- `lean/Fourier_ZMod_DFT_Translation_Theorem.lean`
- `lean/Fourier_ZMod_DFT_Convolution_Theorem.lean`

This file packages those statements for the canonical "first full system" cycle length `N = 13`,
so other modules and docs can reference stable names without repeating the specialization.
-/

open scoped BigOperators
open scoped ZMod

namespace FourierZMod13

open ZMod AddChar

/-- Specialized translation diagonalization on the 13-cycle. -/
theorem dft_translate_13
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (Φ : ZMod 13 → E) (t k : ZMod 13) :
    𝓕 (FourierZMod.translate (N := 13) (E := E) t Φ) k =
      stdAddChar (t * k) • 𝓕 Φ k := by
  simpa using (FourierZMod.dft_translate (N := 13) (E := E) Φ t k)

/-- Specialized convolution diagonalization on the 13-cycle. -/
theorem dft_conv_13
    (f g : ZMod 13 → ℂ) (k : ZMod 13) :
    𝓕 (FourierZMod.conv (N := 13) f g) k = (𝓕 f k) * (𝓕 g k) := by
  simpa using (FourierZMod.dft_conv (N := 13) f g k)

/-- Specialized explicit inverse-transform formula on the 13-cycle. -/
theorem invDFT_apply_13
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (Ψ : ZMod 13 → E) (k : ZMod 13) :
    𝓕⁻ Ψ k = (13 : ℂ)⁻¹ • ∑ j : ZMod 13, stdAddChar (j * k) • Ψ j := by
  simpa using (FourierZMod.invDFT_apply (N := 13) (E := E) Ψ k)

/-- Specialized discrete inversion (double DFT) formula on the 13-cycle. -/
theorem dft_dft_13
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (Φ : ZMod 13 → E) :
    𝓕 (𝓕 Φ) = fun j : ZMod 13 => (13 : ℂ) • Φ (-j) := by
  simpa using (FourierZMod.dft_dft (N := 13) (E := E) Φ)

end FourierZMod13
