import Mathlib.Analysis.Fourier.ZMod

/-!
# Discrete Fourier on `ZMod N`: translation becomes multiplication

This file is a small, proof-relevant bridge for the "Fourier is inevitable on cycles" story.

Mathlib already provides a canonical discrete Fourier transform on the finite cycle `ZMod N`:
`ZMod.dft` (notation `𝓕` in scope `ZMod`), built from the standard additive character
`ZMod.stdAddChar`.

Here we prove the key eigen-structure fact:

* Translating a signal in position space corresponds to multiplying its Fourier transform by the
  corresponding character in frequency space.

This is a discrete, exact statement (no floating numerics).
-/

open scoped BigOperators
open scoped ZMod

namespace FourierZMod

open ZMod AddChar

variable {N : ℕ}
variable {E : Type*}

/-- Time-domain translation on the cycle `ZMod N`: `(τ_t Φ)(j) = Φ(j + t)`. -/
def translate (t : ZMod N) (Φ : ZMod N → E) : ZMod N → E :=
  fun j => Φ (j + t)

@[simp] lemma translate_apply (t : ZMod N) (Φ : ZMod N → E) (j : ZMod N) :
    translate (N := N) (E := E) t Φ j = Φ (j + t) := rfl

variable [NeZero N]
variable [AddCommGroup E] [Module ℂ E]

/--
**Translation diagonalization:**

For the canonical discrete Fourier transform `𝓕` on `ZMod N`,
translating by `t` multiplies the Fourier transform by `stdAddChar (t*k)`.

This is the finite-cycle analogue of the usual "shift in time = phase in frequency" law.
-/
theorem dft_translate (Φ : ZMod N → E) (t k : ZMod N) :
    𝓕 (translate (N := N) (E := E) t Φ) k = stdAddChar (t * k) • 𝓕 Φ k := by
  -- Expand the DFT and the translation.
  simp [translate, ZMod.dft_apply]
  -- Change variables `j ↦ j + t`.
  have hchange :
      (∑ j : ZMod N, stdAddChar (-(j * k)) • Φ (j + t)) =
        ∑ i : ZMod N, stdAddChar (-((i - t) * k)) • Φ i := by
    refine Fintype.sum_equiv (Equiv.addRight t) _ _ ?_
    intro j
    simp
  -- Rewrite using the change of variables, then factor out the character multiplier.
  rw [hchange]
  -- Rewrite the `Fintype.sum` on the RHS as `Finset.univ.sum` so we can use `Finset.smul_sum`.
  change
      (Finset.univ.sum fun i : ZMod N => stdAddChar (-((i - t) * k)) • Φ i) =
        stdAddChar (t * k) •
          (Finset.univ.sum fun j : ZMod N => stdAddChar (-(j * k)) • Φ j)
  -- Push the global scalar inside the sum.
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  -- Reduce to a scalar identity in the additive character.
  -- `-((i - t) * k) = t*k - i*k = t*k + (-(i*k))`, so the character splits multiplicatively.
  have hscalar :
      stdAddChar (-((i - t) * k)) =
        stdAddChar (t * k) * stdAddChar (-(i * k)) := by
    -- Rewrite the argument as a sum `t*k + (-(i*k))`, then split using `map_add_eq_mul`.
    have harg : -((i - t) * k) = t * k + -(i * k) := by
      calc
        -((i - t) * k) = -((i * k) - (t * k)) := by
          simp [sub_mul]
        _ = (t * k) - (i * k) := by
          simp [neg_sub]
        _ = t * k + -(i * k) := by
          simp [sub_eq_add_neg]
    -- Now split the additive character on the sum.
    calc
      stdAddChar (-((i - t) * k)) = stdAddChar (t * k + -(i * k)) := by
        simp [harg]
      _ = stdAddChar (t * k) * stdAddChar (-(i * k)) := by
        simp [map_add_eq_mul]
  -- Use `smul_smul` to combine the two scalars on the RHS.
  -- (Multiplication in `ℂ` is commutative, so the order is irrelevant.)
  simp [hscalar, smul_smul]

end FourierZMod
