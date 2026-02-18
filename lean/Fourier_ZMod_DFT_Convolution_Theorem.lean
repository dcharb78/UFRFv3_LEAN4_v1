import Mathlib.Analysis.Fourier.ZMod

/-!
# Discrete Fourier on `ZMod N`: convolution diagonalizes to pointwise multiplication

Mathlib provides the canonical discrete Fourier transform `ZMod.dft` (notation `𝓕` in scope `ZMod`)
on the finite cycle `ZMod N`.

This file proves the classic finite-group fact:

* circular convolution on `ZMod N` becomes pointwise multiplication after applying `𝓕`.

This is the precise algebraic mechanism behind "Fourier works on cyclic/time-series data":
translation symmetry forces the character basis, and convolution operators become diagonal in that basis.
-/

open scoped BigOperators
open scoped ZMod

namespace FourierZMod

open ZMod AddChar

variable {N : ℕ} [NeZero N]

/-- Circular convolution on the finite cycle `ZMod N` (ℂ-valued). -/
noncomputable def conv (f g : ZMod N → ℂ) : ZMod N → ℂ :=
  fun j => ∑ i : ZMod N, f i * g (j - i)

@[simp] lemma conv_apply (f g : ZMod N → ℂ) (j : ZMod N) :
    conv (N := N) f g j = ∑ i : ZMod N, f i * g (j - i) := rfl

/--
**Convolution diagonalization:**

For the canonical DFT `𝓕` on `ZMod N`, we have:

`𝓕 (f ⋆ g) = (𝓕 f) * (𝓕 g)` (pointwise multiplication).
-/
theorem dft_conv (f g : ZMod N → ℂ) (k : ZMod N) :
    𝓕 (conv (N := N) f g) k = (𝓕 f k) * (𝓕 g k) := by
  classical
  -- Expand all DFT applications to explicit finite sums (math-only; no numerics).
  simp [ZMod.dft_apply, conv, smul_eq_mul]
  -- Introduce the canonical additive character evaluated along the frequency `k`.
  let χ : ZMod N → ℂ := fun x => stdAddChar (-(x * k))

  -- Switch to explicit `Finset.univ` sums to use `Finset.mul_sum` / `Finset.sum_mul`.
  change
      (Finset.univ.sum fun x : ZMod N =>
        χ x * (Finset.univ.sum fun i : ZMod N => f i * g (x - i))) =
        (Finset.univ.sum fun x : ZMod N => χ x * f x) *
          (Finset.univ.sum fun x : ZMod N => χ x * g x)

  -- Key inner shift lemma: `x ↦ x - i` becomes multiplication by `χ i`.
  have shift_char (i : ZMod N) :
      (∑ x : ZMod N, χ x * g (x - i)) = χ i * ∑ b : ZMod N, χ b * g b := by
    -- Change variables `x = b + i`, so `x - i = b`.
    have hvar :
        (∑ x : ZMod N, χ x * g (x - i)) = ∑ b : ZMod N, χ (b + i) * g b := by
      refine
        (Fintype.sum_equiv (Equiv.addRight i)
          (fun b : ZMod N => χ (b + i) * g b)
          (fun x : ZMod N => χ x * g (x - i)) ?_).symm
      intro b
      simp
    -- Split the character on `b+i` and factor the `χ i` term out of the sum.
    calc
      (∑ x : ZMod N, χ x * g (x - i)) = ∑ b : ZMod N, χ (b + i) * g b := hvar
      _ = ∑ b : ZMod N, (χ b * χ i) * g b := by
        apply Fintype.sum_congr
        intro b
        -- Prove the scalar character split first, then multiply by `g b`.
        have hχ : χ (b + i) = χ b * χ i := by
          -- `χ (b+i) = stdAddChar (-( (b+i) * k))`
          --         = stdAddChar (-(b*k) + -(i*k))`
          --         = χ b * χ i`.
          -- (Depending on simp normal forms, this may appear as either `(b+i)*k` or `k*(i+b)`.)
          simp [χ, mul_add, map_add_eq_mul, mul_comm]
        simp [hχ, mul_assoc]
      _ = ∑ b : ZMod N, χ i * (χ b * g b) := by
        apply Fintype.sum_congr
        intro b
        simp [mul_comm, mul_left_comm]
      _ = χ i * ∑ b : ZMod N, χ b * g b := by
        -- Factor the constant scalar out of the finite sum.
        simpa using
          (Finset.mul_sum (s := Finset.univ) (f := fun b : ZMod N => χ b * g b) (a := χ i)).symm

  -- Now expand the LHS into a double sum, swap the order, apply `shift_char`, and factor.
  -- LHS as a double sum:
  -- `χ x * ∑ i ... = ∑ i, χ x * ...`, then swap the order of summation.
  have hdist :
      (Finset.univ.sum fun x : ZMod N =>
          χ x * (Finset.univ.sum fun i : ZMod N => f i * g (x - i))) =
        Finset.univ.sum (fun x : ZMod N =>
          Finset.univ.sum (fun i : ZMod N => χ x * (f i * g (x - i)))) := by
    apply Finset.sum_congr rfl
    intro x hx
    simpa using
      (Finset.mul_sum (s := Finset.univ) (f := fun i : ZMod N => f i * g (x - i)) (a := χ x))

  have hswap :
      (Finset.univ.sum fun x : ZMod N =>
          Finset.univ.sum fun i : ZMod N => χ x * (f i * g (x - i))) =
        (Finset.univ.sum fun i : ZMod N =>
          Finset.univ.sum fun x : ZMod N => χ x * (f i * g (x - i))) := by
    -- Use the binder-sum commutation lemma, and `simpa` since `∑` is definitional to `univ.sum`.
    simpa using
      (Finset.sum_comm :
        (∑ x : ZMod N, ∑ i : ZMod N, χ x * (f i * g (x - i))) =
          ∑ i : ZMod N, ∑ x : ZMod N, χ x * (f i * g (x - i)))

  -- For a fixed `i`, evaluate the inner sum in terms of `shift_char`.
  have inner_eval (i : ZMod N) :
      (∑ x : ZMod N, χ x * (f i * g (x - i))) =
        (χ i * f i) * (∑ b : ZMod N, χ b * g b) := by
    -- Rewrite the integrand so `f i` factors out.
    have hrewrite :
        (∑ x : ZMod N, χ x * (f i * g (x - i))) =
          ∑ x : ZMod N, f i * (χ x * g (x - i)) := by
      apply Fintype.sum_congr
      intro x
      simp [mul_assoc, mul_comm]
    have hfactor :
        (∑ x : ZMod N, f i * (χ x * g (x - i))) =
          f i * (∑ x : ZMod N, χ x * g (x - i)) := by
      change (Finset.univ.sum (fun x : ZMod N => f i * (χ x * g (x - i)))) =
        f i * (Finset.univ.sum (fun x : ZMod N => χ x * g (x - i)))
      simpa using
        (Finset.mul_sum (s := Finset.univ) (f := fun x : ZMod N => χ x * g (x - i)) (a := f i)).symm
    -- Apply the shift lemma and reassociate/commute scalars.
    calc
      (∑ x : ZMod N, χ x * (f i * g (x - i))) =
          ∑ x : ZMod N, f i * (χ x * g (x - i)) := hrewrite
      _ = f i * (∑ x : ZMod N, χ x * g (x - i)) := hfactor
      _ = f i * (χ i * (∑ b : ZMod N, χ b * g b)) := by
        -- rewrite the inner sum using `shift_char`
        simpa [mul_assoc] using congrArg (fun t => f i * t) (shift_char i)
      _ = (χ i * f i) * (∑ b : ZMod N, χ b * g b) := by
        simp [mul_assoc, mul_comm]

  -- Put it all together.
  calc
    (Finset.univ.sum fun x : ZMod N =>
          χ x * (Finset.univ.sum fun i : ZMod N => f i * g (x - i)))
        = Finset.univ.sum (fun i : ZMod N => (χ i * f i) * (∑ b : ZMod N, χ b * g b)) := by
          rw [hdist, hswap]
          -- Apply `inner_eval` to the inner sum.
          apply Finset.sum_congr rfl
          intro i hi
          simpa using inner_eval i
    _ = (Finset.univ.sum fun x : ZMod N => χ x * f x) * (Finset.univ.sum fun x : ZMod N => χ x * g x) := by
          -- Factor the common right scalar out of the sum.
          have hfactorRight :
              (Finset.univ.sum fun i : ZMod N => (χ i * f i) * (∑ b : ZMod N, χ b * g b)) =
                (Finset.univ.sum fun i : ZMod N => χ i * f i) * (∑ b : ZMod N, χ b * g b) := by
            -- `sum_mul` factors the right scalar out.
            simpa using
              (Finset.sum_mul (s := Finset.univ) (f := fun i : ZMod N => χ i * f i)
                (a := (∑ b : ZMod N, χ b * g b))).symm
          -- Rewrite `∑ b` to `univ.sum`.
          simp [hfactorRight]

end FourierZMod
