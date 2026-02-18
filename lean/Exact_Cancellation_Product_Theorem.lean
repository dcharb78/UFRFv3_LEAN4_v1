import Exact_Cancellation_Theorem

/-!
# Exact Cancellation (All Generators)

`lean/Exact_Cancellation_Theorem.lean` proves a one-factor parity anchor:

`g(X) * exp(-X/2)` is an even power series, where `g(X) = (exp X - 1)/X`.

This file upgrades that to *any generator list* `gens : List Nat` by rescaling and multiplying:

Let

`A_gens(X) := ∏_{d ∈ gens} g(dX) = ∏ rescale (d : ℚ) g`.

Then:

`A_gens(X) * exp(-(σ₁(gens)/2) X)` is even,

where `σ₁(gens)` is the (Nat) sum of the generator list, cast into `ℚ`.

This is the precise “perfect cancellation across all scales” statement: after removing the
linear bias `exp((σ₁/2)X)`, all odd-degree coefficients vanish simultaneously.

No placeholders.
-/

namespace ExactCancellationProduct

open PowerSeries
open ExactCancellation

abbrev Q := ExactCancellation.Q

-- ------------------------------------------------------------
-- Helpers
-- ------------------------------------------------------------

/-- If `f(-X)=f(X)`, then also `(f(aX))(-X) = f(aX)` (rescaling preserves evenness). -/
theorem even_rescale (f : Q⟦X⟧) (a : Q)
    (h : PowerSeries.evalNegHom (A := Q) f = f) :
    PowerSeries.evalNegHom (A := Q) (PowerSeries.rescale a f) = PowerSeries.rescale a f := by
  -- `evalNegHom = rescale (-1)` and `rescale (-1) (rescale a f) = rescale (-a) f`.
  -- But since `rescale (-1) f = f`, rescaling by `a` gives `rescale (-a) f = rescale a f`.
  calc
    PowerSeries.evalNegHom (A := Q) (PowerSeries.rescale a f)
        = PowerSeries.rescale (-1 : Q) (PowerSeries.rescale a f) := by
            rfl
    _ = PowerSeries.rescale (a * (-1 : Q)) f := by
          simp [PowerSeries.rescale_rescale]
    _ = PowerSeries.rescale (-a) f := by
          simp
    _ = PowerSeries.rescale a (PowerSeries.rescale (-1 : Q) f) := by
          -- `rescale a (rescale (-1) f) = rescale (-a) f`
          simpa using (PowerSeries.rescale_rescale (f := f) (a := (-1 : Q)) (b := a)).symm
    _ = PowerSeries.rescale a (PowerSeries.evalNegHom (A := Q) f) := by
          rfl
    _ = PowerSeries.rescale a f := by
          simp [h]

-- ------------------------------------------------------------
-- Definitions
-- ------------------------------------------------------------

noncomputable def gScaled (d : Nat) : Q⟦X⟧ :=
  PowerSeries.rescale (d : Q) ExactCancellation.g

noncomputable def expNegHalfScaled (d : Nat) : Q⟦X⟧ :=
  PowerSeries.rescale (-(d : Q) / 2) ExactCancellation.E

noncomputable def A (gens : List Nat) : Q⟦X⟧ :=
  (gens.map gScaled).prod

noncomputable def bias (gens : List Nat) : Q⟦X⟧ :=
  PowerSeries.rescale (-((gens.sum : Nat) : Q) / 2) ExactCancellation.E

noncomputable def factor (d : Nat) : Q⟦X⟧ :=
  PowerSeries.rescale (d : Q) (ExactCancellation.g * ExactCancellation.EnegHalf)

noncomputable def P (gens : List Nat) : Q⟦X⟧ :=
  (gens.map factor).prod

-- ------------------------------------------------------------
-- Factor algebra
-- ------------------------------------------------------------

theorem factor_is_even (d : Nat) :
    PowerSeries.evalNegHom (A := Q) (factor d) = factor d := by
  -- `factor d` is a rescale of the already-even base factor.
  simpa [factor] using
    (even_rescale (f := (ExactCancellation.g * ExactCancellation.EnegHalf)) (a := (d : Q))
      (h := ExactCancellation.g_mul_expNegHalf_is_even))

theorem factor_eq_gScaled_mul_expNegHalfScaled (d : Nat) :
    factor d = gScaled d * expNegHalfScaled d := by
  -- Expand the rescale of a product, and rewrite `EnegHalf` as a rescale of `E`.
  have hneg : ExactCancellation.EnegHalf = PowerSeries.rescale (-2⁻¹ : Q) ExactCancellation.E :=
    ExactCancellation.EnegHalf_eq_rescale
  have hscale : ((-2⁻¹ : Q) * (d : Q)) = (-(d : Q) / 2) := by
    ring
  -- `rescale d (g * EnegHalf) = rescale d g * rescale d EnegHalf = g(dX) * exp(-(d/2)X)`.
  unfold factor gScaled expNegHalfScaled
  calc
    PowerSeries.rescale (d : Q) (ExactCancellation.g * ExactCancellation.EnegHalf)
        = PowerSeries.rescale (d : Q) ExactCancellation.g *
            PowerSeries.rescale (d : Q) ExactCancellation.EnegHalf := by
              exact
                (PowerSeries.rescale (d : Q)).map_mul
                  ExactCancellation.g ExactCancellation.EnegHalf
    _ = PowerSeries.rescale (d : Q) ExactCancellation.g *
          PowerSeries.rescale (-(d : Q) / 2) ExactCancellation.E := by
          -- Collapse the nested rescale defining `EnegHalf`, and normalize the scalar.
          apply congrArg (fun t => PowerSeries.rescale (d : Q) ExactCancellation.g * t)
          simp [hneg, PowerSeries.rescale_rescale, hscale]

-- ------------------------------------------------------------
-- Product evenness
-- ------------------------------------------------------------

theorem P_is_even (gens : List Nat) :
    PowerSeries.evalNegHom (A := Q) (P gens) = P gens := by
  induction gens with
  | nil =>
      simp [P]
  | cons d ds ih =>
      have ih' : PowerSeries.evalNegHom (A := Q) ((ds.map factor).prod) = (ds.map factor).prod := by
        simpa [P] using ih
      -- `evalNegHom` is a ring hom, so it preserves multiplication.
      simp [P, factor_is_even, ih', map_mul]

-- ------------------------------------------------------------
-- Exponential product collapses to the summed exponent
-- ------------------------------------------------------------

/--
Bias recursion:

`bias (d :: gens) = exp(-(d/2)X) * bias(gens)`.

This is the exact algebraic step behind the “position-counted (index) tick” view: local
exponential phases multiply, and the exponent sums.
-/
theorem expNegHalfScaled_mul_bias_eq_bias_cons (d : Nat) (gens : List Nat) :
    expNegHalfScaled d * bias gens = bias (d :: gens) := by
  unfold expNegHalfScaled bias
  -- Normalize the `Nat` sum on the RHS and rewrite `E` as `exp Q`.
  simp [List.sum_cons, ExactCancellation.E]
  have h :=
    (PowerSeries.exp_mul_exp_eq_exp_add (A := Q)
      (a := (-((d : Q)) / 2)) (b := (-(List.map Nat.cast gens).sum / 2)))
  have hscale :
      (-((d : Q)) / 2 + -(List.map Nat.cast gens).sum / 2) =
        (-(List.map Nat.cast gens).sum + -((d : Q))) / 2 := by
          ring_nf
  simpa [hscale] using h

theorem prod_expNegHalfScaled_eq_bias (gens : List Nat) :
    (gens.map expNegHalfScaled).prod = bias gens := by
  induction gens with
  | nil =>
      -- `bias [] = exp(0*X) = 1`.
      simp [bias, ExactCancellation.E]
  | cons d ds ih =>
      -- Use `e^{aX} * e^{bX} = e^{(a+b)X}`.
      have hmul : expNegHalfScaled d * bias ds = bias (d :: ds) :=
        expNegHalfScaled_mul_bias_eq_bias_cons (d := d) (gens := ds)
      -- Finish by rewriting the list product.
      simp [List.map_cons, List.prod_cons, ih, hmul]

-- ------------------------------------------------------------
-- Final packaged statement
-- ------------------------------------------------------------

/--
Decomposition lemma:

`P(gens)` is the product of the already-even factors `factor d = g(dX) * exp(-(d/2)X)`.

This product can be regrouped as:

`P(gens) = A(gens) * bias(gens)`,

where `A(gens)` is the product of all `g(dX)` terms and `bias(gens)` is the single
summed exponential `exp(-(σ₁(gens)/2) X)`.
-/
theorem P_eq_A_mul_bias (gens : List Nat) :
    P gens = A gens * bias gens := by
  induction gens with
  | nil =>
      simp [P, A, bias, ExactCancellation.E]
  | cons d ds ih =>
      have hfac : factor d = gScaled d * expNegHalfScaled d :=
        factor_eq_gScaled_mul_expNegHalfScaled (d := d)
      have hbias : expNegHalfScaled d * bias ds = bias (d :: ds) :=
        expNegHalfScaled_mul_bias_eq_bias_cons (d := d) (gens := ds)
      have ih' : (ds.map factor).prod = A ds * bias ds := by
        simpa [P] using ih
      -- Expand `P`/`A` at the head and regroup using commutativity.
      calc
        P (d :: ds) = factor d * (ds.map factor).prod := by
          simp [P]
        _ = factor d * (A ds * bias ds) := by
          simp [ih']
        _ = (gScaled d * expNegHalfScaled d) * (A ds * bias ds) := by
          simp [hfac, mul_assoc]
        _ = (gScaled d * A ds) * (expNegHalfScaled d * bias ds) := by
          ac_rfl
        _ = (gScaled d * A ds) * bias (d :: ds) := by
          simp [hbias]
        _ = A (d :: ds) * bias (d :: ds) := by
          simp [A, mul_assoc]

/--
Main theorem:

`A(gens) * bias(gens)` is even, i.e. invariant under `X ↦ -X`.
-/
theorem A_mul_bias_is_even (gens : List Nat) :
    PowerSeries.evalNegHom (A := Q) (A gens * bias gens) = A gens * bias gens := by
  -- `P(gens)` is even by construction, and `P(gens) = A(gens) * bias(gens)`.
  have hP : PowerSeries.evalNegHom (A := Q) (P gens) = P gens := P_is_even gens
  have hdecomp : P gens = A gens * bias gens := P_eq_A_mul_bias (gens := gens)
  calc
    PowerSeries.evalNegHom (A := Q) (A gens * bias gens)
        = PowerSeries.evalNegHom (A := Q) (P gens) := by
            simp [hdecomp]
    _ = P gens := hP
    _ = A gens * bias gens := hdecomp

end ExactCancellationProduct
