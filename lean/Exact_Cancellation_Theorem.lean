import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Exact Cancellation (Even/Odd Decomposition)

This file formalizes a small but important structural identity behind the repo's
`Tₙ` coefficient patterns.

Define the power series

`g(X) := (exp(X) - 1) / X`,

not by division (which is not available in the power series ring), but by the
*characterizing equation*:

`g * X = exp - 1`.

Then the following classical identity implies an exact parity decomposition:

`(exp X - 1)/X = exp(X/2) * (2*sinh(X/2)/X)`,

and `2*sinh(X/2)/X` is an **even** power series (only even powers of `X`).

We encode the same statement as:

`g(X) * exp(-X/2)` is an **even** power series, i.e. invariant under `X ↦ -X`.

This is a precise "exact cancellation at every term" anchor: after stripping the
linear `exp(X/2)` factor, the remaining series has no odd-degree coefficients.

We work over `ℚ` to match the repo's exact coefficient computations.
-/

namespace ExactCancellation

open PowerSeries

abbrev Q := ℚ

/-- The power series with coefficients `1/(n+1)!`, i.e. the unique series `g`
such that `g*X = exp - 1`. -/
def g : Q⟦X⟧ := PowerSeries.mk (fun n => (1 : Q) / ((n + 1).factorial))

/-- `exp(X)` as a power series over `ℚ`. -/
def E : Q⟦X⟧ := PowerSeries.exp Q

/-- `exp(X/2)` as a power series (noncomputable because `rescale` is noncomputable). -/
noncomputable def Ehalf : Q⟦X⟧ := PowerSeries.rescale (1 / 2 : Q) E

/-- `exp(-X/2)` as a power series, defined as `f(-X)` applied to `exp(X/2)`. -/
noncomputable def EnegHalf : Q⟦X⟧ := PowerSeries.evalNegHom (A := Q) Ehalf

/-- Characterization of `g` as `(exp - 1)/X` (in the sense `g * X = exp - 1`). -/
theorem g_mul_X : g * X = E - 1 := by
  ext n
  cases n with
  | zero =>
      simp [g, E]
  | succ n =>
      simp [g, E, PowerSeries.coeff_succ_mul_X]

/-- Rewrite `exp(-X/2)` as a single `rescale` of `exp(X)`. -/
theorem EnegHalf_eq_rescale : EnegHalf = PowerSeries.rescale (-2⁻¹ : Q) E := by
  -- `evalNegHom = rescale (-1)` and
  -- `rescale (-1) (rescale (1/2) E) = rescale ((1/2)*(-1)) E`.
  simp [EnegHalf, Ehalf, PowerSeries.evalNegHom, PowerSeries.rescale_rescale]

/-- Main algebraic identity: `(g * exp(-X/2)) * X = exp(X/2) - exp(-X/2)`. -/
theorem g_mul_EnegHalf_mul_X : (g * EnegHalf) * X = Ehalf - EnegHalf := by
  calc
    (g * EnegHalf) * X = (g * X) * EnegHalf := by
      simp [mul_assoc, mul_comm]
    _ = (E - 1) * EnegHalf := by
      simp [g_mul_X]
    _ = E * EnegHalf - EnegHalf := by
      simp [sub_mul]
    _ = Ehalf - EnegHalf := by
      -- show `E * EnegHalf = Ehalf`
      have hab : (1 : Q) + (-2⁻¹ : Q) = (2⁻¹ : Q) := by
        norm_num
      have hE : E * EnegHalf = Ehalf := by
        have hneg : EnegHalf = PowerSeries.rescale (-2⁻¹ : Q) E := EnegHalf_eq_rescale
        simpa [E, Ehalf, hneg, hab, PowerSeries.rescale_one] using
          (PowerSeries.exp_mul_exp_eq_exp_add (A := Q) (a := (1 : Q)) (b := (-2⁻¹ : Q)))
      simp [hE]

-- Helper: `evalNegHom` swaps `Ehalf` and `EnegHalf`.
theorem evalNeg_Ehalf : PowerSeries.evalNegHom (A := Q) Ehalf = EnegHalf := by
  simp [EnegHalf]

theorem evalNeg_EnegHalf : PowerSeries.evalNegHom (A := Q) EnegHalf = Ehalf := by
  -- Apply `evalNegHom` twice: `rescale (-1)` composed with itself is `rescale 1`.
  simp [EnegHalf, Ehalf, PowerSeries.evalNegHom, PowerSeries.rescale_rescale]

/--
`g(X) * exp(-X/2)` is an **even** power series: it is invariant under `X ↦ -X`.

Equivalently, after factoring out the "linear bias" `exp(X/2)` from `(exp X - 1)/X`,
the remaining factor has only even-degree terms.
-/
theorem g_mul_expNegHalf_is_even :
    PowerSeries.evalNegHom (A := Q) (g * EnegHalf) = g * EnegHalf := by
  have h : (g * EnegHalf) * X = Ehalf - EnegHalf := g_mul_EnegHalf_mul_X
  -- Apply `evalNegHom` to `h`.
  have hneg :
      PowerSeries.evalNegHom (A := Q) ((g * EnegHalf) * X) =
        PowerSeries.evalNegHom (A := Q) (Ehalf - EnegHalf) := by
    simp [h]
  -- Expand both sides.
  have hx : PowerSeries.evalNegHom (A := Q) X = (-X : Q⟦X⟧) := by
    simp [PowerSeries.evalNegHom_X]
  -- LHS becomes `evalNegHom(g*EnegHalf) * (-X)`.
  -- RHS becomes `EnegHalf - Ehalf`.
  have h1 : (PowerSeries.evalNegHom (A := Q) (g * EnegHalf)) * (-X) = EnegHalf - Ehalf := by
    simpa [map_mul, map_sub, hx, evalNeg_Ehalf, evalNeg_EnegHalf] using hneg
  -- Rewrite `EnegHalf - Ehalf` using `h`.
  have h2 : (PowerSeries.evalNegHom (A := Q) (g * EnegHalf)) * (-X) = -((g * EnegHalf) * X) := by
    -- `EnegHalf - Ehalf = -(Ehalf - EnegHalf)` and `Ehalf - EnegHalf = (g*EnegHalf)*X`.
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, h] using h1
  -- Now turn `a * (-X) = -(b*X)` into `a*X = b*X`.
  have h3 : (PowerSeries.evalNegHom (A := Q) (g * EnegHalf)) * X = (g * EnegHalf) * X := by
    -- `a * (-X) = -(a*X)`; cancel negation.
    have : -(PowerSeries.evalNegHom (A := Q) (g * EnegHalf) * X) = -((g * EnegHalf) * X) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using h2
    exact neg_injective this
  -- Cancel the trailing `*X` (multiplication by `X` is injective in `A⟦X⟧`).
  exact PowerSeries.mul_X_cancel h3

end ExactCancellation
