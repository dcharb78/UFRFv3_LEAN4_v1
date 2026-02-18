/-
# Truncated Generating-Function Engine (Degree ≤ N)

This module generalizes the coefficient-multiplication engine from
`Tn_Recurrence_Universality_Theorem.lean` (which is specialized to degree ≤ 4)
to an arbitrary truncation degree `N`.

Core invariants proved (no placeholders):
- **Concurrency / order invariance**: list permutations do not change coefficients.
- **Concurrency composition law**: multiset addition corresponds to coefficient multiplication.
- **Scale invariance**: scaling all generators by `k` scales degree-`n` coefficients by `k^n`.

Engineering note:
We represent truncated coefficient data as a function `Fin (N+1) → ℚ`.
Multiplication is defined by multiplying the corresponding polynomials and then
reading off coefficients up to degree `N`.
-/

import Mathlib

namespace TnTruncated

noncomputable section

open scoped BigOperators

open Polynomial
open Finset (antidiagonal mem_antidiagonal)

-- ============================================================
-- Truncated coefficient container and polynomial bridge
-- ============================================================

/-- Truncated coefficient data: coefficients `0..N` of a series. -/
def Coeffs (N : Nat) : Type := Fin (N + 1) → ℚ

/-- The multiplicative identity coefficients: `1 + 0·t + ... + 0·t^N`. -/
def coeffsOne (N : Nat) : Coeffs N :=
  fun i => if (i : Nat) = 0 then 1 else 0

/-- Convert coefficient data to a polynomial with the same coefficients in degrees `0..N`. -/
def toPoly (N : Nat) (c : Coeffs N) : Polynomial ℚ :=
  ∑ i : Fin (N + 1), Polynomial.monomial i.1 (c i)

/-- Read polynomial coefficients in degrees `0..N` as `Coeff` data. -/
def ofPoly (N : Nat) (p : Polynomial ℚ) : Coeffs N :=
  fun i => p.coeff i.1

/-- Truncate a polynomial to degrees `0..N` by dropping all higher coefficients. -/
def truncPoly (N : Nat) (p : Polynomial ℚ) : Polynomial ℚ :=
  toPoly N (ofPoly N p)

theorem ofPoly_toPoly (N : Nat) (c : Coeffs N) : ofPoly N (toPoly N c) = c := by
  funext i
  -- Expand coefficient; only the `i` term survives.
  simp [ofPoly, toPoly, Polynomial.coeff_monomial]
  -- Rewrite `↑x = ↑i` to `x = i` using `Fin.ext`.
  have hrewrite :
      (fun x : Fin (N + 1) => if (x : Nat) = (i : Nat) then c x else 0)
        = (fun x : Fin (N + 1) => if x = i then c x else 0) := by
    funext x
    by_cases hx : x = i
    · subst hx
      simp
    · have hx' : (x : Nat) ≠ (i : Nat) := by
        intro h
        apply hx
        exact Fin.ext h
      simp [hx, hx']
  rw [hrewrite]
  exact Fintype.sum_ite_eq' (ι := Fin (N + 1)) i c

theorem coeff_toPoly_of_le (N : Nat) (c : Coeffs N) {m : Nat} (hm : m ≤ N) :
    (toPoly N c).coeff m = c ⟨m, Nat.lt_succ_of_le hm⟩ := by
  let i0 : Fin (N + 1) := ⟨m, Nat.lt_succ_of_le hm⟩
  have := congrArg (fun f => f i0) (ofPoly_toPoly N c)
  simpa [ofPoly, i0] using this

theorem coeff_truncPoly (N : Nat) (p : Polynomial ℚ) (m : Nat) :
    (truncPoly N p).coeff m = if m ≤ N then p.coeff m else 0 := by
  by_cases hm : m ≤ N
  · -- `m` is within range, so truncation keeps the coefficient.
    have i0_lt : m < N + 1 := Nat.lt_succ_of_le hm
    let i0 : Fin (N + 1) := ⟨m, i0_lt⟩
    have hi0 : (i0 : Nat) = m := rfl
    -- Evaluate the coefficient using the `ofPoly_toPoly` identity.
    have := congrArg (fun c => c i0) (ofPoly_toPoly N (ofPoly N p))
    -- `ofPoly N (toPoly N (ofPoly N p))` is definitional equal to `ofPoly N (truncPoly N p)`.
    -- After rewriting, this is exactly the desired coefficient equality.
    simpa [truncPoly, ofPoly, hi0, hm, i0] using this
  · -- `m` is above range, so truncation makes the coefficient `0`.
    have hm' : N < m := Nat.lt_of_not_ge hm
    -- In `toPoly`, all monomials have degree ≤ N, so coefficient at `m` vanishes
    -- because for every `x : Fin (N+1)` we have `x.val ≤ N < m`.
    simp [truncPoly, toPoly, ofPoly, Polynomial.coeff_monomial, hm]
    have hzero :
        ∀ x : Fin (N + 1), (if (x : Nat) = m then p.coeff (x : Nat) else 0) = 0 := by
      intro x
      have hxle : (x : Nat) ≤ N := Nat.le_of_lt_succ x.isLt
      have hxlt : (x : Nat) < m := Nat.lt_of_le_of_lt hxle hm'
      have hxne : (x : Nat) ≠ m := ne_of_lt hxlt
      simp [hxne]
    simp [hzero]

theorem coeffsOne_eq_ofPoly_one (N : Nat) : coeffsOne N = ofPoly N (1 : Polynomial ℚ) := by
  funext i
  by_cases hi0 : (i : Nat) = 0 <;> simp [coeffsOne, ofPoly, hi0, Polynomial.coeff_one]

theorem truncPoly_one (N : Nat) : truncPoly N (1 : Polynomial ℚ) = 1 := by
  ext m
  -- Work by coefficients using `coeff_truncPoly`.
  rw [coeff_truncPoly]
  by_cases hm : m ≤ N
  · -- In-range: truncation keeps the coefficient, and both sides agree.
    simp [hm]
  · -- Out-of-range: LHS is `0`; RHS is also `0` since `m ≠ 0`.
    have hm0 : m ≠ 0 := by
      intro hm0
      subst hm0
      exact hm (Nat.zero_le N)
    simp [hm, Polynomial.coeff_one, hm0]

-- ============================================================
-- Truncated multiplication (degree ≤ N)
-- ============================================================

/-- Multiply coefficient data by multiplying their `toPoly` polynomials and re-extracting coefficients ≤ N. -/
def mulCoeffs (N : Nat) (a b : Coeffs N) : Coeffs N :=
  ofPoly N (toPoly N a * toPoly N b)

theorem mulCoeffs_comm (N : Nat) (a b : Coeffs N) :
    mulCoeffs N a b = mulCoeffs N b a := by
  funext i
  simp [mulCoeffs, ofPoly, toPoly, mul_comm]

theorem mulCoeffs_one_left (N : Nat) (a : Coeffs N) :
    mulCoeffs N (coeffsOne N) a = a := by
  have h_toPoly_one : toPoly N (coeffsOne N) = (1 : Polynomial ℚ) := by
    -- `coeffsOne = ofPoly 1`, so `toPoly coeffsOne = truncPoly 1 = 1`.
    have h_one : coeffsOne N = ofPoly N (1 : Polynomial ℚ) := coeffsOne_eq_ofPoly_one N
    calc
      toPoly N (coeffsOne N) = toPoly N (ofPoly N (1 : Polynomial ℚ)) := by
        simp [h_one]
      _ = truncPoly N (1 : Polynomial ℚ) := by
        rfl
      _ = 1 := truncPoly_one N
  funext i
  -- Evaluate `ofPoly_toPoly` at `i` to turn coefficients back into data.
  have hcoeff : (toPoly N a).coeff i.1 = a i := by
    have := congrArg (fun f => f i) (ofPoly_toPoly N a)
    simpa [ofPoly] using this
  simp [mulCoeffs, ofPoly, h_toPoly_one, hcoeff]

theorem mulCoeffs_one_right (N : Nat) (a : Coeffs N) :
    mulCoeffs N a (coeffsOne N) = a := by
  -- Use commutativity + left-identity.
  simpa [mulCoeffs_comm] using (mulCoeffs_one_left N a)

theorem coeff_truncPoly_mul_left (N : Nat) (p q : Polynomial ℚ) (m : Nat) (hm : m ≤ N) :
    ((truncPoly N p) * q).coeff m = (p * q).coeff m := by
  -- Expand both sides using the antidiagonal formula.
  simp [Polynomial.coeff_mul]
  refine Finset.sum_congr rfl ?_
  intro x hx
  have hxsum : x.1 + x.2 = m := (mem_antidiagonal.mp hx)
  have hxle : x.1 ≤ m := by
    have : x.1 ≤ x.1 + x.2 := Nat.le_add_right _ _
    simpa [hxsum] using this
  have hxleN : x.1 ≤ N := Nat.le_trans hxle hm
  simp [coeff_truncPoly, hxleN]

theorem ofPoly_mul_left_trunc (N : Nat) (p q : Polynomial ℚ) :
    ofPoly N ((truncPoly N p) * q) = ofPoly N (p * q) := by
  funext i
  have hm : i.1 ≤ N := Nat.le_of_lt_succ i.isLt
  simpa [ofPoly] using (coeff_truncPoly_mul_left N p q i.1 hm)

theorem ofPoly_mul_right_trunc (N : Nat) (p q : Polynomial ℚ) :
    ofPoly N (p * (truncPoly N q)) = ofPoly N (p * q) := by
  -- Commute and reuse the left-trunc lemma.
  funext i
  have hm : i.1 ≤ N := Nat.le_of_lt_succ i.isLt
  -- Use coefficient-level proof to avoid rewriting the whole `ofPoly`.
  have := coeff_truncPoly_mul_left N q p i.1 hm
  -- `((truncPoly q) * p).coeff m = (q * p).coeff m`; commute to match the goal.
  simpa [ofPoly, mul_comm, mul_left_comm, mul_assoc] using this

theorem mulCoeffs_assoc (N : Nat) (a b c : Coeffs N) :
    mulCoeffs N (mulCoeffs N a b) c = mulCoeffs N a (mulCoeffs N b c) := by
  funext i
  -- Reduce to associativity of polynomial multiplication, using the truncation lemmas to
  -- justify that intermediate truncations do not affect degrees `≤ N`.
  -- Left side: coefficients of `(trunc (a*b)) * c`.
  have hL :
      (mulCoeffs N (mulCoeffs N a b) c) i =
        (ofPoly N ((truncPoly N (toPoly N a * toPoly N b)) * (toPoly N c))) i := by
    simp [mulCoeffs, truncPoly]
  -- Right side: coefficients of `a * (trunc (b*c))`.
  have hR :
      (mulCoeffs N a (mulCoeffs N b c)) i =
        (ofPoly N ((toPoly N a) * (truncPoly N (toPoly N b * toPoly N c)))) i := by
    simp [mulCoeffs, truncPoly]
  -- Apply coefficient-preservation for truncation and then polynomial associativity.
  -- (All equalities are at degrees `≤ N` because `i : Fin (N+1)`.)
  have hL' :
      (ofPoly N ((truncPoly N (toPoly N a * toPoly N b)) * (toPoly N c))) i =
        (ofPoly N ((toPoly N a * toPoly N b) * (toPoly N c))) i := by
    simpa using congrArg (fun f => f i) (ofPoly_mul_left_trunc N (toPoly N a * toPoly N b) (toPoly N c))
  have hR' :
      (ofPoly N ((toPoly N a) * (truncPoly N (toPoly N b * toPoly N c)))) i =
        (ofPoly N ((toPoly N a) * (toPoly N b * toPoly N c))) i := by
    simpa using congrArg (fun f => f i) (ofPoly_mul_right_trunc N (toPoly N a) (toPoly N b * toPoly N c))
  -- Put it all together.
  calc
    (mulCoeffs N (mulCoeffs N a b) c) i
        = (ofPoly N ((truncPoly N (toPoly N a * toPoly N b)) * (toPoly N c))) i := by
            simp [hL]
    _ = (ofPoly N (((toPoly N a * toPoly N b)) * (toPoly N c))) i := hL'
    _ = (ofPoly N ((toPoly N a) * (toPoly N b * toPoly N c))) i := by
            simp [mul_assoc]
    _ = (ofPoly N ((toPoly N a) * (truncPoly N (toPoly N b * toPoly N c)))) i := by
            symm
            exact hR'
    _ = (mulCoeffs N a (mulCoeffs N b c)) i := by
            simp [hR]

-- ============================================================
-- Factor coefficients: (exp(d*t)-1)/(d*t) truncated to degree N
-- ============================================================

/-- Factor coefficient at degree `n`: `d^n / (n+1)!` in `ℚ`. -/
def factorCoeff (d : Nat) (n : Nat) : ℚ :=
  (d ^ n : ℚ) / (Nat.factorial (n + 1) : ℚ)

/-- Coefficient data for the single-generator factor truncated to degree `N`. -/
def factorCoeffs (N : Nat) (d : Nat) : Coeffs N :=
  fun i => factorCoeff d i.1

-- ============================================================
-- Building the truncated product for a list of generators
-- ============================================================

/-- Degree ≤ N coefficients for `A(t) = ∏ (exp(d*t)-1)/(d*t)` for a list of generators. -/
def aCoeffs (N : Nat) : List Nat → Coeffs N
  | [] => coeffsOne N
  | d :: ds => mulCoeffs N (aCoeffs N ds) (factorCoeffs N d)

@[simp] theorem aCoeffs_nil (N : Nat) : aCoeffs N [] = coeffsOne N := by rfl

@[simp] theorem aCoeffs_cons (N : Nat) (d : Nat) (ds : List Nat) :
    aCoeffs N (d :: ds) = mulCoeffs N (aCoeffs N ds) (factorCoeffs N d) := by
  rfl

theorem aCoeffs_append (N : Nat) (xs ys : List Nat) :
    aCoeffs N (xs ++ ys) = mulCoeffs N (aCoeffs N xs) (aCoeffs N ys) := by
  induction xs with
  | nil =>
      simp [mulCoeffs_one_left]
  | cons d ds ih =>
      simp [aCoeffs, ih]
      calc
        mulCoeffs N (mulCoeffs N (aCoeffs N ds) (aCoeffs N ys)) (factorCoeffs N d) =
            mulCoeffs N (aCoeffs N ds) (mulCoeffs N (aCoeffs N ys) (factorCoeffs N d)) := by
              simpa using mulCoeffs_assoc N (aCoeffs N ds) (aCoeffs N ys) (factorCoeffs N d)
        _ = mulCoeffs N (aCoeffs N ds) (mulCoeffs N (factorCoeffs N d) (aCoeffs N ys)) := by
              simp [mulCoeffs_comm]
        _ = mulCoeffs N (mulCoeffs N (aCoeffs N ds) (factorCoeffs N d)) (aCoeffs N ys) := by
              simpa using (mulCoeffs_assoc N (aCoeffs N ds) (factorCoeffs N d) (aCoeffs N ys)).symm

theorem aCoeffs_swap (N : Nat) (a b : Nat) (zs : List Nat) :
    aCoeffs N (a :: b :: zs) = aCoeffs N (b :: a :: zs) := by
  -- Reduce to commutativity/associativity of `mulCoeffs`.
  simp [aCoeffs]
  calc
    mulCoeffs N (mulCoeffs N (aCoeffs N zs) (factorCoeffs N b)) (factorCoeffs N a) =
        mulCoeffs N (aCoeffs N zs) (mulCoeffs N (factorCoeffs N b) (factorCoeffs N a)) := by
          simpa using mulCoeffs_assoc N (aCoeffs N zs) (factorCoeffs N b) (factorCoeffs N a)
    _ = mulCoeffs N (aCoeffs N zs) (mulCoeffs N (factorCoeffs N a) (factorCoeffs N b)) := by
          simp [mulCoeffs_comm]
    _ = mulCoeffs N (mulCoeffs N (aCoeffs N zs) (factorCoeffs N a)) (factorCoeffs N b) := by
          simpa using (mulCoeffs_assoc N (aCoeffs N zs) (factorCoeffs N a) (factorCoeffs N b)).symm

theorem aCoeffs_perm (N : Nat) {xs ys : List Nat} (h : List.Perm xs ys) :
    aCoeffs N xs = aCoeffs N ys := by
  induction h with
  | nil => rfl
  | cons a h ih =>
      simp [aCoeffs, ih]
  | swap a b zs =>
      simpa using (aCoeffs_swap N a b zs).symm
  | trans h₁ h₂ ih₁ ih₂ =>
      exact Eq.trans ih₁ ih₂

-- ============================================================
-- Order-free (concurrent) formulation: multisets
-- ============================================================

/-- Lift `aCoeffs` from lists to multisets of generators (order invariance). -/
def aCoeffsMS (N : Nat) : Multiset Nat → Coeffs N :=
  Quot.lift (aCoeffs N) (by
    intro xs ys h
    exact aCoeffs_perm N h
  )

@[simp] theorem aCoeffsMS_coe (N : Nat) (xs : List Nat) :
    aCoeffsMS N (xs : Multiset Nat) = aCoeffs N xs := rfl

@[simp] theorem aCoeffsMS_zero (N : Nat) : aCoeffsMS N (0 : Multiset Nat) = coeffsOne N := by
  rfl

theorem aCoeffsMS_add (N : Nat) (s t : Multiset Nat) :
    aCoeffsMS N (s + t) = mulCoeffs N (aCoeffsMS N s) (aCoeffsMS N t) := by
  refine Quotient.inductionOn₂ s t (fun xs ys => ?_)
  simp [aCoeffsMS, aCoeffs_append]

-- ============================================================
-- Scale invariance
-- ============================================================

/-- Scale coefficient data by `k^n` in degree `n`. -/
def scaleCoeffs (N : Nat) (k : Nat) (c : Coeffs N) : Coeffs N :=
  fun i => (k : ℚ) ^ i.1 * c i

theorem factorCoeffs_scale (N : Nat) (k d : Nat) :
    factorCoeffs N (k * d) = scaleCoeffs N k (factorCoeffs N d) := by
  funext i
  simp [factorCoeffs, factorCoeff, scaleCoeffs, Nat.cast_mul, mul_pow, mul_div_assoc]

theorem mulCoeffs_scale (N : Nat) (k : Nat) (a b : Coeffs N) :
    mulCoeffs N (scaleCoeffs N k a) (scaleCoeffs N k b) =
      scaleCoeffs N k (mulCoeffs N a b) := by
  funext i
  have hn : i.1 ≤ N := Nat.le_of_lt_succ i.isLt
  -- Unfold, then use the antidiagonal coefficient formula for both products.
  simp [mulCoeffs, ofPoly, scaleCoeffs, Polynomial.coeff_mul]
  -- Rewrite each scaled summand as `(k^n) * (unscaled summand)` and factor out `k^n`.
  have hsummand :
      ∀ x : Nat × Nat,
        x ∈ antidiagonal i.1 →
          (toPoly N (scaleCoeffs N k a)).coeff x.1 * (toPoly N (scaleCoeffs N k b)).coeff x.2 =
            (k : ℚ) ^ i.1 * ((toPoly N a).coeff x.1 * (toPoly N b).coeff x.2) := by
    intro x hx
    have hxsum : x.1 + x.2 = i.1 := mem_antidiagonal.mp hx
    have hxle1 : x.1 ≤ i.1 := by
      have : x.1 ≤ x.1 + x.2 := Nat.le_add_right _ _
      simpa [hxsum] using this
    have hxle2 : x.2 ≤ i.1 := by
      have : x.2 ≤ x.1 + x.2 := Nat.le_add_left _ _
      simpa [hxsum] using this
    have hxleN1 : x.1 ≤ N := Nat.le_trans hxle1 hn
    have hxleN2 : x.2 ≤ N := Nat.le_trans hxle2 hn
    -- Use exact coefficient lookup for degrees ≤ N.
    let i1 : Fin (N + 1) := ⟨x.1, Nat.lt_succ_of_le hxleN1⟩
    let i2 : Fin (N + 1) := ⟨x.2, Nat.lt_succ_of_le hxleN2⟩
    have hA_scale : (toPoly N (scaleCoeffs N k a)).coeff x.1 = (k : ℚ) ^ x.1 * a i1 := by
      simpa [scaleCoeffs, i1] using (coeff_toPoly_of_le N (scaleCoeffs N k a) hxleN1)
    have hB_scale : (toPoly N (scaleCoeffs N k b)).coeff x.2 = (k : ℚ) ^ x.2 * b i2 := by
      simpa [scaleCoeffs, i2] using (coeff_toPoly_of_le N (scaleCoeffs N k b) hxleN2)
    have hA : (toPoly N a).coeff x.1 = a i1 := by
      simpa [i1] using (coeff_toPoly_of_le N a hxleN1)
    have hB : (toPoly N b).coeff x.2 = b i2 := by
      simpa [i2] using (coeff_toPoly_of_le N b hxleN2)
    -- Combine scaling factors.
    calc
      (toPoly N (scaleCoeffs N k a)).coeff x.1 * (toPoly N (scaleCoeffs N k b)).coeff x.2
          = ((k : ℚ) ^ x.1 * a i1) * ((k : ℚ) ^ x.2 * b i2) := by
              simp [hA_scale, hB_scale]
      _ = ((k : ℚ) ^ x.1 * (k : ℚ) ^ x.2) * (a i1 * b i2) := by
              ac_rfl
      _ = (k : ℚ) ^ (x.1 + x.2) * (a i1 * b i2) := by
              simp [pow_add]
      _ = (k : ℚ) ^ i.1 * ((toPoly N a).coeff x.1 * (toPoly N b).coeff x.2) := by
              simp [hxsum, hA, hB]
  -- Apply the summand rewrite, then pull out the constant factor.
  have :
      (∑ x ∈ antidiagonal i.1,
          (toPoly N (scaleCoeffs N k a)).coeff x.1 * (toPoly N (scaleCoeffs N k b)).coeff x.2) =
        (k : ℚ) ^ i.1 *
          ∑ x ∈ antidiagonal i.1, (toPoly N a).coeff x.1 * (toPoly N b).coeff x.2 := by
    -- First rewrite the summand.
    have hsum :
        (∑ x ∈ antidiagonal i.1,
            (toPoly N (scaleCoeffs N k a)).coeff x.1 * (toPoly N (scaleCoeffs N k b)).coeff x.2) =
          ∑ x ∈ antidiagonal i.1, (k : ℚ) ^ i.1 * ((toPoly N a).coeff x.1 * (toPoly N b).coeff x.2) := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      exact hsummand x hx
    -- Then factor out `(k^n)` using `Finset.mul_sum`.
    calc
      (∑ x ∈ antidiagonal i.1,
            (toPoly N (scaleCoeffs N k a)).coeff x.1 * (toPoly N (scaleCoeffs N k b)).coeff x.2)
          = ∑ x ∈ antidiagonal i.1, (k : ℚ) ^ i.1 * ((toPoly N a).coeff x.1 * (toPoly N b).coeff x.2) := hsum
      _ = (k : ℚ) ^ i.1 * ∑ x ∈ antidiagonal i.1, (toPoly N a).coeff x.1 * (toPoly N b).coeff x.2 := by
            simpa using
              (Finset.mul_sum (antidiagonal i.1)
                (fun x => (toPoly N a).coeff x.1 * (toPoly N b).coeff x.2) ((k : ℚ) ^ i.1)).symm
  simp [this]

theorem aCoeffs_scale (N : Nat) (k : Nat) (gens : List Nat) :
    aCoeffs N (gens.map (fun d => k * d)) = scaleCoeffs N k (aCoeffs N gens) := by
  induction gens with
  | nil =>
      funext i
      by_cases hi0 : (i : Nat) = 0 <;> simp [aCoeffs, coeffsOne, scaleCoeffs, hi0]
  | cons d ds ih =>
      simp [aCoeffs, ih, factorCoeffs_scale, mulCoeffs_scale]

theorem aCoeffsMS_scale (N : Nat) (k : Nat) (s : Multiset Nat) :
    aCoeffsMS N (s.map (fun d => k * d)) = scaleCoeffs N k (aCoeffsMS N s) := by
  refine Quotient.inductionOn s (fun xs => ?_)
  simp [aCoeffsMS, aCoeffs_scale]

section MonoidPackaging

-- Package the concurrency law as a commutative monoid hom:
-- generator multisets (addition) ↦ truncated coefficient data (multiplication).

local instance (N : Nat) : One (Coeffs N) := ⟨coeffsOne N⟩
local instance (N : Nat) : Mul (Coeffs N) := ⟨mulCoeffs N⟩

local instance (N : Nat) : CommMonoid (Coeffs N) where
  one := coeffsOne N
  mul := mulCoeffs N
  mul_assoc := mulCoeffs_assoc N
  one_mul := mulCoeffs_one_left N
  mul_one := mulCoeffs_one_right N
  mul_comm := mulCoeffs_comm N

/-- `aCoeffsMS` is a commutative-monoid hom from multiset union to coefficient multiplication. -/
def aCoeffsMS_hom (N : Nat) : Multiplicative (Multiset Nat) →* Coeffs N where
  toFun s := aCoeffsMS N s.toAdd
  map_one' := by
    change aCoeffsMS N (0 : Multiset Nat) = coeffsOne N
    exact aCoeffsMS_zero N
  map_mul' := by
    intro s t
    -- `Multiplicative.mul` is multiset addition, and `CommMonoid.mul` is `mulCoeffs`.
    change aCoeffsMS N (s.toAdd + t.toAdd) = mulCoeffs N (aCoeffsMS N s.toAdd) (aCoeffsMS N t.toAdd)
    exact aCoeffsMS_add N s.toAdd t.toAdd

end MonoidPackaging

end
