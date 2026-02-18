/-
# Tₙ Recurrence Universality Theorem (Lean, No Placeholders)

This file validates the low-order `Tₙ` closed forms *from first principles*:

We start with the generating function used throughout the repo:

`A(t) = ∏ (exp(d*t) - 1) / (d*t)`.

As a formal power series, each factor expands as:

`(exp(d*t) - 1)/(d*t) = Σ_{n>=0} d^n * t^n / (n+1)!`.

Multiplying factors and reading coefficients gives:

- `T₁ = σ₁/2`
- `T₂ = (3*σ₁^2 + σ₂)/12`
- `T₃ = σ₁(σ₁^2 + σ₂)/8`
- `T₄ = (15*σ₁^4 + 30*σ₁^2*σ₂ + 5*σ₂^2 - 2*σ₄)/240`

These identities are *universal* (depend only on the generator list through low power sums)
and are proven here by an explicit truncated coefficient recursion (degree ≤ 4).

This file contains no placeholders.
-/

import Mathlib

namespace TnRecurrence

-- ============================================================
-- Power sums σₖ = Σ dᵢᵏ
-- ============================================================

/-- Power sum `σₖ = Σ dᵢᵏ` (recursive form for clean induction). -/
def sigma : List Nat → Nat → Nat
  | [], _ => 0
  | d :: ds, k => d ^ k + sigma ds k

@[simp] theorem sigma_nil (k : Nat) : sigma [] k = 0 := by rfl
@[simp] theorem sigma_cons (d : Nat) (ds : List Nat) (k : Nat) :
    sigma (d :: ds) k = d ^ k + sigma ds k := by rfl

/-- Casted power sum `σₖ` in `ℚ`. -/
def sigmaQ (gens : List Nat) (k : Nat) : ℚ :=
  (sigma gens k : ℚ)

@[simp] theorem sigmaQ_nil (k : Nat) : sigmaQ [] k = 0 := by rfl

@[simp] theorem sigmaQ_cons (d : Nat) (ds : List Nat) (k : Nat) :
    sigmaQ (d :: ds) k = (d ^ k : ℚ) + sigmaQ ds k := by
  -- `sigma` is recursive, but `Nat.cast` does not reduce through `+` by `rfl`.
  simp [sigmaQ, sigma, Nat.cast_add]

-- ============================================================
-- Truncated (degree ≤ 4) coefficient recursion for A(t)
-- ============================================================

/-!
We only need coefficients up to `t^4`.

For a single generator `d`, the factor series is:

`f_d(t) = Σ_{n=0..4} (d^n)/(n+1)! * t^n + O(t^5)`.

We maintain coefficients `(c0,c1,c2,c3,c4)` for the product so far and update via
truncated convolution.
-/

structure Coeffs5 where
  c0 : ℚ
  c1 : ℚ
  c2 : ℚ
  c3 : ℚ
  c4 : ℚ
deriving Repr

@[ext] theorem Coeffs5.ext (a b : Coeffs5)
    (h0 : a.c0 = b.c0)
    (h1 : a.c1 = b.c1)
    (h2 : a.c2 = b.c2)
    (h3 : a.c3 = b.c3)
    (h4 : a.c4 = b.c4) : a = b := by
  cases a
  cases b
  simp_all

def coeffsInit : Coeffs5 :=
  { c0 := 1, c1 := 0, c2 := 0, c3 := 0, c4 := 0 }

def factorC1 (d : Nat) : ℚ := (d : ℚ) / 2
def factorC2 (d : Nat) : ℚ := (d ^ 2 : ℚ) / 6
def factorC3 (d : Nat) : ℚ := (d ^ 3 : ℚ) / 24
def factorC4 (d : Nat) : ℚ := (d ^ 4 : ℚ) / 120

/-- Multiply existing coefficients by the single-generator factor (truncated to degree 4). -/
def mulFactor (d : Nat) (c : Coeffs5) : Coeffs5 :=
  { c0 := c.c0
    c1 := c.c1 + factorC1 d * c.c0
    c2 := c.c2 + factorC1 d * c.c1 + factorC2 d * c.c0
    c3 := c.c3 + factorC1 d * c.c2 + factorC2 d * c.c1 + factorC3 d * c.c0
    c4 :=
      c.c4
        + factorC1 d * c.c3
        + factorC2 d * c.c2
        + factorC3 d * c.c1
        + factorC4 d * c.c0 }

/-- The single-generator factor coefficients (degree ≤ 4). -/
def factorCoeffs (d : Nat) : Coeffs5 :=
  { c0 := 1
    c1 := factorC1 d
    c2 := factorC2 d
    c3 := factorC3 d
    c4 := factorC4 d }

/-- Truncated multiplication (degree ≤ 4) for coefficient tuples. -/
def mulCoeffs (a b : Coeffs5) : Coeffs5 :=
  { c0 := a.c0 * b.c0
    c1 := a.c0 * b.c1 + a.c1 * b.c0
    c2 := a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0
    c3 := a.c0 * b.c3 + a.c1 * b.c2 + a.c2 * b.c1 + a.c3 * b.c0
    c4 := a.c0 * b.c4 + a.c1 * b.c3 + a.c2 * b.c2 + a.c3 * b.c1 + a.c4 * b.c0 }

theorem mulFactor_eq_mulCoeffs (d : Nat) (c : Coeffs5) :
    mulFactor d c = mulCoeffs c (factorCoeffs d) := by
  ext <;> simp [mulFactor, mulCoeffs, factorCoeffs, factorC1, factorC2, factorC3, factorC4] <;> ring

theorem mulCoeffs_assoc (a b c : Coeffs5) :
    mulCoeffs (mulCoeffs a b) c = mulCoeffs a (mulCoeffs b c) := by
  ext <;> simp [mulCoeffs] <;> ring

theorem mulCoeffs_comm (a b : Coeffs5) :
    mulCoeffs a b = mulCoeffs b a := by
  ext <;> simp [mulCoeffs] <;> ring

theorem mulCoeffs_init_left (a : Coeffs5) : mulCoeffs coeffsInit a = a := by
  ext <;> simp [mulCoeffs, coeffsInit]

theorem mulCoeffs_init_right (a : Coeffs5) : mulCoeffs a coeffsInit = a := by
  ext <;> simp [mulCoeffs, coeffsInit]

/-- Degree ≤ 4 coefficients of `A(t)` for a list of generators. -/
def aCoeffs : List Nat → Coeffs5
  | [] => coeffsInit
  | d :: ds => mulFactor d (aCoeffs ds)

@[simp] theorem aCoeffs_nil : aCoeffs [] = coeffsInit := by rfl
@[simp] theorem aCoeffs_cons (d : Nat) (ds : List Nat) :
    aCoeffs (d :: ds) = mulFactor d (aCoeffs ds) := by rfl

theorem aCoeffs_append (xs ys : List Nat) :
    aCoeffs (xs ++ ys) = mulCoeffs (aCoeffs xs) (aCoeffs ys) := by
  induction xs with
  | nil =>
      simp [mulCoeffs_init_left]
  | cons d ds ih =>
      -- Expand one step of the product recursion and rearrange using associativity/commutativity.
      simp [aCoeffs, ih, mulFactor_eq_mulCoeffs]
      calc
        mulCoeffs (mulCoeffs (aCoeffs ds) (aCoeffs ys)) (factorCoeffs d) =
            mulCoeffs (aCoeffs ds) (mulCoeffs (aCoeffs ys) (factorCoeffs d)) := by
              simpa using mulCoeffs_assoc (aCoeffs ds) (aCoeffs ys) (factorCoeffs d)
        _ = mulCoeffs (aCoeffs ds) (mulCoeffs (factorCoeffs d) (aCoeffs ys)) := by
              simp [mulCoeffs_comm]
        _ = mulCoeffs (mulCoeffs (aCoeffs ds) (factorCoeffs d)) (aCoeffs ys) := by
              simpa using (mulCoeffs_assoc (aCoeffs ds) (factorCoeffs d) (aCoeffs ys)).symm

theorem aCoeffs_swap (a b : Nat) (zs : List Nat) :
    aCoeffs (a :: b :: zs) = aCoeffs (b :: a :: zs) := by
  -- Reduce to commutativity/associativity of truncated multiplication.
  simp [aCoeffs, mulFactor_eq_mulCoeffs]
  calc
    mulCoeffs (mulCoeffs (aCoeffs zs) (factorCoeffs b)) (factorCoeffs a) =
        mulCoeffs (aCoeffs zs) (mulCoeffs (factorCoeffs b) (factorCoeffs a)) := by
          simpa using mulCoeffs_assoc (aCoeffs zs) (factorCoeffs b) (factorCoeffs a)
    _ = mulCoeffs (aCoeffs zs) (mulCoeffs (factorCoeffs a) (factorCoeffs b)) := by
          simp [mulCoeffs_comm]
    _ = mulCoeffs (mulCoeffs (aCoeffs zs) (factorCoeffs a)) (factorCoeffs b) := by
          simpa using (mulCoeffs_assoc (aCoeffs zs) (factorCoeffs a) (factorCoeffs b)).symm

theorem aCoeffs_perm {xs ys : List Nat} (h : List.Perm xs ys) : aCoeffs xs = aCoeffs ys := by
  induction h with
  | nil =>
      rfl
  | cons a h ih =>
      simp [aCoeffs, ih]
  | swap a b zs =>
      simpa using (aCoeffs_swap a b zs).symm
  | trans h₁ h₂ ih₁ ih₂ =>
      exact Eq.trans ih₁ ih₂

-- ============================================================
-- Order-free / concurrent formulation: Multiset of generators
-- ============================================================

/--
Lift `aCoeffs` from lists to multisets of generators.

This is the core "concurrent" invariant: `aCoeffs` does not depend on the order of generators.
-/
def aCoeffsMS : Multiset Nat → Coeffs5 :=
  Quot.lift aCoeffs (by
    intro xs ys h
    exact aCoeffs_perm h
  )

@[simp] theorem aCoeffsMS_coe (xs : List Nat) :
    aCoeffsMS (xs : Multiset Nat) = aCoeffs xs := rfl

@[simp] theorem aCoeffsMS_zero : aCoeffsMS (0 : Multiset Nat) = coeffsInit := by
  rfl

theorem aCoeffsMS_add (s t : Multiset Nat) :
    aCoeffsMS (s + t) = mulCoeffs (aCoeffsMS s) (aCoeffsMS t) := by
  refine Quotient.inductionOn₂ s t (fun xs ys => ?_)
  -- On representatives, multiset addition is list append.
  simp [aCoeffsMS, aCoeffs_append]

-- ============================================================
-- Scale invariance (generator scaling ↔ t ↦ k·t)
-- ============================================================

/--
Scaling all generators by `k` corresponds to the change of variables `t ↦ k*t`,
so the coefficient of `t^n` scales by `k^n`.

We prove the homogeneity property for the truncated coefficients `c0..c4`.
-/
def scaleCoeffs (k : Nat) (c : Coeffs5) : Coeffs5 :=
  { c0 := c.c0
    c1 := (k : ℚ) * c.c1
    c2 := (k : ℚ) ^ 2 * c.c2
    c3 := (k : ℚ) ^ 3 * c.c3
    c4 := (k : ℚ) ^ 4 * c.c4 }

@[simp] theorem scaleCoeffs_init (k : Nat) : scaleCoeffs k coeffsInit = coeffsInit := by
  ext <;> simp [scaleCoeffs, coeffsInit]

theorem factorCoeffs_scale (k d : Nat) :
    factorCoeffs (k * d) = scaleCoeffs k (factorCoeffs d) := by
  ext <;> simp [factorCoeffs, scaleCoeffs, factorC1, factorC2, factorC3, factorC4,
    Nat.cast_mul] <;> ring

theorem mulCoeffs_scale (k : Nat) (a b : Coeffs5) :
    mulCoeffs (scaleCoeffs k a) (scaleCoeffs k b) = scaleCoeffs k (mulCoeffs a b) := by
  ext <;> simp [mulCoeffs, scaleCoeffs] <;> ring

theorem aCoeffs_scale (k : Nat) (gens : List Nat) :
    aCoeffs (gens.map (fun d => k * d)) = scaleCoeffs k (aCoeffs gens) := by
  induction gens with
  | nil =>
      simp [aCoeffs, scaleCoeffs_init]
  | cons d ds ih =>
      -- One step of the product recursion + the factor scaling law.
      simp [aCoeffs, mulFactor_eq_mulCoeffs, ih, factorCoeffs_scale, mulCoeffs_scale]

theorem aCoeffsMS_scale (k : Nat) (s : Multiset Nat) :
    aCoeffsMS (s.map (fun d => k * d)) = scaleCoeffs k (aCoeffsMS s) := by
  refine Quotient.inductionOn s (fun xs => ?_)
  simp [aCoeffsMS, aCoeffs_scale, scaleCoeffs]

section MonoidPackaging

-- Package the above "concurrency" law as an actual monoid hom:
-- generator multisets (addition) ↦ truncated coefficient series (multiplication).
local instance : One Coeffs5 := ⟨coeffsInit⟩
local instance : Mul Coeffs5 := ⟨mulCoeffs⟩

local instance : CommMonoid Coeffs5 where
  one := coeffsInit
  mul := mulCoeffs
  mul_assoc := mulCoeffs_assoc
  one_mul := mulCoeffs_init_left
  mul_one := mulCoeffs_init_right
  mul_comm := mulCoeffs_comm

/-- `aCoeffsMS` is a commutative-monoid hom from multiset union to series multiplication. -/
def aCoeffsMS_hom : Multiplicative (Multiset Nat) →* Coeffs5 where
  toFun s := aCoeffsMS s.toAdd
  map_one' := by
    simp
    rfl
  map_mul' := by
    intro s t
    simp [aCoeffsMS_add]
    rfl

end MonoidPackaging

-- ============================================================
-- Closed forms for the low-order coefficients
-- ============================================================

@[simp] theorem aCoeffs_c0 (gens : List Nat) : (aCoeffs gens).c0 = 1 := by
  induction gens with
  | nil => simp [aCoeffs, coeffsInit]
  | cons d ds ih =>
      simp [aCoeffs, mulFactor, ih]

theorem coeff1_formula (gens : List Nat) :
    (aCoeffs gens).c1 = sigmaQ gens 1 / 2 := by
  induction gens with
  | nil =>
      simp [aCoeffs, coeffsInit, sigmaQ]
  | cons d ds ih =>
      -- unfold update, use IH for ds, and simplify.
      simp [aCoeffs, mulFactor, factorC1, sigmaQ, ih]
      ring

theorem coeff2_formula (gens : List Nat) :
    (aCoeffs gens).c2 = (3 * (sigmaQ gens 1) ^ 2 + sigmaQ gens 2) / 24 := by
  induction gens with
  | nil =>
      simp [aCoeffs, coeffsInit, sigmaQ]
  | cons d ds ih =>
      have h1 : (aCoeffs ds).c1 = sigmaQ ds 1 / 2 := coeff1_formula ds
      -- Unfold one multiplication step and substitute formulas for ds.
      simp [aCoeffs, mulFactor, factorC1, factorC2, sigmaQ, ih, h1]
      ring

theorem coeff3_formula (gens : List Nat) :
    (aCoeffs gens).c3 =
      sigmaQ gens 1 * ((sigmaQ gens 1) ^ 2 + sigmaQ gens 2) / 48 := by
  induction gens with
  | nil =>
      simp [aCoeffs, coeffsInit, sigmaQ]
  | cons d ds ih =>
      have h1 : (aCoeffs ds).c1 = sigmaQ ds 1 / 2 := coeff1_formula ds
      have h2 : (aCoeffs ds).c2 = (3 * (sigmaQ ds 1) ^ 2 + sigmaQ ds 2) / 24 := coeff2_formula ds
      simp [aCoeffs, mulFactor, factorC1, factorC2, factorC3, sigmaQ, ih, h1, h2]
      ring

theorem coeff4_formula (gens : List Nat) :
    (aCoeffs gens).c4 =
      (15 * (sigmaQ gens 1) ^ 4
        + 30 * (sigmaQ gens 1) ^ 2 * (sigmaQ gens 2)
        + 5 * (sigmaQ gens 2) ^ 2
        - 2 * sigmaQ gens 4) / 5760 := by
  induction gens with
  | nil =>
      simp [aCoeffs, coeffsInit, sigmaQ]
  | cons d ds ih =>
      have h1 : (aCoeffs ds).c1 = sigmaQ ds 1 / 2 := coeff1_formula ds
      have h2 : (aCoeffs ds).c2 = (3 * (sigmaQ ds 1) ^ 2 + sigmaQ ds 2) / 24 := coeff2_formula ds
      have h3 : (aCoeffs ds).c3 = sigmaQ ds 1 * ((sigmaQ ds 1) ^ 2 + sigmaQ ds 2) / 48 :=
        coeff3_formula ds
      simp [aCoeffs, mulFactor, factorC1, factorC2, factorC3, factorC4, sigmaQ, ih, h1, h2, h3]
      ring

-- ============================================================
-- Tₙ values (from coefficients): Tₙ = n! * [tⁿ]A(t)
-- ============================================================

def TnFromGen (gens : List Nat) : Nat → ℚ
  | 0 => 1
  | 1 => (aCoeffs gens).c1
  | 2 => 2 * (aCoeffs gens).c2
  | 3 => 6 * (aCoeffs gens).c3
  | 4 => 24 * (aCoeffs gens).c4
  | _ => 0

theorem TnFromGen_scale (k : Nat) (gens : List Nat) (n : Nat) :
    TnFromGen (gens.map (fun d => k * d)) n = (k : ℚ) ^ n * TnFromGen gens n := by
  -- We only define `TnFromGen` up to `n = 4`; higher `n` are `0`, so the scaling law is trivial there.
  cases n with
  | zero =>
      simp [TnFromGen]
  | succ n =>
      cases n with
      | zero =>
          simp [TnFromGen, aCoeffs_scale, scaleCoeffs]
      | succ n =>
          cases n with
          | zero =>
              simp [TnFromGen, aCoeffs_scale, scaleCoeffs]
              ring
          | succ n =>
              cases n with
              | zero =>
                  simp [TnFromGen, aCoeffs_scale, scaleCoeffs]
                  ring
              | succ n =>
                  cases n with
                  | zero =>
                      simp [TnFromGen, aCoeffs_scale, scaleCoeffs]
                      ring
                  | succ n =>
                      simp [TnFromGen]

theorem T2_formula (gens : List Nat) :
    TnFromGen gens 2 = (3 * (sigmaQ gens 1) ^ 2 + sigmaQ gens 2) / 12 := by
  simp [TnFromGen, coeff2_formula]
  ring

theorem T3_formula (gens : List Nat) :
    TnFromGen gens 3 = sigmaQ gens 1 * ((sigmaQ gens 1) ^ 2 + sigmaQ gens 2) / 8 := by
  simp [TnFromGen, coeff3_formula]
  ring

theorem T4_formula (gens : List Nat) :
    TnFromGen gens 4 =
      (15 * (sigmaQ gens 1) ^ 4
        + 30 * (sigmaQ gens 1) ^ 2 * (sigmaQ gens 2)
        + 5 * (sigmaQ gens 2) ^ 2
        - 2 * sigmaQ gens 4) / 240 := by
  simp [TnFromGen, coeff4_formula]
  ring

-- ============================================================
-- Concrete generator sets (UFRF / Monster)
-- ============================================================

def ufrfGenerators : List Nat := [3, 5, 7, 11, 13]
def monsterGenerators : List Nat := [47, 59, 71]

theorem T2_universal_for_ufrf_and_monster :
    TnFromGen ufrfGenerators 2 =
        (3 * (sigmaQ ufrfGenerators 1) ^ 2 + sigmaQ ufrfGenerators 2) / 12 ∧
    TnFromGen monsterGenerators 2 =
        (3 * (sigmaQ monsterGenerators 1) ^ 2 + sigmaQ monsterGenerators 2) / 12 := by
  constructor <;> simp [T2_formula]

theorem T3_universal_for_ufrf_and_monster :
    TnFromGen ufrfGenerators 3 =
        sigmaQ ufrfGenerators 1 * ((sigmaQ ufrfGenerators 1) ^ 2 + sigmaQ ufrfGenerators 2) / 8 ∧
    TnFromGen monsterGenerators 3 =
        sigmaQ monsterGenerators 1 * ((sigmaQ monsterGenerators 1) ^ 2 + sigmaQ monsterGenerators 2) / 8 := by
  constructor <;> simp [T3_formula]

theorem T4_universal_for_ufrf_and_monster :
    TnFromGen ufrfGenerators 4 =
        (15 * (sigmaQ ufrfGenerators 1) ^ 4
          + 30 * (sigmaQ ufrfGenerators 1) ^ 2 * (sigmaQ ufrfGenerators 2)
          + 5 * (sigmaQ ufrfGenerators 2) ^ 2
          - 2 * sigmaQ ufrfGenerators 4) / 240 ∧
    TnFromGen monsterGenerators 4 =
        (15 * (sigmaQ monsterGenerators 1) ^ 4
          + 30 * (sigmaQ monsterGenerators 1) ^ 2 * (sigmaQ monsterGenerators 2)
          + 5 * (sigmaQ monsterGenerators 2) ^ 2
          - 2 * sigmaQ monsterGenerators 4) / 240 := by
  constructor <;> simp [T4_formula]

end TnRecurrence
