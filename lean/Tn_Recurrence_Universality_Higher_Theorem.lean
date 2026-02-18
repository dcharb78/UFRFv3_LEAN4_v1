import Mathlib

/-!
# Higher Coefficient Universality (Degree ≤ 7)

This file extends the coefficient-level "universality" results for the generating function:

`A(t) = ∏ (exp(d*t) - 1) / (d*t)`.

Each factor expands as:

`(exp(d*t) - 1)/(d*t) = Σ_{n>=0} d^n * t^n / (n+1)!`.

We compute coefficients up to `t^7` by an explicit truncated convolution recursion, and
prove closed forms for `c₅, c₆, c₇` in terms of the power sums `σₖ = Σ dᵢ^k`.

Engineering goal:
- no placeholders
- minimal axioms (pure algebra over `ℚ`)

This is the Lean counterpart to the repo note:
`TN_DENOMINATOR_EMERGENCE_TEST.md` (coefficients, not `Tₙ` denominators).
-/

namespace TnRecurrenceHigher

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
  simp [sigmaQ, sigma, Nat.cast_add]

-- ============================================================
-- Truncated (degree ≤ 7) coefficient recursion for A(t)
-- ============================================================

structure Coeffs8 where
  c0 : ℚ
  c1 : ℚ
  c2 : ℚ
  c3 : ℚ
  c4 : ℚ
  c5 : ℚ
  c6 : ℚ
  c7 : ℚ
deriving Repr

@[ext] theorem Coeffs8.ext (a b : Coeffs8)
    (h0 : a.c0 = b.c0)
    (h1 : a.c1 = b.c1)
    (h2 : a.c2 = b.c2)
    (h3 : a.c3 = b.c3)
    (h4 : a.c4 = b.c4)
    (h5 : a.c5 = b.c5)
    (h6 : a.c6 = b.c6)
    (h7 : a.c7 = b.c7) : a = b := by
  cases a
  cases b
  simp_all

def coeffsInit : Coeffs8 :=
  { c0 := 1, c1 := 0, c2 := 0, c3 := 0, c4 := 0, c5 := 0, c6 := 0, c7 := 0 }

-- Factor coefficients: `d^n / (n+1)!` for `n = 1..7`.
def factorC1 (d : Nat) : ℚ := (d : ℚ) / 2
def factorC2 (d : Nat) : ℚ := (d ^ 2 : ℚ) / 6
def factorC3 (d : Nat) : ℚ := (d ^ 3 : ℚ) / 24
def factorC4 (d : Nat) : ℚ := (d ^ 4 : ℚ) / 120
def factorC5 (d : Nat) : ℚ := (d ^ 5 : ℚ) / 720
def factorC6 (d : Nat) : ℚ := (d ^ 6 : ℚ) / 5040
def factorC7 (d : Nat) : ℚ := (d ^ 7 : ℚ) / 40320

/-- Multiply existing coefficients by the single-generator factor (truncated to degree 7). -/
def mulFactor (d : Nat) (c : Coeffs8) : Coeffs8 :=
  { c0 := c.c0
    c1 := c.c1 + factorC1 d * c.c0
    c2 := c.c2 + factorC1 d * c.c1 + factorC2 d * c.c0
    c3 := c.c3 + factorC1 d * c.c2 + factorC2 d * c.c1 + factorC3 d * c.c0
    c4 := c.c4 + factorC1 d * c.c3 + factorC2 d * c.c2 + factorC3 d * c.c1 + factorC4 d * c.c0
    c5 := c.c5 + factorC1 d * c.c4 + factorC2 d * c.c3 + factorC3 d * c.c2 + factorC4 d * c.c1
        + factorC5 d * c.c0
    c6 := c.c6 + factorC1 d * c.c5 + factorC2 d * c.c4 + factorC3 d * c.c3 + factorC4 d * c.c2
        + factorC5 d * c.c1 + factorC6 d * c.c0
    c7 := c.c7 + factorC1 d * c.c6 + factorC2 d * c.c5 + factorC3 d * c.c4 + factorC4 d * c.c3
        + factorC5 d * c.c2 + factorC6 d * c.c1 + factorC7 d * c.c0 }

/-- Degree ≤ 7 coefficients of `A(t)` for a list of generators. -/
def aCoeffs : List Nat → Coeffs8
  | [] => coeffsInit
  | d :: ds => mulFactor d (aCoeffs ds)

@[simp] theorem aCoeffs_nil : aCoeffs [] = coeffsInit := by rfl
@[simp] theorem aCoeffs_cons (d : Nat) (ds : List Nat) :
    aCoeffs (d :: ds) = mulFactor d (aCoeffs ds) := by rfl

@[simp] theorem aCoeffs_c0 (gens : List Nat) : (aCoeffs gens).c0 = 1 := by
  induction gens with
  | nil => simp [aCoeffs, coeffsInit]
  | cons d ds ih =>
      simp [aCoeffs, mulFactor, ih]

-- ============================================================
-- Closed forms for coefficients c₁..c₇
-- ============================================================

theorem coeff1_formula (gens : List Nat) :
    (aCoeffs gens).c1 = sigmaQ gens 1 / 2 := by
  induction gens with
  | nil =>
      simp [aCoeffs, coeffsInit, sigmaQ]
  | cons d ds ih =>
      simp [aCoeffs, mulFactor, factorC1, sigmaQ, ih]
      ring

theorem coeff2_formula (gens : List Nat) :
    (aCoeffs gens).c2 = (3 * (sigmaQ gens 1) ^ 2 + sigmaQ gens 2) / 24 := by
  induction gens with
  | nil =>
      simp [aCoeffs, coeffsInit, sigmaQ]
  | cons d ds ih =>
      have h1 : (aCoeffs ds).c1 = sigmaQ ds 1 / 2 := coeff1_formula ds
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

/--
`c₅` closed form (universal, coefficient-level):

```
c₅ =
  -(σ₄ σ₁)/5760
  + (σ₂² σ₁)/2304
  + (σ₂ σ₁³)/1152
  + (σ₁⁵)/3840
```

Notably: there is no `σ₅` term.
-/
theorem coeff5_formula (gens : List Nat) :
    (aCoeffs gens).c5 =
      -(sigmaQ gens 4 * sigmaQ gens 1) / 5760
      + ((sigmaQ gens 2) ^ 2 * sigmaQ gens 1) / 2304
      + (sigmaQ gens 2 * (sigmaQ gens 1) ^ 3) / 1152
      + ((sigmaQ gens 1) ^ 5) / 3840 := by
  induction gens with
  | nil =>
      simp [aCoeffs, coeffsInit, sigmaQ]
  | cons d ds ih =>
      have h1 : (aCoeffs ds).c1 = sigmaQ ds 1 / 2 := coeff1_formula ds
      have h2 : (aCoeffs ds).c2 = (3 * (sigmaQ ds 1) ^ 2 + sigmaQ ds 2) / 24 := coeff2_formula ds
      have h3 : (aCoeffs ds).c3 = sigmaQ ds 1 * ((sigmaQ ds 1) ^ 2 + sigmaQ ds 2) / 48 :=
        coeff3_formula ds
      have h4 : (aCoeffs ds).c4 =
          (15 * (sigmaQ ds 1) ^ 4
            + 30 * (sigmaQ ds 1) ^ 2 * (sigmaQ ds 2)
            + 5 * (sigmaQ ds 2) ^ 2
            - 2 * sigmaQ ds 4) / 5760 := coeff4_formula ds
      simp [aCoeffs, mulFactor, factorC1, factorC2, factorC3, factorC4, factorC5, sigmaQ, ih, h1, h2, h3, h4]
      ring

/--
`c₆` closed form (universal, coefficient-level):

```
c₆ =
  +(σ₆)/181440
  -(σ₄ σ₂)/69120
  -(σ₄ σ₁²)/23040
  +(σ₂³)/82944
  +(σ₂² σ₁²)/9216
  +(σ₂ σ₁⁴)/9216
  +(σ₁⁶)/46080
```
-/
theorem coeff6_formula (gens : List Nat) :
    (aCoeffs gens).c6 =
      (sigmaQ gens 6) / 181440
      - (sigmaQ gens 4 * sigmaQ gens 2) / 69120
      - (sigmaQ gens 4 * (sigmaQ gens 1) ^ 2) / 23040
      + ((sigmaQ gens 2) ^ 3) / 82944
      + ((sigmaQ gens 2) ^ 2 * (sigmaQ gens 1) ^ 2) / 9216
      + (sigmaQ gens 2 * (sigmaQ gens 1) ^ 4) / 9216
      + ((sigmaQ gens 1) ^ 6) / 46080 := by
  induction gens with
  | nil =>
      simp [aCoeffs, coeffsInit, sigmaQ]
  | cons d ds ih =>
      have h1 : (aCoeffs ds).c1 = sigmaQ ds 1 / 2 := coeff1_formula ds
      have h2 : (aCoeffs ds).c2 = (3 * (sigmaQ ds 1) ^ 2 + sigmaQ ds 2) / 24 := coeff2_formula ds
      have h3 : (aCoeffs ds).c3 = sigmaQ ds 1 * ((sigmaQ ds 1) ^ 2 + sigmaQ ds 2) / 48 :=
        coeff3_formula ds
      have h4 : (aCoeffs ds).c4 =
          (15 * (sigmaQ ds 1) ^ 4
            + 30 * (sigmaQ ds 1) ^ 2 * (sigmaQ ds 2)
            + 5 * (sigmaQ ds 2) ^ 2
            - 2 * sigmaQ ds 4) / 5760 := coeff4_formula ds
      have h5 : (aCoeffs ds).c5 =
          -(sigmaQ ds 4 * sigmaQ ds 1) / 5760
          + ((sigmaQ ds 2) ^ 2 * sigmaQ ds 1) / 2304
          + (sigmaQ ds 2 * (sigmaQ ds 1) ^ 3) / 1152
          + ((sigmaQ ds 1) ^ 5) / 3840 := coeff5_formula ds
      simp [aCoeffs, mulFactor, factorC1, factorC2, factorC3, factorC4, factorC5, factorC6,
        sigmaQ, ih, h1, h2, h3, h4, h5]
      ring

/--
`c₇` closed form (universal, coefficient-level):

```
c₇ =
  +(σ₆ σ₁)/362880
  -(σ₄ σ₂ σ₁)/138240
  -(σ₄ σ₁³)/138240
  +(σ₂³ σ₁)/165888
  +(σ₂² σ₁³)/55296
  +(σ₂ σ₁⁵)/92160
  +(σ₁⁷)/645120
```

Notably: there is no `σ₇` term.
-/
theorem coeff7_formula (gens : List Nat) :
    (aCoeffs gens).c7 =
      (sigmaQ gens 6 * sigmaQ gens 1) / 362880
      - (sigmaQ gens 4 * sigmaQ gens 2 * sigmaQ gens 1) / 138240
      - (sigmaQ gens 4 * (sigmaQ gens 1) ^ 3) / 138240
      + ((sigmaQ gens 2) ^ 3 * sigmaQ gens 1) / 165888
      + ((sigmaQ gens 2) ^ 2 * (sigmaQ gens 1) ^ 3) / 55296
      + (sigmaQ gens 2 * (sigmaQ gens 1) ^ 5) / 92160
      + ((sigmaQ gens 1) ^ 7) / 645120 := by
  induction gens with
  | nil =>
      simp [aCoeffs, coeffsInit, sigmaQ]
  | cons d ds ih =>
      have h1 : (aCoeffs ds).c1 = sigmaQ ds 1 / 2 := coeff1_formula ds
      have h2 : (aCoeffs ds).c2 = (3 * (sigmaQ ds 1) ^ 2 + sigmaQ ds 2) / 24 := coeff2_formula ds
      have h3 : (aCoeffs ds).c3 = sigmaQ ds 1 * ((sigmaQ ds 1) ^ 2 + sigmaQ ds 2) / 48 :=
        coeff3_formula ds
      have h4 : (aCoeffs ds).c4 =
          (15 * (sigmaQ ds 1) ^ 4
            + 30 * (sigmaQ ds 1) ^ 2 * (sigmaQ ds 2)
            + 5 * (sigmaQ ds 2) ^ 2
            - 2 * sigmaQ ds 4) / 5760 := coeff4_formula ds
      have h5 : (aCoeffs ds).c5 =
          -(sigmaQ ds 4 * sigmaQ ds 1) / 5760
          + ((sigmaQ ds 2) ^ 2 * sigmaQ ds 1) / 2304
          + (sigmaQ ds 2 * (sigmaQ ds 1) ^ 3) / 1152
          + ((sigmaQ ds 1) ^ 5) / 3840 := coeff5_formula ds
      have h6 : (aCoeffs ds).c6 =
          (sigmaQ ds 6) / 181440
          - (sigmaQ ds 4 * sigmaQ ds 2) / 69120
          - (sigmaQ ds 4 * (sigmaQ ds 1) ^ 2) / 23040
          + ((sigmaQ ds 2) ^ 3) / 82944
          + ((sigmaQ ds 2) ^ 2 * (sigmaQ ds 1) ^ 2) / 9216
          + (sigmaQ ds 2 * (sigmaQ ds 1) ^ 4) / 9216
          + ((sigmaQ ds 1) ^ 6) / 46080 := coeff6_formula ds
      simp [aCoeffs, mulFactor, factorC1, factorC2, factorC3, factorC4, factorC5, factorC6, factorC7,
        sigmaQ, ih, h1, h2, h3, h4, h5, h6]
      ring

-- ============================================================
-- Tₙ values (from coefficients): Tₙ = n! * [tⁿ]A(t)
-- ============================================================

/--
`Tₙ` values derived from the coefficient tuple, for `n ≤ 7`.

By construction (single generator check): if `A(t) = (exp(d*t)-1)/(d*t)`,
then `[tⁿ]A(t) = d^n/(n+1)!`, hence `Tₙ = n! * [tⁿ]A(t) = d^n/(n+1)`.
-/
def TnFromGenUpTo7 (gens : List Nat) : Nat → ℚ
  | 0 => 1
  | 1 => (aCoeffs gens).c1
  | 2 => 2 * (aCoeffs gens).c2
  | 3 => 6 * (aCoeffs gens).c3
  | 4 => 24 * (aCoeffs gens).c4
  | 5 => 120 * (aCoeffs gens).c5
  | 6 => 720 * (aCoeffs gens).c6
  | 7 => 5040 * (aCoeffs gens).c7
  | _ => 0

theorem T5_formula (gens : List Nat) :
    TnFromGenUpTo7 gens 5 =
      (3 * (sigmaQ gens 1) ^ 5
        + 10 * sigmaQ gens 2 * (sigmaQ gens 1) ^ 3
        + 5 * (sigmaQ gens 2) ^ 2 * sigmaQ gens 1
        - 2 * sigmaQ gens 4 * sigmaQ gens 1) / 96 := by
  simp [TnFromGenUpTo7, coeff5_formula]
  ring

theorem T6_formula (gens : List Nat) :
    TnFromGenUpTo7 gens 6 =
      (16 * sigmaQ gens 6
        - 42 * sigmaQ gens 4 * sigmaQ gens 2
        - 126 * sigmaQ gens 4 * (sigmaQ gens 1) ^ 2
        + 35 * (sigmaQ gens 2) ^ 3
        + 315 * (sigmaQ gens 2) ^ 2 * (sigmaQ gens 1) ^ 2
        + 315 * sigmaQ gens 2 * (sigmaQ gens 1) ^ 4
        + 63 * (sigmaQ gens 1) ^ 6) / 4032 := by
  simp [TnFromGenUpTo7, coeff6_formula]
  ring

theorem T7_formula (gens : List Nat) :
    TnFromGenUpTo7 gens 7 =
      (16 * sigmaQ gens 6 * sigmaQ gens 1
        - 42 * sigmaQ gens 4 * sigmaQ gens 2 * sigmaQ gens 1
        - 42 * sigmaQ gens 4 * (sigmaQ gens 1) ^ 3
        + 35 * (sigmaQ gens 2) ^ 3 * sigmaQ gens 1
        + 105 * (sigmaQ gens 2) ^ 2 * (sigmaQ gens 1) ^ 3
        + 63 * sigmaQ gens 2 * (sigmaQ gens 1) ^ 5
        + 9 * (sigmaQ gens 1) ^ 7) / 1152 := by
  simp [TnFromGenUpTo7, coeff7_formula]
  ring

-- ------------------------------------------------------------
-- Concrete generator sets (UFRF / Monster)
-- ------------------------------------------------------------

def ufrfGenerators : List Nat := [3, 5, 7, 11, 13]
def monsterGenerators : List Nat := [47, 59, 71]

theorem T5_universal_for_ufrf_and_monster :
    TnFromGenUpTo7 ufrfGenerators 5 =
        (3 * (sigmaQ ufrfGenerators 1) ^ 5
          + 10 * sigmaQ ufrfGenerators 2 * (sigmaQ ufrfGenerators 1) ^ 3
          + 5 * (sigmaQ ufrfGenerators 2) ^ 2 * sigmaQ ufrfGenerators 1
          - 2 * sigmaQ ufrfGenerators 4 * sigmaQ ufrfGenerators 1) / 96
      ∧
    TnFromGenUpTo7 monsterGenerators 5 =
        (3 * (sigmaQ monsterGenerators 1) ^ 5
          + 10 * sigmaQ monsterGenerators 2 * (sigmaQ monsterGenerators 1) ^ 3
          + 5 * (sigmaQ monsterGenerators 2) ^ 2 * sigmaQ monsterGenerators 1
          - 2 * sigmaQ monsterGenerators 4 * sigmaQ monsterGenerators 1) / 96 := by
  constructor <;> simpa using (T5_formula (gens := _))

theorem T6_universal_for_ufrf_and_monster :
    TnFromGenUpTo7 ufrfGenerators 6 =
        (16 * sigmaQ ufrfGenerators 6
          - 42 * sigmaQ ufrfGenerators 4 * sigmaQ ufrfGenerators 2
          - 126 * sigmaQ ufrfGenerators 4 * (sigmaQ ufrfGenerators 1) ^ 2
          + 35 * (sigmaQ ufrfGenerators 2) ^ 3
          + 315 * (sigmaQ ufrfGenerators 2) ^ 2 * (sigmaQ ufrfGenerators 1) ^ 2
          + 315 * sigmaQ ufrfGenerators 2 * (sigmaQ ufrfGenerators 1) ^ 4
          + 63 * (sigmaQ ufrfGenerators 1) ^ 6) / 4032
      ∧
    TnFromGenUpTo7 monsterGenerators 6 =
        (16 * sigmaQ monsterGenerators 6
          - 42 * sigmaQ monsterGenerators 4 * sigmaQ monsterGenerators 2
          - 126 * sigmaQ monsterGenerators 4 * (sigmaQ monsterGenerators 1) ^ 2
          + 35 * (sigmaQ monsterGenerators 2) ^ 3
          + 315 * (sigmaQ monsterGenerators 2) ^ 2 * (sigmaQ monsterGenerators 1) ^ 2
          + 315 * sigmaQ monsterGenerators 2 * (sigmaQ monsterGenerators 1) ^ 4
          + 63 * (sigmaQ monsterGenerators 1) ^ 6) / 4032 := by
  constructor <;> simpa using (T6_formula (gens := _))

theorem T7_universal_for_ufrf_and_monster :
    TnFromGenUpTo7 ufrfGenerators 7 =
        (16 * sigmaQ ufrfGenerators 6 * sigmaQ ufrfGenerators 1
          - 42 * sigmaQ ufrfGenerators 4 * sigmaQ ufrfGenerators 2 * sigmaQ ufrfGenerators 1
          - 42 * sigmaQ ufrfGenerators 4 * (sigmaQ ufrfGenerators 1) ^ 3
          + 35 * (sigmaQ ufrfGenerators 2) ^ 3 * sigmaQ ufrfGenerators 1
          + 105 * (sigmaQ ufrfGenerators 2) ^ 2 * (sigmaQ ufrfGenerators 1) ^ 3
          + 63 * sigmaQ ufrfGenerators 2 * (sigmaQ ufrfGenerators 1) ^ 5
          + 9 * (sigmaQ ufrfGenerators 1) ^ 7) / 1152
      ∧
    TnFromGenUpTo7 monsterGenerators 7 =
        (16 * sigmaQ monsterGenerators 6 * sigmaQ monsterGenerators 1
          - 42 * sigmaQ monsterGenerators 4 * sigmaQ monsterGenerators 2 * sigmaQ monsterGenerators 1
          - 42 * sigmaQ monsterGenerators 4 * (sigmaQ monsterGenerators 1) ^ 3
          + 35 * (sigmaQ monsterGenerators 2) ^ 3 * sigmaQ monsterGenerators 1
          + 105 * (sigmaQ monsterGenerators 2) ^ 2 * (sigmaQ monsterGenerators 1) ^ 3
          + 63 * sigmaQ monsterGenerators 2 * (sigmaQ monsterGenerators 1) ^ 5
          + 9 * (sigmaQ monsterGenerators 1) ^ 7) / 1152 := by
  constructor <;> simpa using (T7_formula (gens := _))

end TnRecurrenceHigher
