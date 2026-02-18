import Tn_Recurrence_Universality_Degree9_Theorem

/-!
# Higher Coefficient Universality (Degree ≤ 10)

This file extends the explicit coefficient closed-form chain to degree 10:
the coefficient `[t^10]` of

`A(t) = ∏ (exp(d*t) - 1) / (d*t)`.

We keep the same proof-engineering constraints used throughout the repo:
* pure algebra over `ℚ`
* no stubs
* formulas expressed via power sums `σₖ = Σ dᵢ^k`
-/

namespace TnRecurrenceHigher

-- ============================================================
-- Truncated (degree ≤ 10) coefficient recursion for A(t)
-- ============================================================

structure Coeffs11 where
  c0 : ℚ
  c1 : ℚ
  c2 : ℚ
  c3 : ℚ
  c4 : ℚ
  c5 : ℚ
  c6 : ℚ
  c7 : ℚ
  c8 : ℚ
  c9 : ℚ
  c10 : ℚ
deriving Repr

def coeffsInit11 : Coeffs11 :=
  { c0 := 1, c1 := 0, c2 := 0, c3 := 0, c4 := 0, c5 := 0, c6 := 0, c7 := 0, c8 := 0, c9 := 0, c10 := 0 }

-- Factor coefficient: `d^10 / (10+1)! = d^10 / 11!`.
def factorC10 (d : Nat) : ℚ := (d ^ 10 : ℚ) / 39916800

/-- Multiply existing coefficients by the single-generator factor (truncated to degree 10). -/
def mulFactor11 (d : Nat) (c : Coeffs11) : Coeffs11 :=
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
        + factorC5 d * c.c2 + factorC6 d * c.c1 + factorC7 d * c.c0
    c8 := c.c8 + factorC1 d * c.c7 + factorC2 d * c.c6 + factorC3 d * c.c5 + factorC4 d * c.c4
        + factorC5 d * c.c3 + factorC6 d * c.c2 + factorC7 d * c.c1 + factorC8 d * c.c0
    c9 := c.c9 + factorC1 d * c.c8 + factorC2 d * c.c7 + factorC3 d * c.c6 + factorC4 d * c.c5
        + factorC5 d * c.c4 + factorC6 d * c.c3 + factorC7 d * c.c2 + factorC8 d * c.c1
        + factorC9 d * c.c0
    c10 := c.c10 + factorC1 d * c.c9 + factorC2 d * c.c8 + factorC3 d * c.c7 + factorC4 d * c.c6
        + factorC5 d * c.c5 + factorC6 d * c.c4 + factorC7 d * c.c3 + factorC8 d * c.c2
        + factorC9 d * c.c1 + factorC10 d * c.c0 }

/-- Degree ≤ 10 coefficients of `A(t)` for a list of generators. -/
def aCoeffs11 : List Nat → Coeffs11
  | [] => coeffsInit11
  | d :: ds => mulFactor11 d (aCoeffs11 ds)

@[simp] theorem aCoeffs11_nil : aCoeffs11 [] = coeffsInit11 := by rfl
@[simp] theorem aCoeffs11_cons (d : Nat) (ds : List Nat) :
    aCoeffs11 (d :: ds) = mulFactor11 d (aCoeffs11 ds) := by rfl

@[simp] theorem aCoeffs11_c0 (gens : List Nat) : (aCoeffs11 gens).c0 = 1 := by
  induction gens with
  | nil => simp [aCoeffs11, coeffsInit11]
  | cons d ds ih =>
      simp [aCoeffs11, mulFactor11, ih]

-- ============================================================
-- Projection: reuse all degree ≤ 9 facts from `aCoeffs10`
-- ============================================================

def toCoeffs10 (c : Coeffs11) : Coeffs10 :=
  { c0 := c.c0
    c1 := c.c1
    c2 := c.c2
    c3 := c.c3
    c4 := c.c4
    c5 := c.c5
    c6 := c.c6
    c7 := c.c7
    c8 := c.c8
    c9 := c.c9 }

theorem toCoeffs10_mulFactor11 (d : Nat) (c : Coeffs11) :
    toCoeffs10 (mulFactor11 d c) = mulFactor10 d (toCoeffs10 c) := by
  rfl

theorem toCoeffs10_aCoeffs11 (gens : List Nat) :
    toCoeffs10 (aCoeffs11 gens) = aCoeffs10 gens := by
  induction gens with
  | nil =>
      simp [aCoeffs11, aCoeffs10, coeffsInit11, coeffsInit10, toCoeffs10]
  | cons d ds ih =>
      simpa [aCoeffs11, aCoeffs10, toCoeffs10_mulFactor11] using congrArg (mulFactor10 d) ih

theorem aCoeffs11_c1_eq (gens : List Nat) : (aCoeffs11 gens).c1 = (aCoeffs10 gens).c1 := by
  have h := congrArg Coeffs10.c1 (toCoeffs10_aCoeffs11 gens)
  simpa [toCoeffs10] using h

theorem aCoeffs11_c2_eq (gens : List Nat) : (aCoeffs11 gens).c2 = (aCoeffs10 gens).c2 := by
  have h := congrArg Coeffs10.c2 (toCoeffs10_aCoeffs11 gens)
  simpa [toCoeffs10] using h

theorem aCoeffs11_c3_eq (gens : List Nat) : (aCoeffs11 gens).c3 = (aCoeffs10 gens).c3 := by
  have h := congrArg Coeffs10.c3 (toCoeffs10_aCoeffs11 gens)
  simpa [toCoeffs10] using h

theorem aCoeffs11_c4_eq (gens : List Nat) : (aCoeffs11 gens).c4 = (aCoeffs10 gens).c4 := by
  have h := congrArg Coeffs10.c4 (toCoeffs10_aCoeffs11 gens)
  simpa [toCoeffs10] using h

theorem aCoeffs11_c5_eq (gens : List Nat) : (aCoeffs11 gens).c5 = (aCoeffs10 gens).c5 := by
  have h := congrArg Coeffs10.c5 (toCoeffs10_aCoeffs11 gens)
  simpa [toCoeffs10] using h

theorem aCoeffs11_c6_eq (gens : List Nat) : (aCoeffs11 gens).c6 = (aCoeffs10 gens).c6 := by
  have h := congrArg Coeffs10.c6 (toCoeffs10_aCoeffs11 gens)
  simpa [toCoeffs10] using h

theorem aCoeffs11_c7_eq (gens : List Nat) : (aCoeffs11 gens).c7 = (aCoeffs10 gens).c7 := by
  have h := congrArg Coeffs10.c7 (toCoeffs10_aCoeffs11 gens)
  simpa [toCoeffs10] using h

theorem aCoeffs11_c8_eq (gens : List Nat) : (aCoeffs11 gens).c8 = (aCoeffs10 gens).c8 := by
  have h := congrArg Coeffs10.c8 (toCoeffs10_aCoeffs11 gens)
  simpa [toCoeffs10] using h

theorem aCoeffs11_c9_eq (gens : List Nat) : (aCoeffs11 gens).c9 = (aCoeffs10 gens).c9 := by
  have h := congrArg Coeffs10.c9 (toCoeffs10_aCoeffs11 gens)
  simpa [toCoeffs10] using h

-- ============================================================
-- New closed form: coefficient c₁₀
-- ============================================================

theorem coeff10_formula (gens : List Nat) :
    (aCoeffs11 gens).c10 =
      ((sigmaQ gens 1) ^ 10) / 3715891200
      + ((sigmaQ gens 1) ^ 8 * sigmaQ gens 2) / 247726080
      + ((sigmaQ gens 1) ^ 6 * (sigmaQ gens 2) ^ 2) / 53084160
      - ((sigmaQ gens 1) ^ 6 * sigmaQ gens 4) / 132710400
      + ((sigmaQ gens 1) ^ 4 * (sigmaQ gens 2) ^ 3) / 31850496
      - ((sigmaQ gens 1) ^ 4 * sigmaQ gens 2 * sigmaQ gens 4) / 26542080
      + ((sigmaQ gens 1) ^ 4 * sigmaQ gens 6) / 69672960
      + ((sigmaQ gens 1) ^ 2 * (sigmaQ gens 2) ^ 4) / 63700992
      - ((sigmaQ gens 1) ^ 2 * (sigmaQ gens 2) ^ 2 * sigmaQ gens 4) / 26542080
      + ((sigmaQ gens 1) ^ 2 * sigmaQ gens 2 * sigmaQ gens 6) / 34836480
      + ((sigmaQ gens 1) ^ 2 * (sigmaQ gens 4) ^ 2) / 132710400
      - ((sigmaQ gens 1) ^ 2 * sigmaQ gens 8) / 77414400
      + (sigmaQ gens 10) / 479001600
      + ((sigmaQ gens 2) ^ 5) / 955514880
      - ((sigmaQ gens 2) ^ 3 * sigmaQ gens 4) / 238878720
      + ((sigmaQ gens 2) ^ 2 * sigmaQ gens 6) / 209018880
      + (sigmaQ gens 2 * (sigmaQ gens 4) ^ 2) / 398131200
      - (sigmaQ gens 2 * sigmaQ gens 8) / 232243200
      - (sigmaQ gens 4 * sigmaQ gens 6) / 522547200 := by
  induction gens with
  | nil =>
      simp [aCoeffs11, coeffsInit11, sigmaQ]
  | cons d ds ih =>
      -- Closed forms for degree ≤ 7 come from the previous universality file (via `aCoeffs9` → `aCoeffs`).
      have h1 : (aCoeffs11 ds).c1 = sigmaQ ds 1 / 2 := by
        calc
          (aCoeffs11 ds).c1 = (aCoeffs10 ds).c1 := aCoeffs11_c1_eq ds
          _ = (aCoeffs9 ds).c1 := aCoeffs10_c1_eq ds
          _ = (aCoeffs ds).c1 := aCoeffs9_c1_eq ds
          _ = sigmaQ ds 1 / 2 := by simpa using (coeff1_formula ds)
      have h2 : (aCoeffs11 ds).c2 = (3 * (sigmaQ ds 1) ^ 2 + sigmaQ ds 2) / 24 := by
        calc
          (aCoeffs11 ds).c2 = (aCoeffs10 ds).c2 := aCoeffs11_c2_eq ds
          _ = (aCoeffs9 ds).c2 := aCoeffs10_c2_eq ds
          _ = (aCoeffs ds).c2 := aCoeffs9_c2_eq ds
          _ = (3 * (sigmaQ ds 1) ^ 2 + sigmaQ ds 2) / 24 := by simpa using (coeff2_formula ds)
      have h3 : (aCoeffs11 ds).c3 = sigmaQ ds 1 * ((sigmaQ ds 1) ^ 2 + sigmaQ ds 2) / 48 := by
        calc
          (aCoeffs11 ds).c3 = (aCoeffs10 ds).c3 := aCoeffs11_c3_eq ds
          _ = (aCoeffs9 ds).c3 := aCoeffs10_c3_eq ds
          _ = (aCoeffs ds).c3 := aCoeffs9_c3_eq ds
          _ = sigmaQ ds 1 * ((sigmaQ ds 1) ^ 2 + sigmaQ ds 2) / 48 := by simpa using (coeff3_formula ds)
      have h4 : (aCoeffs11 ds).c4 =
          (15 * (sigmaQ ds 1) ^ 4
            + 30 * (sigmaQ ds 1) ^ 2 * (sigmaQ ds 2)
            + 5 * (sigmaQ ds 2) ^ 2
            - 2 * sigmaQ ds 4) / 5760 := by
        calc
          (aCoeffs11 ds).c4 = (aCoeffs10 ds).c4 := aCoeffs11_c4_eq ds
          _ = (aCoeffs9 ds).c4 := aCoeffs10_c4_eq ds
          _ = (aCoeffs ds).c4 := aCoeffs9_c4_eq ds
          _ =
              (15 * (sigmaQ ds 1) ^ 4
                + 30 * (sigmaQ ds 1) ^ 2 * (sigmaQ ds 2)
                + 5 * (sigmaQ ds 2) ^ 2
                - 2 * sigmaQ ds 4) / 5760 := by simpa using (coeff4_formula ds)
      have h5 : (aCoeffs11 ds).c5 =
          -(sigmaQ ds 4 * sigmaQ ds 1) / 5760
          + ((sigmaQ ds 2) ^ 2 * sigmaQ ds 1) / 2304
          + (sigmaQ ds 2 * (sigmaQ ds 1) ^ 3) / 1152
          + ((sigmaQ ds 1) ^ 5) / 3840 := by
        calc
          (aCoeffs11 ds).c5 = (aCoeffs10 ds).c5 := aCoeffs11_c5_eq ds
          _ = (aCoeffs9 ds).c5 := aCoeffs10_c5_eq ds
          _ = (aCoeffs ds).c5 := aCoeffs9_c5_eq ds
          _ =
              -(sigmaQ ds 4 * sigmaQ ds 1) / 5760
              + ((sigmaQ ds 2) ^ 2 * sigmaQ ds 1) / 2304
              + (sigmaQ ds 2 * (sigmaQ ds 1) ^ 3) / 1152
              + ((sigmaQ ds 1) ^ 5) / 3840 := by simpa using (coeff5_formula ds)
      have h6 : (aCoeffs11 ds).c6 =
          (sigmaQ ds 6) / 181440
          - (sigmaQ ds 4 * sigmaQ ds 2) / 69120
          - (sigmaQ ds 4 * (sigmaQ ds 1) ^ 2) / 23040
          + ((sigmaQ ds 2) ^ 3) / 82944
          + ((sigmaQ ds 2) ^ 2 * (sigmaQ ds 1) ^ 2) / 9216
          + (sigmaQ ds 2 * (sigmaQ ds 1) ^ 4) / 9216
          + ((sigmaQ ds 1) ^ 6) / 46080 := by
        calc
          (aCoeffs11 ds).c6 = (aCoeffs10 ds).c6 := aCoeffs11_c6_eq ds
          _ = (aCoeffs9 ds).c6 := aCoeffs10_c6_eq ds
          _ = (aCoeffs ds).c6 := aCoeffs9_c6_eq ds
          _ =
              (sigmaQ ds 6) / 181440
              - (sigmaQ ds 4 * sigmaQ ds 2) / 69120
              - (sigmaQ ds 4 * (sigmaQ ds 1) ^ 2) / 23040
              + ((sigmaQ ds 2) ^ 3) / 82944
              + ((sigmaQ ds 2) ^ 2 * (sigmaQ ds 1) ^ 2) / 9216
              + (sigmaQ ds 2 * (sigmaQ ds 1) ^ 4) / 9216
              + ((sigmaQ ds 1) ^ 6) / 46080 := by simpa using (coeff6_formula ds)
      have h7 : (aCoeffs11 ds).c7 =
          (sigmaQ ds 6 * sigmaQ ds 1) / 362880
          - (sigmaQ ds 4 * sigmaQ ds 2 * sigmaQ ds 1) / 138240
          - (sigmaQ ds 4 * (sigmaQ ds 1) ^ 3) / 138240
          + ((sigmaQ ds 2) ^ 3 * sigmaQ ds 1) / 165888
          + ((sigmaQ ds 2) ^ 2 * (sigmaQ ds 1) ^ 3) / 55296
          + (sigmaQ ds 2 * (sigmaQ ds 1) ^ 5) / 92160
          + ((sigmaQ ds 1) ^ 7) / 645120 := by
        calc
          (aCoeffs11 ds).c7 = (aCoeffs10 ds).c7 := aCoeffs11_c7_eq ds
          _ = (aCoeffs9 ds).c7 := aCoeffs10_c7_eq ds
          _ = (aCoeffs ds).c7 := aCoeffs9_c7_eq ds
          _ =
              (sigmaQ ds 6 * sigmaQ ds 1) / 362880
              - (sigmaQ ds 4 * sigmaQ ds 2 * sigmaQ ds 1) / 138240
              - (sigmaQ ds 4 * (sigmaQ ds 1) ^ 3) / 138240
              + ((sigmaQ ds 2) ^ 3 * sigmaQ ds 1) / 165888
              + ((sigmaQ ds 2) ^ 2 * (sigmaQ ds 1) ^ 3) / 55296
              + (sigmaQ ds 2 * (sigmaQ ds 1) ^ 5) / 92160
              + ((sigmaQ ds 1) ^ 7) / 645120 := by simpa using (coeff7_formula ds)
      -- Degree-8 and degree-9 closed forms come from the degree extension files.
      have h8 : (aCoeffs11 ds).c8 =
          ((sigmaQ ds 1) ^ 8) / 10321920
          + ((sigmaQ ds 1) ^ 6 * sigmaQ ds 2) / 1105920
          + ((sigmaQ ds 1) ^ 4 * (sigmaQ ds 2) ^ 2) / 442368
          - ((sigmaQ ds 1) ^ 4 * sigmaQ ds 4) / 1105920
          + ((sigmaQ ds 1) ^ 2 * (sigmaQ ds 2) ^ 3) / 663552
          - ((sigmaQ ds 1) ^ 2 * sigmaQ ds 2 * sigmaQ ds 4) / 552960
          + ((sigmaQ ds 1) ^ 2 * sigmaQ ds 6) / 1451520
          + ((sigmaQ ds 2) ^ 4) / 7962624
          - ((sigmaQ ds 2) ^ 2 * sigmaQ ds 4) / 3317760
          + (sigmaQ ds 2 * sigmaQ ds 6) / 4354560
          + ((sigmaQ ds 4) ^ 2) / 16588800
          - (sigmaQ ds 8) / 9676800 := by
        calc
          (aCoeffs11 ds).c8 = (aCoeffs10 ds).c8 := aCoeffs11_c8_eq ds
          _ = (aCoeffs9 ds).c8 := aCoeffs10_c8_eq ds
          _ = _ := by simpa using (coeff8_formula ds)
      have h9 : (aCoeffs11 ds).c9 =
          ((sigmaQ ds 1) ^ 9) / 185794560
          + ((sigmaQ ds 1) ^ 7 * sigmaQ ds 2) / 15482880
          + ((sigmaQ ds 1) ^ 5 * (sigmaQ ds 2) ^ 2) / 4423680
          - ((sigmaQ ds 1) ^ 5 * sigmaQ ds 4) / 11059200
          + ((sigmaQ ds 1) ^ 3 * (sigmaQ ds 2) ^ 3) / 3981312
          - ((sigmaQ ds 1) ^ 3 * sigmaQ ds 2 * sigmaQ ds 4) / 3317760
          + ((sigmaQ ds 1) ^ 3 * sigmaQ ds 6) / 8709120
          + (sigmaQ ds 1 * (sigmaQ ds 2) ^ 4) / 15925248
          - (sigmaQ ds 1 * (sigmaQ ds 2) ^ 2 * sigmaQ ds 4) / 6635520
          + (sigmaQ ds 1 * sigmaQ ds 2 * sigmaQ ds 6) / 8709120
          + (sigmaQ ds 1 * (sigmaQ ds 4) ^ 2) / 33177600
          - (sigmaQ ds 1 * sigmaQ ds 8) / 19353600 := by
        calc
          (aCoeffs11 ds).c9 = (aCoeffs10 ds).c9 := aCoeffs11_c9_eq ds
          _ = _ := by simpa using (coeff9_formula ds)
      simp [aCoeffs11, mulFactor11, factorC1, factorC2, factorC3, factorC4, factorC5, factorC6, factorC7, factorC8,
        factorC9, factorC10, sigmaQ, ih, h1, h2, h3, h4, h5, h6, h7, h8, h9, aCoeffs11_c0]
      ring

-- ============================================================
-- Tₙ values (from coefficients): Tₙ = n! * [tⁿ]A(t) (n ≤ 10)
-- ============================================================

def TnFromGenUpTo10 (gens : List Nat) : Nat → ℚ
  | 0 => 1
  | 1 => (aCoeffs11 gens).c1
  | 2 => 2 * (aCoeffs11 gens).c2
  | 3 => 6 * (aCoeffs11 gens).c3
  | 4 => 24 * (aCoeffs11 gens).c4
  | 5 => 120 * (aCoeffs11 gens).c5
  | 6 => 720 * (aCoeffs11 gens).c6
  | 7 => 5040 * (aCoeffs11 gens).c7
  | 8 => 40320 * (aCoeffs11 gens).c8
  | 9 => 362880 * (aCoeffs11 gens).c9
  | 10 => 3628800 * (aCoeffs11 gens).c10
  | _ => 0

theorem T10_formula (gens : List Nat) :
    TnFromGenUpTo10 gens 10 =
      (99 * (sigmaQ gens 1) ^ 10
        + 1485 * (sigmaQ gens 1) ^ 8 * sigmaQ gens 2
        + 6930 * (sigmaQ gens 1) ^ 6 * (sigmaQ gens 2) ^ 2
        - 2772 * (sigmaQ gens 1) ^ 6 * sigmaQ gens 4
        + 11550 * (sigmaQ gens 1) ^ 4 * (sigmaQ gens 2) ^ 3
        - 13860 * (sigmaQ gens 1) ^ 4 * sigmaQ gens 2 * sigmaQ gens 4
        + 5280 * (sigmaQ gens 1) ^ 4 * sigmaQ gens 6
        + 5775 * (sigmaQ gens 1) ^ 2 * (sigmaQ gens 2) ^ 4
        - 13860 * (sigmaQ gens 1) ^ 2 * (sigmaQ gens 2) ^ 2 * sigmaQ gens 4
        + 10560 * (sigmaQ gens 1) ^ 2 * sigmaQ gens 2 * sigmaQ gens 6
        + 2772 * (sigmaQ gens 1) ^ 2 * (sigmaQ gens 4) ^ 2
        - 4752 * (sigmaQ gens 1) ^ 2 * sigmaQ gens 8
        + 768 * sigmaQ gens 10
        + 385 * (sigmaQ gens 2) ^ 5
        - 1540 * (sigmaQ gens 2) ^ 3 * sigmaQ gens 4
        + 1760 * (sigmaQ gens 2) ^ 2 * sigmaQ gens 6
        + 924 * sigmaQ gens 2 * (sigmaQ gens 4) ^ 2
        - 1584 * sigmaQ gens 2 * sigmaQ gens 8
        - 704 * sigmaQ gens 4 * sigmaQ gens 6) / 101376 := by
  simp [TnFromGenUpTo10, coeff10_formula]
  ring

theorem T10_universal_for_ufrf_and_monster :
    TnFromGenUpTo10 ufrfGenerators 10 =
        (99 * (sigmaQ ufrfGenerators 1) ^ 10
          + 1485 * (sigmaQ ufrfGenerators 1) ^ 8 * sigmaQ ufrfGenerators 2
          + 6930 * (sigmaQ ufrfGenerators 1) ^ 6 * (sigmaQ ufrfGenerators 2) ^ 2
          - 2772 * (sigmaQ ufrfGenerators 1) ^ 6 * sigmaQ ufrfGenerators 4
          + 11550 * (sigmaQ ufrfGenerators 1) ^ 4 * (sigmaQ ufrfGenerators 2) ^ 3
          - 13860 * (sigmaQ ufrfGenerators 1) ^ 4 * sigmaQ ufrfGenerators 2 * sigmaQ ufrfGenerators 4
          + 5280 * (sigmaQ ufrfGenerators 1) ^ 4 * sigmaQ ufrfGenerators 6
          + 5775 * (sigmaQ ufrfGenerators 1) ^ 2 * (sigmaQ ufrfGenerators 2) ^ 4
          - 13860 * (sigmaQ ufrfGenerators 1) ^ 2 * (sigmaQ ufrfGenerators 2) ^ 2 * sigmaQ ufrfGenerators 4
          + 10560 * (sigmaQ ufrfGenerators 1) ^ 2 * sigmaQ ufrfGenerators 2 * sigmaQ ufrfGenerators 6
          + 2772 * (sigmaQ ufrfGenerators 1) ^ 2 * (sigmaQ ufrfGenerators 4) ^ 2
          - 4752 * (sigmaQ ufrfGenerators 1) ^ 2 * sigmaQ ufrfGenerators 8
          + 768 * sigmaQ ufrfGenerators 10
          + 385 * (sigmaQ ufrfGenerators 2) ^ 5
          - 1540 * (sigmaQ ufrfGenerators 2) ^ 3 * sigmaQ ufrfGenerators 4
          + 1760 * (sigmaQ ufrfGenerators 2) ^ 2 * sigmaQ ufrfGenerators 6
          + 924 * sigmaQ ufrfGenerators 2 * (sigmaQ ufrfGenerators 4) ^ 2
          - 1584 * sigmaQ ufrfGenerators 2 * sigmaQ ufrfGenerators 8
          - 704 * sigmaQ ufrfGenerators 4 * sigmaQ ufrfGenerators 6) / 101376
      ∧
    TnFromGenUpTo10 monsterGenerators 10 =
        (99 * (sigmaQ monsterGenerators 1) ^ 10
          + 1485 * (sigmaQ monsterGenerators 1) ^ 8 * sigmaQ monsterGenerators 2
          + 6930 * (sigmaQ monsterGenerators 1) ^ 6 * (sigmaQ monsterGenerators 2) ^ 2
          - 2772 * (sigmaQ monsterGenerators 1) ^ 6 * sigmaQ monsterGenerators 4
          + 11550 * (sigmaQ monsterGenerators 1) ^ 4 * (sigmaQ monsterGenerators 2) ^ 3
          - 13860 * (sigmaQ monsterGenerators 1) ^ 4 * sigmaQ monsterGenerators 2 * sigmaQ monsterGenerators 4
          + 5280 * (sigmaQ monsterGenerators 1) ^ 4 * sigmaQ monsterGenerators 6
          + 5775 * (sigmaQ monsterGenerators 1) ^ 2 * (sigmaQ monsterGenerators 2) ^ 4
          - 13860 * (sigmaQ monsterGenerators 1) ^ 2 * (sigmaQ monsterGenerators 2) ^ 2 * sigmaQ monsterGenerators 4
          + 10560 * (sigmaQ monsterGenerators 1) ^ 2 * sigmaQ monsterGenerators 2 * sigmaQ monsterGenerators 6
          + 2772 * (sigmaQ monsterGenerators 1) ^ 2 * (sigmaQ monsterGenerators 4) ^ 2
          - 4752 * (sigmaQ monsterGenerators 1) ^ 2 * sigmaQ monsterGenerators 8
          + 768 * sigmaQ monsterGenerators 10
          + 385 * (sigmaQ monsterGenerators 2) ^ 5
          - 1540 * (sigmaQ monsterGenerators 2) ^ 3 * sigmaQ monsterGenerators 4
          + 1760 * (sigmaQ monsterGenerators 2) ^ 2 * sigmaQ monsterGenerators 6
          + 924 * sigmaQ monsterGenerators 2 * (sigmaQ monsterGenerators 4) ^ 2
          - 1584 * sigmaQ monsterGenerators 2 * sigmaQ monsterGenerators 8
          - 704 * sigmaQ monsterGenerators 4 * sigmaQ monsterGenerators 6) / 101376 := by
  constructor <;> simpa using (T10_formula (gens := _))

end TnRecurrenceHigher

