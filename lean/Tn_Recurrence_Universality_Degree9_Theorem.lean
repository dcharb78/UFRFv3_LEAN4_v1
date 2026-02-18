import Tn_Recurrence_Universality_Degree8_Theorem

/-!
# Higher Coefficient Universality (Degree ≤ 9)

This file extends the explicit coefficient closed-form chain one more step:
the coefficient `[t^9]` of

`A(t) = ∏ (exp(d*t) - 1) / (d*t)`.

We keep the same proof-engineering constraints used throughout the repo:
* pure algebra over `ℚ`
* no stubs
* formulas expressed via power sums `σₖ = Σ dᵢ^k`
-/

namespace TnRecurrenceHigher

-- ============================================================
-- Truncated (degree ≤ 9) coefficient recursion for A(t)
-- ============================================================

structure Coeffs10 where
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
deriving Repr

def coeffsInit10 : Coeffs10 :=
  { c0 := 1, c1 := 0, c2 := 0, c3 := 0, c4 := 0, c5 := 0, c6 := 0, c7 := 0, c8 := 0, c9 := 0 }

-- Factor coefficient: `d^9 / (9+1)! = d^9 / 10!`.
def factorC9 (d : Nat) : ℚ := (d ^ 9 : ℚ) / 3628800

/-- Multiply existing coefficients by the single-generator factor (truncated to degree 9). -/
def mulFactor10 (d : Nat) (c : Coeffs10) : Coeffs10 :=
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
        + factorC9 d * c.c0 }

/-- Degree ≤ 9 coefficients of `A(t)` for a list of generators. -/
def aCoeffs10 : List Nat → Coeffs10
  | [] => coeffsInit10
  | d :: ds => mulFactor10 d (aCoeffs10 ds)

@[simp] theorem aCoeffs10_nil : aCoeffs10 [] = coeffsInit10 := by rfl
@[simp] theorem aCoeffs10_cons (d : Nat) (ds : List Nat) :
    aCoeffs10 (d :: ds) = mulFactor10 d (aCoeffs10 ds) := by rfl

@[simp] theorem aCoeffs10_c0 (gens : List Nat) : (aCoeffs10 gens).c0 = 1 := by
  induction gens with
  | nil => simp [aCoeffs10, coeffsInit10]
  | cons d ds ih =>
      simp [aCoeffs10, mulFactor10, ih]

-- ============================================================
-- Projection: reuse all degree ≤ 8 facts from `aCoeffs9`
-- ============================================================

def toCoeffs9 (c : Coeffs10) : Coeffs9 :=
  { c0 := c.c0
    c1 := c.c1
    c2 := c.c2
    c3 := c.c3
    c4 := c.c4
    c5 := c.c5
    c6 := c.c6
    c7 := c.c7
    c8 := c.c8 }

theorem toCoeffs9_mulFactor10 (d : Nat) (c : Coeffs10) :
    toCoeffs9 (mulFactor10 d c) = mulFactor9 d (toCoeffs9 c) := by
  rfl

theorem toCoeffs9_aCoeffs10 (gens : List Nat) :
    toCoeffs9 (aCoeffs10 gens) = aCoeffs9 gens := by
  induction gens with
  | nil =>
      simp [aCoeffs10, aCoeffs9, coeffsInit10, coeffsInit9, toCoeffs9]
  | cons d ds ih =>
      simpa [aCoeffs10, aCoeffs9, toCoeffs9_mulFactor10] using congrArg (mulFactor9 d) ih

theorem aCoeffs10_c1_eq (gens : List Nat) : (aCoeffs10 gens).c1 = (aCoeffs9 gens).c1 := by
  have h := congrArg Coeffs9.c1 (toCoeffs9_aCoeffs10 gens)
  simpa [toCoeffs9] using h

theorem aCoeffs10_c2_eq (gens : List Nat) : (aCoeffs10 gens).c2 = (aCoeffs9 gens).c2 := by
  have h := congrArg Coeffs9.c2 (toCoeffs9_aCoeffs10 gens)
  simpa [toCoeffs9] using h

theorem aCoeffs10_c3_eq (gens : List Nat) : (aCoeffs10 gens).c3 = (aCoeffs9 gens).c3 := by
  have h := congrArg Coeffs9.c3 (toCoeffs9_aCoeffs10 gens)
  simpa [toCoeffs9] using h

theorem aCoeffs10_c4_eq (gens : List Nat) : (aCoeffs10 gens).c4 = (aCoeffs9 gens).c4 := by
  have h := congrArg Coeffs9.c4 (toCoeffs9_aCoeffs10 gens)
  simpa [toCoeffs9] using h

theorem aCoeffs10_c5_eq (gens : List Nat) : (aCoeffs10 gens).c5 = (aCoeffs9 gens).c5 := by
  have h := congrArg Coeffs9.c5 (toCoeffs9_aCoeffs10 gens)
  simpa [toCoeffs9] using h

theorem aCoeffs10_c6_eq (gens : List Nat) : (aCoeffs10 gens).c6 = (aCoeffs9 gens).c6 := by
  have h := congrArg Coeffs9.c6 (toCoeffs9_aCoeffs10 gens)
  simpa [toCoeffs9] using h

theorem aCoeffs10_c7_eq (gens : List Nat) : (aCoeffs10 gens).c7 = (aCoeffs9 gens).c7 := by
  have h := congrArg Coeffs9.c7 (toCoeffs9_aCoeffs10 gens)
  simpa [toCoeffs9] using h

theorem aCoeffs10_c8_eq (gens : List Nat) : (aCoeffs10 gens).c8 = (aCoeffs9 gens).c8 := by
  have h := congrArg Coeffs9.c8 (toCoeffs9_aCoeffs10 gens)
  simpa [toCoeffs9] using h

-- ============================================================
-- New closed form: coefficient c₉
-- ============================================================

theorem coeff9_formula (gens : List Nat) :
    (aCoeffs10 gens).c9 =
      ((sigmaQ gens 1) ^ 9) / 185794560
      + ((sigmaQ gens 1) ^ 7 * sigmaQ gens 2) / 15482880
      + ((sigmaQ gens 1) ^ 5 * (sigmaQ gens 2) ^ 2) / 4423680
      - ((sigmaQ gens 1) ^ 5 * sigmaQ gens 4) / 11059200
      + ((sigmaQ gens 1) ^ 3 * (sigmaQ gens 2) ^ 3) / 3981312
      - ((sigmaQ gens 1) ^ 3 * sigmaQ gens 2 * sigmaQ gens 4) / 3317760
      + ((sigmaQ gens 1) ^ 3 * sigmaQ gens 6) / 8709120
      + (sigmaQ gens 1 * (sigmaQ gens 2) ^ 4) / 15925248
      - (sigmaQ gens 1 * (sigmaQ gens 2) ^ 2 * sigmaQ gens 4) / 6635520
      + (sigmaQ gens 1 * sigmaQ gens 2 * sigmaQ gens 6) / 8709120
      + (sigmaQ gens 1 * (sigmaQ gens 4) ^ 2) / 33177600
      - (sigmaQ gens 1 * sigmaQ gens 8) / 19353600 := by
  induction gens with
  | nil =>
      simp [aCoeffs10, coeffsInit10, sigmaQ]
  | cons d ds ih =>
      -- Closed forms for degree ≤ 7 come from the previous universality file (via `aCoeffs9` → `aCoeffs`).
      have h1 : (aCoeffs10 ds).c1 = sigmaQ ds 1 / 2 := by
        calc
          (aCoeffs10 ds).c1 = (aCoeffs9 ds).c1 := aCoeffs10_c1_eq ds
          _ = (aCoeffs ds).c1 := aCoeffs9_c1_eq ds
          _ = sigmaQ ds 1 / 2 := by simpa using (coeff1_formula ds)
      have h2 : (aCoeffs10 ds).c2 = (3 * (sigmaQ ds 1) ^ 2 + sigmaQ ds 2) / 24 := by
        calc
          (aCoeffs10 ds).c2 = (aCoeffs9 ds).c2 := aCoeffs10_c2_eq ds
          _ = (aCoeffs ds).c2 := aCoeffs9_c2_eq ds
          _ = (3 * (sigmaQ ds 1) ^ 2 + sigmaQ ds 2) / 24 := by simpa using (coeff2_formula ds)
      have h3 : (aCoeffs10 ds).c3 = sigmaQ ds 1 * ((sigmaQ ds 1) ^ 2 + sigmaQ ds 2) / 48 := by
        calc
          (aCoeffs10 ds).c3 = (aCoeffs9 ds).c3 := aCoeffs10_c3_eq ds
          _ = (aCoeffs ds).c3 := aCoeffs9_c3_eq ds
          _ = sigmaQ ds 1 * ((sigmaQ ds 1) ^ 2 + sigmaQ ds 2) / 48 := by simpa using (coeff3_formula ds)
      have h4 : (aCoeffs10 ds).c4 =
          (15 * (sigmaQ ds 1) ^ 4
            + 30 * (sigmaQ ds 1) ^ 2 * (sigmaQ ds 2)
            + 5 * (sigmaQ ds 2) ^ 2
            - 2 * sigmaQ ds 4) / 5760 := by
        calc
          (aCoeffs10 ds).c4 = (aCoeffs9 ds).c4 := aCoeffs10_c4_eq ds
          _ = (aCoeffs ds).c4 := aCoeffs9_c4_eq ds
          _ =
              (15 * (sigmaQ ds 1) ^ 4
                + 30 * (sigmaQ ds 1) ^ 2 * (sigmaQ ds 2)
                + 5 * (sigmaQ ds 2) ^ 2
                - 2 * sigmaQ ds 4) / 5760 := by simpa using (coeff4_formula ds)
      have h5 : (aCoeffs10 ds).c5 =
          -(sigmaQ ds 4 * sigmaQ ds 1) / 5760
          + ((sigmaQ ds 2) ^ 2 * sigmaQ ds 1) / 2304
          + (sigmaQ ds 2 * (sigmaQ ds 1) ^ 3) / 1152
          + ((sigmaQ ds 1) ^ 5) / 3840 := by
        calc
          (aCoeffs10 ds).c5 = (aCoeffs9 ds).c5 := aCoeffs10_c5_eq ds
          _ = (aCoeffs ds).c5 := aCoeffs9_c5_eq ds
          _ =
              -(sigmaQ ds 4 * sigmaQ ds 1) / 5760
              + ((sigmaQ ds 2) ^ 2 * sigmaQ ds 1) / 2304
              + (sigmaQ ds 2 * (sigmaQ ds 1) ^ 3) / 1152
              + ((sigmaQ ds 1) ^ 5) / 3840 := by simpa using (coeff5_formula ds)
      have h6 : (aCoeffs10 ds).c6 =
          (sigmaQ ds 6) / 181440
          - (sigmaQ ds 4 * sigmaQ ds 2) / 69120
          - (sigmaQ ds 4 * (sigmaQ ds 1) ^ 2) / 23040
          + ((sigmaQ ds 2) ^ 3) / 82944
          + ((sigmaQ ds 2) ^ 2 * (sigmaQ ds 1) ^ 2) / 9216
          + (sigmaQ ds 2 * (sigmaQ ds 1) ^ 4) / 9216
          + ((sigmaQ ds 1) ^ 6) / 46080 := by
        calc
          (aCoeffs10 ds).c6 = (aCoeffs9 ds).c6 := aCoeffs10_c6_eq ds
          _ = (aCoeffs ds).c6 := aCoeffs9_c6_eq ds
          _ =
              (sigmaQ ds 6) / 181440
              - (sigmaQ ds 4 * sigmaQ ds 2) / 69120
              - (sigmaQ ds 4 * (sigmaQ ds 1) ^ 2) / 23040
              + ((sigmaQ ds 2) ^ 3) / 82944
              + ((sigmaQ ds 2) ^ 2 * (sigmaQ ds 1) ^ 2) / 9216
              + (sigmaQ ds 2 * (sigmaQ ds 1) ^ 4) / 9216
              + ((sigmaQ ds 1) ^ 6) / 46080 := by simpa using (coeff6_formula ds)
      have h7 : (aCoeffs10 ds).c7 =
          (sigmaQ ds 6 * sigmaQ ds 1) / 362880
          - (sigmaQ ds 4 * sigmaQ ds 2 * sigmaQ ds 1) / 138240
          - (sigmaQ ds 4 * (sigmaQ ds 1) ^ 3) / 138240
          + ((sigmaQ ds 2) ^ 3 * sigmaQ ds 1) / 165888
          + ((sigmaQ ds 2) ^ 2 * (sigmaQ ds 1) ^ 3) / 55296
          + (sigmaQ ds 2 * (sigmaQ ds 1) ^ 5) / 92160
          + ((sigmaQ ds 1) ^ 7) / 645120 := by
        calc
          (aCoeffs10 ds).c7 = (aCoeffs9 ds).c7 := aCoeffs10_c7_eq ds
          _ = (aCoeffs ds).c7 := aCoeffs9_c7_eq ds
          _ =
              (sigmaQ ds 6 * sigmaQ ds 1) / 362880
              - (sigmaQ ds 4 * sigmaQ ds 2 * sigmaQ ds 1) / 138240
              - (sigmaQ ds 4 * (sigmaQ ds 1) ^ 3) / 138240
              + ((sigmaQ ds 2) ^ 3 * sigmaQ ds 1) / 165888
              + ((sigmaQ ds 2) ^ 2 * (sigmaQ ds 1) ^ 3) / 55296
              + (sigmaQ ds 2 * (sigmaQ ds 1) ^ 5) / 92160
              + ((sigmaQ ds 1) ^ 7) / 645120 := by simpa using (coeff7_formula ds)
      -- Degree-8 closed form comes from the degree-8 extension file.
      have h8 : (aCoeffs10 ds).c8 =
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
          (aCoeffs10 ds).c8 = (aCoeffs9 ds).c8 := aCoeffs10_c8_eq ds
          _ = ((sigmaQ ds 1) ^ 8) / 10321920
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
                - (sigmaQ ds 8) / 9676800 := by simpa using (coeff8_formula ds)
      simp [aCoeffs10, mulFactor10, factorC1, factorC2, factorC3, factorC4, factorC5, factorC6, factorC7, factorC8,
        factorC9, sigmaQ, ih, h1, h2, h3, h4, h5, h6, h7, h8, aCoeffs10_c0]
      ring

-- ============================================================
-- Tₙ values (from coefficients): Tₙ = n! * [tⁿ]A(t) (n ≤ 9)
-- ============================================================

def TnFromGenUpTo9 (gens : List Nat) : Nat → ℚ
  | 0 => 1
  | 1 => (aCoeffs10 gens).c1
  | 2 => 2 * (aCoeffs10 gens).c2
  | 3 => 6 * (aCoeffs10 gens).c3
  | 4 => 24 * (aCoeffs10 gens).c4
  | 5 => 120 * (aCoeffs10 gens).c5
  | 6 => 720 * (aCoeffs10 gens).c6
  | 7 => 5040 * (aCoeffs10 gens).c7
  | 8 => 40320 * (aCoeffs10 gens).c8
  | 9 => 362880 * (aCoeffs10 gens).c9
  | _ => 0

theorem T9_formula (gens : List Nat) :
    TnFromGenUpTo9 gens 9 =
      (15 * (sigmaQ gens 1) ^ 9
        + 180 * (sigmaQ gens 1) ^ 7 * sigmaQ gens 2
        + 630 * (sigmaQ gens 1) ^ 5 * (sigmaQ gens 2) ^ 2
        - 252 * (sigmaQ gens 1) ^ 5 * sigmaQ gens 4
        + 700 * (sigmaQ gens 1) ^ 3 * (sigmaQ gens 2) ^ 3
        - 840 * (sigmaQ gens 1) ^ 3 * sigmaQ gens 2 * sigmaQ gens 4
        + 320 * (sigmaQ gens 1) ^ 3 * sigmaQ gens 6
        + 175 * sigmaQ gens 1 * (sigmaQ gens 2) ^ 4
        - 420 * sigmaQ gens 1 * (sigmaQ gens 2) ^ 2 * sigmaQ gens 4
        + 320 * sigmaQ gens 1 * sigmaQ gens 2 * sigmaQ gens 6
        + 84 * sigmaQ gens 1 * (sigmaQ gens 4) ^ 2
        - 144 * sigmaQ gens 1 * sigmaQ gens 8) / 7680 := by
  simp [TnFromGenUpTo9, coeff9_formula]
  ring

theorem T9_universal_for_ufrf_and_monster :
    TnFromGenUpTo9 ufrfGenerators 9 =
        (15 * (sigmaQ ufrfGenerators 1) ^ 9
          + 180 * (sigmaQ ufrfGenerators 1) ^ 7 * sigmaQ ufrfGenerators 2
          + 630 * (sigmaQ ufrfGenerators 1) ^ 5 * (sigmaQ ufrfGenerators 2) ^ 2
          - 252 * (sigmaQ ufrfGenerators 1) ^ 5 * sigmaQ ufrfGenerators 4
          + 700 * (sigmaQ ufrfGenerators 1) ^ 3 * (sigmaQ ufrfGenerators 2) ^ 3
          - 840 * (sigmaQ ufrfGenerators 1) ^ 3 * sigmaQ ufrfGenerators 2 * sigmaQ ufrfGenerators 4
          + 320 * (sigmaQ ufrfGenerators 1) ^ 3 * sigmaQ ufrfGenerators 6
          + 175 * sigmaQ ufrfGenerators 1 * (sigmaQ ufrfGenerators 2) ^ 4
          - 420 * sigmaQ ufrfGenerators 1 * (sigmaQ ufrfGenerators 2) ^ 2 * sigmaQ ufrfGenerators 4
          + 320 * sigmaQ ufrfGenerators 1 * sigmaQ ufrfGenerators 2 * sigmaQ ufrfGenerators 6
          + 84 * sigmaQ ufrfGenerators 1 * (sigmaQ ufrfGenerators 4) ^ 2
          - 144 * sigmaQ ufrfGenerators 1 * sigmaQ ufrfGenerators 8) / 7680
      ∧
    TnFromGenUpTo9 monsterGenerators 9 =
        (15 * (sigmaQ monsterGenerators 1) ^ 9
          + 180 * (sigmaQ monsterGenerators 1) ^ 7 * sigmaQ monsterGenerators 2
          + 630 * (sigmaQ monsterGenerators 1) ^ 5 * (sigmaQ monsterGenerators 2) ^ 2
          - 252 * (sigmaQ monsterGenerators 1) ^ 5 * sigmaQ monsterGenerators 4
          + 700 * (sigmaQ monsterGenerators 1) ^ 3 * (sigmaQ monsterGenerators 2) ^ 3
          - 840 * (sigmaQ monsterGenerators 1) ^ 3 * sigmaQ monsterGenerators 2 * sigmaQ monsterGenerators 4
          + 320 * (sigmaQ monsterGenerators 1) ^ 3 * sigmaQ monsterGenerators 6
          + 175 * sigmaQ monsterGenerators 1 * (sigmaQ monsterGenerators 2) ^ 4
          - 420 * sigmaQ monsterGenerators 1 * (sigmaQ monsterGenerators 2) ^ 2 * sigmaQ monsterGenerators 4
          + 320 * sigmaQ monsterGenerators 1 * sigmaQ monsterGenerators 2 * sigmaQ monsterGenerators 6
          + 84 * sigmaQ monsterGenerators 1 * (sigmaQ monsterGenerators 4) ^ 2
          - 144 * sigmaQ monsterGenerators 1 * sigmaQ monsterGenerators 8) / 7680 := by
  constructor <;> simpa using (T9_formula (gens := _))

end TnRecurrenceHigher

