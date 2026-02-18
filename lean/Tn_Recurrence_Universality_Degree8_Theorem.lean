import Tn_Recurrence_Universality_Higher_Theorem

/-!
# Higher Coefficient Universality (Degree ≤ 8)

This file extends `Tn_Recurrence_Universality_Higher_Theorem` by one more term:
the coefficient `[t^8]` of

`A(t) = ∏ (exp(d*t) - 1) / (d*t)`.

The engineering rule stays the same:
* no placeholder stubs
* minimal axioms (pure algebra over `ℚ`)
* closed form in terms of power sums `σₖ = Σ dᵢ^k`

We *reuse* all degree ≤ 7 facts from the previous file via a projection lemma,
and prove only the new degree-8 closed form.
-/

namespace TnRecurrenceHigher

-- ============================================================
-- Truncated (degree ≤ 8) coefficient recursion for A(t)
-- ============================================================

structure Coeffs9 where
  c0 : ℚ
  c1 : ℚ
  c2 : ℚ
  c3 : ℚ
  c4 : ℚ
  c5 : ℚ
  c6 : ℚ
  c7 : ℚ
  c8 : ℚ
deriving Repr

def coeffsInit9 : Coeffs9 :=
  { c0 := 1, c1 := 0, c2 := 0, c3 := 0, c4 := 0, c5 := 0, c6 := 0, c7 := 0, c8 := 0 }

-- Factor coefficient: `d^8 / (8+1)! = d^8 / 9!`.
def factorC8 (d : Nat) : ℚ := (d ^ 8 : ℚ) / 362880

/-- Multiply existing coefficients by the single-generator factor (truncated to degree 8). -/
def mulFactor9 (d : Nat) (c : Coeffs9) : Coeffs9 :=
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
        + factorC5 d * c.c3 + factorC6 d * c.c2 + factorC7 d * c.c1 + factorC8 d * c.c0 }

/-- Degree ≤ 8 coefficients of `A(t)` for a list of generators. -/
def aCoeffs9 : List Nat → Coeffs9
  | [] => coeffsInit9
  | d :: ds => mulFactor9 d (aCoeffs9 ds)

@[simp] theorem aCoeffs9_nil : aCoeffs9 [] = coeffsInit9 := by rfl
@[simp] theorem aCoeffs9_cons (d : Nat) (ds : List Nat) :
    aCoeffs9 (d :: ds) = mulFactor9 d (aCoeffs9 ds) := by rfl

@[simp] theorem aCoeffs9_c0 (gens : List Nat) : (aCoeffs9 gens).c0 = 1 := by
  induction gens with
  | nil => simp [aCoeffs9, coeffsInit9]
  | cons d ds ih =>
      simp [aCoeffs9, mulFactor9, ih]

-- ============================================================
-- Projection: reuse all degree ≤ 7 facts from `aCoeffs` (Coeff8)
-- ============================================================

def toCoeffs8 (c : Coeffs9) : Coeffs8 :=
  { c0 := c.c0
    c1 := c.c1
    c2 := c.c2
    c3 := c.c3
    c4 := c.c4
    c5 := c.c5
    c6 := c.c6
    c7 := c.c7 }

theorem toCoeffs8_mulFactor9 (d : Nat) (c : Coeffs9) :
    toCoeffs8 (mulFactor9 d c) = mulFactor d (toCoeffs8 c) := by
  rfl

theorem toCoeffs8_aCoeffs9 (gens : List Nat) :
    toCoeffs8 (aCoeffs9 gens) = aCoeffs gens := by
  induction gens with
  | nil =>
      simp [aCoeffs9, aCoeffs, coeffsInit9, coeffsInit, toCoeffs8]
  | cons d ds ih =>
      -- Reduce the degree-≤7 projection to the known `mulFactor` recursion, then apply IH.
      -- (We make the congruence step explicit so simp doesn't get stuck on record equality.)
      simpa [aCoeffs9, aCoeffs, toCoeffs8_mulFactor9] using congrArg (mulFactor d) ih

theorem aCoeffs9_c1_eq (gens : List Nat) : (aCoeffs9 gens).c1 = (aCoeffs gens).c1 := by
  have h := congrArg Coeffs8.c1 (toCoeffs8_aCoeffs9 gens)
  simpa [toCoeffs8] using h

theorem aCoeffs9_c2_eq (gens : List Nat) : (aCoeffs9 gens).c2 = (aCoeffs gens).c2 := by
  have h := congrArg Coeffs8.c2 (toCoeffs8_aCoeffs9 gens)
  simpa [toCoeffs8] using h

theorem aCoeffs9_c3_eq (gens : List Nat) : (aCoeffs9 gens).c3 = (aCoeffs gens).c3 := by
  have h := congrArg Coeffs8.c3 (toCoeffs8_aCoeffs9 gens)
  simpa [toCoeffs8] using h

theorem aCoeffs9_c4_eq (gens : List Nat) : (aCoeffs9 gens).c4 = (aCoeffs gens).c4 := by
  have h := congrArg Coeffs8.c4 (toCoeffs8_aCoeffs9 gens)
  simpa [toCoeffs8] using h

theorem aCoeffs9_c5_eq (gens : List Nat) : (aCoeffs9 gens).c5 = (aCoeffs gens).c5 := by
  have h := congrArg Coeffs8.c5 (toCoeffs8_aCoeffs9 gens)
  simpa [toCoeffs8] using h

theorem aCoeffs9_c6_eq (gens : List Nat) : (aCoeffs9 gens).c6 = (aCoeffs gens).c6 := by
  have h := congrArg Coeffs8.c6 (toCoeffs8_aCoeffs9 gens)
  simpa [toCoeffs8] using h

theorem aCoeffs9_c7_eq (gens : List Nat) : (aCoeffs9 gens).c7 = (aCoeffs gens).c7 := by
  have h := congrArg Coeffs8.c7 (toCoeffs8_aCoeffs9 gens)
  simpa [toCoeffs8] using h

-- ============================================================
-- New closed form: coefficient c₈
-- ============================================================

/--
`c₈` closed form (universal, coefficient-level).

This is the degree-8 extension of the repo's explicit universality chain:
it expresses `[t^8]A(t)` purely in terms of power sums `σₖ`.
-/
theorem coeff8_formula (gens : List Nat) :
    (aCoeffs9 gens).c8 =
      ((sigmaQ gens 1) ^ 8) / 10321920
      + ((sigmaQ gens 1) ^ 6 * sigmaQ gens 2) / 1105920
      + ((sigmaQ gens 1) ^ 4 * (sigmaQ gens 2) ^ 2) / 442368
      - ((sigmaQ gens 1) ^ 4 * sigmaQ gens 4) / 1105920
      + ((sigmaQ gens 1) ^ 2 * (sigmaQ gens 2) ^ 3) / 663552
      - ((sigmaQ gens 1) ^ 2 * sigmaQ gens 2 * sigmaQ gens 4) / 552960
      + ((sigmaQ gens 1) ^ 2 * sigmaQ gens 6) / 1451520
      + ((sigmaQ gens 2) ^ 4) / 7962624
      - ((sigmaQ gens 2) ^ 2 * sigmaQ gens 4) / 3317760
      + (sigmaQ gens 2 * sigmaQ gens 6) / 4354560
      + ((sigmaQ gens 4) ^ 2) / 16588800
      - (sigmaQ gens 8) / 9676800 := by
  induction gens with
  | nil =>
      simp [aCoeffs9, coeffsInit9, sigmaQ]
  | cons d ds ih =>
      -- Reuse degree ≤ 7 coefficient formulas (as equalities for `aCoeffs9 ds`).
      have h1 : (aCoeffs9 ds).c1 = sigmaQ ds 1 / 2 := by
        calc
          (aCoeffs9 ds).c1 = (aCoeffs ds).c1 := aCoeffs9_c1_eq ds
          _ = sigmaQ ds 1 / 2 := by simpa using (coeff1_formula ds)
      have h2 : (aCoeffs9 ds).c2 = (3 * (sigmaQ ds 1) ^ 2 + sigmaQ ds 2) / 24 := by
        calc
          (aCoeffs9 ds).c2 = (aCoeffs ds).c2 := aCoeffs9_c2_eq ds
          _ = (3 * (sigmaQ ds 1) ^ 2 + sigmaQ ds 2) / 24 := by
                simpa using (coeff2_formula ds)
      have h3 : (aCoeffs9 ds).c3 = sigmaQ ds 1 * ((sigmaQ ds 1) ^ 2 + sigmaQ ds 2) / 48 := by
        calc
          (aCoeffs9 ds).c3 = (aCoeffs ds).c3 := aCoeffs9_c3_eq ds
          _ = sigmaQ ds 1 * ((sigmaQ ds 1) ^ 2 + sigmaQ ds 2) / 48 := by
                simpa using (coeff3_formula ds)
      have h4 : (aCoeffs9 ds).c4 =
          (15 * (sigmaQ ds 1) ^ 4
            + 30 * (sigmaQ ds 1) ^ 2 * (sigmaQ ds 2)
            + 5 * (sigmaQ ds 2) ^ 2
            - 2 * sigmaQ ds 4) / 5760 := by
        calc
          (aCoeffs9 ds).c4 = (aCoeffs ds).c4 := aCoeffs9_c4_eq ds
          _ =
              (15 * (sigmaQ ds 1) ^ 4
                + 30 * (sigmaQ ds 1) ^ 2 * (sigmaQ ds 2)
                + 5 * (sigmaQ ds 2) ^ 2
                - 2 * sigmaQ ds 4) / 5760 := by
                  simpa using (coeff4_formula ds)
      have h5 : (aCoeffs9 ds).c5 =
          -(sigmaQ ds 4 * sigmaQ ds 1) / 5760
          + ((sigmaQ ds 2) ^ 2 * sigmaQ ds 1) / 2304
          + (sigmaQ ds 2 * (sigmaQ ds 1) ^ 3) / 1152
          + ((sigmaQ ds 1) ^ 5) / 3840 := by
        calc
          (aCoeffs9 ds).c5 = (aCoeffs ds).c5 := aCoeffs9_c5_eq ds
          _ =
              -(sigmaQ ds 4 * sigmaQ ds 1) / 5760
              + ((sigmaQ ds 2) ^ 2 * sigmaQ ds 1) / 2304
              + (sigmaQ ds 2 * (sigmaQ ds 1) ^ 3) / 1152
              + ((sigmaQ ds 1) ^ 5) / 3840 := by
                  simpa using (coeff5_formula ds)
      have h6 : (aCoeffs9 ds).c6 =
          (sigmaQ ds 6) / 181440
          - (sigmaQ ds 4 * sigmaQ ds 2) / 69120
          - (sigmaQ ds 4 * (sigmaQ ds 1) ^ 2) / 23040
          + ((sigmaQ ds 2) ^ 3) / 82944
          + ((sigmaQ ds 2) ^ 2 * (sigmaQ ds 1) ^ 2) / 9216
          + (sigmaQ ds 2 * (sigmaQ ds 1) ^ 4) / 9216
          + ((sigmaQ ds 1) ^ 6) / 46080 := by
        calc
          (aCoeffs9 ds).c6 = (aCoeffs ds).c6 := aCoeffs9_c6_eq ds
          _ =
              (sigmaQ ds 6) / 181440
              - (sigmaQ ds 4 * sigmaQ ds 2) / 69120
              - (sigmaQ ds 4 * (sigmaQ ds 1) ^ 2) / 23040
              + ((sigmaQ ds 2) ^ 3) / 82944
              + ((sigmaQ ds 2) ^ 2 * (sigmaQ ds 1) ^ 2) / 9216
              + (sigmaQ ds 2 * (sigmaQ ds 1) ^ 4) / 9216
              + ((sigmaQ ds 1) ^ 6) / 46080 := by
                  simpa using (coeff6_formula ds)
      have h7 : (aCoeffs9 ds).c7 =
          (sigmaQ ds 6 * sigmaQ ds 1) / 362880
          - (sigmaQ ds 4 * sigmaQ ds 2 * sigmaQ ds 1) / 138240
          - (sigmaQ ds 4 * (sigmaQ ds 1) ^ 3) / 138240
          + ((sigmaQ ds 2) ^ 3 * sigmaQ ds 1) / 165888
          + ((sigmaQ ds 2) ^ 2 * (sigmaQ ds 1) ^ 3) / 55296
          + (sigmaQ ds 2 * (sigmaQ ds 1) ^ 5) / 92160
          + ((sigmaQ ds 1) ^ 7) / 645120 := by
        calc
          (aCoeffs9 ds).c7 = (aCoeffs ds).c7 := aCoeffs9_c7_eq ds
          _ =
              (sigmaQ ds 6 * sigmaQ ds 1) / 362880
              - (sigmaQ ds 4 * sigmaQ ds 2 * sigmaQ ds 1) / 138240
              - (sigmaQ ds 4 * (sigmaQ ds 1) ^ 3) / 138240
              + ((sigmaQ ds 2) ^ 3 * sigmaQ ds 1) / 165888
              + ((sigmaQ ds 2) ^ 2 * (sigmaQ ds 1) ^ 3) / 55296
              + (sigmaQ ds 2 * (sigmaQ ds 1) ^ 5) / 92160
              + ((sigmaQ ds 1) ^ 7) / 645120 := by
                  simpa using (coeff7_formula ds)
      simp [aCoeffs9, mulFactor9, factorC1, factorC2, factorC3, factorC4, factorC5, factorC6, factorC7,
        factorC8, sigmaQ, ih, h1, h2, h3, h4, h5, h6, h7]
      ring

-- ============================================================
-- Tₙ values (from coefficients): Tₙ = n! * [tⁿ]A(t) (n ≤ 8)
-- ============================================================

def TnFromGenUpTo8 (gens : List Nat) : Nat → ℚ
  | 0 => 1
  | 1 => (aCoeffs9 gens).c1
  | 2 => 2 * (aCoeffs9 gens).c2
  | 3 => 6 * (aCoeffs9 gens).c3
  | 4 => 24 * (aCoeffs9 gens).c4
  | 5 => 120 * (aCoeffs9 gens).c5
  | 6 => 720 * (aCoeffs9 gens).c6
  | 7 => 5040 * (aCoeffs9 gens).c7
  | 8 => 40320 * (aCoeffs9 gens).c8
  | _ => 0

theorem T8_formula (gens : List Nat) :
    TnFromGenUpTo8 gens 8 =
      (135 * (sigmaQ gens 1) ^ 8
        + 1260 * (sigmaQ gens 1) ^ 6 * sigmaQ gens 2
        + 3150 * (sigmaQ gens 1) ^ 4 * (sigmaQ gens 2) ^ 2
        - 1260 * (sigmaQ gens 1) ^ 4 * sigmaQ gens 4
        + 2100 * (sigmaQ gens 1) ^ 2 * (sigmaQ gens 2) ^ 3
        - 2520 * (sigmaQ gens 1) ^ 2 * sigmaQ gens 2 * sigmaQ gens 4
        + 960 * (sigmaQ gens 1) ^ 2 * sigmaQ gens 6
        + 175 * (sigmaQ gens 2) ^ 4
        - 420 * (sigmaQ gens 2) ^ 2 * sigmaQ gens 4
        + 320 * sigmaQ gens 2 * sigmaQ gens 6
        + 84 * (sigmaQ gens 4) ^ 2
        - 144 * sigmaQ gens 8) / 34560 := by
  simp [TnFromGenUpTo8, coeff8_formula]
  ring

-- ------------------------------------------------------------
-- Concrete generator sets (UFRF / Monster), same as in the degree ≤ 7 file
-- ------------------------------------------------------------

theorem T8_universal_for_ufrf_and_monster :
    TnFromGenUpTo8 ufrfGenerators 8 =
        (135 * (sigmaQ ufrfGenerators 1) ^ 8
          + 1260 * (sigmaQ ufrfGenerators 1) ^ 6 * sigmaQ ufrfGenerators 2
          + 3150 * (sigmaQ ufrfGenerators 1) ^ 4 * (sigmaQ ufrfGenerators 2) ^ 2
          - 1260 * (sigmaQ ufrfGenerators 1) ^ 4 * sigmaQ ufrfGenerators 4
          + 2100 * (sigmaQ ufrfGenerators 1) ^ 2 * (sigmaQ ufrfGenerators 2) ^ 3
          - 2520 * (sigmaQ ufrfGenerators 1) ^ 2 * sigmaQ ufrfGenerators 2 * sigmaQ ufrfGenerators 4
          + 960 * (sigmaQ ufrfGenerators 1) ^ 2 * sigmaQ ufrfGenerators 6
          + 175 * (sigmaQ ufrfGenerators 2) ^ 4
          - 420 * (sigmaQ ufrfGenerators 2) ^ 2 * sigmaQ ufrfGenerators 4
          + 320 * sigmaQ ufrfGenerators 2 * sigmaQ ufrfGenerators 6
          + 84 * (sigmaQ ufrfGenerators 4) ^ 2
          - 144 * sigmaQ ufrfGenerators 8) / 34560
      ∧
    TnFromGenUpTo8 monsterGenerators 8 =
        (135 * (sigmaQ monsterGenerators 1) ^ 8
          + 1260 * (sigmaQ monsterGenerators 1) ^ 6 * sigmaQ monsterGenerators 2
          + 3150 * (sigmaQ monsterGenerators 1) ^ 4 * (sigmaQ monsterGenerators 2) ^ 2
          - 1260 * (sigmaQ monsterGenerators 1) ^ 4 * sigmaQ monsterGenerators 4
          + 2100 * (sigmaQ monsterGenerators 1) ^ 2 * (sigmaQ monsterGenerators 2) ^ 3
          - 2520 * (sigmaQ monsterGenerators 1) ^ 2 * sigmaQ monsterGenerators 2 * sigmaQ monsterGenerators 4
          + 960 * (sigmaQ monsterGenerators 1) ^ 2 * sigmaQ monsterGenerators 6
          + 175 * (sigmaQ monsterGenerators 2) ^ 4
          - 420 * (sigmaQ monsterGenerators 2) ^ 2 * sigmaQ monsterGenerators 4
          + 320 * sigmaQ monsterGenerators 2 * sigmaQ monsterGenerators 6
          + 84 * (sigmaQ monsterGenerators 4) ^ 2
          - 144 * sigmaQ monsterGenerators 8) / 34560 := by
  constructor <;> simpa using (T8_formula (gens := _))

end TnRecurrenceHigher
