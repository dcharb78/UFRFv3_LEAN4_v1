import Mathlib

/-!
# Coefficient Denominator Emergence (Degrees ≤ 10)

This repo proves universal closed forms for the coefficients `cₙ = [tⁿ]A(t)` of

`A(t) = ∏ (exp(d*t) - 1) / (d*t)`

through degree 10 (see:
`lean/Tn_Recurrence_Universality_Theorem.lean` and
`lean/Tn_Recurrence_Universality_Higher_Theorem.lean`, and
`lean/Tn_Recurrence_Universality_Degree8_Theorem.lean`, and
`lean/Tn_Recurrence_Universality_Degree9_Theorem.lean`, and
`lean/Tn_Recurrence_Universality_Degree10_Theorem.lean`).

Each closed form is a `ℚ`-linear combination of power-sum monomials with explicit rational
coefficients. A simple, exact way to summarize the “denominator emergence” idea is:

*Take the LCM of the (finite) set of denominators that appear in the explicit formula at degree `n`.*

This file computes those LCMs for `n ≤ 10` and records a few small “first appearance” facts
for odd primes in the odd part.

Scope:
- fully discrete (`Nat` arithmetic + `native_decide`)
- no analytic claims about infinite products or convergence
- no claims about degrees beyond 10
-/

namespace CoefficientDenominatorEmergence

-- A tiny helper: LCM over a list of naturals.
def lcmList : List Nat → Nat
  | [] => 1
  | n :: ns => Nat.lcm n (lcmList ns)

-- Low-degree denominators from the explicit coefficient formulas:
-- c1: /2, c2: /24, c3: /48, c4: /5760.
def D1 : Nat := 2
def D2 : Nat := 24
def D3 : Nat := 48
def D4 : Nat := 5760

-- Degree 5 denominator LCM from the explicit c5 formula:
--   /5760, /2304, /1152, /3840.
def D5 : Nat := lcmList [5760, 2304, 1152, 3840]

-- Degree 6 denominator LCM from the explicit c6 formula:
--   /181440, /69120, /23040, /82944, /9216, /9216, /46080.
def D6 : Nat := lcmList [181440, 69120, 23040, 82944, 9216, 9216, 46080]

-- Degree 7 denominator LCM from the explicit c7 formula:
--   /362880, /138240, /138240, /165888, /55296, /92160, /645120.
def D7 : Nat := lcmList [362880, 138240, 138240, 165888, 55296, 92160, 645120]

-- Degree 8 denominator LCM from the explicit c8 formula:
--   /10321920, /1105920, /442368, /1105920, /663552, /552960, /1451520,
--   /7962624, /3317760, /4354560, /16588800, /9676800.
def D8 : Nat :=
  lcmList [10321920, 1105920, 442368, 1105920, 663552, 552960, 1451520, 7962624,
    3317760, 4354560, 16588800, 9676800]

-- Degree 9 denominator LCM from the explicit c9 formula:
--   /185794560, /15482880, /4423680, /11059200, /3981312, /3317760, /8709120,
--   /15925248, /6635520, /8709120, /33177600, /19353600.
def D9 : Nat :=
  lcmList [185794560, 15482880, 4423680, 11059200, 3981312, 3317760, 8709120, 15925248,
    6635520, 8709120, 33177600, 19353600]

-- Degree 10 denominator LCM from the explicit c10 formula:
--   /3715891200, /247726080, /53084160, /132710400, /31850496, /26542080, /69672960,
--   /63700992, /26542080, /34836480, /132710400, /77414400, /479001600, /955514880,
--   /238878720, /209018880, /398131200, /232243200, /522547200.
def D10 : Nat :=
  lcmList [3715891200, 247726080, 53084160, 132710400, 31850496, 26542080, 69672960, 63700992,
    26542080, 34836480, 132710400, 77414400, 479001600, 955514880, 238878720, 209018880, 398131200,
    232243200, 522547200]

-- Exact computed values (matches the repo note `TN_DENOMINATOR_EMERGENCE_TEST.md` for n ≤ 7).
theorem D5_value : D5 = 11520 := by native_decide
theorem D6_value : D6 = 2903040 := by native_decide
theorem D7_value : D7 = 5806080 := by native_decide
theorem D8_value : D8 = 1393459200 := by native_decide
theorem D9_value : D9 = 2786918400 := by native_decide
theorem D10_value : D10 = 367873228800 := by native_decide

-- Factorizations for the first few degrees (2-adic "geometric" part times odd part).
theorem D1_factor : D1 = 2 ^ 1 := by native_decide
theorem D2_factor : D2 = 2 ^ 3 * 3 := by native_decide
theorem D3_factor : D3 = 2 ^ 4 * 3 := by native_decide
theorem D4_factor : D4 = 2 ^ 7 * 3 ^ 2 * 5 := by native_decide

-- Factorizations (2-adic part times odd part).
theorem D5_factor : D5 = 2 ^ 8 * 3 ^ 2 * 5 := by native_decide
theorem D6_factor : D6 = 2 ^ 10 * 3 ^ 4 * 5 * 7 := by native_decide
theorem D7_factor : D7 = 2 ^ 11 * 3 ^ 4 * 5 * 7 := by native_decide
theorem D8_factor : D8 = 2 ^ 15 * 3 ^ 5 * 5 ^ 2 * 7 := by native_decide
theorem D9_factor : D9 = 2 ^ 16 * 3 ^ 5 * 5 ^ 2 * 7 := by native_decide
theorem D10_factor : D10 = 2 ^ 18 * 3 ^ 6 * 5 ^ 2 * 7 * 11 := by native_decide

-- “First appearance” checks for the UFRF odd primes in these denominators.
theorem prime3_first_appears : (3 ∣ D2) ∧ ¬ (3 ∣ D1) := by native_decide
theorem prime5_first_appears : (5 ∣ D4) ∧ ¬ (5 ∣ D3) := by native_decide
theorem prime7_first_appears : (7 ∣ D6) ∧ ¬ (7 ∣ D5) := by native_decide

-- First appearance of the next UFRF odd prime `11` happens at degree 10.
theorem prime11_first_appears : (11 ∣ D10) ∧ ¬ (11 ∣ D9) := by native_decide

-- Up through degree 10, 13 does not divide the universal coefficient denominators.
theorem prime13_not_yet : ¬ (13 ∣ D10) := by native_decide

/--
Pack the degree ≤ 10 denominator emergence facts into one conjunction.

This is used by `context/UFRF_UNIFIED_PROOF.lean` so the canonical spine can import one
stable lemma rather than many individual fields.
-/
abbrev DenominatorEmergenceSummary : Prop :=
    D5 = 11520
    ∧ D6 = 2903040
    ∧ D7 = 5806080
    ∧ D8 = 1393459200
    ∧ D9 = 2786918400
    ∧ D10 = 367873228800
    ∧ (D5 = 2 ^ 8 * 3 ^ 2 * 5)
    ∧ (D6 = 2 ^ 10 * 3 ^ 4 * 5 * 7)
    ∧ (D7 = 2 ^ 11 * 3 ^ 4 * 5 * 7)
    ∧ (D8 = 2 ^ 15 * 3 ^ 5 * 5 ^ 2 * 7)
    ∧ (D9 = 2 ^ 16 * 3 ^ 5 * 5 ^ 2 * 7)
    ∧ (D10 = 2 ^ 18 * 3 ^ 6 * 5 ^ 2 * 7 * 11)
    ∧ ((7 ∣ D6) ∧ ¬ (7 ∣ D5))
    ∧ ((11 ∣ D10) ∧ ¬ (11 ∣ D9))
    ∧ (¬ (13 ∣ D10))

theorem denominator_emergence_summary : DenominatorEmergenceSummary := by
  refine ⟨D5_value, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact D6_value
  · exact D7_value
  · exact D8_value
  · exact D9_value
  · exact D10_value
  · exact D5_factor
  · exact D6_factor
  · exact D7_factor
  · exact D8_factor
  · exact D9_factor
  · exact D10_factor
  · exact prime7_first_appears
  · exact prime11_first_appears
  · exact prime13_not_yet

end CoefficientDenominatorEmergence
