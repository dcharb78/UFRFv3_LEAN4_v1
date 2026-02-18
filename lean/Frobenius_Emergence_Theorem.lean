/-
# Frobenius Emergence Theorem (Computational)

## Purpose

The `Monster` triple `[47, 59, 71]` can be obtained from specific UFRF pairs
using the (two-generator) Frobenius-number expression:

`F(a,b) = a*b - a - b`.

This file only claims the concrete equalities for the specific pairs used in
the UFRF narrative; it does **not** prove the general Frobenius theorem
(`F(a,b) = ab-a-b` when `gcd a b = 1`) in full generality.
-/

import Mathlib

namespace FrobeniusEmergence

/-- A convenient arithmetic expression often used for the two-generator Frobenius number. -/
def frobeniusNumber (a b : ℕ) : ℕ :=
  a * b - a - b

/-- The UFRF Level-1 generator list used across this repo. -/
def ufrfGenerators : List ℕ := [3, 5, 7, 11, 13]

/--
Enumerate all two-generator Frobenius expressions `F(a,b) = ab-a-b` for pairs `a < b` drawn
from `xs`, in list order.

This is intentionally a concrete computation helper (not a general Frobenius theorem about
semigroups).
-/
def frobeniusAll (xs : List ℕ) : List ℕ :=
  List.flatMap
    (fun a => List.flatMap (fun b => if a < b then [frobeniusNumber a b] else []) xs)
    xs

theorem frobenius_5_13 : frobeniusNumber 5 13 = 47 := by
  native_decide

theorem frobenius_7_11 : frobeniusNumber 7 11 = 59 := by
  native_decide

theorem frobenius_7_13 : frobeniusNumber 7 13 = 71 := by
  native_decide

theorem frobeniusAll_ufrfGenerators :
  frobeniusAll ufrfGenerators = [7, 11, 19, 23, 23, 39, 47, 59, 71, 119] := by
  native_decide

/-- The unique Level-2 list obtained by deleting duplicates from `frobeniusAll ufrfGenerators`. -/
def L2Full : List ℕ :=
  (frobeniusAll ufrfGenerators).eraseDups

theorem L2Full_eq :
  L2Full = [7, 11, 19, 23, 39, 47, 59, 71, 119] := by
  native_decide

theorem frobeniusAll_ufrfGenerators_length :
  (frobeniusAll ufrfGenerators).length = 10 := by
  native_decide

theorem L2Full_length : L2Full.length = 9 := by
  native_decide

theorem frobenius_emergence_complete :
    frobeniusNumber 5 13 = 47
  ∧ frobeniusNumber 7 11 = 59
  ∧ frobeniusNumber 7 13 = 71 := by
  exact ⟨frobenius_5_13, frobenius_7_11, frobenius_7_13⟩

/-- The Monster generators used throughout the repo. -/
def monsterGenerators : List ℕ := [47, 59, 71]

theorem monsterGenerators_eq_frobenius :
  monsterGenerators = [frobeniusNumber 5 13, frobeniusNumber 7 11, frobeniusNumber 7 13] := by
  native_decide

theorem monsterGenerators_subset_L2Full : monsterGenerators ⊆ L2Full := by
  native_decide

theorem monster_mod13_positions :
    (47 % 13 = 8)
  ∧ (59 % 13 = 7)
  ∧ (71 % 13 = 6) := by
  native_decide

end FrobeniusEmergence
