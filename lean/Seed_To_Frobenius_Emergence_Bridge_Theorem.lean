import Monster_AP12_Filter_Theorem

/-!
# Seed → Frobenius Emergence Bridge (Nonredundancy of `11` and `13`)

In the *semigroup* (additive-closure) lens, the UFRF generators `[3,5,7,11,13]` have a redundant
presentation: the smaller seed `[3,5,7]` already reaches `11` and `13` as nonnegative linear
combinations.

However, the Level-2 **Frobenius emergence** pipeline used throughout this repo does *not* act on
the full semigroup closure. It acts on **explicit generator pairs** `(a,b)` drawn from the chosen
generator list and forms the concrete expression `a*b - a - b`.

This file makes the “why include `11` and `13`?” point precise in the simplest possible discrete
way:

* Using only the seed `[3,5,7]` (or adding just one of `{11,13}`) yields **no** AP(12) triple in
  the resulting Level-2 list.
* Using the full UFRF list `[3,5,7,11,13]` yields the unique AP(12) triple `(47,59,71)`.

No placeholders; proofs are finite computations via `native_decide`.
-/

namespace SeedToFrobeniusBridge

open FrobeniusEmergence
open MonsterAP12Filter

/-- Level-2 list builder for an arbitrary generator list (pairwise Frobenius values, with dups removed). -/
def L2Of (xs : List Nat) : List Nat :=
  (frobeniusAll xs).eraseDups

/-- Apply the AP(12) selection rule to the Level-2 list derived from `xs`. -/
def ap12From (xs : List Nat) : List (Nat × Nat × Nat) :=
  ap12Triples (L2Of xs)

/-- Canonical seed-only generator list. -/
def seed : List Nat := [3, 5, 7]

/-- Seed extended with `11` only. -/
def seed11 : List Nat := [3, 5, 7, 11]

/-- Seed extended with `13` only. -/
def seed13 : List Nat := [3, 5, 7, 13]

/-- Full UFRF generator list (seed extended with both `11` and `13`). -/
def seed11_13 : List Nat := [3, 5, 7, 11, 13]

theorem ap12From_seed_eq_nil : ap12From seed = [] := by
  native_decide

theorem ap12From_seed11_eq_nil : ap12From seed11 = [] := by
  native_decide

theorem ap12From_seed13_eq_nil : ap12From seed13 = [] := by
  native_decide

theorem ap12From_seed11_13_eq_monster :
    ap12From seed11_13 = [(47, 59, 71)] := by
  native_decide

/-- Order-invariant AP(12) start-point set is empty for the seed variants missing `{11,13}`. -/
theorem ap12StartSet_L2_seed_eq_empty :
    MonsterAP12Filter.ap12StartSet (L2Of seed) = ∅ := by
  native_decide

theorem ap12StartSet_L2_seed11_eq_empty :
    MonsterAP12Filter.ap12StartSet (L2Of seed11) = ∅ := by
  native_decide

theorem ap12StartSet_L2_seed13_eq_empty :
    MonsterAP12Filter.ap12StartSet (L2Of seed13) = ∅ := by
  native_decide

theorem ap12StartSet_L2_seed11_13_eq_singleton :
    MonsterAP12Filter.ap12StartSet (L2Of seed11_13) = {47} := by
  native_decide

/-- Proposition summarizing the AP(12) outcomes for the seed variants. -/
def seed_variants_ap12_summary : Prop :=
    ap12From seed = []
      ∧ ap12From seed11 = []
      ∧ ap12From seed13 = []
      ∧ ap12From seed11_13 = [(47, 59, 71)]
      ∧ MonsterAP12Filter.ap12StartSet (L2Of seed) = ∅
      ∧ MonsterAP12Filter.ap12StartSet (L2Of seed11) = ∅
      ∧ MonsterAP12Filter.ap12StartSet (L2Of seed13) = ∅
      ∧ MonsterAP12Filter.ap12StartSet (L2Of seed11_13) = {47}

theorem ap12From_seed_variants_summary : seed_variants_ap12_summary := by
  refine ⟨ap12From_seed_eq_nil, ap12From_seed11_eq_nil, ap12From_seed13_eq_nil, ap12From_seed11_13_eq_monster, ?_, ?_, ?_, ?_⟩
  · exact ap12StartSet_L2_seed_eq_empty
  · exact ap12StartSet_L2_seed11_eq_empty
  · exact ap12StartSet_L2_seed13_eq_empty
  · exact ap12StartSet_L2_seed11_13_eq_singleton

end SeedToFrobeniusBridge
