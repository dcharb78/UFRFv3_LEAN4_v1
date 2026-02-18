import Mathlib
import GetBangCompat

/-!
# Monster Pair-Origin Uniqueness (Finite Deterministic Bridge)

Protocol-level finite summary:
- enumerate UFRF pairwise Frobenius values;
- certify unique pair origins for `47,59,71`;
- retain AP(12) and `product+1` consistency.

Mirrors `monster_pair_origin_uniqueness_protocol.py`.
-/

namespace MonsterPairOriginUniquenessPrediction

def frob (a b : Nat) : Nat := a * b - a - b

def pairs : List (Nat × Nat) :=
  [(3, 5), (3, 7), (3, 11), (3, 13), (5, 7), (5, 11), (5, 13), (7, 11), (7, 13), (11, 13)]

def pairValues : List Nat := pairs.map (fun p => frob p.1 p.2)
def preimage (t : Nat) : List (Nat × Nat) := pairs.filter (fun p => frob p.1 p.2 == t)

def targetTriple : List Nat := [47, 59, 71]
def productPlusOne : Nat := 47 * 59 * 71 + 1

theorem finite_monster_pair_origin_uniqueness_summary :
    pairValues = [7, 11, 19, 23, 23, 39, 47, 59, 71, 119] ∧
    preimage 47 = [(5, 13)] ∧
    preimage 59 = [(7, 11)] ∧
    preimage 71 = [(7, 13)] ∧
    (targetTriple.get! 1 - targetTriple.get! 0 = 12) ∧
    (targetTriple.get! 2 - targetTriple.get! 1 = 12) ∧
    productPlusOne = 196884 := by
  native_decide

end MonsterPairOriginUniquenessPrediction
