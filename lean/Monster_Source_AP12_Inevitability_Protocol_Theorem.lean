import Mathlib
import GetBangCompat

/-!
# Monster Source-AP12 Inevitability (Finite Deterministic Bridge)

Protocol-level finite summary:
- derive source values from all UFRF pairwise Frobenius values;
- enumerate AP(12) triples in those source values;
- certify unique hit `(47,59,71)` and `product+1 = 196884`.

Mirrors `monster_source_ap12_inevitability_protocol.py`.
-/

namespace MonsterSourceAP12InevitabilityPrediction

def frob (a b : Nat) : Nat := a * b - a - b

def pairs : List (Nat × Nat) :=
  [(3, 5), (3, 7), (3, 11), (3, 13), (5, 7), (5, 11), (5, 13), (7, 11), (7, 13), (11, 13)]

def pairValues : List Nat := pairs.map (fun p => frob p.1 p.2)
def sourceValues : List Nat := pairValues.eraseDups
def preimage (t : Nat) : List (Nat × Nat) := pairs.filter (fun p => frob p.1 p.2 == t)

def ap12Triples : List (Nat × Nat × Nat) :=
  sourceValues.bind (fun a =>
    sourceValues.bind (fun b =>
      sourceValues.bind (fun c =>
        if (a < b) && (b < c) && (b - a == 12) && (c - b == 12)
        then [(a, b, c)]
        else [])))

def productPlusOne (t : Nat × Nat × Nat) : Nat :=
  match t with
  | (a, b, c) => a * b * c + 1

def triplesHit196884 : List (Nat × Nat × Nat) :=
  ap12Triples.filter (fun t => productPlusOne t == 196884)

theorem finite_monster_source_ap12_inevitability_summary :
    pairValues = [7, 11, 19, 23, 23, 39, 47, 59, 71, 119] ∧
    sourceValues = [7, 11, 19, 23, 39, 47, 59, 71, 119] ∧
    ap12Triples = [(47, 59, 71)] ∧
    triplesHit196884 = [(47, 59, 71)] ∧
    preimage 47 = [(5, 13)] ∧
    preimage 59 = [(7, 11)] ∧
    preimage 71 = [(7, 13)] ∧
    productPlusOne (47, 59, 71) = 196884 := by
  native_decide

end MonsterSourceAP12InevitabilityPrediction
