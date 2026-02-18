import Mathlib
import GetBangCompat

/-!
# Moonshine Inevitability From Source (Finite Deterministic Synthesis Bridge)

Protocol-level finite summary:
- derive source values from all UFRF pairwise Frobenius values;
- derive the unique AP(12) triple from those source values;
- certify `c₁ = product + 1` and denominator-ladder equalities for `c₂/c₃/c₄`.

Mirrors `moonshine_inevitability_from_source_protocol.py`.
-/

namespace MoonshineInevitabilityFromSourcePrediction

def frobenius (a b : Nat) : Nat := a * b - a - b

def pairs : List (Nat × Nat) :=
  [(3, 5), (3, 7), (3, 11), (3, 13), (5, 7), (5, 11), (5, 13), (7, 11), (7, 13), (11, 13)]

def pairValues : List Nat := pairs.map (fun p => frobenius p.1 p.2)
def sourceValues : List Nat := pairValues.eraseDups

def ap12Triples : List (Nat × Nat × Nat) :=
  sourceValues.bind (fun a =>
    sourceValues.bind (fun b =>
      sourceValues.bind (fun c =>
        if (a < b) && (b < c) && (b - a == 12) && (c - b == 12)
        then [(a, b, c)]
        else [])))

def monsterTriple : Nat × Nat × Nat :=
  match ap12Triples with
  | t :: _ => t
  | [] => (0, 0, 0)

def m1 : Nat := monsterTriple.1
def m2 : Nat := monsterTriple.2.1
def m3 : Nat := monsterTriple.2.2

def product : Nat := m1 * m2 * m3
def c1 : Nat := 196884

def e1 : Nat := m1 + m2 + m3
def e2 : Nat := m1 * m2 + m1 * m3 + m2 * m3
def e3 : Nat := product

def c2 : Int := 21493760
def c2num : Int := 8 * (e1 : Int) * (e3 : Int) + 61 * (e2 : Int) - 31 * (e1 : Int) + 9800

def c3 : Int := 864299970
def c3num : Int :=
  4 * (e3 : Int) ^ 2 - 4 * (e2 : Int) * (e3 : Int) - 8 * (e2 : Int) ^ 2
  - 2487 * (e2 : Int) - 39 * (e1 : Int) - 34

def c4 : Int := 20245856256
def c4num : Int :=
  1147 * (e3 : Int) ^ 2 + 9 * (e2 : Int) * (e3 : Int) + 8 * (e2 : Int) ^ 2
  - 1547 * (e2 : Int) - 32 * (e1 : Int) + 5

theorem finite_moonshine_inevitability_from_source_summary :
    pairValues = [7, 11, 19, 23, 23, 39, 47, 59, 71, 119] ∧
    sourceValues = [7, 11, 19, 23, 39, 47, 59, 71, 119] ∧
    ap12Triples = [(47, 59, 71)] ∧
    monsterTriple = (47, 59, 71) ∧
    m2 - m1 = 12 ∧
    m3 - m2 = 12 ∧
    c1 = product + 1 ∧
    e1 = 177 ∧
    c2num = 13 * c2 ∧
    c3num = 169 * c3 ∧
    c4num = 2197 * c4 := by
  native_decide

end MoonshineInevitabilityFromSourcePrediction
