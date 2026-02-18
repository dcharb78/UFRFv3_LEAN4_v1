import Mathlib

/-!
# Decimal Nested Tick Projection (Finite Deterministic Bridge)

Deterministic scaffold for concurrent base-10 nesting:
- each level state is a decimal digit (`0..9`);
- level-`k` state of `n` equals level-`1` state of the scaled index
  `n / 10^(k-1)`.

Mirrors `decimal_nested_tick_projection_protocol.py`.
-/

namespace DecimalNestedTickProjectionPrediction

def digitAt (n level : Nat) : Nat :=
  (n / (10 ^ (level - 1))) % 10

def anchor144000 : List Nat :=
  (List.range 6).map (fun i => digitAt 144000 (i + 1))

def projectionSamples : List (Nat × Nat) :=
  [(2197, 3), (196884, 5), (144000, 6), (13 ^ 7, 4), (144, 2)]

def projectionHolds (p : Nat × Nat) : Bool :=
  let n := p.1
  let k := p.2
  digitAt n k = digitAt (n / (10 ^ (k - 1))) 1

def allProjectionHolds : Bool :=
  projectionSamples.all projectionHolds

def inRange (n level : Nat) : Bool :=
  digitAt n level < 10

def stateRangeCheck : Bool :=
  (List.range 500).all (fun n => (List.range 6).all (fun i => inRange n (i + 1)))

theorem finite_decimal_nested_tick_projection_summary :
    anchor144000 = [0, 0, 0, 4, 4, 1] ∧
    allProjectionHolds = true ∧
    stateRangeCheck = true := by
  native_decide

end DecimalNestedTickProjectionPrediction
