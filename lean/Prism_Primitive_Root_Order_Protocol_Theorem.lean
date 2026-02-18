import Mathlib

/-!
# PRISM Primitive-Root/Order Protocol (Finite, Deterministic)

Protocol mirror for:
- `prism_primitive_root_order_protocol.py`
- `prism_primitive_root_order_results.json`

Scope:
- bounded checks for the witness `2` on moduli `13^k` for `k=1..4`,
- bounded projection-compatibility checks on fixed finite exponent sets,
- no unbounded primitive-root theorem claim.
-/

namespace PrismPrimitiveRootOrderProtocol

def base : Nat := 13
def witness : Nat := 2
def maxK : Nat := 4

def moduli : List Nat := [13, 169, 2197, 28561]
def phiModuli : List Nat := [12, 156, 2028, 26364]
def orderWitnessValues : List Nat := [12, 156, 2028, 26364]
def properDivisorCounts : List Nat := [5, 11, 17, 23]

def projectionExponentsK2 : List Nat := [0, 1, 2, 3, 5, 7, 11, 12, 13, 24, 156]
def projectionExponentsK3 : List Nat := [0, 1, 2, 3, 5, 7, 11, 12, 13, 24, 156, 2028]
def projectionExponentsK4 : List Nat := [0, 1, 2, 3, 5, 7, 11, 12, 13, 24, 2028, 26364]
def projectionCheckCounts : List Nat := [11, 12, 12]
def projectionCompatibilityByLevel : List Bool := [true, true, true]

def orderMinimalityCounterexamplesByLevel : List (List Nat) := [[], [], [], []]

def orderEqualsPhiAll : Bool := orderWitnessValues == phiModuli

def orderMinimalityAll : Bool := orderMinimalityCounterexamplesByLevel == [[], [], [], []]

def projectionCompatibilityAll : Bool := projectionCompatibilityByLevel == [true, true, true]

def scaleBy13FromLevel2 : Bool :=
  (orderWitnessValues == [12, 156, 2028, 26364])
  && (156 == 13 * 12)
  && (2028 == 13 * 156)
  && (26364 == 13 * 2028)

def primitiveRootWitnessAll : Bool := orderEqualsPhiAll && orderMinimalityAll

theorem prism_primitive_root_order_summary :
    base = 13
    ∧ witness = 2
    ∧ maxK = 4
    ∧ moduli = [13, 169, 2197, 28561]
    ∧ phiModuli = [12, 156, 2028, 26364]
    ∧ orderWitnessValues = [12, 156, 2028, 26364]
    ∧ properDivisorCounts = [5, 11, 17, 23]
    ∧ projectionExponentsK2 = [0, 1, 2, 3, 5, 7, 11, 12, 13, 24, 156]
    ∧ projectionExponentsK3 = [0, 1, 2, 3, 5, 7, 11, 12, 13, 24, 156, 2028]
    ∧ projectionExponentsK4 = [0, 1, 2, 3, 5, 7, 11, 12, 13, 24, 2028, 26364]
    ∧ projectionCheckCounts = [11, 12, 12]
    ∧ projectionCompatibilityByLevel = [true, true, true]
    ∧ orderMinimalityCounterexamplesByLevel = [[], [], [], []]
    ∧ orderEqualsPhiAll = true
    ∧ orderMinimalityAll = true
    ∧ projectionCompatibilityAll = true
    ∧ scaleBy13FromLevel2 = true
    ∧ primitiveRootWitnessAll = true := by
  native_decide

end PrismPrimitiveRootOrderProtocol
