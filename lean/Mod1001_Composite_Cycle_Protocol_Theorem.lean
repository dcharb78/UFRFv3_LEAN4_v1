import Mathlib

/-!
# Mod-1001 Composite Cycle (Finite Deterministic Bridge)

Protocol-level finite summary over concrete anchors:
- `1001 = 7*11*13`;
- `10^3 ≡ -1 (mod 1001)`, `10^6 ≡ 1 (mod 1001)`;
- for anchor `n`, multiplying by `10^3` gives mod-1001 negation and
  multiplying by `10^6` returns the same residue.

Mirrors `mod1001_composite_cycle_protocol.py`.
-/

namespace Mod1001CompositeCyclePrediction

def M : Nat := 1001
def anchors : List Nat := [13, 169, 2197, 196883, 196884, 144000]

def flipOk (n : Nat) : Bool := (((n * 10 ^ 3) + n) % M == 0)
def returnOk (n : Nat) : Bool := ((n * 10 ^ 6) % M == n % M)
def negOk (n : Nat) : Bool := ((n * 10 ^ 3) % M == (M - (n % M)) % M)

def allFlip : Bool := anchors.all flipOk
def allReturn : Bool := anchors.all returnOk
def allNeg : Bool := anchors.all negOk

theorem finite_mod1001_composite_cycle_summary :
    M = 7 * 11 * 13 ∧
    (10 ^ 3 : Nat) % M = M - 1 ∧
    (10 ^ 6 : Nat) % M = 1 ∧
    allFlip = true ∧
    allReturn = true ∧
    allNeg = true := by
  native_decide

end Mod1001CompositeCyclePrediction
