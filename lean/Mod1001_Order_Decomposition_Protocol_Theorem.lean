import Mathlib

/-!
# Mod-1001 Order Decomposition (Finite Deterministic Bridge)

Protocol-level finite summary:
- axis returns for base-10 on `7,11,13` have periods `6,2,6`;
- combined axis period is `lcm(6,2,6)=6`;
- `10^6 ≡ 1 (mod 1001)` and there is no smaller positive return mod `1001`.

Mirrors `mod1001_order_decomposition_protocol.py`.
-/

namespace Mod1001OrderDecompositionPrediction

def axes : List Nat := [7, 11, 13]
def allAxesReturn (k : Nat) : Bool :=
  axes.all (fun m => (10 ^ k : Nat) % m == 1)

def noSmallSimultaneousAxisReturn : Bool :=
  ([1, 2, 3, 4, 5] : List Nat).all (fun k => allAxesReturn k = false)

def noSmallMod1001Return : Bool :=
  ([1, 2, 3, 4, 5] : List Nat).all (fun k => ((10 ^ k : Nat) % 1001 ≠ 1))

theorem finite_mod1001_order_decomposition_summary :
    ((10 ^ 6 : Nat) % 7 = 1) ∧
    ((10 ^ 2 : Nat) % 11 = 1) ∧
    ((10 ^ 6 : Nat) % 13 = 1) ∧
    Nat.lcm (Nat.lcm 6 2) 6 = 6 ∧
    allAxesReturn 6 = true ∧
    noSmallSimultaneousAxisReturn = true ∧
    ((10 ^ 6 : Nat) % 1001 = 1) ∧
    noSmallMod1001Return = true := by
  native_decide

end Mod1001OrderDecompositionPrediction
