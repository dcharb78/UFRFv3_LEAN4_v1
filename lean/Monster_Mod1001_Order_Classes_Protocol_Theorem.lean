import Mathlib

/-!
# Monster Mod-1001 Order Classes (Finite Deterministic Synthesis Bridge)

Protocol-level finite summary:
- Monster anchors `47,59,71` are exact order-60 units modulo `1001`;
- product residue class is exact order-60;
- `c₁` residue class (`196884 mod 1001`) is exact order-30,
  matching source anchor `3` order class.

Mirrors `monster_mod1001_order_classes_protocol.py`.
-/

namespace MonsterMod1001OrderClassesPrediction

def modulus : Nat := 1001
def monster : List Nat := [47, 59, 71]
def properDivs60 : List Nat := [1, 2, 3, 4, 5, 6, 10, 12, 15, 20, 30]
def properDivs30 : List Nat := [1, 2, 3, 5, 6, 10, 15]

def isUnitMod1001 (a : Nat) : Bool := Nat.gcd a modulus == 1

def exactOrder60 (a : Nat) : Bool :=
  (((a ^ 60 : Nat) % modulus) == 1) &&
    (properDivs60.all (fun k => !(((a ^ k : Nat) % modulus) == 1)))

def exactOrder30 (a : Nat) : Bool :=
  (((a ^ 30 : Nat) % modulus) == 1) &&
    (properDivs30.all (fun k => !(((a ^ k : Nat) % modulus) == 1)))

def product : Nat := 47 * 59 * 71
def productResidue : Nat := product % modulus
def c1 : Nat := 196884
def c1Residue : Nat := c1 % modulus

theorem finite_monster_mod1001_order_classes_summary :
    monster.all isUnitMod1001 = true ∧
    exactOrder60 47 = true ∧
    exactOrder60 59 = true ∧
    exactOrder60 71 = true ∧
    productResidue = 687 ∧
    exactOrder60 productResidue = true ∧
    c1Residue = 688 ∧
    exactOrder30 c1Residue = true ∧
    exactOrder30 3 = true := by
  native_decide

end MonsterMod1001OrderClassesPrediction
