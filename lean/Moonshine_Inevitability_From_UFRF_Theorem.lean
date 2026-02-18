import Mathlib
import Frobenius_Emergence_Theorem
import Monster_AP12_Filter_Theorem
import J_Function_Coefficient_Theorem

/-!
# Moonshine Inevitability From UFRF (Deterministic Model)

This file bundles an explicit inevitability chain already implicit in the repo:

1. Start from the fixed UFRF generator list (`FrobeniusEmergence.ufrfGenerators`).
2. Build `L2Full` via pairwise Frobenius expressions.
3. Apply the AP(12) filter on triples.
4. The filter output is uniquely `(47,59,71)`.
5. Product-plus-one of that unique triple equals `jCoefficient 1`.

So within this formal discrete pipeline, the Moonshine anchor is not a special
one-off insertion; it is the unique deterministic output of the UFRF→AP12 path.
-/

namespace MoonshineInevitability

open FrobeniusEmergence
open MonsterAP12Filter

/-- Product-plus-one functional used for the Moonshine `c₁` anchor. -/
def tripleProductPlusOne (t : Nat × Nat × Nat) : Nat :=
  let (a, b, c) := t
  a * b * c + 1

/-- AP(12)-filtered triple list from the UFRF Level-2 Frobenius list. -/
def ufrfAP12Triples : List (Nat × Nat × Nat) :=
  ap12Triples L2Full

theorem ufrfAP12Triples_eq_singleton :
    ufrfAP12Triples = [(47, 59, 71)] := by
  simpa [ufrfAP12Triples] using ap12Triples_L2Full

theorem unique_ap12_triple_mem
    (t : Nat × Nat × Nat)
    (ht : t ∈ ufrfAP12Triples) :
    t = (47, 59, 71) := by
  simpa [ufrfAP12Triples_eq_singleton] using ht

theorem monster_triple_mem_ap12 : (47, 59, 71) ∈ ufrfAP12Triples := by
  simp [ufrfAP12Triples_eq_singleton]

theorem tripleProductPlusOne_monster :
    tripleProductPlusOne (47, 59, 71) = 196884 := by
  native_decide

theorem j_c1_eq_tripleProductPlusOne_monster :
    JFunctionCoefficient.jCoefficient 1 =
      Int.ofNat (tripleProductPlusOne (47, 59, 71)) := by
  calc
    JFunctionCoefficient.jCoefficient 1 = (196884 : Int) := by
      simpa using JFunctionCoefficient.j_coefficient_c1_value
    _ = Int.ofNat (tripleProductPlusOne (47, 59, 71)) := by
      norm_num [tripleProductPlusOne]

/--
Unique inevitability statement:
there is a unique AP(12) triple produced by the UFRF Frobenius Level-2 list,
and its product-plus-one equals the first j-coefficient.
-/
theorem moonshine_anchor_inevitable_from_ufrf :
    ∃! t : Nat × Nat × Nat,
      t ∈ ufrfAP12Triples
        ∧ JFunctionCoefficient.jCoefficient 1 = Int.ofNat (tripleProductPlusOne t) := by
  refine ⟨(47, 59, 71), ?_, ?_⟩
  · exact ⟨monster_triple_mem_ap12, j_c1_eq_tripleProductPlusOne_monster⟩
  · intro t ht
    exact unique_ap12_triple_mem t ht.1

end MoonshineInevitability
