import Maxwell_Field_Tensor_Duality_Protocol_Theorem

/-!
# Maxwell Tensor Hodge-Star (⋆F) Protocol (Finite, Algebraic Scaffold)

Lean companion to:
- `maxwell_tensor_hodge_star_protocol.py` -> `maxwell_tensor_hodge_star_results.json`

This file defines an explicit tensor-side duality operator `⋆F` on `4×4` matrices
as a pure index permutation/sign map on the six independent components:

`(F01,F02,F03,F23,F31,F12) ↦ (F23,F31,F12,-F01,-F02,-F03)`

and certifies:

1. `⋆F(toF(E,B)) = toF(⋆(E,B))` where `⋆(E,B)=(B,-E)` is the EM6 duality step.
2. `⋆F(⋆F(toF(E,B))) = -toF(E,B)` (order-4 rotation on the image of `toF`).
3. `⋆F(F)` is antisymmetric (by construction).

No PDEs. No placeholders.
-/

namespace MaxwellTensorHodgeStarProtocol

open MaxwellFieldTensorDualityProtocol

-- Tensor-side duality operator `⋆F` (explicit convention tied to `toF`).
def starF {α : Type} [Ring α] (F : Matrix (Fin 4) (Fin 4) α) : Matrix (Fin 4) (Fin 4) α :=
  fun i j =>
    match i.1, j.1 with
    -- Electric -> magnetic
    | 0, 1 => F 2 3
    | 1, 0 => -F 2 3
    | 0, 2 => F 3 1
    | 2, 0 => -F 3 1
    | 0, 3 => F 1 2
    | 3, 0 => -F 1 2
    -- Magnetic -> -electric
    | 2, 3 => -F 0 1
    | 3, 2 => F 0 1
    | 3, 1 => -F 0 2
    | 1, 3 => F 0 2
    | 1, 2 => -F 0 3
    | 2, 1 => F 0 3
    | _, _ => 0

theorem starF_antisymm {α : Type} [Ring α] (F : Matrix (Fin 4) (Fin 4) α) :
    ∀ i j : Fin 4, starF F i j = -starF F j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [starF]

theorem starF_toF {α : Type} [Ring α] (em : MaxwellFieldTensorDualityProtocol.EM6 α) :
    starF (toF em) = toF (MaxwellFieldTensorDualityProtocol.EM6.dual em) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [starF, toF, MaxwellFieldTensorDualityProtocol.EM6.dual]

theorem toF_neg {α : Type} [Ring α] (em : MaxwellFieldTensorDualityProtocol.EM6 α) :
    toF (MaxwellFieldTensorDualityProtocol.EM6.neg em) = -toF em := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toF, MaxwellFieldTensorDualityProtocol.EM6.neg]

theorem starF_starF_toF {α : Type} [Ring α] (em : MaxwellFieldTensorDualityProtocol.EM6 α) :
    starF (starF (toF em)) = -toF em := by
  -- `⋆F(toF em) = toF(⋆em)` and `⋆⋆em = -em`.
  calc
    starF (starF (toF em))
        = starF (toF (MaxwellFieldTensorDualityProtocol.EM6.dual em)) := by
            simp [starF_toF (em := em)]
    _ = toF (MaxwellFieldTensorDualityProtocol.EM6.dual (MaxwellFieldTensorDualityProtocol.EM6.dual em)) := by
            simp [starF_toF]
    _ = toF (MaxwellFieldTensorDualityProtocol.EM6.neg em) := by
            simpa using (MaxwellFieldTensorDualityProtocol.EM6.dual_dual (em := em))
    _ = -toF em := by
            simp [toF_neg (em := em)]

end MaxwellTensorHodgeStarProtocol
