import Maxwell_Duality_Invariants_Protocol_Theorem
import Maxwell_Tensor_Hodge_Star_Protocol_Theorem
import Noether_Symmetry_Conservation_Lens_Theorem

/-!
# Maxwell Tensor Duality Noether Packaging (Finite, Algebraic Protocol)

Lean companion to:
- `maxwell_tensor_duality_noether_protocol.py` -> `maxwell_tensor_duality_noether_results.json`

On the tensor side, define invariants (using the repo's fixed `toF` convention):

- `I1_fromF(F) := (F01^2+F02^2+F03^2) - (F23^2+F31^2+F12^2)`
- `I2_fromF(F) := F01*F23 + F02*F31 + F03*F12`
- `Q(F) := I1_fromF(F)^2 + I2_fromF(F)^2`

Then on the image `F = toF(E,B)`:
- `I1_fromF(⋆F(F)) = -I1_fromF(F)` and `I2_fromF(⋆F(F)) = -I2_fromF(F)`,
- hence `Q(⋆F(F)) = Q(F)`, and using the commutation law `⋆F(toF em)=toF(⋆em)`,
  `Q` is invariant under every iterate `(⋆F)^[n]` on that image.

No PDEs. No placeholders.
-/

namespace MaxwellTensorDualityNoetherProtocol

open MaxwellFieldTensorDualityProtocol

namespace EM6

variable {α : Type} [CommRing α]

open MaxwellInvariantsFromTensorProtocol.EM6
open MaxwellTensorHodgeStarProtocol
open MaxwellDualityInvariantsProtocol.EM6

def Q (F : Matrix (Fin 4) (Fin 4) α) : α :=
  (I1_fromF F) * (I1_fromF F) + (I2_fromF F) * (I2_fromF F)

theorem I1_fromF_star_toF (em : MaxwellFieldTensorDualityProtocol.EM6 α) :
    I1_fromF (starF (toF em)) = -I1_fromF (toF em) := by
  -- `⋆F(toF em) = toF(⋆em)`, and the tensor invariants flip sign under `⋆em`.
  simpa [starF_toF (em := em)] using (I1_fromF_dual (em := em))

theorem I2_fromF_star_toF (em : MaxwellFieldTensorDualityProtocol.EM6 α) :
    I2_fromF (starF (toF em)) = -I2_fromF (toF em) := by
  simpa [starF_toF (em := em)] using (I2_fromF_dual (em := em))

theorem Q_star_toF (em : MaxwellFieldTensorDualityProtocol.EM6 α) :
    Q (starF (toF em)) = Q (toF em) := by
  simp [Q, I1_fromF_star_toF (em := em), I2_fromF_star_toF (em := em)]

-- Transport: iterating `⋆F` on `toF em` agrees with iterating `⋆` on `em`, then encoding.
theorem starF_iterate_toF (em : MaxwellFieldTensorDualityProtocol.EM6 α) :
    ∀ n : Nat, (starF^[n]) (toF em) = toF ((MaxwellFieldTensorDualityProtocol.EM6.dual)^[n] em) := by
  intro n
  induction n generalizing em with
  | zero =>
      simp
  | succ n ih =>
      -- `⋆F^[n+1] (toF em) = ⋆F^[n] (⋆F(toF em))`.
      simpa [Function.iterate_succ_apply, starF_toF (em := em)] using ih (em := MaxwellFieldTensorDualityProtocol.EM6.dual em)

theorem Q_toF (em : MaxwellFieldTensorDualityProtocol.EM6 α) :
    Q (toF em) = (I1 em) * (I1 em) + (I2 em) * (I2 em) := by
  simp [Q, I1_from_tensor (em := em), I2_from_tensor (em := em)]

theorem Q_conserved_iterate_star_toF (em : MaxwellFieldTensorDualityProtocol.EM6 α) (n : Nat) :
    Q ((starF^[n]) (toF em)) = Q (toF em) := by
  -- Rewrite tensor iterates as EM6 iterates, then use the already-certified EM6 iterate conservation.
  simp [starF_iterate_toF (em := em) (n := n), Q_toF (em := ((MaxwellFieldTensorDualityProtocol.EM6.dual)^[n] em)),
    Q_toF (em := em), I1sq_add_I2sq_conserved_iterate_dual (em := em) (n := n)]

end EM6

end MaxwellTensorDualityNoetherProtocol

