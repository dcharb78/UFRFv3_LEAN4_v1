import Maxwell_Field_Tensor_Duality_Protocol_Theorem

/-!
# Maxwell Invariants From Field Tensor (Finite, Algebraic Scaffold)

Lean companion to:
- `maxwell_invariants_from_tensor_protocol.py` -> `maxwell_invariants_from_tensor_results.json`

Using the field-tensor convention in `Maxwell_Field_Tensor_Duality_Protocol_Theorem`,
we prove that the standard invariants (natural units `c=1`):

- `I1 := |E|^2 - |B|^2`
- `I2 := E ⋅ B`

are recovered as explicit contractions of tensor entries:

- `I1 = (F01^2 + F02^2 + F03^2) - (F23^2 + F31^2 + F12^2)`
- `I2 = F01*F23 + F02*F31 + F03*F12`

This is fully algebraic (no PDEs), and fixes the sign conventions deterministically.

No placeholders.
-/

namespace MaxwellInvariantsFromTensorProtocol

open MaxwellFieldTensorDualityProtocol

namespace EM6

variable {α : Type} [CommRing α]

def E2 (em : EM6 α) : α := em.ex * em.ex + em.ey * em.ey + em.ez * em.ez
def B2 (em : EM6 α) : α := em.bx * em.bx + em.by * em.by + em.bz * em.bz

def I1 (em : EM6 α) : α := E2 em - B2 em
def I2 (em : EM6 α) : α := em.ex * em.bx + em.ey * em.by + em.ez * em.bz

def I1_fromF (F : Matrix (Fin 4) (Fin 4) α) : α :=
  (F 0 1) * (F 0 1) + (F 0 2) * (F 0 2) + (F 0 3) * (F 0 3)
    - ((F 2 3) * (F 2 3) + (F 3 1) * (F 3 1) + (F 1 2) * (F 1 2))

def I2_fromF (F : Matrix (Fin 4) (Fin 4) α) : α :=
  (F 0 1) * (F 2 3) + (F 0 2) * (F 3 1) + (F 0 3) * (F 1 2)

theorem I1_from_tensor (em : EM6 α) : I1_fromF (toF em) = I1 em := by
  cases em <;> simp [I1_fromF, I1, E2, B2, MaxwellFieldTensorDualityProtocol.toF] <;> ring

theorem I2_from_tensor (em : EM6 α) : I2_fromF (toF em) = I2 em := by
  cases em <;> simp [I2_fromF, I2, MaxwellFieldTensorDualityProtocol.toF] <;> ring

end EM6

end MaxwellInvariantsFromTensorProtocol

