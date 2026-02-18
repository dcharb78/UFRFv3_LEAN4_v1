import Maxwell_Invariants_From_Tensor_Protocol_Theorem
import Maxwell_Poynting_Identity_Protocol_Theorem
import Noether_Symmetry_Conservation_Lens_Theorem

/-!
# Maxwell Duality Invariants (⋆) Protocol (Finite, Algebraic Scaffold)

Lean companion to:
- `maxwell_duality_invariants_protocol.py` -> `maxwell_duality_invariants_results.json`

We work with the discrete EM duality step (natural units):

`⋆(E,B) := (B, -E)`

With the scalar invariants:
- `I1 := |E|^2 - |B|^2`
- `I2 := E⋅B`

and the Poynting proxy vector:
- `S := E×B`

we prove (over any commutative ring):
1) `I1(⋆em) = -I1(em)` and `I2(⋆em) = -I2(em)` (sign flip),
2) `S(⋆em) = S(em)` (Poynting invariant),
3) hence `I1^2`, `I2^2`, and `I1^2 + I2^2` are conserved under `⋆`,
   and by the Noether discrete lens, conserved under every iterate `⋆^[n]`.

No PDEs. No placeholders.
-/

namespace MaxwellDualityInvariantsProtocol

open MaxwellFieldTensorDualityProtocol
open MaxwellPoyntingIdentityProtocol

namespace EM6

variable {α : Type} [CommRing α]

-- Reuse the scalar invariants defined in the tensor-contraction module.
open MaxwellInvariantsFromTensorProtocol.EM6

def Evec (em : MaxwellFieldTensorDualityProtocol.EM6 α) : Vec3 α :=
  { x := em.ex, y := em.ey, z := em.ez }

def Bvec (em : MaxwellFieldTensorDualityProtocol.EM6 α) : Vec3 α :=
  { x := em.bx, y := em.by, z := em.bz }

def S (em : MaxwellFieldTensorDualityProtocol.EM6 α) : Vec3 α :=
  Vec3.cross (Evec em) (Bvec em)

theorem E2_dual (em : MaxwellFieldTensorDualityProtocol.EM6 α) :
    E2 (MaxwellFieldTensorDualityProtocol.EM6.dual em) = B2 em := by
  cases em <;> simp [E2, B2, MaxwellFieldTensorDualityProtocol.EM6.dual] <;> ring

theorem B2_dual (em : MaxwellFieldTensorDualityProtocol.EM6 α) :
    B2 (MaxwellFieldTensorDualityProtocol.EM6.dual em) = E2 em := by
  cases em <;> simp [E2, B2, MaxwellFieldTensorDualityProtocol.EM6.dual] <;> ring

theorem I1_dual (em : MaxwellFieldTensorDualityProtocol.EM6 α) :
    I1 (MaxwellFieldTensorDualityProtocol.EM6.dual em) = -I1 em := by
  simp [I1, E2_dual (em := em), B2_dual (em := em)]

theorem I2_dual (em : MaxwellFieldTensorDualityProtocol.EM6 α) :
    I2 (MaxwellFieldTensorDualityProtocol.EM6.dual em) = -I2 em := by
  cases em <;> simp [I2, MaxwellFieldTensorDualityProtocol.EM6.dual] <;> ring

theorem S_dual (em : MaxwellFieldTensorDualityProtocol.EM6 α) :
    S (MaxwellFieldTensorDualityProtocol.EM6.dual em) = S em := by
  cases em with
  | mk ex ey ez bx by bz =>
      ext <;> simp [S, Evec, Bvec, MaxwellFieldTensorDualityProtocol.EM6.dual, Vec3.cross] <;> ring

-- Squared invariants are genuinely conserved under `⋆`.
theorem I1_sq_dual (em : MaxwellFieldTensorDualityProtocol.EM6 α) :
    (I1 (MaxwellFieldTensorDualityProtocol.EM6.dual em)) * (I1 (MaxwellFieldTensorDualityProtocol.EM6.dual em))
      = (I1 em) * (I1 em) := by
  simp [I1_dual (em := em)]

theorem I2_sq_dual (em : MaxwellFieldTensorDualityProtocol.EM6 α) :
    (I2 (MaxwellFieldTensorDualityProtocol.EM6.dual em)) * (I2 (MaxwellFieldTensorDualityProtocol.EM6.dual em))
      = (I2 em) * (I2 em) := by
  simp [I2_dual (em := em)]

theorem I1sq_add_I2sq_dual (em : MaxwellFieldTensorDualityProtocol.EM6 α) :
    (I1 (MaxwellFieldTensorDualityProtocol.EM6.dual em)) * (I1 (MaxwellFieldTensorDualityProtocol.EM6.dual em))
        + (I2 (MaxwellFieldTensorDualityProtocol.EM6.dual em)) * (I2 (MaxwellFieldTensorDualityProtocol.EM6.dual em))
      = (I1 em) * (I1 em) + (I2 em) * (I2 em) := by
  simp [I1_dual (em := em), I2_dual (em := em)]

-- Tensor-side compatibility: invariants computed from `F` flip sign under `⋆`.
theorem I1_fromF_dual (em : MaxwellFieldTensorDualityProtocol.EM6 α) :
    I1_fromF (toF (MaxwellFieldTensorDualityProtocol.EM6.dual em)) = -I1_fromF (toF em) := by
  -- `I1_fromF(toF em) = I1 em` and `I1(⋆em) = -I1 em`.
  simp [I1_from_tensor, I1_dual (em := em)]

theorem I2_fromF_dual (em : MaxwellFieldTensorDualityProtocol.EM6 α) :
    I2_fromF (toF (MaxwellFieldTensorDualityProtocol.EM6.dual em)) = -I2_fromF (toF em) := by
  simp [I2_from_tensor, I2_dual (em := em)]

-- Noether lens: one-step invariance implies invariance under every iterate.
theorem S_conserved_iterate_dual (em : MaxwellFieldTensorDualityProtocol.EM6 α) (n : Nat) :
    S ((MaxwellFieldTensorDualityProtocol.EM6.dual)^[n] em) = S em := by
  have h : NoetherDiscrete.ConservedUnder MaxwellFieldTensorDualityProtocol.EM6.dual S := by
    intro x
    simpa using (S_dual (em := x))
  simpa using NoetherDiscrete.conserved_iterate (step := MaxwellFieldTensorDualityProtocol.EM6.dual) (obs := S) h n em

theorem I1sq_add_I2sq_conserved_iterate_dual (em : MaxwellFieldTensorDualityProtocol.EM6 α) (n : Nat) :
    (I1 ((MaxwellFieldTensorDualityProtocol.EM6.dual)^[n] em)) * (I1 ((MaxwellFieldTensorDualityProtocol.EM6.dual)^[n] em))
        + (I2 ((MaxwellFieldTensorDualityProtocol.EM6.dual)^[n] em)) * (I2 ((MaxwellFieldTensorDualityProtocol.EM6.dual)^[n] em))
      = (I1 em) * (I1 em) + (I2 em) * (I2 em) := by
  -- Prove one-step conservation then lift it to iterates.
  let obs : MaxwellFieldTensorDualityProtocol.EM6 α → α :=
    fun x => (I1 x) * (I1 x) + (I2 x) * (I2 x)
  have h : NoetherDiscrete.ConservedUnder MaxwellFieldTensorDualityProtocol.EM6.dual obs := by
    intro x
    -- One-step: both I1 and I2 flip sign, so squares sum is unchanged.
    simpa [obs, I1_dual (em := x), I2_dual (em := x)]
  simpa [obs] using
    NoetherDiscrete.conserved_iterate (step := MaxwellFieldTensorDualityProtocol.EM6.dual) (obs := obs) h n em

end EM6

end MaxwellDualityInvariantsProtocol

