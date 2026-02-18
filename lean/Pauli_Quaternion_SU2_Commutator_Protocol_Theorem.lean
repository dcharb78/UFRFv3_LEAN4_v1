import Pauli_Quaternion_Bridge_Protocol_Theorem

/-!
# Pauli→Quaternion su(2) Commutator Protocol (Finite, Exact)

Lean companion to:
- `pauli_quaternion_su2_commutator_protocol.py` -> `pauli_quaternion_su2_commutator_results.json`

We define the commutator bracket on `2×2` matrices over `ℤ[i]`:

`[A,B] := AB - BA`

For the Pauli→Quaternion units:
`qi := (-i)σx`, `qj := (-i)σy`, `qk := (-i)σz`,
we certify the su(2) structure constants and Jacobi identity on this basis:

`[qi,qj]=2·qk`, `[qj,qk]=2·qi`, `[qk,qi]=2·qj`,
and `[qi,[qj,qk]] + [qj,[qk,qi]] + [qk,[qi,qj]] = 0`.

No placeholders.
-/

namespace PauliQuaternionSU2CommutatorProtocol

open Matrix

local notation "ℤ[i]" => GaussianInt

open PauliQuaternionBridgeProtocol

noncomputable section

abbrev Mat2 : Type := Matrix (Fin 2) (Fin 2) ℤ[i]

def comm (A B : Mat2) : Mat2 := A * B - B * A

theorem pauli_quaternion_su2_commutator_ok :
    comm qi qj = (2 : ℤ[i]) • qk ∧
      comm qj qk = (2 : ℤ[i]) • qi ∧
      comm qk qi = (2 : ℤ[i]) • qj ∧
      (comm qi (comm qj qk) + comm qj (comm qk qi) + comm qk (comm qi qj) = (0 : Mat2)) := by
  native_decide

end

end PauliQuaternionSU2CommutatorProtocol

