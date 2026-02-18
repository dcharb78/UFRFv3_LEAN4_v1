import Dirac_Clifford_Anticommutator_Protocol_Theorem

/-!
# Pauli → Quaternion Bridge Protocol (Finite, Exact)

Lean companion to:
- `pauli_quaternion_bridge_protocol.py` -> `pauli_quaternion_bridge_results.json`

Over `ℤ[i]`, the Pauli matrices realize quaternion units via:

  qi := (-i) σx
  qj := (-i) σy
  qk := (-i) σz

and satisfy the quaternion multiplication table exactly.

This is a small, fully algebraic SU(2) anchor that connects the Dirac/Pauli layer
to quaternion (double-cover) structure without any analytic/PDE assumptions.
-/

namespace PauliQuaternionBridgeProtocol

open Matrix

local notation "ℤ[i]" => GaussianInt

open DiracCliffordAnticommutatorProtocol

noncomputable section

def qi : Matrix (Fin 2) (Fin 2) ℤ[i] := (-gi) • σx
def qj : Matrix (Fin 2) (Fin 2) ℤ[i] := (-gi) • σy
def qk : Matrix (Fin 2) (Fin 2) ℤ[i] := (-gi) • σz

def negI2 : Matrix (Fin 2) (Fin 2) ℤ[i] := (-1 : ℤ[i]) • I2

theorem pauli_quaternion_bridge_ok :
    qi * qi = negI2 ∧
      qj * qj = negI2 ∧
      qk * qk = negI2 ∧
      qi * qj = qk ∧
      qj * qk = qi ∧
      qk * qi = qj ∧
      qj * qi = -qk := by
  native_decide

end

end PauliQuaternionBridgeProtocol

