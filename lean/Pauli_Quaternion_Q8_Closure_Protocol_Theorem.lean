import Pauli_Quaternion_Bridge_Protocol_Theorem

/-!
# Pauli→Quaternion Q8 Closure Protocol (Finite, Exact)

Lean companion to:
- `pauli_quaternion_q8_closure_protocol.py` -> `pauli_quaternion_q8_closure_results.json`

From the Pauli→Quaternion bridge (over `ℤ[i]`), define the 8-element set:

`Q8 := {±I, ±qi, ±qj, ±qk}`

and certify (exactly) that:
- `Q8` has cardinality `8` (no collapse of signed units),
- `Q8` is closed under matrix multiplication,
- the canonical generator `qi` has a 4-step return (`qi^4 = I`),
- the multiplication is noncommutative (order matters).

This is a small algebraic “octave” anchor (Q8) that ties the SU(2)/Pauli layer to
finite quaternion structure without any analytic/PDE assumptions.

No placeholders.
-/

namespace PauliQuaternionQ8ClosureProtocol

open Matrix

local notation "ℤ[i]" => GaussianInt

open DiracCliffordAnticommutatorProtocol
open PauliQuaternionBridgeProtocol

noncomputable section

abbrev Mat2 : Type := Matrix (Fin 2) (Fin 2) ℤ[i]

-- An indexed enumeration of the signed quaternion units.
def q8Elem : Fin 8 → Mat2
  | ⟨0, _⟩ => I2
  | ⟨1, _⟩ => negI2
  | ⟨2, _⟩ => qi
  | ⟨3, _⟩ => -qi
  | ⟨4, _⟩ => qj
  | ⟨5, _⟩ => -qj
  | ⟨6, _⟩ => qk
  | ⟨7, _⟩ => -qk

def Q8 : Finset Mat2 := {I2, negI2, qi, -qi, qj, -qj, qk, -qk}

theorem q8_card : Q8.card = 8 := by
  native_decide

theorem q8_closed : ∀ i j : Fin 8, (q8Elem i) * (q8Elem j) ∈ Q8 := by
  fin_cases i <;> fin_cases j <;> native_decide

theorem q8_noncomm : qi * qj ≠ qj * qi := by
  native_decide

theorem qi_sq : qi ^ 2 = negI2 := by
  native_decide

theorem qi_pow4 : qi ^ 4 = I2 := by
  native_decide

end

end PauliQuaternionQ8ClosureProtocol

