import Mathlib
import GetBangCompat

/-!
# Quantum Hall n/13 Prediction Protocol (Finite Deterministic Bridge)

Finite arithmetic bridge for `UFRF3.1/08-ufrf-predictions-tests.md` §2.1 claim subset:

`ν = n/13` for `n = 1..12`, with highlighted `10/13`.

Mirrors `quantum_hall_n13_prediction_protocol.py`.
-/

namespace QuantumHallN13Prediction

def den : Nat := 13
def ns : List Nat := List.range' 1 12
def fracs : List Rat := ns.map (fun n => (n : Rat) / (den : Rat))

def monotoneIncreasing : Bool :=
  (List.range 11).all (fun k => fracs.get! k < fracs.get! (k + 1))

def allBetweenZeroAndOne : Bool :=
  fracs.all (fun x => (0 : Rat) < x && x < 1)

theorem finite_quantum_hall_n13_summary :
    ns.length = 12 ∧
    fracs.length = 12 ∧
    fracs.get! 0 = (1 : Rat) / 13 ∧
    fracs.get! 11 = (12 : Rat) / 13 ∧
    ((10 : Rat) / 13) ∈ fracs ∧
    monotoneIncreasing = true ∧
    allBetweenZeroAndOne = true := by
  native_decide

end QuantumHallN13Prediction
