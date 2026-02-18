import Mathlib
import GetBangCompat

/-!
# Acoustic n/13 Prediction Protocol (Finite Deterministic Bridge)

Finite arithmetic bridge for `UFRF3.1/08-ufrf-predictions-tests.md` §7 claim subset:

`fₙ = 432 * (n / 13)` for `n = 1..13`.

Mirrors `acoustic_n13_prediction_protocol.py`.
-/

namespace AcousticN13Prediction

def baseFreq : Nat := 432
def den : Nat := 13
def ns : List Nat := List.range' 1 13

def freq (n : Nat) : Rat :=
  (baseFreq : Rat) * (n : Rat) / (den : Rat)

def freqs : List Rat := ns.map freq

def allScaledIdentity : Bool :=
  ns.all (fun n => ((den : Rat) * freq n) == ((baseFreq : Rat) * (n : Rat)))

def constantStep : Bool :=
  (List.range 12).all (fun k =>
    (freqs.get! (k + 1) - freqs.get! k) == ((baseFreq : Rat) / (den : Rat)))

theorem finite_acoustic_n13_summary :
    ns.length = 13 ∧
    freqs.length = 13 ∧
    freqs.get! 0 = (432 : Rat) / 13 ∧
    freqs.get! 9 = (4320 : Rat) / 13 ∧
    freqs.get! 12 = (432 : Rat) ∧
    allScaledIdentity = true ∧
    constantStep = true := by
  native_decide

end AcousticN13Prediction
