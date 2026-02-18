import Mathlib
import GetBangCompat

/-!
# Musical Harmony 13/n Protocol (Finite Deterministic Bridge)

Finite arithmetic bridge for `UFRF3.1/08-ufrf-predictions-tests.md` §7.2 claim subset:

frequency-ratio ladder `13/n` for `n = 1..13`.

Mirrors `musical_harmony_13_over_n_protocol.py`.
-/

namespace MusicalHarmony13OverNPrediction

def ns : List Nat := List.range' 1 13

def ratio (n : Nat) : Rat :=
  (13 : Rat) / (n : Rat)

def ratios : List Rat := ns.map ratio

def allTimesNEqual13 : Bool :=
  ns.all (fun n => ((n : Rat) * ratio n) == (13 : Rat))

def strictlyDecreasing : Bool :=
  (List.range 12).all (fun k => ratios.get! k > ratios.get! (k + 1))

theorem finite_musical_harmony_13_over_n_summary :
    ns.length = 13 ∧
    ratios.length = 13 ∧
    ratios.get! 0 = (13 : Rat) ∧
    ratios.get! 6 = (13 : Rat) / 7 ∧
    ratios.get! 9 = (13 : Rat) / 10 ∧
    ratios.get! 12 = (1 : Rat) ∧
    allTimesNEqual13 = true ∧
    strictlyDecreasing = true := by
  native_decide

end MusicalHarmony13OverNPrediction
