import Mathlib
import GetBangCompat

/-!
# Sub-magic Multiples-of-13 Prediction Protocol (Finite Deterministic Bridge)

Finite arithmetic bridge for `UFRF3.1/08-ufrf-predictions-tests.md` §1.2 claim subset:

`[26, 39, 52, 65, 78, 91, 104, 117]`.

Mirrors `submagic_multiples13_prediction_protocol.py`.
-/

namespace SubmagicMultiples13Prediction

def values : List Nat := [26, 39, 52, 65, 78, 91, 104, 117]

def allMultiples13 : Bool :=
  values.all (fun n => n % 13 == 0)

def constantStep13 : Bool :=
  (List.range 7).all (fun k => values.get! (k + 1) - values.get! k == 13)

theorem finite_submagic_multiples13_summary :
    values.length = 8 ∧
    values.get! 0 = 2 * 13 ∧
    values.get! 7 = 9 * 13 ∧
    allMultiples13 = true ∧
    constantStep13 = true := by
  native_decide

end SubmagicMultiples13Prediction
