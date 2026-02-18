import Mathlib

/-!
# Network 137-Threshold Protocol (Finite Deterministic Bridge)

Finite arithmetic bridge for `UFRF3.1/08-ufrf-predictions-tests.md` §3.1 claim subset:

- threshold `137`,
- local neighboring 13-multiples `130` and `143`,
- distance to `144` anchor is `7`.

Mirrors `network_137_threshold_protocol.py`.
-/

namespace Network137ThresholdPrediction

def threshold : Nat := 137
def lower : Nat := 13 * 10
def upper : Nat := 13 * 11
def scaleAnchor : Nat := 144

theorem finite_network_137_threshold_summary :
    lower = 130 ∧
    upper = 143 ∧
    lower < threshold ∧
    threshold < upper ∧
    threshold - lower = 7 ∧
    upper - threshold = 6 ∧
    scaleAnchor - threshold = 7 ∧
    Nat.Prime threshold := by
  native_decide

end Network137ThresholdPrediction
