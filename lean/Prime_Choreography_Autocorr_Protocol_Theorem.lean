import Mathlib

/-!
# Prime Choreography Autocorrelation Protocol (Finite, Deterministic)

Protocol-level finite statement mirroring:

- `prime_choreography_autocorr_protocol.py`

This is an evidence-lane artifact. It does **not** claim a universal theorem about primes.
It records the exact outputs of a fixed, deterministic model (piecewise waveform + prime-scaled
periods) so the repo can track changes and avoid silent drift.
-/

namespace PrimeChoreographyAutocorrPrediction

def base : Nat := 13
def nSamples : Nat := 715
def maxLag : Nat := 143
def topK : Nat := 15

def primesUFRF : List Nat := [1, 3, 5, 7, 11]
def primesConventional : List Nat := [2, 3, 5, 7, 11]
def primesUniform : List Nat := [1, 1, 1, 1, 1]
def primesNonprimeSwap : List Nat := [1, 3, 5, 7, 9]

/-- Simple inversion count (Kendall-style): how far a list is from increasing order. -/
def inversionCount : List Nat → Nat
  | [] => 0
  | x :: xs =>
      (xs.foldl (fun acc y => acc + (if x > y then 1 else 0)) 0) + inversionCount xs

def topLagsGeBaseUFRF : List Nat :=
  [13, 14, 15, 78, 117, 26, 79, 77, 118, 16, 39, 130, 25, 116, 27]

def topLagsGeBaseConventional : List Nat :=
  [78, 77, 79, 13, 76, 25, 26, 80, 24, 14, 130, 27, 129, 23, 15]

def mult13LagsSortedUFRF : List Nat :=
  [13, 78, 117, 26, 39, 130, 143, 65, 91, 52, 104]

def mult13LagsSortedConventional : List Nat :=
  [78, 13, 26, 130, 52, 104, 117, 39, 143, 65, 91]

def mult13LagsSortedUniform : List Nat :=
  [13, 26, 39, 52, 65, 78, 91, 104, 117, 130, 143]

def mult13LagsSortedNonprimeSwap : List Nat :=
  [117, 13, 78, 130, 39, 26, 143, 91, 104, 65, 52]

theorem prime_choreography_autocorr_summary :
    base = 13
    ∧ nSamples = 715
    ∧ maxLag = 143
    ∧ topK = 15
    ∧ primesUFRF = [1, 3, 5, 7, 11]
    ∧ primesConventional = [2, 3, 5, 7, 11]
    ∧ primesUniform = [1, 1, 1, 1, 1]
    ∧ primesNonprimeSwap = [1, 3, 5, 7, 9]
    ∧ topLagsGeBaseUFRF =
        [13, 14, 15, 78, 117, 26, 79, 77, 118, 16, 39, 130, 25, 116, 27]
    ∧ topLagsGeBaseConventional =
        [78, 77, 79, 13, 76, 25, 26, 80, 24, 14, 130, 27, 129, 23, 15]
    ∧ mult13LagsSortedUFRF =
        [13, 78, 117, 26, 39, 130, 143, 65, 91, 52, 104]
    ∧ mult13LagsSortedConventional =
        [78, 13, 26, 130, 52, 104, 117, 39, 143, 65, 91]
    ∧ mult13LagsSortedUniform =
        [13, 26, 39, 52, 65, 78, 91, 104, 117, 130, 143]
    ∧ mult13LagsSortedNonprimeSwap =
        [117, 13, 78, 130, 39, 26, 143, 91, 104, 65, 52]
    ∧ inversionCount mult13LagsSortedUFRF = 20
    ∧ inversionCount mult13LagsSortedConventional = 20
    ∧ inversionCount mult13LagsSortedUniform = 0
    ∧ inversionCount mult13LagsSortedNonprimeSwap = 28
    ∧ mult13LagsSortedUFRF.get? 0 = some 13
    ∧ mult13LagsSortedConventional.get? 0 = some 78
    ∧ mult13LagsSortedUniform.get? 0 = some 13
    ∧ mult13LagsSortedNonprimeSwap.get? 0 = some 117 := by
  native_decide

end PrimeChoreographyAutocorrPrediction
