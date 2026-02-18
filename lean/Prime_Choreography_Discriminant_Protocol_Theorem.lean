import Mathlib
import GetBangCompat

/-!
# Prime-Choreography Discriminant Protocol (Finite, Deterministic)

Protocol mirror for:
- `prime_choreography_discriminant_protocol.py`
- `prime_choreography_discriminant_results.json`

Scope:
- finite discriminant metrics that separate the known degenerate uniform control
  from multi-period superpositions,
- no universal theorem claims.
-/

namespace PrimeChoreographyDiscriminantProtocol

def base : Nat := 13
def nSamples : Nat := 715
def maxLag : Nat := 143
def topK : Nat := 15

def primesUFRF : List Nat := [1, 3, 5, 7, 11]
def primesConventional : List Nat := [2, 3, 5, 7, 11]
def primesUniform : List Nat := [1, 1, 1, 1, 1]
def primesNonprimeSwap : List Nat := [1, 3, 5, 7, 9]

def mult13LagsUFRF : List Nat := [13, 78, 117, 26, 39, 130, 143, 65, 91, 52, 104]
def mult13LagsConventional : List Nat := [78, 13, 26, 130, 52, 104, 117, 39, 143, 65, 91]
def mult13LagsUniform : List Nat := [13, 26, 39, 52, 65, 78, 91, 104, 117, 130, 143]
def mult13LagsNonprimeSwap : List Nat := [117, 13, 78, 130, 39, 26, 143, 91, 104, 65, 52]

def inversionCount : List Nat → Nat
  | [] => 0
  | x :: xs =>
      (xs.foldl (fun acc y => acc + (if x > y then 1 else 0)) 0) + inversionCount xs

def strictlyAscending : List Nat → Bool
  | [] => true
  | [_] => true
  | x :: y :: xs => (x < y) && strictlyAscending (y :: xs)

def maxInversionCount (xs : List Nat) : Nat :=
  xs.length * (xs.length - 1) / 2

def uniformIsDegenerate : Bool :=
  strictlyAscending mult13LagsUniform && inversionCount mult13LagsUniform == 0

def allNonuniformAreScrambled : Bool :=
  ((strictlyAscending mult13LagsUFRF = false) && inversionCount mult13LagsUFRF > 0)
  && ((strictlyAscending mult13LagsConventional = false) && inversionCount mult13LagsConventional > 0)
  && ((strictlyAscending mult13LagsNonprimeSwap = false) && inversionCount mult13LagsNonprimeSwap > 0)

def ufrfUniformTop13Alias : Bool :=
  mult13LagsUFRF.getD 0 0 == 13 && mult13LagsUniform.getD 0 0 == 13

def ufrfUniformInversionGap : Int :=
  (inversionCount mult13LagsUFRF : Int) - (inversionCount mult13LagsUniform : Int)

def conventionalUniformInversionGap : Int :=
  (inversionCount mult13LagsConventional : Int) - (inversionCount mult13LagsUniform : Int)

def nonprimeUniformInversionGap : Int :=
  (inversionCount mult13LagsNonprimeSwap : Int) - (inversionCount mult13LagsUniform : Int)

def ufrfConventionalEqualInversion : Bool :=
  inversionCount mult13LagsUFRF == inversionCount mult13LagsConventional

theorem prime_choreography_discriminant_summary :
    base = 13
    ∧ nSamples = 715
    ∧ maxLag = 143
    ∧ topK = 15
    ∧ primesUFRF = [1, 3, 5, 7, 11]
    ∧ primesConventional = [2, 3, 5, 7, 11]
    ∧ primesUniform = [1, 1, 1, 1, 1]
    ∧ primesNonprimeSwap = [1, 3, 5, 7, 9]
    ∧ mult13LagsUFRF = [13, 78, 117, 26, 39, 130, 143, 65, 91, 52, 104]
    ∧ mult13LagsConventional = [78, 13, 26, 130, 52, 104, 117, 39, 143, 65, 91]
    ∧ mult13LagsUniform = [13, 26, 39, 52, 65, 78, 91, 104, 117, 130, 143]
    ∧ mult13LagsNonprimeSwap = [117, 13, 78, 130, 39, 26, 143, 91, 104, 65, 52]
    ∧ maxInversionCount mult13LagsUFRF = 55
    ∧ maxInversionCount mult13LagsConventional = 55
    ∧ maxInversionCount mult13LagsUniform = 55
    ∧ maxInversionCount mult13LagsNonprimeSwap = 55
    ∧ inversionCount mult13LagsUFRF = 20
    ∧ inversionCount mult13LagsConventional = 20
    ∧ inversionCount mult13LagsUniform = 0
    ∧ inversionCount mult13LagsNonprimeSwap = 28
    ∧ strictlyAscending mult13LagsUFRF = false
    ∧ strictlyAscending mult13LagsConventional = false
    ∧ strictlyAscending mult13LagsUniform = true
    ∧ strictlyAscending mult13LagsNonprimeSwap = false
    ∧ mult13LagsUFRF.getD 0 0 = 13
    ∧ mult13LagsConventional.getD 0 0 = 78
    ∧ mult13LagsUniform.getD 0 0 = 13
    ∧ mult13LagsNonprimeSwap.getD 0 0 = 117
    ∧ uniformIsDegenerate = true
    ∧ allNonuniformAreScrambled = true
    ∧ ufrfUniformTop13Alias = true
    ∧ ufrfUniformInversionGap = 20
    ∧ conventionalUniformInversionGap = 20
    ∧ nonprimeUniformInversionGap = 28
    ∧ ufrfConventionalEqualInversion = true := by
  native_decide

end PrimeChoreographyDiscriminantProtocol
