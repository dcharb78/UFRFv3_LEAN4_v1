import Mathlib
import GetBangCompat

/-!
# Protein Folding Positions Protocol (Finite Deterministic Bridge)

Finite arithmetic bridge for `UFRF3.1/08-ufrf-predictions-tests.md` §4.2 claim subset:

preferred positions `3.6, 7.2, 10.5` encoded exactly as rationals
`18/5, 36/5, 21/2`.

Mirrors `protein_folding_positions_protocol.py`.
-/

namespace ProteinFoldingPositionsPrediction

def positions : List Rat := [(18 : Rat) / 5, (36 : Rat) / 5, (21 : Rat) / 2]
def rest : Rat := 10
def cycleLen : Rat := 13

def ordered : Bool := positions.get! 0 < positions.get! 1 && positions.get! 1 < positions.get! 2
def secondIsDoubleFirst : Bool := positions.get! 1 == 2 * positions.get! 0
def thirdMinusRestIsHalf : Bool := positions.get! 2 - rest == (1 : Rat) / 2
def allInsideCycle13 : Bool := positions.all (fun p => (0 : Rat) < p && p < cycleLen)

theorem finite_protein_folding_positions_summary :
    positions.length = 3 ∧
    positions.get! 0 = (18 : Rat) / 5 ∧
    positions.get! 1 = (36 : Rat) / 5 ∧
    positions.get! 2 = (21 : Rat) / 2 ∧
    ordered = true ∧
    secondIsDoubleFirst = true ∧
    thirdMinusRestIsHalf = true ∧
    allInsideCycle13 = true := by
  native_decide

end ProteinFoldingPositionsPrediction
