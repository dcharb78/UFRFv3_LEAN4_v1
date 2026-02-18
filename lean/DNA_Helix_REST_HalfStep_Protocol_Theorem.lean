import Mathlib

/-!
# DNA Helix REST-HalfStep Protocol (Finite Deterministic Bridge)

Finite arithmetic bridge for `UFRF3.1/08-ufrf-predictions-tests.md` §4.1 claim subset:

- REST position = `10`
- helical turns = `10.5 = 21/2`
- cycle position = `13`

Mirrors `dna_helix_rest_halfstep_protocol.py`.
-/

namespace DNAHelixRestHalfStepPrediction

def restPos : Rat := 10
def helixTurns : Rat := (21 : Rat) / 2
def cyclePos : Rat := 13

def deltaFromRest : Rat := helixTurns - restPos
def deltaToCycleEnd : Rat := cyclePos - helixTurns

theorem finite_dna_helix_rest_halfstep_summary :
    helixTurns = (21 : Rat) / 2 ∧
    deltaFromRest = (1 : Rat) / 2 ∧
    deltaToCycleEnd = (5 : Rat) / 2 ∧
    restPos < helixTurns ∧
    helixTurns < cyclePos := by
  native_decide

end DNAHelixRestHalfStepPrediction
