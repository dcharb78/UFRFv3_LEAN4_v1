import Mathlib
import GetBangCompat

/-!
# Tc sqrt(phi)-Enhancement Protocol (Finite Deterministic Bridge)

Finite arithmetic bridge for `UFRF3.1/08-ufrf-predictions-tests.md` §2.2 claim subset:

`Tc_optimal = Tc_base * 1.272`.

We encode `1.272` as the exact ratio `159/125`.
Mirrors `tc_sqrtphi_enhancement_protocol.py`.
-/

namespace TcSqrtPhiEnhancementPrediction

def enhancement : Rat := (159 : Rat) / 125
def baselineTcs : List Nat := [50, 100, 125, 200, 250, 300]
def enhancedTcs : List Rat := baselineTcs.map (fun b => (b : Rat) * enhancement)

def allEnhancedAboveBase : Bool :=
  (List.range baselineTcs.length).all (fun k => enhancedTcs.get! k > (baselineTcs.get! k : Rat))

def allScaledBySameRatio : Bool :=
  (List.range baselineTcs.length).all (fun k => enhancedTcs.get! k * (125 : Rat) == (baselineTcs.get! k : Rat) * (159 : Rat))

theorem finite_tc_sqrtphi_enhancement_summary :
    baselineTcs.length = 6 ∧
    enhancedTcs.length = 6 ∧
    enhancement = (159 : Rat) / 125 ∧
    enhancedTcs.get! 2 = (159 : Rat) ∧
    enhancedTcs.get! 4 = (318 : Rat) ∧
    allEnhancedAboveBase = true ∧
    allScaledBySameRatio = true := by
  native_decide

end TcSqrtPhiEnhancementPrediction
