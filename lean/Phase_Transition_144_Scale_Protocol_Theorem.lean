import Mathlib
import GetBangCompat

/-!
# Phase Transition 144-Scale Protocol (Finite Deterministic Bridge)

Finite arithmetic bridge for `UFRF3.1/08-ufrf-predictions-tests.md` §6.1 claim subset,
augmented with an exact mantissa bridge and seed staircase anchors:

- pressure anchor: `144`,
- temperature anchors: `144, 1440, 14400`,
- scale ladder: `144 * 10^n`,
- mantissa bridge: `(36/25) * 10^(n+2) = 144 * 10^n`,
- staircase anchors: `4 -> 14 -> 144 -> 144000`.

Mirrors `phase_transition_144_scale_protocol.py`.
-/

namespace PhaseTransition144ScalePrediction

def base : Nat := 144
def pressure : Nat := 144
def temps : List Nat := [144, 1440, 14400]
def scaleLadder : List Nat := [144, 1440, 14400, 144000]
def seedStair : List Nat := [4, 14, 144, 144000]

def mantissa : Rat := (36 : Rat) / 25
def mantissaAt (k : Nat) : Rat := mantissa * (10 : Rat) ^ k

def tempsRatio10 : Bool :=
  (List.range 2).all (fun k => temps.get! (k + 1) = 10 * temps.get! k)

def bridgeOk : Bool :=
  (List.range 4).all (fun n => mantissaAt (n + 2) == (scaleLadder.get! n : Rat))

theorem finite_phase_transition_144_scale_summary :
    pressure = base ∧
    temps.length = 3 ∧
    tempsRatio10 = true ∧
    scaleLadder.length = 4 ∧
    bridgeOk = true ∧
    mantissaAt 2 = (144 : Rat) ∧
    mantissaAt 3 = (1440 : Rat) ∧
    mantissaAt 4 = (14400 : Rat) ∧
    mantissaAt 5 = (144000 : Rat) ∧
    seedStair.get! 1 = seedStair.get! 0 + 10 ∧
    seedStair.get! 2 = seedStair.get! 1 * 10 + 4 ∧
    seedStair.get! 3 = seedStair.get! 2 * 1000 := by
  native_decide

end PhaseTransition144ScalePrediction
