/-
# Riemann Zero / A-zero Lattice Distance (Computable Check)

This file computes distances from the first 100 nontrivial Riemann zeros (gamma values)
to the "A-zero lattices" for:

- UFRF generators: [3, 5, 7, 11, 13]
- Monster generators: [47, 59, 71]

Key engineering note:
the lattice must be populated up to `gamma <= gammaMax` for each generator.
Using a fixed small `maxN` truncates the lattice badly for large generators and can
produce misleadingly large distances.

We use `Float` so all results are computable and can be validated with `native_decide`.
-/

import Mathlib

namespace RiemannZeroExclusion

-- ============================================================
-- Data: first 100 Riemann zeros (imaginary parts)
-- ============================================================

def riemannZeros : List Float := [
  14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
  37.586178, 40.918719, 43.327073, 48.005151, 49.773832,
  52.970321, 56.446248, 59.347044, 60.831779, 65.112544,
  67.079811, 69.546402, 72.067158, 75.704691, 77.144840,
  79.337375, 82.910381, 84.735493, 87.425275, 88.809111,
  92.491899, 94.651344, 95.870634, 98.831194, 101.317851,
  103.725538, 105.446623, 107.168611, 111.029536, 111.874659,
  114.320221, 116.226680, 118.790783, 121.370125, 122.946829,
  124.256818, 127.516684, 129.578704, 131.087688, 133.497737,
  134.756509, 138.116042, 139.736208, 141.123707, 143.111845,
  146.000982, 147.422765, 150.053520, 150.925257, 153.024693,
  156.112909, 157.597591, 158.849988, 161.188964, 163.030709,
  165.537069, 167.184439, 169.094515, 169.911977, 173.536502,
  174.754191, 176.441434, 178.377407, 179.916484, 182.207078,
  184.874468, 185.598783, 187.228922, 189.416408, 192.026656,
  193.079726, 195.265396, 196.876481, 198.015309, 201.264751,
  202.493594, 204.178642, 205.394702, 207.906258, 209.576509,
  211.690862, 213.347919, 214.547044, 216.169538, 219.067596,
  220.714918, 221.430705, 224.007000, 224.962612, 227.421444,
  229.337446, 231.249188, 233.693404, 236.524229, 237.584284
]

-- ============================================================
-- A-zero lattice (computable, Float-based)
-- ============================================================

def ufrfGenerators : List Nat := [3, 5, 7, 11, 13]
def monsterGenerators : List Nat := [47, 59, 71]

-- We pin pi as a Float literal (IEEE-754 double) for deterministic computation.
def pi : Float := 3.141592653589793

def gammaMax : Float := 250.0

def dedupSorted : List Float → List Float
  | [] => []
  | x :: xs => x :: go x xs
where
  go (prev : Float) : List Float → List Float
    | [] => []
    | y :: ys =>
        if y == prev then
          go prev ys
        else
          y :: go y ys

/-- A-zero lattice points: gamma = 2 * n * pi / d, for each generator d and n >= 1. -/
def aZeroLattice (generators : List Nat) (maxN : Nat) (gammaMax : Float) : List Float :=
  let raw :=
    generators.flatMap (fun d =>
      (List.range' 1 maxN).filterMap (fun n =>
        let gamma := (Float.ofNat (2 * n) * pi) / Float.ofNat d
        if gamma ≤ gammaMax then some gamma else none
      ))
  -- Sort + dedup to match the "set" behavior in the Python analysis.
  dedupSorted (raw.mergeSort (fun a b => a ≤ b))

-- `maxN` must be large enough so that all points with gamma <= gammaMax are included.
def ufrfLattice : List Float := aZeroLattice ufrfGenerators 600 gammaMax
def monsterLattice : List Float := aZeroLattice monsterGenerators 3000 gammaMax

-- Sanity checks: larger `maxN` values should not change the lattice in `[0, gammaMax]`.
-- (If these fail, it indicates truncation is still active and the reported distances are not stable.)
def ufrfLatticeLarge : List Float := aZeroLattice ufrfGenerators 800 gammaMax
def monsterLatticeLarge : List Float := aZeroLattice monsterGenerators 4000 gammaMax

-- "Truncation witness": smaller `maxN` values *do* truncate the lattice for the chosen `gammaMax`.
-- These are used to demonstrate, inside Lean, that inadequate truncation can inflate nearest-lattice
-- distances and mislead downstream interpretations.
def ufrfLatticeTiny : List Float := aZeroLattice ufrfGenerators 200 gammaMax
def monsterLatticeTiny : List Float := aZeroLattice monsterGenerators 500 gammaMax

-- ============================================================
-- Distances and summary stats
-- ============================================================

/-- One step of the nearest-lattice-distance fold (min update). -/
def distStep (gamma : Float) (minDist p : Float) : Float :=
  let dist := Float.abs (gamma - p)
  if dist < minDist then dist else minDist

/-- Distance from `gamma` to the nearest lattice point in `lattice`. -/
def distanceToLattice (gamma : Float) (lattice : List Float) : Float :=
  lattice.foldl (distStep gamma) 1e100

def ufrfDistances : List Float := riemannZeros.map (fun g => distanceToLattice g ufrfLattice)
def monsterDistances : List Float := riemannZeros.map (fun g => distanceToLattice g monsterLattice)

def ufrfDistancesLarge : List Float :=
  riemannZeros.map (fun g => distanceToLattice g ufrfLatticeLarge)

def monsterDistancesLarge : List Float :=
  riemannZeros.map (fun g => distanceToLattice g monsterLatticeLarge)

def ufrfDistancesTiny : List Float :=
  riemannZeros.map (fun g => distanceToLattice g ufrfLatticeTiny)

def monsterDistancesTiny : List Float :=
  riemannZeros.map (fun g => distanceToLattice g monsterLatticeTiny)

def mean (xs : List Float) : Float :=
  xs.foldl (fun acc x => acc + x) 0 / Float.ofNat xs.length

def ufrfMean : Float := mean ufrfDistances
def monsterMean : Float := mean monsterDistances

def ufrfMeanLarge : Float := mean ufrfDistancesLarge
def monsterMeanLarge : Float := mean monsterDistancesLarge

def ufrfMeanTiny : Float := mean ufrfDistancesTiny
def monsterMeanTiny : Float := mean monsterDistancesTiny

def within (t : Float) (xs : List Float) : Nat :=
  (xs.filter (fun x => x < t)).length

def ufrfWithin (t : Float) : Nat := within t ufrfDistances
def monsterWithin (t : Float) : Nat := within t monsterDistances

def ufrfWithinLarge (t : Float) : Nat := within t ufrfDistancesLarge
def monsterWithinLarge (t : Float) : Nat := within t monsterDistancesLarge

-- ============================================================
-- Lean-validated computed facts
-- ============================================================

theorem computed_stats :
  ufrfLattice.length = 1430 ∧
  monsterLattice.length = 6982 ∧
  monsterLattice.length > ufrfLattice.length ∧
  monsterMean < ufrfMean ∧
  ufrfWithin 0.05 = 53 ∧
  monsterWithin 0.05 = 100 := by
  native_decide

theorem lattice_truncation_stable :
  ufrfLatticeLarge.length = ufrfLattice.length ∧
  monsterLatticeLarge.length = monsterLattice.length ∧
  ufrfWithinLarge 0.05 = ufrfWithin 0.05 ∧
  monsterWithinLarge 0.05 = monsterWithin 0.05 ∧
  monsterMeanLarge < ufrfMeanLarge := by
  native_decide

/--
Truncation effect witness:

With too-small `maxN`, the A-zero lattices are truncated at this `gammaMax`, and
the computed mean nearest-lattice distances become larger.
-/
theorem lattice_truncation_inflates_mean :
  ufrfLatticeTiny.length < ufrfLattice.length ∧
  monsterLatticeTiny.length < monsterLattice.length ∧
  ufrfMean < ufrfMeanTiny ∧
  monsterMean < monsterMeanTiny := by
  native_decide

theorem monster_lattice_denser : monsterLattice.length > ufrfLattice.length :=
  computed_stats.2.2.1

theorem monster_mean_distance_smaller : monsterMean < ufrfMean :=
  computed_stats.2.2.2.1

end RiemannZeroExclusion
