import Mathlib

import Universal_Ticks_Theorem
import Frobenius_Emergence_Theorem
import J_Function_Coefficient_Theorem

/-!
# Moonshine in (Log, Mod) Coordinates (Exact, Discrete)

This file reframes the already-proved Moonshine anchor

`c₁ = 47*59*71 + 1 = 196884`

into the repo's *scale-invariant* coordinate language:

* **log axis**: `decade` and `leadingBlock` (base-10, exact `Nat.log`),
* **cycle axis**: residues mod `13` (exact `Nat.%` / `Nat.ModEq`).

Nothing here uses floating-point or arbitrary decimal approximations.
-/

namespace MoonshineLogMod

open UniversalTicks

/-- The canonical Monster / Moonshine anchor as a natural number. -/
def c1Nat : Nat := 47 * 59 * 71 + 1

theorem c1Nat_value : c1Nat = 196884 := by
  native_decide

theorem c1Nat_decade : decade c1Nat = 5 := by
  -- `196884` lies in `[10^5, 10^6)`, hence decade = 5.
  native_decide

theorem c1Nat_leadingBlock : leadingBlock c1Nat = 1 := by
  -- `leadingBlock 196884 = 196884 / 10^5 = 1`.
  native_decide

/-!
## The next coefficient `c₂` in the same coordinates

Unlike `c₁`, the repo does not (yet) give a simple "product + 1" structural formula for `c₂`.
But we can still express its **exact** log/mod coordinates without floats.
-/

/-- The next j-function coefficient `c₂`, as a natural number. -/
def c2Nat : Nat :=
  Int.natAbs (JFunctionCoefficient.jCoefficient 2)

theorem c2Nat_value : c2Nat = 21493760 := by
  native_decide

theorem c2Nat_decade : decade c2Nat = 7 := by
  native_decide

theorem c2Nat_leadingBlock : leadingBlock c2Nat = 2 := by
  native_decide

theorem c2Nat_mod13 : c2Nat % 13 = 2 := by
  native_decide

/-- The next j-function coefficient `c₃`, as a natural number. -/
def c3Nat : Nat :=
  Int.natAbs (JFunctionCoefficient.jCoefficient 3)

theorem c3Nat_value : c3Nat = 864299970 := by
  native_decide

theorem c3Nat_decade : decade c3Nat = 8 := by
  native_decide

theorem c3Nat_leadingBlock : leadingBlock c3Nat = 8 := by
  native_decide

theorem c3Nat_mod13 : c3Nat % 13 = 1 := by
  native_decide

/-- The next j-function coefficient `c₄`, as a natural number. -/
def c4Nat : Nat :=
  Int.natAbs (JFunctionCoefficient.jCoefficient 4)

theorem c4Nat_value : c4Nat = 20245856256 := by
  native_decide

theorem c4Nat_decade : decade c4Nat = 10 := by
  native_decide

theorem c4Nat_leadingBlock : leadingBlock c4Nat = 2 := by
  native_decide

theorem c4Nat_mod13 : c4Nat % 13 = 2 := by
  native_decide

/-- The next j-function coefficient `c₅`, as a natural number. -/
def c5Nat : Nat :=
  Int.natAbs (JFunctionCoefficient.jCoefficient 5)

theorem c5Nat_value : c5Nat = 333202640600 := by
  native_decide

theorem c5Nat_decade : decade c5Nat = 11 := by
  native_decide

theorem c5Nat_leadingBlock : leadingBlock c5Nat = 3 := by
  native_decide

theorem c5Nat_mod13 : c5Nat % 13 = 11 := by
  native_decide

/-- The next j-function coefficient `c₆`, as a natural number. -/
def c6Nat : Nat :=
  Int.natAbs (JFunctionCoefficient.jCoefficient 6)

theorem c6Nat_value : c6Nat = 4252023300096 := by
  native_decide

theorem c6Nat_decade : decade c6Nat = 12 := by
  native_decide

theorem c6Nat_leadingBlock : leadingBlock c6Nat = 4 := by
  native_decide

theorem c6Nat_mod13 : c6Nat % 13 = 0 := by
  native_decide

/-- The next j-function coefficient `c₇`, as a natural number. -/
def c7Nat : Nat :=
  Int.natAbs (JFunctionCoefficient.jCoefficient 7)

theorem c7Nat_value : c7Nat = 44656994071935 := by
  native_decide

theorem c7Nat_decade : decade c7Nat = 13 := by
  native_decide

theorem c7Nat_leadingBlock : leadingBlock c7Nat = 4 := by
  native_decide

theorem c7Nat_mod13 : c7Nat % 13 = 11 := by
  native_decide

/-- The next j-function coefficient `c₈`, as a natural number. -/
def c8Nat : Nat :=
  Int.natAbs (JFunctionCoefficient.jCoefficient 8)

theorem c8Nat_value : c8Nat = 401490886656000 := by
  native_decide

theorem c8Nat_decade : decade c8Nat = 14 := by
  native_decide

theorem c8Nat_leadingBlock : leadingBlock c8Nat = 4 := by
  native_decide

theorem c8Nat_mod13 : c8Nat % 13 = 11 := by
  native_decide

/-- The next j-function coefficient `c₉`, as a natural number. -/
def c9Nat : Nat :=
  Int.natAbs (JFunctionCoefficient.jCoefficient 9)

theorem c9Nat_value : c9Nat = 3176440179718275 := by
  native_decide

theorem c9Nat_decade : decade c9Nat = 15 := by
  native_decide

theorem c9Nat_leadingBlock : leadingBlock c9Nat = 3 := by
  native_decide

theorem c9Nat_mod13 : c9Nat % 13 = 2 := by
  native_decide

/-- The next j-function coefficient `c₁₀`, as a natural number. -/
def c10Nat : Nat :=
  Int.natAbs (JFunctionCoefficient.jCoefficient 10)

theorem c10Nat_value : c10Nat = 22564878527060000 := by
  native_decide

theorem c10Nat_decade : decade c10Nat = 16 := by
  native_decide

theorem c10Nat_leadingBlock : leadingBlock c10Nat = 2 := by
  native_decide

theorem c10Nat_mod13 : c10Nat % 13 = 1 := by
  native_decide

/-!
## Summary: `c₂..c₁₀` in (log, mod) coordinates

This packages the individual coordinate lemmas into one conjunction so the
`context/UFRF_UNIFIED_PROOF.lean` spine can reference a single statement.
-/

theorem c2_to_c10_logmod_summary :
    (c2Nat = 21493760 ∧ decade c2Nat = 7 ∧ leadingBlock c2Nat = 2 ∧ c2Nat % 13 = 2)
      ∧ (c3Nat = 864299970 ∧ decade c3Nat = 8 ∧ leadingBlock c3Nat = 8 ∧ c3Nat % 13 = 1)
      ∧ (c4Nat = 20245856256 ∧ decade c4Nat = 10 ∧ leadingBlock c4Nat = 2 ∧ c4Nat % 13 = 2)
      ∧ (c5Nat = 333202640600 ∧ decade c5Nat = 11 ∧ leadingBlock c5Nat = 3 ∧ c5Nat % 13 = 11)
      ∧ (c6Nat = 4252023300096 ∧ decade c6Nat = 12 ∧ leadingBlock c6Nat = 4 ∧ c6Nat % 13 = 0)
      ∧ (c7Nat = 44656994071935 ∧ decade c7Nat = 13 ∧ leadingBlock c7Nat = 4 ∧ c7Nat % 13 = 11)
      ∧ (c8Nat = 401490886656000 ∧ decade c8Nat = 14 ∧ leadingBlock c8Nat = 4 ∧ c8Nat % 13 = 11)
      ∧ (c9Nat = 3176440179718275 ∧ decade c9Nat = 15 ∧ leadingBlock c9Nat = 3 ∧ c9Nat % 13 = 2)
      ∧ (c10Nat = 22564878527060000 ∧ decade c10Nat = 16 ∧ leadingBlock c10Nat = 2 ∧ c10Nat % 13 = 1) := by
  -- Helper: `a ∧ b ∧ c ∧ d` parses as `a ∧ (b ∧ (c ∧ d))`.
  have pack4 {a b c d : Prop} (ha : a) (hb : b) (hc : c) (hd : d) : a ∧ b ∧ c ∧ d :=
    ⟨ha, ⟨hb, ⟨hc, hd⟩⟩⟩
  refine ⟨pack4 c2Nat_value c2Nat_decade c2Nat_leadingBlock c2Nat_mod13, ?_⟩
  refine ⟨pack4 c3Nat_value c3Nat_decade c3Nat_leadingBlock c3Nat_mod13, ?_⟩
  refine ⟨pack4 c4Nat_value c4Nat_decade c4Nat_leadingBlock c4Nat_mod13, ?_⟩
  refine ⟨pack4 c5Nat_value c5Nat_decade c5Nat_leadingBlock c5Nat_mod13, ?_⟩
  refine ⟨pack4 c6Nat_value c6Nat_decade c6Nat_leadingBlock c6Nat_mod13, ?_⟩
  refine ⟨pack4 c7Nat_value c7Nat_decade c7Nat_leadingBlock c7Nat_mod13, ?_⟩
  refine ⟨pack4 c8Nat_value c8Nat_decade c8Nat_leadingBlock c8Nat_mod13, ?_⟩
  refine ⟨pack4 c9Nat_value c9Nat_decade c9Nat_leadingBlock c9Nat_mod13, ?_⟩
  exact pack4 c10Nat_value c10Nat_decade c10Nat_leadingBlock c10Nat_mod13

/-!
## Mod-13 flip signature for `c₁`

The Monster triple positions are (8,7,6) mod 13 in list order `[47,59,71]`.

From those positions alone, the product-plus-one satisfies:

`47*59*71 + 1 ≡ -1 (mod 13)`.

This matches the repo's `mod 13` flip (`10^3 ≡ -1`) as a purely arithmetic consequence
of the bracketing positions.
-/

private theorem product_plus_one_mod13_of_positions_876 {a b c : Nat}
    (ha : a % 13 = 8) (hb : b % 13 = 7) (hc : c % 13 = 6) :
    (a * b * c + 1) % 13 = 12 := by
  -- Convert `%` equalities into `Nat.ModEq` hypotheses.
  have ha' : a ≡ 8 [MOD 13] := by
    unfold Nat.ModEq
    simp [ha]
  have hb' : b ≡ 7 [MOD 13] := by
    unfold Nat.ModEq
    simp [hb]
  have hc' : c ≡ 6 [MOD 13] := by
    unfold Nat.ModEq
    simp [hc]

  -- Multiply the congruences and add 1.
  have hab : a * b ≡ 8 * 7 [MOD 13] := Nat.ModEq.mul ha' hb'
  have habc : a * b * c ≡ (8 * 7) * 6 [MOD 13] := Nat.ModEq.mul hab hc'
  have habc1 : a * b * c + 1 ≡ (8 * 7) * 6 + 1 [MOD 13] :=
    Nat.ModEq.add_right 1 habc

  -- Close the constant computation.
  have hconst : (8 * 7) * 6 + 1 ≡ 12 [MOD 13] := by
    native_decide

  -- Unfold `ModEq` to a `%` equality.
  have : a * b * c + 1 ≡ 12 [MOD 13] := habc1.trans hconst
  -- `Nat.ModEq` is definitional as equality of `%`.
  simpa [Nat.ModEq] using this

theorem c1Nat_mod13_flip : c1Nat % 13 = 12 := by
  -- Use the Monster mod-13 positions and the general lemma above.
  rcases FrobeniusEmergence.monster_mod13_positions with ⟨h47, h59, h71⟩
  -- `c1Nat` is `47*59*71+1` in the same order as the position theorem.
  unfold c1Nat
  exact product_plus_one_mod13_of_positions_876 (a := 47) (b := 59) (c := 71) h47 h59 h71

/-- Restate the flip signature in `Nat.ModEq` form: `c₁ ≡ -1 (mod 13)`. -/
theorem c1Nat_modEq_neg_one : c1Nat ≡ 12 [MOD 13] := by
  -- `12` is `-1` mod 13 in `Nat` residue form.
  simp [Nat.ModEq, c1Nat_mod13_flip]

/-!
## Convenience corollaries for the literal coefficient value `196884`

These are the same facts restated without the intermediate `c1Nat` definition,
so the unified spine can reference the number directly.
-/

theorem c1_decade_196884 : decade 196884 = 5 := by
  native_decide

theorem c1_leadingBlock_196884 : leadingBlock 196884 = 1 := by
  native_decide

theorem c1_mod13_flip_196884 : (196884 : Nat) % 13 = 12 := by
  rw [← c1Nat_value]
  exact c1Nat_mod13_flip

end MoonshineLogMod
