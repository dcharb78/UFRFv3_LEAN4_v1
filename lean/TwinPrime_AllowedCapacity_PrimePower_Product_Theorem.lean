import TwinPrime_AllowedCapacity_Theorem
import TwinPrime_AllowedCapacity_CRT_List_Theorem
import Nat_Coprime_PrimePowers_Utilities
import Nat_Prime_Distinct_Coprime_Utilities

/-!
# Twin-Prime Allowed-Capacity for Products of Prime Powers (Mechanism Only)

This file synthesizes two already-certified mechanisms into a single exact capacity statement:

1. **Prime-power lifting** (p-adic digit split):
   For `p > 2`, at depth `k` there are exactly `(p-2)·p^k` residues mod `p^(k+1)` whose low digit
   mod `p` avoids `{0, -2}`.
2. **CRT multi-axis factorization** (pairwise-coprime list form):
   If moduli are pairwise coprime, residue classes modulo the product factor as a product of axes.

We still do **not** claim primes occupy these channels; we only count the channels.

No placeholders.
-/

namespace TwinPrimeAllowedCapacityPrimePowerProduct

open TwinPrimeAllowedCapacity
open TwinPrimeAllowedCapacityCRTList

/-! ## Prime-power axis bundle -/

structure PrimePow where
  p : Nat
  k : Nat
  hp : 2 < p

namespace PrimePow

def modulus (pp : PrimePow) : Nat := pp.p ^ (pp.k + 1)

instance (pp : PrimePow) : NeZero pp.p :=
  ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_two pp.hp)⟩

instance (pp : PrimePow) : NeZero pp.modulus := by
  -- `NeZero` is closed under powers in any `MonoidWithZero`.
  dsimp [PrimePow.modulus]
  infer_instance

/--
Axis-level allowed predicate on `ZMod (p^(k+1))`, defined by transporting the
`Fin (p^(k+1))` low-digit predicate through `ZMod.finEquiv`.
-/
def allowedPow (pp : PrimePow) (x : ZMod pp.modulus) : Prop :=
  TwinPrimeAllowedCapacity.AllowedResidue pp.p pp.k ((ZMod.finEquiv pp.modulus).symm x)

noncomputable instance (pp : PrimePow) : DecidablePred (allowedPow pp) := by
  classical
  infer_instance

theorem card_allowedPow (pp : PrimePow) :
    Fintype.card ({x : ZMod pp.modulus // allowedPow pp x}) = (pp.p - 2) * pp.p ^ pp.k := by
  classical

  let e := ZMod.finEquiv pp.modulus
  let S : Type := {x : ZMod pp.modulus // allowedPow pp x}
  let T : Type := {x : Fin pp.modulus // TwinPrimeAllowedCapacity.AllowedResidue pp.p pp.k x}

  have hST : S ≃ T := by
    refine
      { toFun := fun x => ⟨e.symm x.1, by simpa [allowedPow, e] using x.2⟩
        invFun := fun y => ?_
        left_inv := ?_
        right_inv := ?_ }
    · refine ⟨e y.1, ?_⟩
      have he : e.symm (e y.1) = y.1 := by simp [e]
      simpa [allowedPow, e, he] using y.2
    · intro x
      apply Subtype.ext
      simp [e]
    · intro y
      apply Subtype.ext
      simp [e]

  calc
    Fintype.card S = Fintype.card T := Fintype.card_congr hST
    _ = (pp.p - 2) * pp.p ^ pp.k := by
          simpa using (TwinPrimeAllowedCapacity.card_allowedResidue (p := pp.p) (k := pp.k) pp.hp)

end PrimePow

/-! ## Multi-axis product package -/

def mods (pps : List PrimePow) : List Nat := pps.map PrimePow.modulus

def allowedAxisPow : (pps : List PrimePow) → Axis (mods pps) → Prop
  | [] => fun _ => True
  | pp :: ps => fun x => PrimePow.allowedPow pp x.1 ∧ allowedAxisPow ps x.2

noncomputable instance (pps : List PrimePow) : DecidablePred (allowedAxisPow pps) := by
  classical
  induction pps with
  | nil =>
      -- `allowedAxisPow [] _ = True`
      simpa [allowedAxisPow] using (inferInstance : DecidablePred fun _ : Axis (mods []) => True)
  | cons pp ps ih =>
      -- `allowedAxisPow (pp::ps) x = ... ∧ ...`
      infer_instance

noncomputable instance (pps : List PrimePow) : Fintype (Axis (mods pps)) := by
  classical
  refine
    fintypeAxis (mods pps) (fun n hn => ?_)
  rcases List.mem_map.1 hn with ⟨pp, hpp, rfl⟩
  exact NeZero.ne (PrimePow.modulus pp)

lemma mods_prod_ne_zero : ∀ (pps : List PrimePow), (mods pps).prod ≠ 0
  | [] => by simp [mods]
  | pp :: ps => by
      have h0 : PrimePow.modulus pp ≠ 0 := NeZero.ne (PrimePow.modulus pp)
      simpa [mods, List.prod_cons] using Nat.mul_ne_zero h0 (mods_prod_ne_zero ps)

theorem card_allowedAxisPow :
    ∀ (pps : List PrimePow),
      Fintype.card ({a : Axis (mods pps) // allowedAxisPow pps a}) =
        (pps.map (fun pp => (pp.p - 2) * pp.p ^ pp.k)).prod := by
  classical
  intro pps
  induction pps with
  | nil =>
      simp [mods, allowedAxisPow, Axis]
  | cons pp ps ih =>
      let A : Type := {a : ZMod (PrimePow.modulus pp) // PrimePow.allowedPow pp a}
      let B : Type := {b : Axis (mods ps) // allowedAxisPow ps b}

      have h_equiv : ({x : Axis (mods (pp :: ps)) // allowedAxisPow (pp :: ps) x}) ≃ (A × B) := by
        refine
          { toFun := fun x => ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩⟩
            invFun := fun y => ⟨(y.1.1, y.2.1), y.1.2, y.2.2⟩
            left_inv := by intro x; (ext; rfl)
            right_inv := by
              intro y
              cases y with
              | mk a b =>
                simp }

      calc
        Fintype.card ({x : Axis (mods (pp :: ps)) // allowedAxisPow (pp :: ps) x})
            = Fintype.card (A × B) := Fintype.card_congr h_equiv
        _ = Fintype.card A * Fintype.card B := by simp
        _ = ((pp.p - 2) * pp.p ^ pp.k) * (ps.map (fun pp => (pp.p - 2) * pp.p ^ pp.k)).prod := by
              simp [A, B, PrimePow.card_allowedPow pp, ih]
        _ = ((pp :: ps).map (fun pp => (pp.p - 2) * pp.p ^ pp.k)).prod := by
              simp

/-!
## Global capacity on the CRT product modulus

Assume the prime-power moduli are pairwise coprime (e.g. distinct primes).
Then the CRT equivalence reduces the global allowed-capacity to the axis-product capacity.
-/
theorem card_allowedPrimePowerProduct (pps : List PrimePow)
    (co : (mods pps).Pairwise Nat.Coprime) :
    (letI : NeZero (mods pps).prod := ⟨mods_prod_ne_zero pps⟩;
      Fintype.card ({x : ZMod (mods pps).prod // allowedAxisPow pps (axisEquiv (mods pps) co x)}) =
        (pps.map (fun pp => (pp.p - 2) * pp.p ^ pp.k)).prod) := by
  classical
  have hprod0 : (mods pps).prod ≠ 0 := mods_prod_ne_zero pps
  letI : NeZero (mods pps).prod := ⟨hprod0⟩

  let e := axisEquiv (mods pps) co
  let S : Type := {x : ZMod (mods pps).prod // allowedAxisPow pps (e x)}
  let T : Type := {a : Axis (mods pps) // allowedAxisPow pps a}

  have hST : S ≃ T := by
    refine
      { toFun := fun x => ⟨e x.1, x.2⟩
        invFun := fun y => ⟨e.symm y.1, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have he : e (e.symm y.1) = y.1 := by simp [e]
      simpa [he] using y.2
    · intro x
      apply Subtype.ext
      simp [e]
    · intro y
      apply Subtype.ext
      simp [e]

  calc
    Fintype.card S = Fintype.card T := Fintype.card_congr hST
    _ = (pps.map (fun pp => (pp.p - 2) * pp.p ^ pp.k)).prod := card_allowedAxisPow pps

/-!
## Assumption reduction: pairwise-coprime primes ⇒ pairwise-coprime prime powers

Step 224 requires pairwise coprimality of the **moduli** `p^(k+1)`.
In practice, we usually know a semantic input: the base primes are distinct,
so the bases are pairwise coprime. The following lemmas bridge that gap.
-/

theorem mods_pairwise_coprime_of_p_pairwise_coprime :
    ∀ (pps : List PrimePow),
      (pps.map PrimePow.p).Pairwise Nat.Coprime →
      (mods pps).Pairwise Nat.Coprime := by
  intro pps hp
  induction pps with
  | nil =>
      simp [mods]
  | cons pp ps ih =>
      have hhead : ∀ q ∈ (ps.map PrimePow.p), Nat.Coprime pp.p q := (List.pairwise_cons.mp hp).1
      have htail : (ps.map PrimePow.p).Pairwise Nat.Coprime := (List.pairwise_cons.mp hp).2
      apply List.pairwise_cons.2
      refine ⟨?_, ih htail⟩
      intro m hm
      rcases List.mem_map.1 (by simpa [mods] using hm) with ⟨pp', hpp', rfl⟩
      have hpq : Nat.Coprime pp.p pp'.p :=
        hhead pp'.p (by simpa using (List.mem_map_of_mem (f := PrimePow.p) hpp'))
      -- Coprimality lifts from bases to their powers.
      simpa [PrimePow.modulus] using
        (hpq.pow_pow (m := pp.k + 1) (n := pp'.k + 1))

theorem card_allowedPrimePowerProduct_of_p_pairwise_coprime (pps : List PrimePow)
    (hp : (pps.map PrimePow.p).Pairwise Nat.Coprime) :
    (letI : NeZero (mods pps).prod := ⟨mods_prod_ne_zero pps⟩;
      Fintype.card
          ({x : ZMod (mods pps).prod //
              allowedAxisPow pps
                (axisEquiv (mods pps) (mods_pairwise_coprime_of_p_pairwise_coprime pps hp) x)}) =
        (pps.map (fun pp => (pp.p - 2) * pp.p ^ pp.k)).prod) := by
  simpa using
    (card_allowedPrimePowerProduct (pps := pps)
      (co := mods_pairwise_coprime_of_p_pairwise_coprime pps hp))

/-!
## User-level wrapper: "distinct primes" input

Many uses of this capacity statement start from a simple semantic condition:
the base primes are prime and distinct (`Nodup`), instead of a manually assembled
`Pairwise Nat.Coprime` hypothesis. The following wrapper provides that reduction.
-/

theorem card_allowedPrimePowerProduct_of_prime_nodup (pps : List PrimePow)
    (hprime : ∀ p ∈ (pps.map PrimePow.p), Nat.Prime p) (hnodup : (pps.map PrimePow.p).Nodup) :
    (letI : NeZero (mods pps).prod := ⟨mods_prod_ne_zero pps⟩;
      Fintype.card
          ({x : ZMod (mods pps).prod //
              allowedAxisPow pps
                (axisEquiv (mods pps)
                  (mods_pairwise_coprime_of_p_pairwise_coprime pps
                    (List.pairwise_coprime_of_prime_nodup hprime hnodup)) x)}) =
        (pps.map (fun pp => (pp.p - 2) * pp.p ^ pp.k)).prod) := by
  -- Reduce to the already-certified `Pairwise Coprime` wrapper (Step 225).
  simpa using
    (card_allowedPrimePowerProduct_of_p_pairwise_coprime (pps := pps)
      (hp := List.pairwise_coprime_of_prime_nodup hprime hnodup))

end TwinPrimeAllowedCapacityPrimePowerProduct
