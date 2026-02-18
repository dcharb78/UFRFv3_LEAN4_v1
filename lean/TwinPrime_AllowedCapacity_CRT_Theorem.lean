import Mathlib

/-!
# Twin-Prime Allowed-Capacity Multiplicativity (CRT Mechanism)

This file formalizes the *capacity* level "cross-tower independence" mechanism suggested by the
`twinprimeidea/` exploration:

* For a modulus `n > 2`, if we forbid exactly two residue values (`0` and `-2`),
  then the number of allowed residue classes is `n - 2`.
* For coprime moduli `m,n`, Chinese remainder gives an equivalence:
  `ZMod (m*n) ≃ ZMod m × ZMod n`,
  so the allowed classes mod `m*n` factor as a product of allowed classes mod `m` and mod `n`.

This is **not** an occupancy theorem about primes; it is a deterministic counting statement about
allowed residue channels under a fixed local constraint.

No placeholders.
-/

namespace TwinPrimeAllowedCapacityCRT

open Finset

/-! ## Allowed residue predicate on `ZMod n` -/

def allowed (n : Nat) [NeZero n] (x : ZMod n) : Prop :=
  x ≠ 0 ∧ x ≠ (-2 : ZMod n)

noncomputable instance (n : Nat) [NeZero n] : DecidablePred (allowed n) := by
  classical
  infer_instance

lemma neg_two_ne_zero (n : Nat) [NeZero n] (hn : 2 < n) : (-2 : ZMod n) ≠ 0 := by
  have h2 : (2 : ZMod n) ≠ 0 := by
    intro h
    have hdvd : n ∣ 2 :=
      (ZMod.natCast_eq_zero_iff (a := 2) (b := n)).1 (by simpa using h)
    have hpos : 0 < (2 : Nat) := by decide
    exact (Nat.not_dvd_of_pos_of_lt hpos hn) hdvd
  simpa using (neg_ne_zero.mpr h2)

theorem card_allowed (n : Nat) [NeZero n] (hn : 2 < n) :
    Fintype.card ({x : ZMod n // allowed n x}) = n - 2 := by
  classical

  let s : Finset (ZMod n) := (Finset.univ.erase (0 : ZMod n)).erase (-2 : ZMod n)

  have hs_card : s.card = n - 2 := by
    have h0 : (0 : ZMod n) ∈ (Finset.univ : Finset (ZMod n)) := by simp
    have hneg2_mem : (-2 : ZMod n) ∈ (Finset.univ.erase (0 : ZMod n) : Finset (ZMod n)) := by
      have hne : (-2 : ZMod n) ≠ (0 : ZMod n) := neg_two_ne_zero (n := n) hn
      simp [hne]
    have h1 : (Finset.univ.erase (0 : ZMod n)).card = n - 1 := by
      simp [Finset.card_erase_of_mem h0]
    have h2 : s.card = (n - 1) - 1 := by
      simp [s, Finset.card_erase_of_mem hneg2_mem, h1]
    have : (n - 1) - 1 = n - 2 := by omega
    simp [h2, this]

  have h_equiv : ({x : ZMod n // allowed n x}) ≃ s := by
    refine
      { toFun := fun x => ?_
        invFun := fun x => ?_
        left_inv := ?_
        right_inv := ?_ }
    · refine ⟨x.1, ?_⟩
      simp [s, x.2.1, x.2.2]
    · refine ⟨x.1, ?_, ?_⟩
      · have hx' : (x.1 : ZMod n) ∈ (Finset.univ.erase (0 : ZMod n) : Finset (ZMod n)) := by
          have hx : (x.1 : ZMod n) ∈ s := x.2
          exact (Finset.mem_erase.mp hx).2
        exact (Finset.mem_erase.mp hx').1
      · have hx : (x.1 : ZMod n) ∈ s := x.2
        exact (Finset.mem_erase.mp hx).1
    · intro x; ext; rfl
    · intro x; ext; rfl

  calc
    Fintype.card ({x : ZMod n // allowed n x}) = Fintype.card s := Fintype.card_congr h_equiv
    _ = s.card := by simp
    _ = n - 2 := hs_card

/-! ## Multiplicativity via Chinese remainder (two coprime axes) -/

def allowedProd (m n : Nat) [NeZero m] [NeZero n] (y : ZMod m × ZMod n) : Prop :=
  allowed m y.1 ∧ allowed n y.2

noncomputable instance (m n : Nat) [NeZero m] [NeZero n] : DecidablePred (allowedProd m n) := by
  classical
  infer_instance

theorem card_allowedProd (m n : Nat) [NeZero m] [NeZero n] (hm : 2 < m) (hn : 2 < n) :
    Fintype.card ({y : ZMod m × ZMod n // allowedProd m n y}) = (m - 2) * (n - 2) := by
  classical

  let A : Type := {a : ZMod m // allowed m a}
  let B : Type := {b : ZMod n // allowed n b}

  have h_equiv : ({y : ZMod m × ZMod n // allowedProd m n y}) ≃ (A × B) := by
    refine
      { toFun := fun y => ⟨⟨y.1.1, y.2.1⟩, ⟨y.1.2, y.2.2⟩⟩
        invFun := fun y => ⟨(y.1.1, y.2.1), y.1.2, y.2.2⟩
        left_inv := by intro y; ext <;> rfl
        right_inv := by intro y; ext <;> rfl }

  calc
    Fintype.card ({y : ZMod m × ZMod n // allowedProd m n y})
        = Fintype.card (A × B) := Fintype.card_congr h_equiv
    _ = Fintype.card A * Fintype.card B := by simp
    _ = (m - 2) * (n - 2) := by
          simp [A, B, card_allowed (n := m) hm, card_allowed (n := n) hn]

theorem card_allowed_mul (m n : Nat) [NeZero m] [NeZero n]
    (hcop : Nat.Coprime m n) (hm : 2 < m) (hn : 2 < n) :
    Fintype.card ({x : ZMod (m * n) // allowedProd m n ((ZMod.chineseRemainder hcop) x)})
      = (m - 2) * (n - 2) := by
  classical

  have hmn0 : m * n ≠ 0 := Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)
  letI : NeZero (m * n) := ⟨hmn0⟩

  let e := ZMod.chineseRemainder hcop
  let S : Type := {x : ZMod (m * n) // allowedProd m n (e x)}
  let T : Type := {y : ZMod m × ZMod n // allowedProd m n y}

  have hST : S ≃ T := by
    refine
      { toFun := fun x => ⟨e x.1, x.2⟩
        invFun := fun y => ⟨e.symm y.1, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have he : (ZMod.chineseRemainder hcop) (e.symm y.1) = y.1 := by
        simp [e]
      -- transport the property along the `apply_symm_apply` equality
      simpa [allowedProd, he] using y.2
    · intro x
      apply Subtype.ext
      simp [e]
    · intro y
      apply Subtype.ext
      simp [e]

  calc
    Fintype.card S = Fintype.card T := Fintype.card_congr hST
    _ = (m - 2) * (n - 2) := card_allowedProd (m := m) (n := n) hm hn

end TwinPrimeAllowedCapacityCRT

