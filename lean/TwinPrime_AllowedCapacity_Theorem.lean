import Mathlib

/-!
# Twin-Prime Allowed-Capacity (p-adic Mechanism, Prime-Power Level)

This file is a **mechanism theorem** extracted from the `twinprimeidea/` exploration:

* For a fixed odd prime `p`, twin-prime sieving forbids exactly two residue digits mod `p`:
  `0` and `-2` (equivalently `p-2`).
* At higher p-adic depth, each allowed digit lifts to `p^k` residues modulo `p^(k+1)`
  via the canonical `(div, mod)` decomposition.

What we prove here is the *allowed capacity*, not empirical occupancy by primes:

* `|{ r mod p^(k+1) : r mod p ∉ {0, -2} }| = (p-2) * p^k` for `p > 2`.

This is the discrete “index-of-indexes” kernel applied to an arbitrary base `p`:
`Fin (p^(k+1)) ≃ Fin (p^k) × Fin p` (no axioms, just base arithmetic).

No placeholders.
-/

namespace TwinPrimeAllowedCapacity

open Finset

/-! ## Low-digit constraint (mod p) -/

/-- The forbidden "edge digit" `-2 (mod p)` represented as a `Fin p` value. -/
def edge (p : Nat) [NeZero p] : Fin p := Fin.ofNat p (p - 2)

/-- Allowed digit predicate: exclude `0` and `-2 (mod p)`. -/
def AllowedDigit (p : Nat) [NeZero p] (d : Fin p) : Prop :=
  d ≠ 0 ∧ d ≠ edge p

noncomputable instance (p : Nat) [NeZero p] : DecidablePred (AllowedDigit p) := by
  classical
  infer_instance

lemma edge_ne_zero (p : Nat) [NeZero p] (hp : 2 < p) : edge p ≠ (0 : Fin p) := by
  intro h
  have hval : (edge p).val = 0 := by
    simpa using congrArg (fun x : Fin p => x.val) h
  have hlt : p - 2 < p := by omega
  have hed : (edge p).val = p - 2 := by
    simp [edge, Nat.mod_eq_of_lt hlt]
  have hcontra : p - 2 = 0 := by
    simpa [hed] using hval
  have hne : (p - 2) ≠ 0 := by omega
  exact hne hcontra

theorem card_allowedDigit (p : Nat) [NeZero p] (hp : 2 < p) :
    Fintype.card ({d : Fin p // AllowedDigit p d}) = p - 2 := by
  classical

  let s : Finset (Fin p) := (Finset.univ.erase (0 : Fin p)).erase (edge p)

  have hs_card : s.card = p - 2 := by
    have h0 : (0 : Fin p) ∈ (Finset.univ : Finset (Fin p)) := by simp
    have hEdge_mem : edge p ∈ (Finset.univ.erase (0 : Fin p) : Finset (Fin p)) := by
      have hEdge_ne0 : edge p ≠ (0 : Fin p) := edge_ne_zero (p := p) hp
      simp [hEdge_ne0]
    have h1 : (Finset.univ.erase (0 : Fin p)).card = p - 1 := by
      simp [Finset.card_erase_of_mem h0]
    have h2 : s.card = (p - 1) - 1 := by
      simp [s, Finset.card_erase_of_mem hEdge_mem, h1]
    have : (p - 1) - 1 = p - 2 := by omega
    simp [h2, this]

  have h_equiv : ({d : Fin p // AllowedDigit p d}) ≃ s := by
    refine
      { toFun := fun x => ?_
        invFun := fun x => ?_
        left_inv := ?_
        right_inv := ?_ }
    · refine ⟨x.1, ?_⟩
      simp [s, x.2.1, x.2.2]
    · refine ⟨x.1, ?_, ?_⟩
      · have hx' :
            (x.1 : Fin p) ∈ (Finset.univ.erase (0 : Fin p) : Finset (Fin p)) := by
          have hx : (x.1 : Fin p) ∈ s := x.2
          exact (Finset.mem_erase.mp hx).2
        exact (Finset.mem_erase.mp hx').1
      · have hx : (x.1 : Fin p) ∈ s := x.2
        exact (Finset.mem_erase.mp hx).1
    · intro x; ext; rfl
    · intro x; ext; rfl

  calc
    Fintype.card ({d : Fin p // AllowedDigit p d})
        = Fintype.card s := Fintype.card_congr h_equiv
    _ = s.card := by simp
    _ = p - 2 := hs_card

/-! ## Prime-power lifting (p-adic level) -/

/--
Canonical "index-of-indexes" split for prime powers:

`Fin (p^(k+1)) ≃ Fin (p^k) × Fin p`.

This is exactly the `(div, mod)` decomposition (`Nat.mod_add_div`), packaged as an equivalence.
-/
noncomputable def splitEquivPow (p k : Nat) : Fin (p^(k+1)) ≃ Fin (p^k) × Fin p := by
  simpa [Nat.pow_succ] using (finProdFinEquiv (m := p^k) (n := p)).symm

/-- Allowed residue predicate at p-adic depth: check only the low `Fin p` digit. -/
def AllowedResidue (p k : Nat) [NeZero p] (x : Fin (p^(k+1))) : Prop :=
  AllowedDigit p ((splitEquivPow p k x).2)

noncomputable instance (p k : Nat) [NeZero p] : DecidablePred (AllowedResidue p k) := by
  classical
  infer_instance

/--
Allowed-capacity theorem (prime-power level).

This is the exact combinatorial count behind the paper's `(p-2)·p^k` term:
there are `p-2` allowed low digits, each with `p^k` lifts at depth `k`.
-/
theorem card_allowedResidue (p k : Nat) [NeZero p] (hp : 2 < p) :
    Fintype.card ({x : Fin (p^(k+1)) // AllowedResidue p k x}) = (p - 2) * p^k := by
  classical

  let S : Type := {x : Fin (p^(k+1)) // AllowedResidue p k x}
  let T : Type := Fin (p^k) × {d : Fin p // AllowedDigit p d}

  have hST : S ≃ T := by
    refine
      { toFun := fun x => ⟨(splitEquivPow p k x.1).1, ⟨(splitEquivPow p k x.1).2, x.2⟩⟩
        invFun := fun x => ?_
        left_inv := ?_
        right_inv := ?_ }
    · refine ⟨(splitEquivPow p k).symm (x.1, x.2.1), ?_⟩
      have hdigit :
          (splitEquivPow p k ((splitEquivPow p k).symm (x.1, x.2.1))).2 = x.2.1 := by
        simp
      simpa [AllowedResidue, hdigit] using x.2.2
    · intro x
      ext
      simp
    · intro x
      cases x with
      | mk a d =>
        refine Prod.ext ?_ ?_
        · simp
        · apply Subtype.ext
          simp

  calc
    Fintype.card S = Fintype.card T := Fintype.card_congr hST
    _ = Fintype.card (Fin (p^k)) * Fintype.card {d : Fin p // AllowedDigit p d} := by
          simp [T]
    _ = p^k * (p - 2) := by
          simp [card_allowedDigit (p := p) hp]
    _ = (p - 2) * p^k := by ac_rfl

end TwinPrimeAllowedCapacity

/-!
## Universal Tunneling (mod 3)

This is a fully formal arithmetic constraint on *actual* twin primes (not just
allowed-channel capacity).

It is included here as a small bridge between:
- the channel-architecture (forbidden digits `{0,-2}`),
- and the “carry boundary” narrative used in `twinprimeidea/`.

No statistics: this is a direct modular argument.
-/

namespace TwinPrimeTunneling

open Nat

/-\
If `n>3` and both `n` and `n+2` are prime, then `n ≡ 2 (mod 3)`.

Equivalently: beyond the exceptional twin `(3,5)`, every lower twin sits in the
`2 mod 3` residue class (the live “carry boundary” for the `+2` displacement).
-/
theorem lowerTwin_mod3_eq_two {n : Nat} (hn : Nat.Prime n) (hn2 : Nat.Prime (n + 2)) (h3 : 3 < n) :
    n % 3 = 2 := by
  set r : Nat := n % 3 with hr
  have hr_lt : r < 3 := by
    -- `n % 3 < 3`, transported into the `r` name.
    simpa [← hr] using (Nat.mod_lt n (by decide : 0 < 3))

  interval_cases r
  · -- r = 0
    have hnmod : n % 3 = 0 := hr.symm
    have hdiv : 3 ∣ n := Nat.dvd_of_mod_eq_zero hnmod
    have hn_eq : n = 3 := by
      have h := (Nat.dvd_prime hn).1 hdiv
      rcases h with h1 | h3n
      · exact (False.elim ((by decide : (3 : Nat) ≠ 1) h1))
      · exact h3n.symm
    have hlt : (3 : Nat) < 3 := by
      rw [hn_eq] at h3
      exact h3
    exact (False.elim ((Nat.lt_irrefl 3) hlt))
  · -- r = 1
    have hnmod : n % 3 = 1 := hr.symm
    have hn2mod : (n + 2) % 3 = 0 := by
      calc
        (n + 2) % 3 = ((n % 3) + (2 % 3)) % 3 := by
          simp [Nat.add_mod]
        _ = ((1 : Nat) + (2 % 3)) % 3 := by
          simp [hnmod]
        _ = 0 := by decide
    have hdiv : 3 ∣ (n + 2) := Nat.dvd_of_mod_eq_zero hn2mod
    have hn2_eq : n + 2 = 3 := by
      have h := (Nat.dvd_prime hn2).1 hdiv
      rcases h with h1 | h3n2
      · exact (False.elim ((by decide : (3 : Nat) ≠ 1) h1))
      · exact h3n2.symm
    have h5 : (5 : Nat) < n + 2 := by
      -- `3 < n` ⇒ `5 < n+2`
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using (Nat.add_lt_add_right h3 2)
    have hlt : (3 : Nat) < n + 2 := lt_trans (by decide : (3 : Nat) < 5) h5
    have hcontra : (3 : Nat) < 3 := by
      rw [hn2_eq] at hlt
      exact hlt
    exact (False.elim ((Nat.lt_irrefl 3) hcontra))
  · -- r = 2
    rfl

end TwinPrimeTunneling
