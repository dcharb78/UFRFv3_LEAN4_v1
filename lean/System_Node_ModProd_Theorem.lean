import Mathlib.Data.Nat.ChineseRemainder

/-!
# System Node Concurrency: Gluing Modular Axes by Product

UFRF work in this repo often treats *coprime modular axes* as concurrent "subsystems".

This file packages the exact arithmetic backbone of that idea:

*If a family of moduli is pairwise coprime, then congruence modulo each axis is equivalent to
congruence modulo the product modulus.*

Formally, for a list `ms : List Nat` with `ms.Pairwise Nat.Coprime`:

`a ≡ b [MOD ms.prod]  ↔  ∀ m ∈ ms, a ≡ b [MOD m]`.

This is the precise "systems become nodes of other systems" rule: per-axis returns / constraints
compose into a return / constraint for the composite system.

No placeholders; the core engine is Mathlib's list Chinese remainder lemma.
-/

open scoped Function -- for the scoped `on` notation

namespace SystemNodeModProd

/-!
## Main equivalence
-/

theorem modEq_prod_iff_forall_mem {a b : Nat} {ms : List Nat} (hcop : ms.Pairwise Nat.Coprime) :
    a ≡ b [MOD ms.prod] ↔ ∀ m ∈ ms, a ≡ b [MOD m] := by
  -- Convert to the `on id` form expected by `Nat.modEq_list_map_prod_iff`.
  have hcop' : ms.Pairwise (Nat.Coprime on (fun x : Nat => x)) := by
    simpa [Function.onFun] using hcop
  -- Apply the list CRT lemma with `s := id`.
  simpa using
    (Nat.modEq_list_map_prod_iff (a := a) (b := b) (s := (fun x : Nat => x)) (l := ms) hcop')

theorem modEq_prod_of_forall_mem {a b : Nat} {ms : List Nat} (hcop : ms.Pairwise Nat.Coprime)
    (hall : ∀ m ∈ ms, a ≡ b [MOD m]) : a ≡ b [MOD ms.prod] :=
  (modEq_prod_iff_forall_mem (a := a) (b := b) (ms := ms) hcop).2 hall

theorem modEq_mem_of_modEq_prod {a b : Nat} {ms : List Nat} (hcop : ms.Pairwise Nat.Coprime)
    (hprod : a ≡ b [MOD ms.prod]) : ∀ m ∈ ms, a ≡ b [MOD m] :=
  (modEq_prod_iff_forall_mem (a := a) (b := b) (ms := ms) hcop).1 hprod

/-!
## Small helper: `ModEq` to concrete `%` equality
-/

/--
If `1 < m` and `a ≡ 1 [MOD m]`, then the concrete remainder statement is `a % m = 1`.
-/
theorem modEq_one_to_mod_eq_one {a m : Nat} (hm : 1 < m) (h : a ≡ 1 [MOD m]) : a % m = 1 := by
  have hmod : a % m = 1 % m := by
    simpa [Nat.ModEq] using h
  have h1 : (1 : Nat) % m = 1 := by
    simpa using (Nat.mod_eq_of_lt hm)
  simpa [h1] using hmod

end SystemNodeModProd
