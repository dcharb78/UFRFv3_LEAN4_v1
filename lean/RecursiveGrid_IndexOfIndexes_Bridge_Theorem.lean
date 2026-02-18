import Index_Of_Indexes_Theorem
import Recursive_Grid_Base13_Theorem

/-!
# Bridge: Recursive Grid Digits ↔ Index-Of-Indexes `(div, mod)`

The repo contains two complementary discrete encodings of “recursive nesting”:

1. `RecursiveGridBase13.digit d t = ⌊t/13^d⌋ mod 13`
2. `IndexOfIndexes.splitEquiv k : Fin (13^(k+1)) ≃ Fin (13^k) × Fin 13`

This file proves the *bridge facts* that connect them:

* `digit 0 t = t % 13`.
* `splitEquiv` really is the canonical `(div, mod)` decomposition:
  its second component has value `t % 13` and its first component has value `t / 13`.

These lemmas are small but important: they certify that the “recursive grid carry”
mechanism is exactly base-13 arithmetic, not an extra axiom.

No placeholders.
-/

namespace RecursiveGridIndexBridge

open IndexOfIndexes

-- ------------------------------------------------------------
-- Recursive grid: depth-0 digit is just mod 13
-- ------------------------------------------------------------

theorem digit0_eq_mod13 (t : Nat) : RecursiveGridBase13.digit 0 t = t % 13 := by
  simp [RecursiveGridBase13.digit, RecursiveGridBase13.base]

-- ------------------------------------------------------------
-- Index-of-indexes: `splitEquiv` is `(div, mod)` on the underlying `Nat` value.
-- ------------------------------------------------------------

theorem splitEquiv_fst_val (k : Nat) (x : Fin (SL (k + 1))) :
    ((splitEquiv k x).1).1 = x.1 / base := by
  -- `splitEquiv` is definitionally `finProdFinEquiv.symm`, whose `toFun` is `(divNat, modNat)`.
  simp [splitEquiv, SL, base, Nat.pow_succ]

theorem splitEquiv_snd_val (k : Nat) (x : Fin (SL (k + 1))) :
    ((splitEquiv k x).2).1 = x.1 % base := by
  simp [splitEquiv, SL, base, Nat.pow_succ]

/-!
## Full coordinate agreement (`digitsEquiv` ↔ `digit`)

`IndexOfIndexes.digitsEquiv k : Fin (13^k) ≃ Digits k` gives a nested `k`-axis coordinate system.
This section proves that those coordinates are **exactly** the base-13 digits extracted by
`RecursiveGridBase13.digit`.

This is the repo's precise "two views, one mechanism" bridge:

* `Fin (13^k)` (structural node count)
* `Digits k` (concurrent `k`-axis state)
* `digit d t` (depth-`d` phase digit)

all reduce to the same repeated `(div, mod)` recursion.
-/

/-- Extract the depth-`d` digit value from a nested `Digits k` coordinate. -/
def digitsCoord : (k : Nat) → Digits k → Nat → Nat
  | 0, _, _ => 0
  | _ + 1, x, 0 => x.2.1
  | k + 1, x, d + 1 => digitsCoord k x.1 d

theorem digitsEquiv_succ_apply (k : Nat) (x : Fin (SL (k + 1))) :
    digitsEquiv (k + 1) x = (digitsEquiv k (splitEquiv k x).1, (splitEquiv k x).2) := by
  -- Unfolding `digitsEquiv` at `k+1` shows it is `splitEquiv` followed by `prodCongr`.
  simp [digitsEquiv, Digits]
  -- Reduce the remaining `Prod.map` statement by cases on the `(div, mod)` pair.
  cases h : splitEquiv k x with
  | mk a b =>
      simp

theorem digitsCoord_digitsEquiv_eq_digit (k : Nat) (x : Fin (SL k)) :
    ∀ d, d < k → digitsCoord k (digitsEquiv k x) d = RecursiveGridBase13.digit d x.1 := by
  induction k with
  | zero =>
      intro d hd
      exact (Nat.not_lt_zero d hd).elim
  | succ k ih =>
      intro d hd
      cases d with
      | zero =>
          -- depth 0 is the fine `(mod 13)` coordinate.
          have hx :
              digitsCoord (k + 1) (digitsEquiv (k + 1) x) 0 =
                ((splitEquiv k x).2).1 := by
            -- Rewrite `digitsEquiv (k+1) x` as `(digitsEquiv k coarse, fine)`.
            simp [digitsCoord, digitsEquiv_succ_apply]
          -- Now both sides are `x % 13`.
          calc
            digitsCoord (k + 1) (digitsEquiv (k + 1) x) 0
                = ((splitEquiv k x).2).1 := hx
            _ = x.1 % base := splitEquiv_snd_val (k := k) (x := x)
            _ = x.1 % 13 := by simp [IndexOfIndexes.base]
            _ = RecursiveGridBase13.digit 0 x.1 := by
                  simp [digit0_eq_mod13]
      | succ d =>
          have hd' : d < k := Nat.succ_lt_succ_iff.1 hd
          have hx :
              digitsCoord (k + 1) (digitsEquiv (k + 1) x) (d + 1) =
                digitsCoord k (digitsEquiv k (splitEquiv k x).1) d := by
            simp [digitsCoord, digitsEquiv_succ_apply]
          -- Apply the induction hypothesis to the coarse index, then rewrite it as `x / 13`.
          have hcoarse :
              digitsCoord k (digitsEquiv k (splitEquiv k x).1) d =
                RecursiveGridBase13.digit d (((splitEquiv k x).1).1) :=
            ih (x := (splitEquiv k x).1) d hd'
          have hdiv : (((splitEquiv k x).1).1) = x.1 / base := by
            simpa using (splitEquiv_fst_val (k := k) (x := x))
          -- Finish using the recursive-grid depth shift law.
          calc
            digitsCoord (k + 1) (digitsEquiv (k + 1) x) (d + 1)
                = digitsCoord k (digitsEquiv k (splitEquiv k x).1) d := hx
            _ = RecursiveGridBase13.digit d (((splitEquiv k x).1).1) := hcoarse
            _ = RecursiveGridBase13.digit d (x.1 / base) := by simp [hdiv]
            _ = RecursiveGridBase13.digit (d + 1) x.1 := by
                -- Use the depth-shift law, but in the reverse direction.
                simpa [RecursiveGridBase13.base, IndexOfIndexes.base] using
                  (RecursiveGridBase13.digit_succ d x.1).symm

-- ------------------------------------------------------------
-- Bridge: depth-0 digit matches the fine coordinate of `splitEquiv`.
-- ------------------------------------------------------------

theorem digit0_eq_splitEquiv_snd (k t : Nat) (ht : t < base ^ (k + 1)) :
    RecursiveGridBase13.digit 0 t =
      ((splitEquiv k (⟨t, by simpa [SL, base] using ht⟩ : Fin (SL (k + 1)))).2).1 := by
  -- Both sides are literally `t % 13` (the fine coordinate of `(div, mod)`).
  simp [digit0_eq_mod13]
  have h :=
    splitEquiv_snd_val (k := k) (x := (⟨t, by simpa [SL, base] using ht⟩ : Fin (SL (k + 1))))
  -- `h : (splitEquiv k x).2.val = x.val % 13`.
  simpa [base] using h.symm

/--
Bridge recursion:

For `t < 13^(k+1)`, the higher-depth digit of `t` is the lower-depth digit of the coarse
index component produced by `splitEquiv k`.

This is the exact content of “higher depth = same rule on the coarser clock”.
-/
theorem digit_succ_eq_digit_splitEquiv_fst (k d t : Nat) (ht : t < base ^ (k + 1)) :
    RecursiveGridBase13.digit (d + 1) t =
      RecursiveGridBase13.digit d
        (((splitEquiv k (⟨t, by simpa [SL, base] using ht⟩ : Fin (SL (k + 1)))).1).1) := by
  have hcoarse :=
    splitEquiv_fst_val (k := k) (x := (⟨t, by simpa [SL, base] using ht⟩ : Fin (SL (k + 1))))
  -- Start from the recursive-grid shift law and rewrite the quotient using `splitEquiv_fst_val`.
  simpa [hcoarse, RecursiveGridBase13.base, IndexOfIndexes.base] using (RecursiveGridBase13.digit_succ d t)

end RecursiveGridIndexBridge
