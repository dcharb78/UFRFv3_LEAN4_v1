import Mathlib

/-!
# Index-Of-Indexes (Discrete Nesting for the 13-Cycle)

This file formalizes a discrete "index-of-indexes" skeleton:

* Scale levels are powers of a base cycle size `13`.
* Each next level is an **index over** the previous level: `13^(k+1) = 13^k * 13`.
* Concretely, `Fin (13^(k+1))` is equivalent to `Fin (13^k) × Fin 13`
  via the canonical `(div, mod)` decomposition (the same mechanism behind `Nat.mod_add_div`).

This matches the repo narrative that `13, 169, 2197, ...` are *structural node counts*,
not geometric time measurements.
-/

namespace IndexOfIndexes

/-- The canonical "breathing cycle" base used throughout the repo. -/
def base : Nat := 13

/-- Scale-level node count: `base^level`. -/
def SL (level : Nat) : Nat := base ^ level

theorem SL_succ (k : Nat) : SL (k + 1) = SL k * base := by
  simp [SL, base, Nat.pow_succ]

-- Concrete anchors.
theorem SL0 : SL 0 = 1 := by
  simp [SL, base]

theorem SL1 : SL 1 = 13 := by
  simp [SL, base]

theorem SL2 : SL 2 = 169 := by
  native_decide

theorem SL3 : SL 3 = 2197 := by
  native_decide

/--
Core nesting equivalence:

`Fin (SL (k+1))` is equivalent to `(Fin (SL k) × Fin base)`.

This is the formal "index-of-indexes" statement: one `13`-cycle of indices at each level.
-/
def splitEquiv (k : Nat) : Fin (SL (k + 1)) ≃ Fin (SL k) × Fin base := by
  -- `finProdFinEquiv : Fin m × Fin n ≃ Fin (m*n)`; we use its inverse.
  simpa [SL, base, Nat.pow_succ] using (finProdFinEquiv (m := SL k) (n := base)).symm

/-- The inverse direction: join coarse and fine indices into the next-level index. -/
def joinEquiv (k : Nat) : Fin (SL k) × Fin base ≃ Fin (SL (k + 1)) :=
  (splitEquiv k).symm

theorem join_split (k : Nat) (x : Fin (SL (k + 1))) : joinEquiv k (splitEquiv k x) = x := by
  simp [joinEquiv]

theorem split_join (k : Nat) (x : Fin (SL k) × Fin base) : splitEquiv k (joinEquiv k x) = x := by
  simp [joinEquiv]

/--
Numeric specialization: the SL1 "index of indexes" is `13^2 = 169` and decomposes as
`Fin 13 × Fin 13`.
-/
def SL1_split : Fin (SL 2) ≃ Fin (SL 1) × Fin base := by
  simpa using (splitEquiv 1)

-- ------------------------------------------------------------
-- Full k-axis decomposition (concurrent nesting)
-- ------------------------------------------------------------

/--
`Digits k` is a canonical `k`-axis coordinate space made of `k` concurrent copies of `Fin base`.

* `Digits 0 = Unit` (one state),
* `Digits (k+1) = Digits k × Fin base`.

This matches the narrative: a level is an "index over the previous level" and the full state space
is a nested product of the same base cycle.
-/
def Digits : Nat → Type
  | 0 => Unit
  | k + 1 => Digits k × Fin base

/--
Canonical equivalence:

`Fin (base^k) ≃ Digits k`.

So `13^k` states really are `k` concurrent `13`-cycles (nested product coordinates).
-/
def digitsEquiv : (k : Nat) → Fin (SL k) ≃ Digits k
  | 0 =>
      -- `SL 0 = 1`, so this is `Fin 1 ≃ Unit`.
      by simpa [Digits, SL, base] using (finOneEquiv)
  | k + 1 =>
      -- Split one level, then recurse on the coarse index.
      (splitEquiv k).trans (by
        -- Transport the first component via the induction hypothesis.
        simpa [Digits] using (Equiv.prodCongr (digitsEquiv k) (Equiv.refl (Fin base))))

theorem digitsEquiv_bijective (k : Nat) : Function.Bijective (digitsEquiv k) := by
  simpa using (digitsEquiv k).bijective

/-!
## Unit-Interval Addressing (Exact, Discrete)

To connect the “index-of-indexes” spine to the common narrative phrasing
“the interval `[0,1)` contains a full 13-step subcycle”, we use an **exact**
rational addressing:

`addrQ k x := x.val / 13^k`.

This gives a canonical embedding of the `13^k` discrete states into `[0,1)` (in `ℚ`),
and `splitEquiv/joinEquiv` correspond to subdividing each coarse interval into
13 equal refinements.

No axioms; everything is pure base arithmetic.
-/

theorem base_pos : 0 < base := by
  simp [base]

theorem SL_pos (k : Nat) : 0 < SL k := by
  -- `SL k = 13^k` and `13^k > 0`.
  simpa [SL] using (Nat.pow_pos (n := k) base_pos)

/-- Exact rational address of a `13^k`-state inside `[0,1)`: `x ↦ x/13^k`. -/
def addrQ (k : Nat) (x : Fin (SL k)) : ℚ :=
  (x.1 : ℚ) / (SL k : ℚ)

theorem addrQ_nonneg (k : Nat) (x : Fin (SL k)) : 0 ≤ addrQ k x := by
  unfold addrQ
  have hx : (0 : ℚ) ≤ (x.1 : ℚ) := by
    exact_mod_cast (Nat.zero_le x.1)
  have hden : (0 : ℚ) < (SL k : ℚ) := by
    exact_mod_cast (SL_pos k)
  exact div_nonneg hx (le_of_lt hden)

theorem addrQ_lt_one (k : Nat) (x : Fin (SL k)) : addrQ k x < 1 := by
  unfold addrQ
  have hden : (0 : ℚ) < (SL k : ℚ) := by
    exact_mod_cast (SL_pos k)
  have hx : (x.1 : ℚ) < (SL k : ℚ) := by
    exact_mod_cast x.2
  -- `a/b < 1` iff `a < b` when `b > 0`.
  exact (div_lt_one hden).2 hx

/-- `addrQ k : Fin (13^k) → ℚ` is injective (no two indices share the same rational address). -/
theorem addrQ_injective (k : Nat) : Function.Injective (addrQ k) := by
  intro x y h
  -- Clear the common denominator `13^k` in `ℚ`.
  have hden : (SL k : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (SL_pos k))
  -- Unfold the address map so `field_simp` can clear denominators.
  dsimp [addrQ] at h
  have hmul := congrArg (fun q : ℚ => q * (SL k : ℚ)) h
  have hxy : (x.1 : ℚ) = (y.1 : ℚ) := by
    field_simp [hden] at hmul
    exact hmul
  have : x.1 = y.1 := by
    exact_mod_cast hxy
  exact Fin.ext this

theorem joinEquiv_val (k : Nat) (x : Fin (SL k)) (r : Fin base) :
    (joinEquiv k (x, r)).1 = r.1 + base * x.1 := by
  -- `joinEquiv` is definitionally `finProdFinEquiv` (since `splitEquiv` is its inverse).
  simp [joinEquiv, splitEquiv, SL, base, Nat.pow_succ]

/--
Refinement equation for addresses:

Joining `(x,r)` at level `k` produces a next-level address equal to the coarse
address plus an exact `1/13^(k+1)`-scaled offset.
-/
theorem addrQ_join (k : Nat) (x : Fin (SL k)) (r : Fin base) :
    addrQ (k + 1) (joinEquiv k (x, r)) =
      addrQ k x + (r.1 : ℚ) / (SL (k + 1) : ℚ) := by
  unfold addrQ
  -- Rewrite the next-level denominator as `SL k * base` and the joined value as `r + base*x`.
  have hSL : SL (k + 1) = SL k * base := SL_succ k
  have hv : (joinEquiv k (x, r)).1 = r.1 + base * x.1 := joinEquiv_val k x r
  -- Main algebra (exact “coarse address + fine offset” decomposition):
  --   (r + b*x)/(b*m) = r/(b*m) + (b*x)/(b*m) = r/(b*m) + x/m.
  have hb : (base : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt base_pos)
  -- Normalize casts and split the division.
  simp [hSL, hv, Nat.cast_add, Nat.cast_mul, add_div, mul_comm]
  -- Cancel the common `r/(b*m)` term, then cancel the common `b` factor.
  have hcancel :
      (↑base : ℚ) * (↑↑x : ℚ) / ((↑base : ℚ) * (↑(SL k) : ℚ)) = (↑↑x : ℚ) / (↑(SL k) : ℚ) := by
    -- Rewrite into the `a*c / (b*c)` form and apply `mul_div_mul_right` (requires `c ≠ 0`).
    calc
      (↑base : ℚ) * (↑↑x : ℚ) / ((↑base : ℚ) * (↑(SL k) : ℚ)) =
          (↑↑x : ℚ) * (↑base : ℚ) / ((↑(SL k) : ℚ) * (↑base : ℚ)) := by
            simp [mul_comm]
      _ = (↑↑x : ℚ) / (↑(SL k) : ℚ) := by
            simpa [mul_assoc] using
              (mul_div_mul_right (a := (↑↑x : ℚ)) (b := (↑(SL k) : ℚ)) (c := (↑base : ℚ)) hb)
  -- Finish by rewriting the remaining term.
  nlinarith [hcancel]

/--
Interval bound for the refinement law:

At depth `k`, refining a coarse state `x` by a fine digit `r : Fin 13` produces a
next-level address that stays inside the coarse interval of length `1/13^k`:

`addrQ k x ≤ addrQ (k+1) (join(x,r)) < addrQ k x + 1/13^k`.

This makes the “each point contains 13 evenly spaced subpoints” statement explicit
in `[0,1)` coordinates.
-/
theorem addrQ_join_bounds (k : Nat) (x : Fin (SL k)) (r : Fin base) :
    addrQ k x ≤ addrQ (k + 1) (joinEquiv k (x, r))
      ∧ addrQ (k + 1) (joinEquiv k (x, r)) < addrQ k x + (1 : ℚ) / (SL k : ℚ) := by
  have hjoin : addrQ (k + 1) (joinEquiv k (x, r)) =
      addrQ k x + (r.1 : ℚ) / (SL (k + 1) : ℚ) := addrQ_join k x r
  have hdenpos : (0 : ℚ) < (SL (k + 1) : ℚ) := by
    exact_mod_cast (SL_pos (k + 1))
  have hoff_nonneg : 0 ≤ (r.1 : ℚ) / (SL (k + 1) : ℚ) := by
    exact div_nonneg (by exact_mod_cast (Nat.zero_le r.1)) (le_of_lt hdenpos)
  -- `r < 13` implies the fine offset is strictly less than `1/13^k`.
  have hr : (r.1 : ℚ) < (base : ℚ) := by
    exact_mod_cast r.2
  have h1 :
      (r.1 : ℚ) / (SL (k + 1) : ℚ) < (base : ℚ) / (SL (k + 1) : ℚ) := by
    exact div_lt_div_of_pos_right hr hdenpos
  have hb : (base : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt base_pos)
  have hk : (SL k : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (SL_pos k))
  have hSL : (SL (k + 1) : ℚ) = (SL k : ℚ) * base := by
    exact_mod_cast (SL_succ k)
  have h2 : (base : ℚ) / (SL (k + 1) : ℚ) = (1 : ℚ) / (SL k : ℚ) := by
    calc
      (base : ℚ) / (SL (k + 1) : ℚ) = (base : ℚ) / ((SL k : ℚ) * base) := by
        simp [hSL, mul_comm]
      _ = (1 : ℚ) / (SL k : ℚ) := by
        field_simp [hb, hk]
  have hoff_lt : (r.1 : ℚ) / (SL (k + 1) : ℚ) < (1 : ℚ) / (SL k : ℚ) := by
    exact lt_of_lt_of_eq h1 h2
  refine And.intro ?_ ?_
  · -- Lower bound: coarse address plus a nonnegative offset.
    simpa [hjoin] using (le_add_of_nonneg_right hoff_nonneg : addrQ k x ≤ addrQ k x + _)
  · -- Upper bound: coarse address plus an offset strictly less than the coarse interval length.
    have : addrQ k x + (r.1 : ℚ) / (SL (k + 1) : ℚ) < addrQ k x + (1 : ℚ) / (SL k : ℚ) :=
      add_lt_add_left hoff_lt (addrQ k x)
    simpa [hjoin] using this

/--
The same refinement equation stated via `splitEquiv`:
for any next-level index `y`, its address decomposes into the coarse address
plus a fine `1/13^(k+1)` offset.
-/
theorem addrQ_split (k : Nat) (y : Fin (SL (k + 1))) :
    addrQ (k + 1) y =
      addrQ k (splitEquiv k y).1 + (((splitEquiv k y).2).1 : ℚ) / (SL (k + 1) : ℚ) := by
  -- Use `y = joinEquiv k (splitEquiv k y)` and apply `addrQ_join`.
  have hy : joinEquiv k (splitEquiv k y) = y := join_split k y
  -- Rewrite `y` to the joined form, then reuse the join lemma.
  simpa [hy] using (addrQ_join (k := k) (x := (splitEquiv k y).1) (r := (splitEquiv k y).2))

end IndexOfIndexes
