import Index_Of_Indexes_Subcycle_Fiber_Theorem

/-!
# Index-Of-Indexes: Subinterval Containment (0→1 Contains 13 Steps)

This file makes one narrative point **visibly explicit** in `[0,1)` coordinates:

> The coarse interval of any `x : Fin (13^k)` contains exactly the 13 next-level offsets
> coming from the refinement fiber (`Fin 13`), and every such offset lies inside the
> coarse interval.

We keep this strictly discrete (finite sets + rational inequalities), with **no**
measure theory and **no** new axioms.
-/

namespace IndexOfIndexesSubintervals

open IndexOfIndexes
open IndexOfIndexesSubcycle

/-- The coarse interval (in `ℚ`) associated to a state `x : Fin (13^k)`. -/
def coarseInterval (k : Nat) (x : Fin (SL k)) : Set ℚ :=
  { q : ℚ | addrQ k x ≤ q ∧ q < addrQ k x + (1 : ℚ) / (SL k : ℚ) }

/--
Every explicit fine-offset address lies inside the corresponding coarse interval.

This is the base-13 “0→1 refinement containment” law stated directly as a set inclusion.
-/
theorem offsetAddrImage_subset_coarseInterval (k : Nat) (x : Fin (SL k)) :
    offsetAddrImage k x ⊆ coarseInterval k x := by
  intro q hq
  rcases hq with ⟨r, -, rfl⟩
  -- Use the already-proved join bounds, then rewrite the joined address as the explicit offset.
  have hb := addrQ_join_bounds (k := k) (x := x) (r := r)
  have hjoin := addrQ_join (k := k) (x := x) (r := r)
  refine ⟨?_, ?_⟩
  · -- Lower bound.
    have : addrQ k x ≤ addrQ (k + 1) (joinEquiv k (x, r)) := hb.1
    simpa [coarseInterval, hjoin] using this
  · -- Upper bound.
    have : addrQ (k + 1) (joinEquiv k (x, r)) < addrQ k x + (1 : ℚ) / (SL k : ℚ) := hb.2
    simpa [coarseInterval, hjoin] using this

/--
The refinement fiber address-image also lies inside the coarse interval.

This is the same containment statement, but phrased using the fiber-based coordinate view.
-/
theorem fiberAddrImage_subset_coarseInterval (k : Nat) (x : Fin (SL k)) :
    fiberAddrImage k x ⊆ coarseInterval k x := by
  -- Reduce to the explicit offset image using the certified equality.
  simpa [fiberAddrImage_eq_offsetAddrImage] using
    (offsetAddrImage_subset_coarseInterval (k := k) (x := x))

/-- If `x < y` (in `Fin (13^k)`), then the right endpoint of `I_k(x)` is ≤ the left endpoint of `I_k(y)`. -/
theorem rightEndpoint_le_leftEndpoint_of_lt (k : Nat) {x y : Fin (SL k)} (hxy : x < y) :
    addrQ k x + (1 : ℚ) / (SL k : ℚ) ≤ addrQ k y := by
  -- Reduce to a monotonicity statement on numerators: `(x+1)/den ≤ y/den` for `x+1 ≤ y`.
  have hden_nonneg : (0 : ℚ) ≤ (SL k : ℚ) := by
    exact_mod_cast (Nat.zero_le (SL k))
  have hx1_le : x.1 + 1 ≤ y.1 := Nat.succ_le_of_lt (show x.1 < y.1 from hxy)
  have hx1_le_q : (x.1 : ℚ) + 1 ≤ (y.1 : ℚ) := by
    exact_mod_cast hx1_le
  -- Rewrite the right endpoint `addrQ k x + 1/13^k` as `(x+1)/13^k`.
  have hend :
      addrQ k x + (1 : ℚ) / (SL k : ℚ) = ((x.1 : ℚ) + 1) / (SL k : ℚ) := by
    dsimp [addrQ]
    -- `(x/den) + (1/den) = (x+1)/den`
    simpa using (add_div (a := (x.1 : ℚ)) (b := (1 : ℚ)) (c := (SL k : ℚ))).symm
  -- Divide the numerator inequality by a nonnegative denominator.
  -- `(x+1)/den ≤ y/den`
  have hfrac :
      ((x.1 : ℚ) + 1) / (SL k : ℚ) ≤ (y.1 : ℚ) / (SL k : ℚ) :=
    div_le_div_of_nonneg_right hx1_le_q hden_nonneg
  -- Rewrite the goal's left endpoint using `hend`, and the right endpoint by unfolding `addrQ`.
  have : ((x.1 : ℚ) + 1) / (SL k : ℚ) ≤ addrQ k y := by
    simpa [addrQ] using hfrac
  calc
    addrQ k x + (1 : ℚ) / (SL k : ℚ) = ((x.1 : ℚ) + 1) / (SL k : ℚ) := hend
    _ ≤ addrQ k y := this

/-- Coarse intervals at the same level are disjoint when their indices differ. -/
theorem coarseInterval_disjoint (k : Nat) {x y : Fin (SL k)} (hxy : x ≠ y) :
    Disjoint (coarseInterval k x) (coarseInterval k y) := by
  -- Use trichotomy on `Fin` indices.
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · -- Case `x < y`: the intervals do not overlap.
    refine Set.disjoint_left.2 ?_
    intro q hxq hyq
    have hsep := rightEndpoint_le_leftEndpoint_of_lt (k := k) (x := x) (y := y) hlt
    have hy_le : addrQ k y ≤ q := hyq.1
    have q_lt : q < addrQ k x + (1 : ℚ) / (SL k : ℚ) := hxq.2
    have : addrQ k y < addrQ k x + (1 : ℚ) / (SL k : ℚ) := lt_of_le_of_lt hy_le q_lt
    exact (not_lt_of_ge hsep) this
  · -- Case `y < x`: symmetric.
    refine Set.disjoint_left.2 ?_
    intro q hxq hyq
    have hsep := rightEndpoint_le_leftEndpoint_of_lt (k := k) (x := y) (y := x) hgt
    have hx_le : addrQ k x ≤ q := hxq.1
    have q_lt : q < addrQ k y + (1 : ℚ) / (SL k : ℚ) := hyq.2
    have : addrQ k x < addrQ k y + (1 : ℚ) / (SL k : ℚ) := lt_of_le_of_lt hx_le q_lt
    exact (not_lt_of_ge hsep) this

/--
Coverage of `[0,1)` by coarse intervals.

For any rational `q` with `0 ≤ q < 1`, there exists a unique “bin” `x : Fin (13^k)`
whose half-open coarse interval contains `q`.

This is the discrete address-lookup principle: `x = ⌊q * 13^k⌋`.
-/
theorem exists_coarseInterval_of_mem_Icc (k : Nat) {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∃ x : Fin (SL k), q ∈ coarseInterval k x := by
  -- Denominator at level `k`.
  let den : ℚ := (SL k : ℚ)
  have hden_pos : (0 : ℚ) < den := by
    -- `SL k > 0` by construction (`13^k`).
    have : (0 : ℚ) < (SL k : ℚ) := by
      exact_mod_cast (SL_pos k)
    simpa [den] using this
  -- Define the bin index by the natural floor.
  let n : ℕ := Nat.floor (q * den)
  have ha0 : 0 ≤ q * den := mul_nonneg hq0 (le_of_lt hden_pos)
  have hn_le : (n : ℚ) ≤ q * den := by
    simpa [n] using (Nat.floor_le (a := q * den) ha0)
  have ha_lt_den : q * den < den := by
    -- Multiply `q < 1` by the positive denominator.
    have : q * den < 1 * den := (mul_lt_mul_of_pos_right hq1 hden_pos)
    simpa [one_mul] using this
  have hn_lt_den : (n : ℚ) < den := lt_of_le_of_lt hn_le ha_lt_den
  have hn_lt : n < SL k := by
    -- Convert the cast inequality back to naturals.
    have : (n : ℚ) < (SL k : ℚ) := by simpa [den] using hn_lt_den
    exact (Nat.cast_lt (α := ℚ)).1 this
  let x : Fin (SL k) := ⟨n, hn_lt⟩
  refine ⟨x, ?_⟩
  -- Show `q` lies in the half-open interval `[x/den, (x+1)/den)`.
  have hx_le_q : addrQ k x ≤ q := by
    -- `x/den ≤ q` iff `x ≤ q*den`, with `den > 0`.
    have : (n : ℚ) / den ≤ q := (div_le_iff₀ hden_pos).2 hn_le
    simpa [IndexOfIndexes.addrQ, x, den] using this
  have ha_lt_succ : q * den < (n : ℚ) + 1 := by
    simpa [n] using (Nat.lt_floor_add_one (a := q * den))
  have hq_lt_succ_div : q < ((n : ℚ) + 1) / den := (lt_div_iff₀ hden_pos).2 ha_lt_succ
  have hxq_upper_inv : q < addrQ k x + ((SL k : ℚ)⁻¹) := by
    -- Rewrite `x/den + 1/den = (x+1)/den` and use the strict floor bound.
    have hadd :
        addrQ k x + ((SL k : ℚ)⁻¹) = ((n : ℚ) + 1) / den := by
      -- First rewrite `den = (SL k : ℚ)`, then reduce to a common-denominator identity.
      have hden : den = (SL k : ℚ) := by rfl
      -- `a/c + 1/c = (a+1)/c`, then normalize `1/c` to `c⁻¹`.
      have := (add_div (a := (n : ℚ)) (b := (1 : ℚ)) (c := den)).symm
      -- `simp` will turn `1/den` into `den⁻¹`, which is fine now.
      simpa [IndexOfIndexes.addrQ, x, den, div_eq_mul_inv, hden] using this
    -- Use the strict floor bound on the normalized upper endpoint.
    exact (by simpa [hadd, den, div_eq_mul_inv] using hq_lt_succ_div)
  -- Convert `den⁻¹` back into the interval's `1/den` presentation.
  have hxq_upper : q < addrQ k x + (1 : ℚ) / (SL k : ℚ) := by
    simpa [div_eq_mul_inv] using hxq_upper_inv
  exact ⟨hx_le_q, hxq_upper⟩

/-- Uniqueness: a rational cannot lie in two different coarse intervals at the same level. -/
theorem coarseInterval_eq_of_mem_of_mem (k : Nat) {x y : Fin (SL k)} {q : ℚ}
    (hx : q ∈ coarseInterval k x) (hy : q ∈ coarseInterval k y) : x = y := by
  classical
  by_contra hxy
  have hdis : Disjoint (coarseInterval k x) (coarseInterval k y) :=
    coarseInterval_disjoint (k := k) (x := x) (y := y) hxy
  exact (Set.disjoint_left.1 hdis) hx hy

/-- Existence+uniqueness: base-13 address lookup yields a unique bin for any `q ∈ [0,1)`. -/
theorem existsUnique_coarseInterval_of_mem_Icc (k : Nat) {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∃! x : Fin (SL k), q ∈ coarseInterval k x := by
  classical
  obtain ⟨x, hx⟩ := exists_coarseInterval_of_mem_Icc (k := k) (q := q) hq0 hq1
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact (coarseInterval_eq_of_mem_of_mem (k := k) (x := x) (y := y) (q := q) hx hy).symm

/-- Each next-level coarse interval sits inside its parent interval. -/
theorem coarseInterval_succ_subset_parent (k : Nat) (x : Fin (SL k)) (r : Fin base) :
    coarseInterval (k + 1) (joinEquiv k (x, r)) ⊆ coarseInterval k x := by
  intro q hq
  have hden_pos_k1 : (0 : ℚ) < (SL (k + 1) : ℚ) := by
    exact_mod_cast (SL_pos (k + 1))
  have hden_nonneg_k1 : (0 : ℚ) ≤ (SL (k + 1) : ℚ) := le_of_lt hden_pos_k1
  have hjoin := addrQ_join (k := k) (x := x) (r := r)
  -- Lower bound: `addrQ k x ≤ q`.
  have hoff_nonneg : 0 ≤ (r.1 : ℚ) / (SL (k + 1) : ℚ) := by
    have hr : (0 : ℚ) ≤ (r.1 : ℚ) := by
      exact_mod_cast (Nat.zero_le r.1)
    exact div_nonneg hr hden_nonneg_k1
  have hx_le_join :
      addrQ k x ≤ addrQ (k + 1) (joinEquiv k (x, r)) := by
    have : addrQ k x ≤ addrQ k x + (r.1 : ℚ) / (SL (k + 1) : ℚ) :=
      le_add_of_nonneg_right hoff_nonneg
    simpa [hjoin] using this
  have h_lower : addrQ k x ≤ q := le_trans hx_le_join hq.1
  -- Upper bound: `q < addrQ k x + 1/SL k`.
  have hq_lt_child :
      q < addrQ (k + 1) (joinEquiv k (x, r)) + (1 : ℚ) / (SL (k + 1) : ℚ) := hq.2
  have hq_lt_step :
      q < addrQ k x + ((r.1 : ℚ) + 1) / (SL (k + 1) : ℚ) := by
    -- Rewrite the child upper endpoint using the join formula and a common denominator.
    have hsum :
        (r.1 : ℚ) / (SL (k + 1) : ℚ) + (SL (k + 1) : ℚ)⁻¹ =
          ((r.1 : ℚ) + 1) / (SL (k + 1) : ℚ) := by
      -- `a/c + 1/c = (a+1)/c` (normalize `1/c` as `c⁻¹`).
      have :=
        (add_div (a := (r.1 : ℚ)) (b := (1 : ℚ)) (c := (SL (k + 1) : ℚ))).symm
      simpa [div_eq_mul_inv] using this
    -- Expand `addrQ (k+1) join` and fold the two `1/SL(k+1)` terms.
    calc
      q <
          (addrQ k x + (r.1 : ℚ) / (SL (k + 1) : ℚ)) + (1 : ℚ) / (SL (k + 1) : ℚ) := by
            simpa [hjoin, add_assoc, add_left_comm, add_comm] using hq_lt_child
      _ = addrQ k x + ((r.1 : ℚ) / (SL (k + 1) : ℚ) + (1 : ℚ) / (SL (k + 1) : ℚ)) := by
            ring
      _ = addrQ k x + ((r.1 : ℚ) + 1) / (SL (k + 1) : ℚ) := by
            -- Avoid chasing normal forms: rewrite `1/den` as `den⁻¹` and apply `hsum`.
            simpa [div_eq_mul_inv, hsum, add_assoc]
  -- Bound `((r+1)/13^(k+1)) ≤ 1/13^k`.
  have hr1_le : r.1 + 1 ≤ base := Nat.succ_le_of_lt r.2
  have hr1_le_q : (r.1 : ℚ) + 1 ≤ (base : ℚ) := by
    exact_mod_cast hr1_le
  have hfrac_le :
      ((r.1 : ℚ) + 1) / (SL (k + 1) : ℚ) ≤ (base : ℚ) / (SL (k + 1) : ℚ) :=
    div_le_div_of_nonneg_right hr1_le_q hden_nonneg_k1
  have hbase_div :
      (base : ℚ) / (SL (k + 1) : ℚ) = (1 : ℚ) / (SL k : ℚ) := by
    -- `base / (SLk*base) = 1 / SLk` (cancel the common `base` factor).
    have hb : (base : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt base_pos)
    -- Rewrite `SL (k+1)` and cancel.
    have hSL : (SL (k + 1) : ℚ) = (SL k : ℚ) * (base : ℚ) := by
      simpa [Nat.cast_mul] using congrArg (fun t : Nat => (t : ℚ)) (SL_succ k)
    calc
      (base : ℚ) / (SL (k + 1) : ℚ) = (base : ℚ) / ((SL k : ℚ) * (base : ℚ)) := by
        simp [hSL]
      _ = ((1 : ℚ) * (base : ℚ)) / ((SL k : ℚ) * (base : ℚ)) := by
        simp
      _ = (1 : ℚ) / (SL k : ℚ) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (mul_div_mul_right (a := (1 : ℚ)) (b := (SL k : ℚ)) (c := (base : ℚ)) hb)
  have hstep_le : ((r.1 : ℚ) + 1) / (SL (k + 1) : ℚ) ≤ (1 : ℚ) / (SL k : ℚ) := by
    calc
      ((r.1 : ℚ) + 1) / (SL (k + 1) : ℚ) ≤ (base : ℚ) / (SL (k + 1) : ℚ) := hfrac_le
      _ = (1 : ℚ) / (SL k : ℚ) := hbase_div
  have h_upper : q < addrQ k x + (1 : ℚ) / (SL k : ℚ) :=
    lt_of_lt_of_le hq_lt_step (add_le_add_left hstep_le _)
  exact ⟨h_lower, h_upper⟩

/-- Parent selection: any child interval lies inside the coarse interval of its `split` parent. -/
theorem coarseInterval_succ_subset_parent_split (k : Nat) (y : Fin (SL (k + 1))) :
    coarseInterval (k + 1) y ⊆ coarseInterval k (splitEquiv k y).1 := by
  -- Rewrite `y` as a `join` of its `split` coordinates, then apply the join-specific lemma.
  have : joinEquiv k (splitEquiv k y) = y := join_split k y
  simpa [this] using
    (coarseInterval_succ_subset_parent (k := k) (x := (splitEquiv k y).1) (r := (splitEquiv k y).2))

/-- Refinement partition: each coarse interval is exactly the union of its 13 next-level subintervals. -/
theorem coarseInterval_eq_iUnion_succ (k : Nat) (x : Fin (SL k)) :
    coarseInterval k x = ⋃ r : Fin base, coarseInterval (k + 1) (joinEquiv k (x, r)) := by
  ext q
  constructor
  · intro hq
    -- Any `q` inside a coarse interval is in `[0,1)`.
    have hq0 : 0 ≤ q := le_trans (addrQ_nonneg k x) hq.1
    have hden_pos_k : (0 : ℚ) < (SL k : ℚ) := by
      exact_mod_cast (SL_pos k)
    have hx1_le : x.1 + 1 ≤ SL k := Nat.succ_le_of_lt x.2
    have hx1_le_q : (x.1 : ℚ) + 1 ≤ (SL k : ℚ) := by
      exact_mod_cast hx1_le
    have hend_le_one : addrQ k x + (SL k : ℚ)⁻¹ ≤ (1 : ℚ) := by
      -- `addrQ k x + den⁻¹ = (x+1)/den ≤ 1`.
      have hend_div :
          addrQ k x + (1 : ℚ) / (SL k : ℚ) = ((x.1 : ℚ) + 1) / (SL k : ℚ) := by
        dsimp [addrQ]
        simpa using
          (add_div (a := (x.1 : ℚ)) (b := (1 : ℚ)) (c := (SL k : ℚ))).symm
      have hend :
          addrQ k x + (SL k : ℚ)⁻¹ = ((x.1 : ℚ) + 1) / (SL k : ℚ) := by
        simpa [div_eq_mul_inv] using hend_div
      have : ((x.1 : ℚ) + 1) / (SL k : ℚ) ≤ (1 : ℚ) := by
        have : (x.1 : ℚ) + 1 ≤ (1 : ℚ) * (SL k : ℚ) := by
          simpa [one_mul] using hx1_le_q
        exact (div_le_iff₀ hden_pos_k).2 this
      simpa [hend] using this
    have hq2_inv : q < addrQ k x + (SL k : ℚ)⁻¹ := by
      simpa [div_eq_mul_inv] using hq.2
    have hq1 : q < 1 := lt_of_lt_of_le hq2_inv hend_le_one
    -- Look up the unique next-level bin for `q`, then show its parent is `x`.
    have huniq := existsUnique_coarseInterval_of_mem_Icc (k := k + 1) (q := q) hq0 hq1
    rcases huniq with ⟨y, hy, hyuniq⟩
    have hy_parent : q ∈ coarseInterval k (splitEquiv k y).1 :=
      (coarseInterval_succ_subset_parent_split (k := k) (y := y)) hy
    have hsplit : (splitEquiv k y).1 = x :=
      coarseInterval_eq_of_mem_of_mem (k := k) (x := (splitEquiv k y).1) (y := x) (q := q)
        hy_parent hq
    -- Use `y = join(split y)` and rewrite the split parent to be `x`.
    have hsplitpair : splitEquiv k y = (x, (splitEquiv k y).2) := by
      ext <;> simp [hsplit]
    have hj : joinEquiv k (x, (splitEquiv k y).2) = y := by
      have hj' : joinEquiv k (x, (splitEquiv k y).2) = joinEquiv k (splitEquiv k y) := by
        -- Avoid `simp` loops: this is just congruence on the pair equality.
        simpa using congrArg (joinEquiv k) hsplitpair.symm
      calc
        joinEquiv k (x, (splitEquiv k y).2) = joinEquiv k (splitEquiv k y) := hj'
        _ = y := join_split k y
    -- Conclude membership in the union at depth `k+1`.
    refine Set.mem_iUnion.2 ⟨(splitEquiv k y).2, ?_⟩
    simpa [hj] using hy
  · intro hq
    -- Any of the `k+1` subintervals is contained in the parent interval.
    rcases Set.mem_iUnion.1 hq with ⟨r, hr⟩
    exact (coarseInterval_succ_subset_parent (k := k) (x := x) (r := r)) hr

/-- The 13 next-level subintervals inside a parent interval are pairwise disjoint. -/
theorem coarseInterval_succ_disjoint (k : Nat) (x : Fin (SL k)) {r s : Fin base} (hrs : r ≠ s) :
    Disjoint (coarseInterval (k + 1) (joinEquiv k (x, r)))
      (coarseInterval (k + 1) (joinEquiv k (x, s))) := by
  -- Reduce to disjointness of coarse intervals at the same level.
  apply coarseInterval_disjoint (k := k + 1)
  intro h
  -- `joinEquiv` is an equivalence, hence injective.
  have hpair : (x, r) = (x, s) := (joinEquiv k).injective h
  exact hrs (by simpa using congrArg Prod.snd hpair)

/-!
## Canonical Parent Map (Recursion Across Scales)

This makes the “same rule at every scale” recursion explicit:
if a rational `q` lies in a level `(k+1)` bin `y`, then its unique level `k` bin
is the coarse parent `(splitEquiv k y).1`.
-/

/-- If `q` lies in a child bin and in a parent bin, then the parent bin is the split-parent. -/
theorem parent_eq_of_mem_child_and_mem_parent (k : Nat)
    {q : ℚ} {y : Fin (SL (k + 1))} {x : Fin (SL k)}
    (hy : q ∈ coarseInterval (k + 1) y) (hx : q ∈ coarseInterval k x) :
    x = (splitEquiv k y).1 := by
  have hy_parent : q ∈ coarseInterval k (splitEquiv k y).1 :=
    (coarseInterval_succ_subset_parent_split (k := k) (y := y)) hy
  exact coarseInterval_eq_of_mem_of_mem (k := k) (x := x) (y := (splitEquiv k y).1) (q := q) hx hy_parent

/-- The split-parent is the unique level-`k` bin that contains a `q` from a level `(k+1)` bin. -/
theorem existsUnique_parent_of_mem_child (k : Nat)
    {q : ℚ} {y : Fin (SL (k + 1))} (hy : q ∈ coarseInterval (k + 1) y) :
    ∃! x : Fin (SL k), q ∈ coarseInterval k x := by
  classical
  refine ⟨(splitEquiv k y).1,
    (coarseInterval_succ_subset_parent_split (k := k) (y := y)) hy, ?_⟩
  intro x hx
  exact parent_eq_of_mem_child_and_mem_parent (k := k) (q := q) (y := y) (x := x) hy hx

/-!
## Deterministic Floor-Bin Selector

The earlier coverage/uniqueness theorems establish that every `q ∈ [0,1)` lies in a unique
coarse interval at each level `k`.

This section makes that lookup **explicit** as a function:

`floorBin k q := ⌊q * 13^k⌋`.

It is deterministic (no `Classical.choose`) and interacts cleanly with the canonical parent map.
-/

/-- Helper: the floor-index is always in range for any `q ∈ [0,1)`. -/
theorem floor_lt_SL_of_mem_Icc (k : Nat) {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Nat.floor (q * (SL k : ℚ)) < SL k := by
  have hden_pos : (0 : ℚ) < (SL k : ℚ) := by
    exact_mod_cast (SL_pos k)
  have ha0 : 0 ≤ q * (SL k : ℚ) := mul_nonneg hq0 (le_of_lt hden_pos)
  have hn_le : (Nat.floor (q * (SL k : ℚ)) : ℚ) ≤ q * (SL k : ℚ) := by
    simpa using (Nat.floor_le (a := q * (SL k : ℚ)) ha0)
  have ha_lt_den : q * (SL k : ℚ) < (SL k : ℚ) := by
    have : q * (SL k : ℚ) < 1 * (SL k : ℚ) := mul_lt_mul_of_pos_right hq1 hden_pos
    simpa [one_mul] using this
  have hn_lt_den : (Nat.floor (q * (SL k : ℚ)) : ℚ) < (SL k : ℚ) := lt_of_le_of_lt hn_le ha_lt_den
  exact (Nat.cast_lt (α := ℚ)).1 hn_lt_den

/-- The canonical bin selector: `floorBin k q = ⌊q * 13^k⌋`. -/
def floorBin (k : Nat) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1) : Fin (SL k) :=
  ⟨Nat.floor (q * (SL k : ℚ)), floor_lt_SL_of_mem_Icc (k := k) (q := q) hq0 hq1⟩

/-- `floorBin` is the explicit witness for coarse-interval membership. -/
theorem floorBin_mem_coarseInterval (k : Nat) {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    q ∈ coarseInterval k (floorBin k q hq0 hq1) := by
  have hden_pos : (0 : ℚ) < (SL k : ℚ) := by
    exact_mod_cast (SL_pos k)
  have ha0 : 0 ≤ q * (SL k : ℚ) := mul_nonneg hq0 (le_of_lt hden_pos)
  have hn_le : (Nat.floor (q * (SL k : ℚ)) : ℚ) ≤ q * (SL k : ℚ) := by
    simpa using (Nat.floor_le (a := q * (SL k : ℚ)) ha0)
  have hx_le_q : addrQ k (floorBin k q hq0 hq1) ≤ q := by
    -- `n ≤ q*den` implies `n/den ≤ q` for `den > 0`.
    have : (Nat.floor (q * (SL k : ℚ)) : ℚ) / (SL k : ℚ) ≤ q := (div_le_iff₀ hden_pos).2 hn_le
    simpa [floorBin, addrQ] using this
  have ha_lt_succ : q * (SL k : ℚ) < (Nat.floor (q * (SL k : ℚ)) : ℚ) + 1 := by
    simpa using (Nat.lt_floor_add_one (a := q * (SL k : ℚ)))
  have hq_lt_succ_div :
      q < ((Nat.floor (q * (SL k : ℚ)) : ℚ) + 1) / (SL k : ℚ) := (lt_div_iff₀ hden_pos).2 ha_lt_succ
  have hadd :
      addrQ k (floorBin k q hq0 hq1) + (1 : ℚ) / (SL k : ℚ) =
        ((Nat.floor (q * (SL k : ℚ)) : ℚ) + 1) / (SL k : ℚ) := by
    -- `a/c + 1/c = (a+1)/c`
    simpa [floorBin, addrQ, div_eq_mul_inv] using
      (add_div (a := (Nat.floor (q * (SL k : ℚ)) : ℚ)) (b := (1 : ℚ)) (c := (SL k : ℚ))).symm
  have hxq_upper : q < addrQ k (floorBin k q hq0 hq1) + (1 : ℚ) / (SL k : ℚ) := by
    -- Rewrite the strict bound on `(n+1)/den` into the standard half-open endpoint form.
    exact lt_of_lt_of_eq hq_lt_succ_div hadd.symm
  exact ⟨hx_le_q, hxq_upper⟩

/-- `floorBin` is the unique level-`k` bin containing `q ∈ [0,1)`. -/
theorem floorBin_unique (k : Nat) {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∃! x : Fin (SL k), q ∈ coarseInterval k x := by
  refine ⟨floorBin k q hq0 hq1, floorBin_mem_coarseInterval (k := k) (q := q) hq0 hq1, ?_⟩
  intro x hx
  exact coarseInterval_eq_of_mem_of_mem (k := k) (x := x) (y := floorBin k q hq0 hq1) (q := q) hx
    (floorBin_mem_coarseInterval (k := k) (q := q) hq0 hq1)

/--
Canonical recursion for the explicit selector:
the parent of the `(k+1)`-bin returned by `floorBin` is exactly the `k`-bin returned by `floorBin`.
-/
theorem floorBin_parent (k : Nat) {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    floorBin k q hq0 hq1 = (splitEquiv k (floorBin (k + 1) q hq0 hq1)).1 := by
  have hy : q ∈ coarseInterval (k + 1) (floorBin (k + 1) q hq0 hq1) :=
    floorBin_mem_coarseInterval (k := k + 1) (q := q) hq0 hq1
  have hx : q ∈ coarseInterval k (floorBin k q hq0 hq1) :=
    floorBin_mem_coarseInterval (k := k) (q := q) hq0 hq1
  exact parent_eq_of_mem_child_and_mem_parent (k := k) (q := q) (y := floorBin (k + 1) q hq0 hq1)
    (x := floorBin k q hq0 hq1) hy hx

/-!
## Base-13 Digit Extraction (Explicit div/mod)

`splitEquiv` is the canonical `(div, mod)` decomposition at each scale:
it exposes the **parent index** (`/ 13`) and the **next digit** (`% 13`).

This section ties that to the deterministic selector `floorBin` by giving an explicit
“next digit” formula for the remainder component.
-/

theorem splitEquiv_fst_val_eq_div_base (k : Nat) (y : Fin (SL (k + 1))) :
    (splitEquiv k y).1.1 = y.1 / base := by
  simp [splitEquiv]
  change (↑(((finProdFinEquiv (m := SL k) (n := base)).symm y).1) = (↑y / base))
  simp [finProdFinEquiv_symm_apply, Fin.divNat]

theorem splitEquiv_snd_val_eq_mod_base (k : Nat) (y : Fin (SL (k + 1))) :
    (splitEquiv k y).2.1 = y.1 % base := by
  simp [splitEquiv]
  change (↑(((finProdFinEquiv (m := SL k) (n := base)).symm y).2) = (↑y % base))
  simp [finProdFinEquiv_symm_apply, Fin.modNat]

/-- Explicit next-digit (remainder) extracted from the `(k+1)`-scale `floorBin`. -/
def floorDigit (k : Nat) (q : ℚ) (_hq0 : 0 ≤ q) (_hq1 : q < 1) : Fin base :=
  ⟨Nat.floor (q * (SL (k + 1) : ℚ)) % base, Nat.mod_lt _ base_pos⟩

theorem splitEquiv_floorBin_snd_eq_floorDigit (k : Nat) {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (splitEquiv k (floorBin (k + 1) q hq0 hq1)).2 = floorDigit k q hq0 hq1 := by
  ext
  -- Reduce to value equality: the `split` remainder is `y.val % 13`.
  simp [floorDigit, splitEquiv_snd_val_eq_mod_base, floorBin]

theorem splitEquiv_floorBin_eq_parent_and_digit (k : Nat) {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    splitEquiv k (floorBin (k + 1) q hq0 hq1) =
      (floorBin k q hq0 hq1, floorDigit k q hq0 hq1) := by
  refine Prod.ext ?_ ?_
  · -- Parent index recursion (already proven as `floorBin_parent`).
    simpa using (floorBin_parent (k := k) (q := q) hq0 hq1).symm
  · exact splitEquiv_floorBin_snd_eq_floorDigit (k := k) (q := q) hq0 hq1

/-!
## DigitsEquiv Bridge (floorBin ↔ base-13 digits)

`digitsEquiv k : Fin (13^k) ≃ Digits k` exposes the **nested** base-13 coordinate system.
This theorem makes the refinement mechanism explicit in those digit coordinates: selecting the
`(k+1)`-bin adds one digit to the `k`-bin.
-/

theorem digitsEquiv_floorBin_succ (k : Nat) {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    digitsEquiv (k + 1) (floorBin (k + 1) q hq0 hq1) =
      (digitsEquiv k (floorBin k q hq0 hq1), floorDigit k q hq0 hq1) := by
  -- Unfolding `digitsEquiv` at `k+1` shows it is `splitEquiv` followed by recursion on the parent.
  -- Then rewrite the `split` of `floorBin (k+1)` using the parent+digit lemma.
  simp [IndexOfIndexes.digitsEquiv, IndexOfIndexes.Digits, splitEquiv_floorBin_eq_parent_and_digit]

/-!
## Explicit `q ↦ Digits k` Constructor (No Classical Choice)

`floorBin` gives a deterministic `Fin (13^k)` index for any `q ∈ [0,1)`.
This section turns that into an explicit `Digits k` value by extracting the digits
recursively, and proves it agrees with `digitsEquiv (floorBin ...)`.
-/

/-- Deterministic base-13 digit tuple for any `q ∈ [0,1)` at depth `k`. -/
def floorDigits (k : Nat) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1) : Digits k :=
  match k with
  | 0 => ()
  | k + 1 => (floorDigits k q hq0 hq1, floorDigit k q hq0 hq1)

theorem digitsEquiv_floorBin_eq_floorDigits (k : Nat) {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    digitsEquiv k (floorBin k q hq0 hq1) = floorDigits k q hq0 hq1 := by
  induction k with
  | zero =>
      -- `Digits 0 = Unit` and `Fin (13^0) = Fin 1`; both sides are the unique inhabitant.
      simp [floorDigits, IndexOfIndexes.digitsEquiv, IndexOfIndexes.Digits]
  | succ k hk =>
      -- Use the certified “add one digit” law, then discharge the parent component by IH.
      simpa [floorDigits, hk] using (digitsEquiv_floorBin_succ (k := k) (q := q) hq0 hq1)

/-!
## Digit-Addressed Interval Membership

This repackages the interval containment statement in pure digit coordinates:
the `Digits k` tuple computed from `q` is an address for a specific coarse interval in `[0,1)`.
-/

/-- Interpret any `Digits k` coordinate as a rational address in `[0,1)`. -/
def digitAddrQ (k : Nat) (d : Digits k) : ℚ :=
  addrQ k ((digitsEquiv k).symm d)

theorem digitsEquiv_symm_succ (k : Nat) (d : Digits k) (r : Fin base) :
    (digitsEquiv (k + 1)).symm (d, r) = joinEquiv k ((digitsEquiv k).symm d, r) := by
  -- Prove by applying `digitsEquiv (k+1)` to both sides, then simplify.
  apply (digitsEquiv (k + 1)).injective
  simp [IndexOfIndexes.digitsEquiv, IndexOfIndexes.Digits, split_join]

theorem digitAddrQ_succ (k : Nat) (d : Digits k) (r : Fin base) :
    digitAddrQ (k + 1) (d, r) = digitAddrQ k d + (r.1 : ℚ) / (SL (k + 1) : ℚ) := by
  -- Reduce to the `Fin (13^k)` join law via the explicit `digitsEquiv`-inverse recursion.
  simp [digitAddrQ, digitsEquiv_symm_succ, addrQ_join]

theorem mem_coarseInterval_digits (k : Nat) {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    q ∈ coarseInterval k ((digitsEquiv k).symm (floorDigits k q hq0 hq1)) := by
  have hmem : q ∈ coarseInterval k (floorBin k q hq0 hq1) :=
    floorBin_mem_coarseInterval (k := k) (q := q) hq0 hq1
  have hbin :
      floorBin k q hq0 hq1 = (digitsEquiv k).symm (floorDigits k q hq0 hq1) := by
    -- Apply the inverse of `digitsEquiv` to the certified equality.
    have h :=
      congrArg (fun d => (digitsEquiv k).symm d)
        (digitsEquiv_floorBin_eq_floorDigits (k := k) (q := q) hq0 hq1)
    simpa using h
  simpa [hbin] using hmem

theorem digitAddrQ_floorDigits_le (k : Nat) {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    digitAddrQ k (floorDigits k q hq0 hq1) ≤ q := by
  have h := mem_coarseInterval_digits (k := k) (q := q) hq0 hq1
  -- Unpack `coarseInterval` membership and rewrite `digitAddrQ` as the left endpoint.
  exact (by
    rcases h with ⟨hlo, _hhi⟩
    simpa [digitAddrQ, coarseInterval] using hlo)

theorem digitAddrQ_floorDigits_lt_add (k : Nat) {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    q < digitAddrQ k (floorDigits k q hq0 hq1) + (1 : ℚ) / (SL k : ℚ) := by
  have h := mem_coarseInterval_digits (k := k) (q := q) hq0 hq1
  exact (by
    rcases h with ⟨_hlo, hhi⟩
    simpa [digitAddrQ, coarseInterval] using hhi)

/-!
## Residual (“Unresolved Fraction”) at Depth `k`

The digit-address of `q` at depth `k` is the left endpoint of a length `1/13^k` interval.
The residual is the remaining part of `q` after taking that prefix.
-/

/-- The residual part of `q` not captured by its depth-`k` digit prefix. -/
def residualQ (k : Nat) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1) : ℚ :=
  q - digitAddrQ k (floorDigits k q hq0 hq1)

theorem residualQ_nonneg (k : Nat) {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    0 ≤ residualQ k q hq0 hq1 := by
  dsimp [residualQ]
  have hle := digitAddrQ_floorDigits_le (k := k) (q := q) hq0 hq1
  exact sub_nonneg.2 hle

theorem residualQ_lt (k : Nat) {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    residualQ k q hq0 hq1 < (1 : ℚ) / (SL k : ℚ) := by
  dsimp [residualQ]
  have hlt := digitAddrQ_floorDigits_lt_add (k := k) (q := q) hq0 hq1
  have hlt' : q < (1 : ℚ) / (SL k : ℚ) + digitAddrQ k (floorDigits k q hq0 hq1) := by
    simpa [add_comm, add_left_comm, add_assoc] using hlt
  exact (sub_lt_iff_lt_add).2 hlt'

theorem residualQ_bounds (k : Nat) {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    0 ≤ residualQ k q hq0 hq1 ∧ residualQ k q hq0 hq1 < (1 : ℚ) / (SL k : ℚ) := by
  exact ⟨residualQ_nonneg (k := k) (q := q) hq0 hq1, residualQ_lt (k := k) (q := q) hq0 hq1⟩

theorem digitAddrQ_floorDigits_eq_floor (k : Nat) {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    digitAddrQ k (floorDigits k q hq0 hq1) =
      (Nat.floor (q * (SL k : ℚ)) : ℚ) / (SL k : ℚ) := by
  -- Convert the `Digits` tuple back to the explicit bin-index (`floorBin`), then unfold.
  have hbin :
      floorBin k q hq0 hq1 = (digitsEquiv k).symm (floorDigits k q hq0 hq1) := by
    have h :=
      congrArg (fun d => (digitsEquiv k).symm d)
        (digitsEquiv_floorBin_eq_floorDigits (k := k) (q := q) hq0 hq1)
    simpa using h
  -- Replace the `Digits`-inverse by `floorBin`, then unfold `addrQ/floorBin`.
  dsimp [digitAddrQ]
  -- `hbin` is oriented as `floorBin = symm floorDigits`, so rewrite using its symmetric form.
  rw [hbin.symm]
  simp [addrQ, floorBin]

/-!
## Resolution Operator (Depth-`k` Projection)

The map `resolveQ k` takes any `q ∈ [0,1)` and returns the depth-`k` digit-address prefix
(equivalently: the nearest-left gridpoint in the `13^k`-adic partition).

The main kernel property is **idempotence**: resolving twice at the same depth is the same as
resolving once.
-/

/-- Resolve `q` at depth `k` by taking its digit-address prefix (a `13^k`-gridpoint in `[0,1)`). -/
def resolveQ (k : Nat) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1) : ℚ :=
  digitAddrQ k (floorDigits k q hq0 hq1)

theorem resolveQ_eq_floor (k : Nat) {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    resolveQ k q hq0 hq1 = (Nat.floor (q * (SL k : ℚ)) : ℚ) / (SL k : ℚ) := by
  simpa [resolveQ] using digitAddrQ_floorDigits_eq_floor (k := k) (q := q) hq0 hq1

theorem resolveQ_eq_addrQ_floorBin (k : Nat) {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    resolveQ k q hq0 hq1 = addrQ k (floorBin k q hq0 hq1) := by
  -- Both sides reduce to the same explicit `Nat.floor` expression.
  have hleft := resolveQ_eq_floor (k := k) (q := q) hq0 hq1
  have hright : addrQ k (floorBin k q hq0 hq1) =
      (Nat.floor (q * (SL k : ℚ)) : ℚ) / (SL k : ℚ) := by
    simp [addrQ, floorBin]
  simpa [hright] using hleft

theorem resolveQ_nonneg (k : Nat) {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    0 ≤ resolveQ k q hq0 hq1 := by
  have h := resolveQ_eq_floor (k := k) (q := q) hq0 hq1
  have hnum : (0 : ℚ) ≤ (Nat.floor (q * (SL k : ℚ)) : ℚ) := by
    exact_mod_cast (Nat.zero_le (Nat.floor (q * (SL k : ℚ))))
  have hden : (0 : ℚ) < (SL k : ℚ) := by
    exact_mod_cast (SL_pos k)
  simpa [h] using (div_nonneg hnum (le_of_lt hden))

theorem resolveQ_lt_one (k : Nat) {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    resolveQ k q hq0 hq1 < 1 := by
  have h := resolveQ_eq_floor (k := k) (q := q) hq0 hq1
  have hden : (0 : ℚ) < (SL k : ℚ) := by
    exact_mod_cast (SL_pos k)
  have hn : Nat.floor (q * (SL k : ℚ)) < SL k :=
    floor_lt_SL_of_mem_Icc (k := k) (q := q) hq0 hq1
  have hnum : (Nat.floor (q * (SL k : ℚ)) : ℚ) < (SL k : ℚ) := by
    exact_mod_cast hn
  have : (Nat.floor (q * (SL k : ℚ)) : ℚ) / (SL k : ℚ) < 1 := (div_lt_one hden).2 hnum
  simpa [h] using this

theorem resolveQ_idempotent (k : Nat) {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    resolveQ k
        (resolveQ k q hq0 hq1)
        (resolveQ_nonneg (k := k) (q := q) hq0 hq1)
        (resolveQ_lt_one (k := k) (q := q) hq0 hq1)
      = resolveQ k q hq0 hq1 := by
  let n : Nat := Nat.floor (q * (SL k : ℚ))
  have hn_lt : n < SL k := by
    simpa [n] using (floor_lt_SL_of_mem_Icc (k := k) (q := q) hq0 hq1)
  have hq_res : resolveQ k q hq0 hq1 = (n : ℚ) / (SL k : ℚ) := by
    have h := resolveQ_eq_floor (k := k) (q := q) hq0 hq1
    simpa [resolveQ, n] using h
  have hden_ne : (SL k : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (SL_pos k))
  have hmul : ((n : ℚ) / (SL k : ℚ)) * (SL k : ℚ) = (n : ℚ) := by
    field_simp [hden_ne]
  have hfloor : Nat.floor (((n : ℚ) / (SL k : ℚ)) * (SL k : ℚ)) = n := by
    calc
      Nat.floor (((n : ℚ) / (SL k : ℚ)) * (SL k : ℚ)) = Nat.floor (n : ℚ) := by simp [hmul]
      _ = n := by simp
  have hout :=
    resolveQ_eq_floor (k := k) (q := (n : ℚ) / (SL k : ℚ))
      (hq0 := by
        have hn0 : (0 : ℚ) ≤ (n : ℚ) := by exact_mod_cast (Nat.zero_le n)
        have hden : (0 : ℚ) < (SL k : ℚ) := by exact_mod_cast (SL_pos k)
        exact div_nonneg hn0 (le_of_lt hden))
      (hq1 := by
        have hden : (0 : ℚ) < (SL k : ℚ) := by exact_mod_cast (SL_pos k)
        have hnum : (n : ℚ) < (SL k : ℚ) := by exact_mod_cast hn_lt
        exact (div_lt_one hden).2 hnum)
  have :
      resolveQ k
          ((n : ℚ) / (SL k : ℚ))
          (by
            have hn0 : (0 : ℚ) ≤ (n : ℚ) := by exact_mod_cast (Nat.zero_le n)
            have hden : (0 : ℚ) < (SL k : ℚ) := by exact_mod_cast (SL_pos k)
            exact div_nonneg hn0 (le_of_lt hden))
          (by
            have hden : (0 : ℚ) < (SL k : ℚ) := by exact_mod_cast (SL_pos k)
            have hnum : (n : ℚ) < (SL k : ℚ) := by exact_mod_cast hn_lt
            exact (div_lt_one hden).2 hnum)
        = (n : ℚ) / (SL k : ℚ) := by
      -- Closed form + floor cancellation on the grid.
      simpa [resolveQ, hfloor] using hout
  simp [hq_res, this]

theorem resolveQ_succ (k : Nat) {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    resolveQ (k + 1) q hq0 hq1 =
      resolveQ k q hq0 hq1 + (floorDigit k q hq0 hq1).1 / (SL (k + 1) : ℚ) := by
  simp [resolveQ, floorDigits, digitAddrQ_succ]

theorem resolveQ_le_succ (k : Nat) {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    resolveQ k q hq0 hq1 ≤ resolveQ (k + 1) q hq0 hq1 := by
  rw [resolveQ_succ (k := k) (q := q) hq0 hq1]
  have hr0 : (0 : ℚ) ≤ ((floorDigit k q hq0 hq1).1 : ℚ) := by
    exact_mod_cast (Nat.zero_le (floorDigit k q hq0 hq1).1)
  have hden : (0 : ℚ) < (SL (k + 1) : ℚ) := by
    exact_mod_cast (SL_pos (k + 1))
  have hterm : 0 ≤ (floorDigit k q hq0 hq1).1 / (SL (k + 1) : ℚ) :=
    div_nonneg hr0 (le_of_lt hden)
  exact le_add_of_nonneg_right hterm

theorem resolveQ_succ_lt_parent (k : Nat) {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    resolveQ (k + 1) q hq0 hq1 < resolveQ k q hq0 hq1 + (1 : ℚ) / (SL k : ℚ) := by
  rw [resolveQ_succ (k := k) (q := q) hq0 hq1]
  have hden : (0 : ℚ) < (SL (k + 1) : ℚ) := by
    exact_mod_cast (SL_pos (k + 1))
  have hrlt : ((floorDigit k q hq0 hq1).1 : ℚ) < (base : ℚ) := by
    exact_mod_cast (floorDigit k q hq0 hq1).2
  have hterm :
      (floorDigit k q hq0 hq1).1 / (SL (k + 1) : ℚ) < (base : ℚ) / (SL (k + 1) : ℚ) :=
    (div_lt_div_of_pos_right hrlt hden)
  have hbase : (base : ℚ) / (SL (k + 1) : ℚ) = (1 : ℚ) / (SL k : ℚ) := by
    simp [SL, Nat.pow_succ, base, div_eq_mul_inv]
  have hterm' : (floorDigit k q hq0 hq1).1 / (SL (k + 1) : ℚ) < (1 : ℚ) / (SL k : ℚ) := by
    simpa [hbase] using hterm
  exact add_lt_add_left hterm' _

theorem resolveQ_add_residualQ (k : Nat) {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    q = resolveQ k q hq0 hq1 + residualQ k q hq0 hq1 := by
  simp [resolveQ, residualQ]

/-!
## “Resolved Point” Exactness on the 13-adic Grid

If a rational `q` is *exactly* on the level-`k` grid (denominator `13^k`),
then its digit-address at depth `k` is exact (no residual).

This is a purely discrete statement about the `0→1` refinement kernel.
-/

theorem digitAddrQ_floorDigits_eq_of_grid (k : Nat) (n : Nat) (hn : n < SL k) :
    digitAddrQ k
        (floorDigits k ((n : ℚ) / (SL k : ℚ))
          (by
            have hn0 : (0 : ℚ) ≤ (n : ℚ) := by exact_mod_cast (Nat.zero_le n)
            have hden : (0 : ℚ) < (SL k : ℚ) := by exact_mod_cast (SL_pos k)
            exact div_nonneg hn0 (le_of_lt hden))
          (by
            have hden : (0 : ℚ) < (SL k : ℚ) := by exact_mod_cast (SL_pos k)
            have hnum : (n : ℚ) < (SL k : ℚ) := by exact_mod_cast hn
            exact (div_lt_one hden).2 hnum))
      = (n : ℚ) / (SL k : ℚ) := by
  have hden : (SL k : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (SL_pos k))
  have hmul : ((n : ℚ) / (SL k : ℚ)) * (SL k : ℚ) = (n : ℚ) := by
    field_simp [hden]
  have hfloor : Nat.floor (((n : ℚ) / (SL k : ℚ)) * (SL k : ℚ)) = n := by
    calc
      Nat.floor (((n : ℚ) / (SL k : ℚ)) * (SL k : ℚ)) = Nat.floor (n : ℚ) := by simp [hmul]
      _ = n := by simp
  -- Closed form digit address + floor cancellation on the grid.
  have h :=
    digitAddrQ_floorDigits_eq_floor (k := k) (q := ((n : ℚ) / (SL k : ℚ)))
      (hq0 := by
        have hn0 : (0 : ℚ) ≤ (n : ℚ) := by exact_mod_cast (Nat.zero_le n)
        have hden : (0 : ℚ) < (SL k : ℚ) := by exact_mod_cast (SL_pos k)
        exact div_nonneg hn0 (le_of_lt hden))
      (hq1 := by
        have hden : (0 : ℚ) < (SL k : ℚ) := by exact_mod_cast (SL_pos k)
        have hnum : (n : ℚ) < (SL k : ℚ) := by exact_mod_cast hn
        exact (div_lt_one hden).2 hnum)
  simpa [hfloor] using h

theorem residualQ_eq_zero_of_grid (k : Nat) (n : Nat) (hn : n < SL k) :
    residualQ k
        ((n : ℚ) / (SL k : ℚ))
        (by
          have hn0 : (0 : ℚ) ≤ (n : ℚ) := by exact_mod_cast (Nat.zero_le n)
          have hden : (0 : ℚ) < (SL k : ℚ) := by exact_mod_cast (SL_pos k)
          exact div_nonneg hn0 (le_of_lt hden))
        (by
          have hden : (0 : ℚ) < (SL k : ℚ) := by exact_mod_cast (SL_pos k)
          have hnum : (n : ℚ) < (SL k : ℚ) := by exact_mod_cast hn
          exact (div_lt_one hden).2 hnum)
      = 0 := by
  dsimp [residualQ]
  have h := digitAddrQ_floorDigits_eq_of_grid (k := k) (n := n) hn
  simp [h]

theorem resolveQ_fixed_point_iff_grid (k : Nat) {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    resolveQ k q hq0 hq1 = q ↔ ∃ n : Nat, n < SL k ∧ q = (n : ℚ) / (SL k : ℚ) := by
  constructor
  · intro hfix
    let n : Nat := Nat.floor (q * (SL k : ℚ))
    have hn_lt : n < SL k := by
      simpa [n] using (floor_lt_SL_of_mem_Icc (k := k) (q := q) hq0 hq1)
    have hgrid : resolveQ k q hq0 hq1 = (n : ℚ) / (SL k : ℚ) := by
      simpa [n] using (resolveQ_eq_floor (k := k) (q := q) hq0 hq1)
    refine ⟨n, hn_lt, ?_⟩
    exact hfix.symm.trans hgrid
  · rintro ⟨n, hn, rfl⟩
    have hden : (SL k : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (SL_pos k))
    have hmul : ((n : ℚ) / (SL k : ℚ)) * (SL k : ℚ) = (n : ℚ) := by
      field_simp [hden]
    have hfloor : Nat.floor (((n : ℚ) / (SL k : ℚ)) * (SL k : ℚ)) = n := by
      calc
        Nat.floor (((n : ℚ) / (SL k : ℚ)) * (SL k : ℚ)) = Nat.floor (n : ℚ) := by simp [hmul]
        _ = n := by simp
    have hout :=
      resolveQ_eq_floor (k := k) (q := (n : ℚ) / (SL k : ℚ))
        (hq0 := by
          have hn0 : (0 : ℚ) ≤ (n : ℚ) := by exact_mod_cast (Nat.zero_le n)
          have hpos : (0 : ℚ) < (SL k : ℚ) := by exact_mod_cast (SL_pos k)
          exact div_nonneg hn0 (le_of_lt hpos))
        (hq1 := by
          have hpos : (0 : ℚ) < (SL k : ℚ) := by exact_mod_cast (SL_pos k)
          have hnum : (n : ℚ) < (SL k : ℚ) := by exact_mod_cast hn
          exact (div_lt_one hpos).2 hnum)
    -- Closed form + floor cancellation on the grid.
    simpa [resolveQ, hfloor] using hout

theorem residualQ_eq_zero_iff_grid (k : Nat) {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    residualQ k q hq0 hq1 = 0 ↔ ∃ n : Nat, n < SL k ∧ q = (n : ℚ) / (SL k : ℚ) := by
  constructor
  · intro hres
    have hdecomp := resolveQ_add_residualQ (k := k) (q := q) hq0 hq1
    have hq' : q = resolveQ k q hq0 hq1 := by
      simpa [hres] using hdecomp
    exact (resolveQ_fixed_point_iff_grid (k := k) (q := q) hq0 hq1).1 hq'.symm
  · rintro ⟨n, hn, hq⟩
    have hfix : resolveQ k q hq0 hq1 = q :=
      (resolveQ_fixed_point_iff_grid (k := k) (q := q) hq0 hq1).2 ⟨n, hn, hq⟩
    have hfix' : digitAddrQ k (floorDigits k q hq0 hq1) = q := by
      simpa [resolveQ] using hfix
    -- `residualQ` is `q - resolveQ` (unfolded), so fixed points have zero residue.
    simp [residualQ, hfix']

theorem resolveQ_le (k : Nat) {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    resolveQ k q hq0 hq1 ≤ q := by
  have hnonneg : 0 ≤ residualQ k q hq0 hq1 :=
    (residualQ_bounds (k := k) (q := q) hq0 hq1).1
  have hsum : resolveQ k q hq0 hq1 + residualQ k q hq0 hq1 = q := by
    simpa using (Eq.symm (resolveQ_add_residualQ (k := k) (q := q) hq0 hq1))
  calc
    resolveQ k q hq0 hq1 ≤ resolveQ k q hq0 hq1 + residualQ k q hq0 hq1 :=
      le_add_of_nonneg_right hnonneg
    _ = q := hsum

theorem lt_resolveQ_add_invSL (k : Nat) {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    q < resolveQ k q hq0 hq1 + (1 : ℚ) / (SL k : ℚ) := by
  have hlt :
      resolveQ k q hq0 hq1 + residualQ k q hq0 hq1 <
        resolveQ k q hq0 hq1 + (1 : ℚ) / (SL k : ℚ) := by
    exact add_lt_add_left (residualQ_lt (k := k) (q := q) hq0 hq1) (resolveQ k q hq0 hq1)
  have hdecomp : q = resolveQ k q hq0 hq1 + residualQ k q hq0 hq1 :=
    resolveQ_add_residualQ (k := k) (q := q) hq0 hq1
  exact lt_of_eq_of_lt hdecomp hlt

theorem resolveQ_eq_addrQ_of_mem_coarseInterval (k : Nat)
    {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    {x : Fin (SL k)} (hx : q ∈ coarseInterval k x) :
    resolveQ k q hq0 hq1 = addrQ k x := by
  have hx0 : q ∈ coarseInterval k (floorBin k q hq0 hq1) :=
    floorBin_mem_coarseInterval (k := k) (q := q) hq0 hq1
  have hxeq : x = floorBin k q hq0 hq1 :=
    coarseInterval_eq_of_mem_of_mem (k := k) (x := x) (y := floorBin k q hq0 hq1) (q := q) hx hx0
  have hfloor : floorBin k q hq0 hq1 = x := hxeq.symm
  have hres : resolveQ k q hq0 hq1 = addrQ k (floorBin k q hq0 hq1) :=
    resolveQ_eq_addrQ_floorBin (k := k) (q := q) hq0 hq1
  simpa [hfloor] using hres

theorem mem_coarseInterval_iff_resolveQ_eq_addrQ (k : Nat)
    {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) (x : Fin (SL k)) :
    q ∈ coarseInterval k x ↔ resolveQ k q hq0 hq1 = addrQ k x := by
  constructor
  · intro hx
    exact resolveQ_eq_addrQ_of_mem_coarseInterval (k := k) (q := q) hq0 hq1 hx
  · intro hEq
    dsimp [coarseInterval]
    refine ⟨?_, ?_⟩
    · -- Lower bound: `addrQ k x ≤ q` from `resolveQ_le`.
      have hle : resolveQ k q hq0 hq1 ≤ q := resolveQ_le (k := k) (q := q) hq0 hq1
      simpa [hEq] using hle
    · -- Upper bound: `q < addrQ k x + 1/SL k` from `lt_resolveQ_add_invSL`.
      have hlt : q < resolveQ k q hq0 hq1 + (1 : ℚ) / (SL k : ℚ) :=
        lt_resolveQ_add_invSL (k := k) (q := q) hq0 hq1
      simpa [hEq] using hlt

theorem floorBin_eq_of_resolveQ_eq_addrQ (k : Nat)
    {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) {x : Fin (SL k)}
    (hEq : resolveQ k q hq0 hq1 = addrQ k x) :
    floorBin k q hq0 hq1 = x := by
  have hx : q ∈ coarseInterval k x :=
    (mem_coarseInterval_iff_resolveQ_eq_addrQ (k := k) (q := q) hq0 hq1 x).2 hEq
  have hy : q ∈ coarseInterval k (floorBin k q hq0 hq1) :=
    floorBin_mem_coarseInterval (k := k) (q := q) hq0 hq1
  have hxeq :
      x = floorBin k q hq0 hq1 :=
    coarseInterval_eq_of_mem_of_mem (k := k) (x := x) (y := floorBin k q hq0 hq1) (q := q) hx hy
  exact hxeq.symm

theorem resolveQ_eq_addrQ_iff_floorBin_eq (k : Nat)
    {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) (x : Fin (SL k)) :
    resolveQ k q hq0 hq1 = addrQ k x ↔ floorBin k q hq0 hq1 = x := by
  constructor
  · intro hEq
    exact floorBin_eq_of_resolveQ_eq_addrQ (k := k) (q := q) hq0 hq1 (x := x) hEq
  · intro hBin
    have hRes : resolveQ k q hq0 hq1 = addrQ k (floorBin k q hq0 hq1) :=
      resolveQ_eq_addrQ_floorBin (k := k) (q := q) hq0 hq1
    simpa [hBin] using hRes

theorem mem_coarseInterval_iff_floorBin_eq (k : Nat)
    {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) (x : Fin (SL k)) :
    q ∈ coarseInterval k x ↔ floorBin k q hq0 hq1 = x := by
  -- Coarse-bin membership is equivalent to the resolved-prefix equality, which is
  -- equivalent to equality of the unique selected bin (`floorBin`).
  exact Iff.trans
    (mem_coarseInterval_iff_resolveQ_eq_addrQ (k := k) (q := q) hq0 hq1 x)
    (resolveQ_eq_addrQ_iff_floorBin_eq (k := k) (q := q) hq0 hq1 x)

theorem floorBin_mono (k : Nat) {q q' : ℚ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hq0' : 0 ≤ q') (hq1' : q' < 1) (hqq' : q ≤ q') :
    floorBin k q hq0 hq1 ≤ floorBin k q' hq0' hq1' := by
  have hSL0 : 0 ≤ (SL k : ℚ) := by
    exact_mod_cast (Nat.zero_le (SL k))
  have hm : q * (SL k : ℚ) ≤ q' * (SL k : ℚ) :=
    mul_le_mul_of_nonneg_right hqq' hSL0
  -- `floorBin` is defined by a `Nat.floor`, and `Nat.floor` is monotone.
  simpa [floorBin] using (Nat.floor_mono hm)

theorem resolveQ_mono (k : Nat) {q q' : ℚ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hq0' : 0 ≤ q') (hq1' : q' < 1) (hqq' : q ≤ q') :
    resolveQ k q hq0 hq1 ≤ resolveQ k q' hq0' hq1' := by
  have hSL0 : 0 ≤ (SL k : ℚ) := by
    exact_mod_cast (Nat.zero_le (SL k))
  have hm : q * (SL k : ℚ) ≤ q' * (SL k : ℚ) :=
    mul_le_mul_of_nonneg_right hqq' hSL0
  have hfloor : (Nat.floor (q * (SL k : ℚ)) : ℚ) ≤ (Nat.floor (q' * (SL k : ℚ)) : ℚ) := by
    exact_mod_cast (Nat.floor_mono hm)
  have hden : 0 < (SL k : ℚ) := by
    exact_mod_cast (SL_pos k)
  -- Rewrite both sides using the closed form, then divide the floor inequality by the positive denominator.
  calc
    resolveQ k q hq0 hq1
        = (Nat.floor (q * (SL k : ℚ)) : ℚ) / (SL k : ℚ) := by
          simpa using (resolveQ_eq_floor (k := k) (q := q) hq0 hq1)
    _ ≤ (Nat.floor (q' * (SL k : ℚ)) : ℚ) / (SL k : ℚ) :=
          div_le_div_of_nonneg_right hfloor (le_of_lt hden)
    _ = resolveQ k q' hq0' hq1' := by
          symm
          simpa using (resolveQ_eq_floor (k := k) (q := q') hq0' hq1')

theorem floorBin_lt_imp_exists_gridpoint_between (k : Nat) {q q' : ℚ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hq0' : 0 ≤ q') (hq1' : q' < 1)
    (hbin : floorBin k q hq0 hq1 < floorBin k q' hq0' hq1') :
    ∃ n : Nat, n < SL k ∧ q < (n : ℚ) / (SL k : ℚ) ∧ (n : ℚ) / (SL k : ℚ) ≤ q' := by
  have hden_pos : (0 : ℚ) < (SL k : ℚ) := by
    exact_mod_cast (SL_pos k)
  have hfloorlt : Nat.floor (q * (SL k : ℚ)) < Nat.floor (q' * (SL k : ℚ)) := by
    -- `floorBin` compares by the underlying floor-index.
    simpa [floorBin] using hbin
  let n : Nat := Nat.floor (q * (SL k : ℚ)) + 1
  have hn_le_floor' : n ≤ Nat.floor (q' * (SL k : ℚ)) :=
    Nat.succ_le_of_lt hfloorlt
  have hfloor'_lt_SL : Nat.floor (q' * (SL k : ℚ)) < SL k :=
    floor_lt_SL_of_mem_Icc (k := k) (q := q') hq0' hq1'
  have hn_lt_SL : n < SL k := lt_of_le_of_lt hn_le_floor' hfloor'_lt_SL
  refine ⟨n, hn_lt_SL, ?_, ?_⟩
  · -- Left strict bound: `q < n / den` (equivalently: `q*den < n`).
    have hqn : q * (SL k : ℚ) < (n : ℚ) := by
      have h := (Nat.lt_floor_add_one (a := q * (SL k : ℚ)))
      simpa [n] using h
    exact (lt_div_iff₀ hden_pos).2 hqn
  · -- Right bound: `n / den ≤ q'` (equivalently: `n ≤ q'*den`).
    have hb0 : 0 ≤ q' * (SL k : ℚ) := mul_nonneg hq0' (le_of_lt hden_pos)
    have hfloor_le_b : (Nat.floor (q' * (SL k : ℚ)) : ℚ) ≤ q' * (SL k : ℚ) := by
      simpa using (Nat.floor_le (a := q' * (SL k : ℚ)) hb0)
    have hn_le_floor_cast :
        (n : ℚ) ≤ (Nat.floor (q' * (SL k : ℚ)) : ℚ) := by
      exact_mod_cast hn_le_floor'
    have hn_le_b : (n : ℚ) ≤ q' * (SL k : ℚ) :=
      le_trans hn_le_floor_cast hfloor_le_b
    exact (div_le_iff₀ hden_pos).2 hn_le_b

theorem resolveQ_lt_imp_exists_gridpoint_between (k : Nat) {q q' : ℚ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hq0' : 0 ≤ q') (hq1' : q' < 1)
    (hres : resolveQ k q hq0 hq1 < resolveQ k q' hq0' hq1') :
    ∃ n : Nat, n < SL k ∧ q < (n : ℚ) / (SL k : ℚ) ∧ (n : ℚ) / (SL k : ℚ) ≤ q' := by
  have hden_pos : (0 : ℚ) < (SL k : ℚ) := by
    exact_mod_cast (SL_pos k)
  -- Convert the strict inequality of resolved prefixes into a strict inequality on the floor indices.
  have hnum_lt : (Nat.floor (q * (SL k : ℚ)) : ℚ) < (Nat.floor (q' * (SL k : ℚ)) : ℚ) := by
    -- `resolveQ` has the explicit `Nat.floor` form at depth `k`.
    have hq := resolveQ_eq_floor (k := k) (q := q) hq0 hq1
    have hq' := resolveQ_eq_floor (k := k) (q := q') hq0' hq1'
    -- Rewrite, then clear the positive denominator.
    have : ((Nat.floor (q * (SL k : ℚ)) : ℚ) / (SL k : ℚ))
          < ((Nat.floor (q' * (SL k : ℚ)) : ℚ) / (SL k : ℚ)) := by
      simpa [hq, hq'] using hres
    exact (div_lt_div_iff_of_pos_right hden_pos).1 this
  have hfloorlt : Nat.floor (q * (SL k : ℚ)) < Nat.floor (q' * (SL k : ℚ)) := by
    exact_mod_cast hnum_lt
  have hbin : floorBin k q hq0 hq1 < floorBin k q' hq0' hq1' := by
    simpa [floorBin] using hfloorlt
  exact floorBin_lt_imp_exists_gridpoint_between (k := k) (q := q) (q' := q') hq0 hq1 hq0' hq1' hbin

end IndexOfIndexesSubintervals
