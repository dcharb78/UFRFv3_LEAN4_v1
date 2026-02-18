import Index_Of_Indexes_Theorem
import Breathing_Cycle_LOG_Partition_Theorem
import RecursiveGrid_IndexOfIndexes_Bridge_Theorem

/-!
# Multi-Axis Phase Lift (Bounded, Discrete)

`BreathingCycleLOGPartition.phaseOf : Fin 13 → Phase` classifies a single digit/position
into one of the five breathing-cycle phase classes.

This file lifts that digit-level classifier to the concurrent `IndexOfIndexes.Digits k`
coordinate system (the canonical `13^k` state space) and proves the basic per-axis
counting independence:

For any depth `d < k+1`, the number of `Digits (k+1)` states whose depth-`d` digit lies in
phase `p` is exactly:

`13^k * |phaseSet p|`.

This is purely discrete mechanism: it is a counting statement about nested base-13 digits.
No physical interpretation is asserted here.
-/

namespace MultiAxisPhaseLift

open IndexOfIndexes
open BreathingCycleLOGPartition

abbrev Pos13 := BreathingCycleLOGPartition.Pos
abbrev Phase13 := BreathingCycleLOGPartition.Phase

/-- Definitional transport: `Fin base` is the same as `Fin 13` (`Pos13`). -/
def basePosEquiv : Fin base ≃ Pos13 := by
  simpa [IndexOfIndexes.base, BreathingCycleLOGPartition.Pos] using (Equiv.refl (Fin 13))

/-- `Digits k` is finite for every `k` (nested products of `Fin 13`). -/
instance instFintypeDigits : (k : Nat) → Fintype (Digits k)
  | 0 => by
      -- `Digits 0 = Unit`
      dsimp [Digits]
      infer_instance
  | k + 1 => by
      -- `Digits (k+1) = Digits k × Fin base`
      letI : Fintype (Digits k) := instFintypeDigits k
      dsimp [Digits]
      infer_instance

/--
Extract the depth-`d` digit from a nested `Digits k` coordinate (as a `Fin base` value).

Depth `0` is the fine (least-significant) digit, depth `1` is the next digit, etc.
-/
def digitAt : (k : Nat) → Digits k → Nat → Fin base
  | 0, _, _ => ⟨0, by simp [IndexOfIndexes.base]⟩
  | _ + 1, x, 0 => x.2
  | k + 1, x, d + 1 => digitAt k x.1 d

/-- The lifted phase lens: apply `phaseOf` to the extracted digit at depth `d`. -/
def phaseAt (k : Nat) (x : Digits k) (d : Nat) : Phase13 :=
  phaseOf (basePosEquiv (digitAt k x d))

/-- Cardinality of the `Digits k` state space is exactly `13^k`. -/
theorem card_Digits (k : Nat) : Fintype.card (Digits k) = SL k := by
  classical
  have h := Fintype.card_congr (digitsEquiv k)
  -- `h : card (Fin (SL k)) = card (Digits k)` and `card (Fin n) = n`.
  have : SL k = Fintype.card (Digits k) := by
    simpa using h
  exact this.symm

/-- Phase-class cardinality expressed as a finset-cardinality (`phaseSet`). -/
theorem card_phaseOf_eq (p : Phase13) :
    Fintype.card { z : Pos13 // phaseOf z = p } = (phaseSet p).card := by
  classical
  have H : ∀ z : Pos13, z ∈ phaseSet p ↔ phaseOf z = p := by
    intro z
    simpa using (mem_phaseSet_iff_phaseOf_eq z p)
  simpa using
    (Fintype.card_of_subtype (p := fun z : Pos13 => phaseOf z = p) (s := phaseSet p) H)

/-- Transport the phase predicate from `Fin base` to `Pos13` via `basePosEquiv`. -/
def digitPhaseEquiv (p : Phase13) :
    { r : Fin base // phaseOf (basePosEquiv r) = p } ≃ { z : Pos13 // phaseOf z = p } := by
  refine
    { toFun := fun r => ⟨basePosEquiv r.1, r.2⟩
      invFun := fun z => ⟨basePosEquiv.symm z.1, by simpa using z.2⟩
      left_inv := by
        intro r
        apply Subtype.ext
        simp
      right_inv := by
        intro z
        apply Subtype.ext
        simp }

theorem card_digitPhase (p : Phase13) :
    Fintype.card { r : Fin base // phaseOf (basePosEquiv r) = p } = (phaseSet p).card := by
  classical
  have hCard :
      Fintype.card { r : Fin base // phaseOf (basePosEquiv r) = p } =
        Fintype.card { z : Pos13 // phaseOf z = p } := by
    simpa using (Fintype.card_congr (digitPhaseEquiv p))
  exact hCard.trans (card_phaseOf_eq (p := p))

/-- Depth-0 cardinality factorization: predicate depends only on the fine digit. -/
def depth0Equiv (k : Nat) (p : Phase13) :
    { y : Digits (k + 1) // phaseAt (k + 1) y 0 = p } ≃
      Digits k × { r : Fin base // phaseOf (basePosEquiv r) = p } := by
  refine
    { toFun := fun y =>
        (y.1.1, ⟨y.1.2, by simpa [phaseAt, digitAt] using y.2⟩)
      invFun := fun z =>
        ⟨(z.1, z.2.1), by simpa [phaseAt, digitAt] using z.2.2⟩
      left_inv := by
        intro y
        apply Subtype.ext
        simp
      right_inv := by
        intro z
        cases z with
        | mk x r =>
            cases r with
            | mk r hr =>
                simp }

theorem phaseAt_axis_count_depth0 (k : Nat) (p : Phase13) :
    Fintype.card { y : Digits (k + 1) // phaseAt (k + 1) y 0 = p } =
      SL k * (phaseSet p).card := by
  classical
  calc
    Fintype.card { y : Digits (k + 1) // phaseAt (k + 1) y 0 = p } =
        Fintype.card (Digits k × { r : Fin base // phaseOf (basePosEquiv r) = p }) := by
          simpa using (Fintype.card_congr (depth0Equiv (k := k) (p := p)))
    _ = Fintype.card (Digits k) * Fintype.card { r : Fin base // phaseOf (basePosEquiv r) = p } := by
          simp [Fintype.card_prod]
    _ = SL k * (phaseSet p).card := by
          simp [card_Digits, card_digitPhase]

/-- Depth-`d+1` factorization: predicate depends only on the prefix (`Digits k`) component. -/
def depthSuccEquiv (k : Nat) (d : Nat) (p : Phase13) :
    { y : Digits (k + 1) // phaseAt (k + 1) y (d + 1) = p } ≃
      { x : Digits k // phaseAt k x d = p } × Fin base := by
  refine
    { toFun := fun y =>
        (⟨y.1.1, by simpa [phaseAt, digitAt] using y.2⟩, y.1.2)
      invFun := fun z =>
        ⟨(z.1.1, z.2), by simpa [phaseAt, digitAt] using z.1.2⟩
      left_inv := by
        intro y
        apply Subtype.ext
        simp
      right_inv := by
        intro z
        cases z with
        | mk x r =>
            cases x with
            | mk x hx =>
                simp }

/--
Packaged statement: multi-axis phase lift with per-axis counting independence.

At digit-depth `d < k+1`, the number of `Digits (k+1)` states whose `d`-th digit is in phase `p`
is exactly `13^k * |phaseSet p|`.
-/
def multi_axis_phase_lift_stmt : Prop :=
  ∀ (k d : Nat) (_hd : d < k + 1) (p : Phase13),
    Fintype.card { y : Digits (k + 1) // phaseAt (k + 1) y d = p } =
      SL k * (phaseSet p).card

theorem multi_axis_phase_lift : multi_axis_phase_lift_stmt := by
  intro k d hd p
  -- Induct on the depth `d`, with the induction hypothesis quantified over `k`.
  revert k hd p
  induction d with
  | zero =>
      intro k _ p
      -- Depth 0 is the fine digit; the count is a direct product factorization.
      simpa using (phaseAt_axis_count_depth0 (k := k) (p := p))
  | succ d ih =>
      intro k hd p
      cases k with
      | zero =>
          -- `d+1 < 1` is impossible.
          have hd0 : d < 0 := by
            have : Nat.succ d < Nat.succ 0 := by
              simpa using hd
            exact Nat.succ_lt_succ_iff.1 this
          exact (Nat.not_lt_zero d hd0).elim
      | succ k' =>
          -- Reduce depth `d+1` at `k+2` to depth `d` at `k+1`, then multiply by the free fine digit.
          have hd' : d < k' + 1 := by
            have : Nat.succ d < Nat.succ (k' + 1) := by
              -- `Nat.succ k' + 1` is definitional `Nat.succ (k' + 1)` after normalization.
              simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hd
            exact Nat.succ_lt_succ_iff.1 this
          -- Factor the subtype as `(prefix-subtype) × Fin base`.
          have hCard :
              Fintype.card { y : Digits (Nat.succ k' + 1) // phaseAt (Nat.succ k' + 1) y (d + 1) = p } =
                Fintype.card ({ x : Digits (k' + 1) // phaseAt (k' + 1) x d = p } × Fin base) := by
            simpa using
              (Fintype.card_congr (depthSuccEquiv (k := Nat.succ k') (d := d) (p := p)))
          -- Use IH on the prefix count (parameter `k`), then rewrite `SL (k+1) = SL k * base`.
          have hPrefix :
              Fintype.card { x : Digits (k' + 1) // phaseAt (k' + 1) x d = p } =
                SL k' * (phaseSet p).card := by
            -- IH expects the predecessor parameter `k'` and proof `d < k'+1`.
            simpa using (ih (k := k') hd' p)
          calc
            Fintype.card { y : Digits (Nat.succ k' + 1) // phaseAt (Nat.succ k' + 1) y (d + 1) = p }
                = Fintype.card ({ x : Digits (k' + 1) // phaseAt (k' + 1) x d = p } × Fin base) := by
                    exact hCard
            _ = Fintype.card { x : Digits (k' + 1) // phaseAt (k' + 1) x d = p } * Fintype.card (Fin base) := by
                    simp [Fintype.card_prod]
            _ = (SL k' * (phaseSet p).card) * base := by
                    simp [hPrefix]
            _ = SL (k' + 1) * (phaseSet p).card := by
                    -- `SL (k+1) = SL k * base`, and rearrange multiplication.
                    simp [SL_succ, Nat.mul_assoc, Nat.mul_comm]

/-
## Transport Back to `Fin (13^k)` (Canonical View)

The kernel typically speaks in `Fin (13^k)` coordinates. The lemma below transports the
multi-axis phase-counting statement back to that view via `digitsEquiv`.
-/

/-- Phase lens on the canonical `Fin (13^k)` state space, defined via `digitsEquiv`. -/
def phaseAtFin (k : Nat) (x : Fin (SL k)) (d : Nat) : Phase13 :=
  phaseAt k (digitsEquiv k x) d

def phaseAtFinEquiv (k d : Nat) (p : Phase13) :
    { x : Fin (SL (k + 1)) // phaseAtFin (k + 1) x d = p } ≃
      { y : Digits (k + 1) // phaseAt (k + 1) y d = p } := by
  refine
    { toFun := fun x => ⟨digitsEquiv (k + 1) x.1, x.2⟩
      invFun := fun y =>
        ⟨(digitsEquiv (k + 1)).symm y.1, by
          -- `phaseAtFin` is definitionally `phaseAt ∘ digitsEquiv`.
          simpa [phaseAtFin] using y.2⟩
      left_inv := by
        intro x
        apply Subtype.ext
        simp
      right_inv := by
        intro y
        apply Subtype.ext
        simp }

def multi_axis_phase_lift_fin_stmt : Prop :=
  ∀ (k d : Nat) (_hd : d < k + 1) (p : Phase13),
    Fintype.card { x : Fin (SL (k + 1)) // phaseAtFin (k + 1) x d = p } =
      SL k * (phaseSet p).card

theorem multi_axis_phase_lift_fin : multi_axis_phase_lift_fin_stmt := by
  intro k d hd p
  classical
  have hCard :
      Fintype.card { x : Fin (SL (k + 1)) // phaseAtFin (k + 1) x d = p } =
        Fintype.card { y : Digits (k + 1) // phaseAt (k + 1) y d = p } := by
    simpa using (Fintype.card_congr (phaseAtFinEquiv (k := k) (d := d) (p := p)))
  -- Reduce to the already-proved `Digits` statement.
  exact hCard.trans (multi_axis_phase_lift k d hd p)

/-!
## Phase Lens Projection Compatibility (Mechanism Only)

This is the discrete statement that the `phaseAtFin` lens is compatible with the natural
prefix projection `Fin (13^(k+1)) → Fin (13^k)` induced by `digitsEquiv`.

Interpretation: deeper-digit phase classification depends only on the corresponding prefix,
so it is stable under "forgetting" the finest digit.
-/

/-- Prefix projection `Fin (13^(k+1)) → Fin (13^k)` via `digitsEquiv`. -/
def prefixFin (k : Nat) (x : Fin (SL (k + 1))) : Fin (SL k) :=
  (digitsEquiv k).symm (digitsEquiv (k + 1) x).1

def phaseAtFin_projection_compat_stmt : Prop :=
  ∀ (k : Nat) (x : Fin (SL (k + 1))) (d : Nat),
    phaseAtFin (k + 1) x (d + 1) = phaseAtFin k (prefixFin k x) d

theorem phaseAtFin_projection_compat : phaseAtFin_projection_compat_stmt := by
  intro k x d
  -- Unfold to the `Digits` view and use the definitional recursion of `digitAt`.
  simp [phaseAtFin, prefixFin, phaseAt, digitAt]

/-!
## Phase Lens ↔ Recursive-Grid Digit Bridge (Mechanism Equivalence)

`RecursiveGridIndexBridge.digitsCoord` extracts base-13 digits from a `Digits k` coordinate and
proves those digits agree with the recursive-grid digit extractor `RecursiveGridBase13.digit`.

The lemma below shows our `digitAt`/`phaseAtFin` lens is the same mechanism: it is just
the phase classifier applied to the recursive digit at depth `d`.
-/

theorem digitAt_val_eq_digitsCoord :
    ∀ (k : Nat) (x : Digits k) (d : Nat),
      (digitAt k x d).1 = RecursiveGridIndexBridge.digitsCoord k x d := by
  intro k
  induction k with
  | zero =>
      intro x d
      cases x
      simp [digitAt, RecursiveGridIndexBridge.digitsCoord]
  | succ k ih =>
      intro x d
      cases d with
      | zero =>
          simp [digitAt, RecursiveGridIndexBridge.digitsCoord]
      | succ d =>
          simpa [digitAt, RecursiveGridIndexBridge.digitsCoord] using (ih x.1 d)

theorem phaseAtFin_eq_phaseOf_recursiveDigit
    (k : Nat) (x : Fin (SL k)) (d : Nat) (hd : d < k) :
    phaseAtFin k x d =
      phaseOf
        (basePosEquiv
          (⟨RecursiveGridBase13.digit d x.1, by
              -- `RecursiveGridBase13.base = 13 = IndexOfIndexes.base`.
              simpa [RecursiveGridBase13.base, IndexOfIndexes.base] using
                (RecursiveGridBase13.digit_lt_base d x.1)⟩ : Fin base)) := by
  -- Identify the underlying digit value with the recursive-grid digit.
  have hDigitVal :
      (digitAt k (digitsEquiv k x) d).1 = RecursiveGridBase13.digit d x.1 := by
    calc
      (digitAt k (digitsEquiv k x) d).1 =
          RecursiveGridIndexBridge.digitsCoord k (digitsEquiv k x) d := by
            simpa using (digitAt_val_eq_digitsCoord (k := k) (x := digitsEquiv k x) (d := d))
      _ = RecursiveGridBase13.digit d x.1 := by
            simpa using
              (RecursiveGridIndexBridge.digitsCoord_digitsEquiv_eq_digit (k := k) (x := x) d hd)
  -- Upgrade the `.val` equality to a `Fin` equality and rewrite the phase lens.
  have hFin :
      digitAt k (digitsEquiv k x) d =
        (⟨RecursiveGridBase13.digit d x.1, by
            simpa [RecursiveGridBase13.base, IndexOfIndexes.base] using
              (RecursiveGridBase13.digit_lt_base d x.1)⟩ : Fin base) := by
    apply Fin.ext
    exact hDigitVal
  -- Now unfold `phaseAtFin` and rewrite by the identified digit.
  simp [phaseAtFin, phaseAt, hFin]

def phaseAtFin_recursive_digit_bridge_stmt : Prop :=
  ∀ (k : Nat) (x : Fin (SL k)) (d : Nat) (hd : d < k),
    phaseAtFin k x d =
      phaseOf
        (basePosEquiv
          (⟨RecursiveGridBase13.digit d x.1, by
              simpa [RecursiveGridBase13.base, IndexOfIndexes.base] using
                (RecursiveGridBase13.digit_lt_base d x.1)⟩ : Fin base))

theorem phaseAtFin_recursive_digit_bridge : phaseAtFin_recursive_digit_bridge_stmt := by
  intro k x d hd
  exact phaseAtFin_eq_phaseOf_recursiveDigit (k := k) (x := x) (d := d) hd

/-
## Phase Successor Lift With Carry (Bounded, Discrete)

This step makes the depth-0 *dynamic* explicit:

* Global successor on `Fin (13^k)` is "add 1 with wrap".
* Depth-0 position evolves by the single-digit successor `succ13` (mod 13).
* The prefix projection only changes at the carry boundary `digit0 = 12`.

This is still mechanism-only (no physical interpretation).
-/

/-- Wrap-around successor on the canonical `Fin (13^k)` clock. -/
def succSL (k : Nat) (x : Fin (SL k)) : Fin (SL k) :=
  ⟨(x.1 + 1) % SL k, Nat.mod_lt _ (SL_pos k)⟩

/-- The depth-0 position corresponding to a `Nat` tick (reduce mod 13). -/
def pos0 (t : Nat) : Pos13 :=
  ⟨t % base, by
    have hb : 0 < base := by simp [IndexOfIndexes.base]
    exact Nat.mod_lt t hb⟩

theorem pos0_val (t : Nat) : (pos0 t).1 = t % base := by
  rfl

theorem pos0_succSL (k : Nat) (x : Fin (SL (k + 1))) :
    pos0 (succSL (k + 1) x).1 = succ13 (pos0 x.1) := by
  apply Fin.ext
  -- Reduce mod `SL (k+1)` then mod `base` (since `base ∣ SL (k+1)`).
  have hdiv : base ∣ SL (k + 1) := by
    refine ⟨SL k, ?_⟩
    -- `SL (k+1) = SL k * base`.
    simp [SL_succ, Nat.mul_comm, Nat.mul_assoc]
  -- Evaluate both sides in `Nat` values.
  -- LHS = `((x+1) % SL(k+1)) % base`.
  -- RHS = `((x % base) + 1) % base`.
  have hmod :
      ((x.1 + 1) % SL (k + 1)) % base = (x.1 + 1) % base := by
    simpa using (Nat.mod_mod_of_dvd (x.1 + 1) hdiv)
  calc
    (pos0 (succSL (k + 1) x).1).1
        = ((x.1 + 1) % SL (k + 1)) % base := by
            simp [pos0, succSL]
    _ = (x.1 + 1) % base := hmod
    _ = (x.1 % base + 1) % base := by
            -- Expand `(+1) % base` via `Nat.add_mod`.
            simp [Nat.add_mod, IndexOfIndexes.base]
    _ = (succ13 (pos0 x.1)).1 := by
            simp [succ13, pos0, IndexOfIndexes.base]

theorem phaseAtFin_depth0_eq_phaseOf_pos0 (k : Nat) (x : Fin (SL (k + 1))) :
    phaseAtFin (k + 1) x 0 = phaseOf (pos0 x.1) := by
  -- Use the certified recursive-digit bridge at depth `0`.
  have h :=
    phaseAtFin_recursive_digit_bridge (k := k + 1) (x := x) (d := 0) (hd := Nat.zero_lt_succ k)
  -- `digit 0 t = t % 13`.
  simpa [pos0, basePosEquiv, RecursiveGridBase13.digit, RecursiveGridBase13.base,
    IndexOfIndexes.base] using h

theorem phaseAtFin_depth0_succSL (k : Nat) (x : Fin (SL (k + 1))) :
    phaseAtFin (k + 1) (succSL (k + 1) x) 0 = phaseOf (succ13 (pos0 x.1)) := by
  -- Rewrite the LHS by `pos0` and the RHS by the `pos0` successor law.
  simpa [phaseAtFin_depth0_eq_phaseOf_pos0, pos0_succSL] using
    (phaseAtFin_depth0_eq_phaseOf_pos0 (k := k) (x := succSL (k + 1) x))

theorem phaseAtFin_depth0_succSL_eq_of_not_boundary
    (k : Nat) (x : Fin (SL (k + 1))) (hx : pos0 x.1 ∉ phaseBoundaries) :
    phaseAtFin (k + 1) (succSL (k + 1) x) 0 = phaseAtFin (k + 1) x 0 := by
  -- Lift the single-digit boundary lemma through `pos0`.
  have hphase : phaseOf (succ13 (pos0 x.1)) = phaseOf (pos0 x.1) :=
    phaseOf_succ13_eq_of_not_boundary (pos0 x.1) hx
  calc
    phaseAtFin (k + 1) (succSL (k + 1) x) 0
        = phaseOf (succ13 (pos0 x.1)) := phaseAtFin_depth0_succSL (k := k) (x := x)
    _ = phaseOf (pos0 x.1) := hphase
    _ = phaseAtFin (k + 1) x 0 := (phaseAtFin_depth0_eq_phaseOf_pos0 (k := k) (x := x)).symm

theorem mod_return_of_dvd_succ (t : Nat) (h : base ∣ t + 1) : t % base = base - 1 := by
  have hb0 : 0 < base := by simp [IndexOfIndexes.base]
  -- `0 = (t+1) % base = (t % base + 1) % base`.
  have h0 : (t % base + 1) % base = 0 := by
    have : (t + 1) % base = 0 := Nat.mod_eq_zero_of_dvd h
    -- Expand `(t+1) % base` via `Nat.add_mod` and simplify `1 % base = 1`.
    simpa [Nat.add_mod, IndexOfIndexes.base] using this
  -- Let `r = t % base`. Since `r < base`, the only way `(r+1) % base = 0` is `r+1 = base`.
  have hr_lt : t % base < base := Nat.mod_lt t hb0
  have hr1_le : t % base + 1 ≤ base := Nat.succ_le_of_lt hr_lt
  have hr1_ge : base ≤ t % base + 1 := Nat.le_of_not_gt (by
    intro hlt
    -- If `r+1 < base`, then `(r+1) % base = r+1 ≠ 0`.
    have : (t % base + 1) % base = t % base + 1 := Nat.mod_eq_of_lt hlt
    simpa [this] using h0)
  have hr1_eq : t % base + 1 = base := le_antisymm hr1_le hr1_ge
  -- Turn `r+1 = base` into `r = base-1`.
  have : base = (t % base).succ := by
    simpa [Nat.succ_eq_add_one] using hr1_eq.symm
  -- `pred` is `-1` on `Nat`.
  have : base.pred = t % base := Nat.pred_eq_of_eq_succ this
  simpa [Nat.pred_eq_sub_one] using this.symm

theorem prefixFin_succSL_eq_ite (k : Nat) (x : Fin (SL (k + 1))) :
    prefixFin k (succSL (k + 1) x) =
      if x.1 % base = base - 1 then succSL k (prefixFin k x) else prefixFin k x := by
  apply Fin.ext
  set t : Nat := x.1
  have hb0 : 0 < base := by simp [IndexOfIndexes.base]
  have ht_lt : t < SL (k + 1) := by simpa [t] using x.2
  -- Prefix coordinate is the quotient by `base`.
  have hpref_val (y : Fin (SL (k + 1))) : (prefixFin k y).1 = y.1 / base := by
    simpa [prefixFin, RecursiveGridIndexBridge.digitsEquiv_succ_apply] using
      (RecursiveGridIndexBridge.splitEquiv_fst_val (k := k) (x := y))
  have hL : (prefixFin k (succSL (k + 1) x)).1 = (succSL (k + 1) x).1 / base := hpref_val _ 
  have hR : (prefixFin k x).1 = t / base := by simpa [t] using (hpref_val x)
  -- The successor value is either `t+1` or wraps to `0` at the terminal tick.
  by_cases hlast : t + 1 = SL (k + 1)
  · have hs : (succSL (k + 1) x).1 = 0 := by
      simp [succSL, t, hlast]
    -- Carry holds since `base ∣ SL (k+1) = t+1`.
    have hdiv : base ∣ t + 1 := by
      refine ⟨SL k, ?_⟩
      simpa [hlast, SL_succ, Nat.mul_comm, Nat.mul_assoc]
    have hcarry : t % base = base - 1 := mod_return_of_dvd_succ (t := t) hdiv
    -- In the wrap case, `t/base + 1 = SL k`.
    have hq : t / base + 1 = SL k := by
      have h1 : (t + 1) / base = t / base + 1 := Nat.succ_div_of_dvd hdiv
      have h2 : (t + 1) / base = SL k := by
        calc
          (t + 1) / base = SL (k + 1) / base := by simpa [hlast]
          _ = (SL k * base) / base := by simp [SL_succ]
          _ = SL k := Nat.mul_div_cancel (SL k) hb0
      calc
        t / base + 1 = (t + 1) / base := by simpa using h1.symm
        _ = SL k := h2
    -- Both sides evaluate to `0` (full wrap at this scale implies wrap at the prefix scale).
    have hL0 : (prefixFin k (succSL (k + 1) x)).1 = 0 := by
      calc
        (prefixFin k (succSL (k + 1) x)).1 = (succSL (k + 1) x).1 / base := hL
        _ = 0 / base := by simpa [hs]
        _ = 0 := by simp
    have hR0 : (succSL k (prefixFin k x)).1 = 0 := by
      -- `prefixFin k x` has value `t/base`, and `t/base + 1 = SL k`, so successor wraps to `0`.
      simp [succSL, hR, hq]
    -- Close the goal without unfolding `succSL (k+1) x` inside `prefixFin`.
    simpa [t, hcarry, hL0, hR0]
  · have ht1_le : t + 1 ≤ SL (k + 1) := Nat.succ_le_of_lt ht_lt
    have ht1_lt : t + 1 < SL (k + 1) := Nat.lt_of_le_of_ne ht1_le hlast
    have hs : (succSL (k + 1) x).1 = t + 1 := by
      simp [succSL, t, Nat.mod_eq_of_lt ht1_lt]
    -- Split on carry boundary at depth 0.
    by_cases hcarry : t % base = base - 1
    · have hdiv : base ∣ t + 1 := by
        have hc0 : (t + 1) % base = 0 := by
          have := (RecursiveGridBase13.carry_at_return (t := t) (ht := hcarry)).1
          simpa [RecursiveGridBase13.base, IndexOfIndexes.base] using this
        exact Nat.dvd_of_mod_eq_zero hc0
      have h1 : (t + 1) / base = t / base + 1 := Nat.succ_div_of_dvd hdiv
      -- No wrap at the prefix level: `(t+1)/base < SL k`.
      have htdiv1_lt : t / base + 1 < SL k := by
        have hmul : t + 1 < base * SL k := by
          simpa [SL_succ, Nat.mul_comm, Nat.mul_assoc] using ht1_lt
        have : (t + 1) / base < SL k := Nat.div_lt_of_lt_mul hmul
        simpa [h1] using this
      have hL1 : (prefixFin k (succSL (k + 1) x)).1 = t / base + 1 := by
        calc
          (prefixFin k (succSL (k + 1) x)).1 = (succSL (k + 1) x).1 / base := hL
          _ = (t + 1) / base := by simpa [hs]
          _ = t / base + 1 := by simpa [h1]
      have hR1 : (succSL k (prefixFin k x)).1 = t / base + 1 := by
        -- No wrap at the prefix: the mod is identity.
        simp [succSL, hR, Nat.mod_eq_of_lt htdiv1_lt]
      simpa [t, hcarry, hL1, hR1]
    · have hndiv : ¬ base ∣ t + 1 := by
        intro hdiv
        exact hcarry (mod_return_of_dvd_succ (t := t) hdiv)
      have h1 : (t + 1) / base = t / base := Nat.succ_div_of_not_dvd hndiv
      have hL1 : (prefixFin k (succSL (k + 1) x)).1 = t / base := by
        calc
          (prefixFin k (succSL (k + 1) x)).1 = (succSL (k + 1) x).1 / base := hL
          _ = (t + 1) / base := by simpa [hs]
          _ = t / base := by simpa [h1]
      -- Condition is false, so RHS is `prefixFin k x` and its value is `t/base`.
      simpa [t, hcarry, hL1, hR]

def phase_successor_lift_with_carry_stmt : Prop :=
  (∀ k (x : Fin (SL (k + 1))),
    phaseAtFin (k + 1) (succSL (k + 1) x) 0 = phaseOf (succ13 (pos0 x.1)))
  ∧ (∀ k (x : Fin (SL (k + 1))) (hx : pos0 x.1 ∉ phaseBoundaries),
      phaseAtFin (k + 1) (succSL (k + 1) x) 0 = phaseAtFin (k + 1) x 0)
  ∧ (∀ k (x : Fin (SL (k + 1))),
      prefixFin k (succSL (k + 1) x) =
        if x.1 % base = base - 1 then succSL k (prefixFin k x) else prefixFin k x)

theorem phase_successor_lift_with_carry : phase_successor_lift_with_carry_stmt := by
  refine ⟨?_, ?_, ?_⟩
  · intro k x
    -- rewrite via `pos0_succSL`.
    simpa [pos0_succSL] using (phaseAtFin_depth0_succSL (k := k) (x := x))
  · intro k x hx
    exact phaseAtFin_depth0_succSL_eq_of_not_boundary (k := k) (x := x) hx
  · intro k x
    exact prefixFin_succSL_eq_ite (k := k) (x := x)

/-!
## Carry-Chain Successor Lift (General Depth, Mechanism Only)

Step 295 made the depth-0 *carry boundary* explicit.

This generalizes the same idea: dropping `d` least-significant base-13 digits yields a
prefix projection `Fin (13^(k+d)) → Fin (13^k)` that updates under global successor exactly
when successor creates a carry across the first `d` digits.

We express the carry-chain boundary as a divisibility predicate:

`base^d ∣ t + 1`  (equivalently: lower `d` digits are all at return).
-/

theorem prefixFin_val (k : Nat) (y : Fin (SL (k + 1))) : (prefixFin k y).1 = y.1 / base := by
  simpa [prefixFin, RecursiveGridIndexBridge.digitsEquiv_succ_apply] using
    (RecursiveGridIndexBridge.splitEquiv_fst_val (k := k) (x := y))

theorem dvd_succ_of_mod_return (t : Nat) (h : t % base = base - 1) : base ∣ t + 1 := by
  have hb1 : 1 ≤ base := by simp [IndexOfIndexes.base]
  have hb_lt : 1 < base := by simp [IndexOfIndexes.base]
  have h1mod : 1 % base = 1 := Nat.mod_eq_of_lt hb_lt
  have h0 : (t + 1) % base = 0 := by
    calc
      (t + 1) % base = (t % base + 1 % base) % base := by
        simp [Nat.add_mod]
      _ = (t % base + 1) % base := by simp [h1mod]
      _ = (base - 1 + 1) % base := by simp [h]
      _ = base % base := by simp [Nat.sub_add_cancel hb1]
      _ = 0 := by simp
  exact Nat.dvd_of_mod_eq_zero h0

theorem pow_dvd_succ_iff (d t : Nat) :
    base ^ (d + 1) ∣ t + 1 ↔ base ∣ t + 1 ∧ base ^ d ∣ t / base + 1 := by
  constructor
  · intro hpow
    have hb0 : 0 < base := by simp [IndexOfIndexes.base]
    have hbasepow : base ∣ base ^ (d + 1) := by
      refine ⟨base ^ d, ?_⟩
      simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    have hbase : base ∣ t + 1 := Nat.dvd_trans hbasepow hpow
    rcases hpow with ⟨q, hq⟩
    have hquot : (t + 1) / base = base ^ d * q := by
      calc
        (t + 1) / base = (base ^ (d + 1) * q) / base := by simpa [hq]
        _ = ((base ^ d * q) * base) / base := by
              simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        _ = base ^ d * q := Nat.mul_div_cancel (base ^ d * q) hb0
    have hsuccdiv : (t + 1) / base = t / base + 1 := Nat.succ_div_of_dvd hbase
    have hdivd : base ^ d ∣ t / base + 1 := by
      refine ⟨q, ?_⟩
      calc
        t / base + 1 = (t + 1) / base := by simpa using hsuccdiv.symm
        _ = base ^ d * q := hquot
    exact ⟨hbase, hdivd⟩
  · rintro ⟨hbase, hdivd⟩
    have hb0 : 0 < base := by simp [IndexOfIndexes.base]
    have hmod : t % base = base - 1 := mod_return_of_dvd_succ (t := t) hbase
    have hfactor : t + 1 = base * (t / base + 1) := by
      have hb1 : 1 ≤ base := by simp [IndexOfIndexes.base]
      calc
        t + 1 = (base * (t / base) + t % base) + 1 := by
          simpa [Nat.div_add_mod t base]
        _ = base * (t / base) + (t % base + 1) := by
          simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        _ = base * (t / base) + ((base - 1) + 1) := by
          simp [hmod]
        _ = base * (t / base) + base := by
          simp [Nat.sub_add_cancel hb1]
        _ = base * (t / base + 1) := by
          simp [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    rcases hdivd with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    -- `t+1 = base * (base^d * q) = base^(d+1) * q`.
    calc
      t + 1 = base * (t / base + 1) := hfactor
      _ = base * (base ^ d * q) := by simpa [hq]
      _ = base ^ (d + 1) * q := by
            simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-- Drop the first `d` least-significant base-13 digits: `Fin (13^(k+d)) → Fin (13^k)`. -/
def prefixFinPow (k d : Nat) : Fin (SL (k + d)) → Fin (SL k) :=
  match d with
  | 0 => fun x => by simpa [Nat.add_zero] using x
  | Nat.succ d' => fun x => prefixFinPow k d' (prefixFin (k + d') x)

theorem prefixFinPow_succSL_eq_ite_dvd (k d : Nat) (x : Fin (SL (k + d))) :
    prefixFinPow k d (succSL (k + d) x) =
      if base ^ d ∣ x.1 + 1 then succSL k (prefixFinPow k d x) else prefixFinPow k d x := by
  induction d with
  | zero =>
      -- `base^0 = 1` divides everything, and `prefixFinPow k 0` is the identity.
      simp [prefixFinPow, Nat.pow_zero]
  | succ d ih =>
      -- Unfold one digit of the prefix projection.
      set y : Fin (SL (k + d)) := prefixFin (k + d) x
      have hy_val : y.1 = x.1 / base := by
        simpa [y] using (prefixFin_val (k := k + d) (y := x))
      have hstep :
          prefixFin (k + d) (succSL (k + d + 1) x) =
            if x.1 % base = base - 1 then succSL (k + d) (prefixFin (k + d) x) else prefixFin (k + d) x := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (prefixFin_succSL_eq_ite (k := k + d) (x := x))
      by_cases hcarry0 : x.1 % base = base - 1
      · have hbase : base ∣ x.1 + 1 := dvd_succ_of_mod_return (t := x.1) hcarry0
        have hpow :
            base ^ (d + 1) ∣ x.1 + 1 ↔ base ^ d ∣ x.1 / base + 1 := by
          constructor
          · intro hpow'
            exact (pow_dvd_succ_iff (d := d) (t := x.1)).1 hpow' |>.2
          · intro hdiv
            exact (pow_dvd_succ_iff (d := d) (t := x.1)).2 ⟨hbase, hdiv⟩
        -- Reduce to IH on the prefix `y`.
        have hpow_y : base ^ d ∣ y.1 + 1 ↔ base ^ d ∣ x.1 / base + 1 := by
          simpa [hy_val]
        have hprefix :
            prefixFin (k + d) (succSL (k + (d + 1)) x) =
              succSL (k + d) (prefixFin (k + d) x) := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, hcarry0] using hstep
        have hih :
            prefixFinPow k d (succSL (k + d) y) =
              if base ^ d ∣ y.1 + 1 then succSL k (prefixFinPow k d y) else prefixFinPow k d y := by
          simpa using (ih (x := y))
        by_cases hdvd : base ^ (d + 1) ∣ x.1 + 1
        · have hdvd2 : base ^ d ∣ x.1 / base + 1 := (hpow).1 hdvd
          have hdvd_y : base ^ d ∣ y.1 + 1 := (hpow_y).2 hdvd2
          simp [prefixFinPow, hdvd, hprefix, y, hih, hdvd_y]
        · have hdvd2 : ¬ base ^ d ∣ x.1 / base + 1 := by
            intro h
            exact hdvd ((hpow).2 h)
          have hdvd_y : ¬ base ^ d ∣ y.1 + 1 := by
            intro h
            exact hdvd2 ((hpow_y).1 h)
          simp [prefixFinPow, hdvd, hprefix, y, hih, hdvd_y]
      · have hnot_base : ¬ base ∣ x.1 + 1 := by
          intro hdiv
          exact hcarry0 (mod_return_of_dvd_succ (t := x.1) hdiv)
        have hb0 : 0 < base := by simp [IndexOfIndexes.base]
        have hbasepow : base ∣ base ^ (d + 1) := by
          refine ⟨base ^ d, ?_⟩
          simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        have hnot_pow : ¬ base ^ (d + 1) ∣ x.1 + 1 := by
          intro hpow
          exact hnot_base (Nat.dvd_trans hbasepow hpow)
        -- No carry at the fine digit implies the prefix is unchanged, and the global carry-chain predicate is false.
        have hprefix :
            prefixFin (k + d) (succSL (k + (d + 1)) x) = prefixFin (k + d) x := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, hcarry0] using hstep
        simp [prefixFinPow, hprefix, hnot_pow]

def prefixFinPow_succSL_eq_ite_dvd_stmt : Prop :=
  ∀ (k d : Nat) (x : Fin (SL (k + d))),
    prefixFinPow k d (succSL (k + d) x) =
      if base ^ d ∣ x.1 + 1 then succSL k (prefixFinPow k d x) else prefixFinPow k d x

theorem prefixFinPow_succSL_eq_ite_dvd_all : prefixFinPow_succSL_eq_ite_dvd_stmt := by
  intro k d x
  exact prefixFinPow_succSL_eq_ite_dvd (k := k) (d := d) (x := x)

/-!
## Carry-Chain Boundary Equivalence (Mod-Power Form, Mechanism Only)

Step 296 expressed the carry-chain boundary as a divisibility predicate:
`base^d ∣ t + 1`.

This step proves the equivalent mod-power form:
`t % base^d = base^d - 1`,
and restates the prefix successor law in that form.
-/

theorem mod_eq_pred_of_dvd_succ (t m : Nat) (hm : 0 < m) (h : m ∣ t + 1) :
    t % m = m - 1 := by
  -- Let `r = t % m`. Since `m ∣ t+1`, we have `m ∣ r+1`. With `r < m`, this forces `r = m-1`.
  have ht1 :
      t + 1 = m * (t / m) + (t % m + 1) := by
    have ht : m * (t / m) + t % m = t := Nat.div_add_mod t m
    calc
      t + 1 = (m * (t / m) + t % m) + 1 := by simpa [ht]
      _ = m * (t / m) + (t % m + 1) := by
            simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hsum : m ∣ m * (t / m) + (t % m + 1) := by
    simpa [ht1] using h
  have hmul : m ∣ m * (t / m) := Nat.dvd_mul_right m (t / m)
  have hr1 : m ∣ t % m + 1 := (Nat.dvd_add_right hmul).1 hsum
  have hr_lt : t % m < m := Nat.mod_lt t hm
  have hr1_le : t % m + 1 ≤ m := Nat.succ_le_of_lt hr_lt
  have hr1_pos : 0 < t % m + 1 := Nat.succ_pos _
  have hr1_ge : m ≤ t % m + 1 := Nat.le_of_dvd hr1_pos hr1
  have hr1_eq : t % m + 1 = m := le_antisymm hr1_le hr1_ge
  have : m = (t % m).succ := by
    simpa [Nat.succ_eq_add_one] using hr1_eq.symm
  have : m.pred = t % m := Nat.pred_eq_of_eq_succ this
  simpa [Nat.pred_eq_sub_one] using this.symm

theorem dvd_succ_of_mod_eq_pred (t m : Nat) (hm : 0 < m) (h : t % m = m - 1) :
    m ∣ t + 1 := by
  have hm1 : 1 ≤ m := Nat.succ_le_of_lt hm
  have hm_eq : m = t % m + 1 := by
    calc
      m = (m - 1) + 1 := (Nat.sub_add_cancel hm1).symm
      _ = t % m + 1 := by simpa [h]
  refine ⟨t / m + 1, ?_⟩
  -- `Nat.dvd` expects `t+1 = m * witness`; prove the reverse equality and flip.
  symm
  calc
    m * (t / m + 1) = m * (t / m) + m := by
      simp [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    _ = m * (t / m) + (t % m + 1) := by
      -- Avoid simp recursion: rewrite the second addend using `hm_eq` directly.
      simpa using congrArg (fun z => m * (t / m) + z) hm_eq
    _ = (m * (t / m) + t % m) + 1 := by
      simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    _ = t + 1 := by
      simpa [Nat.div_add_mod]

theorem dvd_succ_iff_mod_eq_pred (t m : Nat) (hm : 0 < m) :
    (m ∣ t + 1) ↔ (t % m = m - 1) := by
  constructor
  · intro h
    exact mod_eq_pred_of_dvd_succ (t := t) (m := m) hm h
  · intro h
    exact dvd_succ_of_mod_eq_pred (t := t) (m := m) hm h

theorem basePow_dvd_succ_iff_mod_eq_pred (d t : Nat) :
    (base ^ d ∣ t + 1) ↔ (t % base ^ d = base ^ d - 1) := by
  have hm : 0 < base ^ d := Nat.pow_pos (n := d) (by simp [IndexOfIndexes.base])
  simpa using (dvd_succ_iff_mod_eq_pred (t := t) (m := base ^ d) hm)

theorem prefixFinPow_succSL_eq_ite_mod (k d : Nat) (x : Fin (SL (k + d))) :
    prefixFinPow k d (succSL (k + d) x) =
      if x.1 % base ^ d = base ^ d - 1 then succSL k (prefixFinPow k d x) else prefixFinPow k d x := by
  have h := prefixFinPow_succSL_eq_ite_dvd (k := k) (d := d) (x := x)
  have heq := basePow_dvd_succ_iff_mod_eq_pred (d := d) (t := x.1)
  by_cases hdvd : base ^ d ∣ x.1 + 1
  · have hmod : x.1 % base ^ d = base ^ d - 1 := (heq).1 hdvd
    simp [h, hdvd, hmod]
  · have hmod : x.1 % base ^ d ≠ base ^ d - 1 := by
      intro hmod
      exact hdvd ((heq).2 hmod)
    simp [h, hdvd, hmod]

def prefixFinPow_succSL_eq_ite_mod_stmt : Prop :=
  ∀ (k d : Nat) (x : Fin (SL (k + d))),
    prefixFinPow k d (succSL (k + d) x) =
      if x.1 % base ^ d = base ^ d - 1 then succSL k (prefixFinPow k d x) else prefixFinPow k d x

theorem prefixFinPow_succSL_eq_ite_mod_all : prefixFinPow_succSL_eq_ite_mod_stmt := by
  intro k d x
  exact prefixFinPow_succSL_eq_ite_mod (k := k) (d := d) (x := x)

/-!
## Carry-Chain Boundary (Digit-Tail Form, Mechanism Only)

Step 297 expressed the carry-chain boundary as the explicit mod-power predicate:
`t % base^d = base^d - 1`.

This step connects that mod-power boundary to the *digit* boundary:
the first `d` base-13 digits of `t` are all at the return state (`base-1 = 12`).
-/

/-- “Tail-return” predicate: the first `d` base-13 digits of `t` are all at the return state. -/
def tailReturn (d t : Nat) : Prop :=
  ∀ i, i < d → RecursiveGridBase13.digit i t = base - 1

theorem tailReturn_succ_iff (d t : Nat) :
    tailReturn (d + 1) t ↔ (t % base = base - 1 ∧ tailReturn d (t / base)) := by
  constructor
  · intro ht
    have h0_digit : RecursiveGridBase13.digit 0 t = base - 1 := ht 0 (by simp)
    have h0 : t % base = base - 1 := by
      simpa [RecursiveGridBase13.digit, RecursiveGridBase13.base, IndexOfIndexes.base] using h0_digit
    refine ⟨h0, ?_⟩
    intro i hi
    have hsucc : RecursiveGridBase13.digit (i + 1) t = base - 1 :=
      ht (i + 1) (Nat.succ_lt_succ hi)
    have hrew : RecursiveGridBase13.digit i (t / base) = RecursiveGridBase13.digit (i + 1) t := by
      simpa [RecursiveGridBase13.base, IndexOfIndexes.base] using
        (RecursiveGridBase13.digit_succ i t).symm
    simpa [hrew] using hsucc
  · rintro ⟨h0, ht⟩
    intro i hi
    cases i with
    | zero =>
        simpa [RecursiveGridBase13.digit, RecursiveGridBase13.base, IndexOfIndexes.base] using h0
    | succ j =>
        have hj : j < d := Nat.lt_of_succ_lt_succ hi
        have hjdigit : RecursiveGridBase13.digit j (t / base) = base - 1 := ht j hj
        calc
          RecursiveGridBase13.digit (j + 1) t =
              RecursiveGridBase13.digit j (t / RecursiveGridBase13.base) := by
                simpa using (RecursiveGridBase13.digit_succ j t)
          _ = RecursiveGridBase13.digit j (t / base) := by
                simp [RecursiveGridBase13.base, IndexOfIndexes.base]
          _ = base - 1 := hjdigit

theorem basePow_dvd_succ_iff_tailReturn (d : Nat) :
    ∀ t : Nat, (base ^ d ∣ t + 1) ↔ tailReturn d t := by
  induction d with
  | zero =>
      intro t
      -- `base^0 = 1` divides everything; the tail predicate for `d=0` is vacuous.
      simp [tailReturn]
  | succ d ih =>
      intro t
      have hb0 : 0 < base := by simp [IndexOfIndexes.base]
      have hbase : (base ∣ t + 1) ↔ (t % base = base - 1) :=
        dvd_succ_iff_mod_eq_pred (t := t) (m := base) hb0
      -- Use the divisibility recursion (`pow_dvd_succ_iff`) and unfold `tailReturn` one digit.
      calc
        base ^ (d + 1) ∣ t + 1 ↔ (base ∣ t + 1 ∧ base ^ d ∣ t / base + 1) := by
            simpa using (pow_dvd_succ_iff (d := d) (t := t))
        _ ↔ (t % base = base - 1 ∧ tailReturn d (t / base)) := by
            constructor
            · rintro ⟨h0, hrest⟩
              exact ⟨(hbase).1 h0, (ih (t := t / base)).1 hrest⟩
            · rintro ⟨h0, hrest⟩
              exact ⟨(hbase).2 h0, (ih (t := t / base)).2 hrest⟩
        _ ↔ tailReturn (d + 1) t := by
            simpa using (tailReturn_succ_iff (d := d) (t := t)).symm

theorem basePow_mod_eq_pred_iff_tailReturn (d t : Nat) :
    (t % base ^ d = base ^ d - 1) ↔ tailReturn d t := by
  -- Step 297: `base^d ∣ t+1 ↔ t % base^d = base^d - 1`.
  have hmod : (base ^ d ∣ t + 1) ↔ (t % base ^ d = base ^ d - 1) :=
    basePow_dvd_succ_iff_mod_eq_pred (d := d) (t := t)
  -- Step 298: `base^d ∣ t+1 ↔ tailReturn d t`.
  have htail : (base ^ d ∣ t + 1) ↔ tailReturn d t :=
    basePow_dvd_succ_iff_tailReturn (d := d) (t := t)
  exact hmod.symm.trans htail

def basePow_mod_eq_pred_iff_tailReturn_stmt : Prop :=
  ∀ (d t : Nat), (t % base ^ d = base ^ d - 1) ↔ tailReturn d t

theorem basePow_mod_eq_pred_iff_tailReturn_all : basePow_mod_eq_pred_iff_tailReturn_stmt := by
  intro d t
  exact basePow_mod_eq_pred_iff_tailReturn (d := d) (t := t)

/-!
## Carry-Chain Boundary (DigitsEquiv Tail Form, Mechanism Only)

Step 298 expressed the carry-chain boundary as a digit predicate in the *recursive-grid* digit
extractor `RecursiveGridBase13.digit`.

This step transports the same predicate into the canonical nested coordinate system
`digitsEquiv : Fin (13^k) ≃ Digits k` via `digitAt`.
-/

/-- The return digit (`12`) as a `Fin 13` value. -/
def returnDigit : Fin base :=
  ⟨base - 1, by simp [IndexOfIndexes.base]⟩

/-- Digit-tail predicate expressed in the canonical `Digits` coordinate system. -/
def tailReturnDigits (k d : Nat) (x : Fin (SL (k + d))) : Prop :=
  ∀ i, i < d → digitAt (k + d) (digitsEquiv (k + d) x) i = returnDigit

theorem digitAt_digitsEquiv_val_eq_digit (k : Nat) (x : Fin (SL k)) (d : Nat) (hd : d < k) :
    (digitAt k (digitsEquiv k x) d).1 = RecursiveGridBase13.digit d x.1 := by
  calc
    (digitAt k (digitsEquiv k x) d).1 =
        RecursiveGridIndexBridge.digitsCoord k (digitsEquiv k x) d := by
          simpa using (digitAt_val_eq_digitsCoord (k := k) (x := digitsEquiv k x) (d := d))
    _ = RecursiveGridBase13.digit d x.1 := by
          simpa using
            (RecursiveGridIndexBridge.digitsCoord_digitsEquiv_eq_digit (k := k) (x := x) d hd)

theorem tailReturnDigits_iff_tailReturn (k d : Nat) (x : Fin (SL (k + d))) :
    tailReturnDigits k d x ↔ tailReturn d x.1 := by
  constructor
  · intro ht
    intro i hi
    have hid : i < k + d := Nat.lt_of_lt_of_le hi (Nat.le_add_left d k)
    have hEq : digitAt (k + d) (digitsEquiv (k + d) x) i = returnDigit := ht i hi
    have hval : (digitAt (k + d) (digitsEquiv (k + d) x) i).1 = base - 1 := by
      -- Reduce to an equality of `Nat` values.
      have := congrArg Fin.val hEq
      simpa [returnDigit] using this
    have hdigit :
        (digitAt (k + d) (digitsEquiv (k + d) x) i).1 = RecursiveGridBase13.digit i x.1 :=
      digitAt_digitsEquiv_val_eq_digit (k := k + d) (x := x) (d := i) hid
    calc
      RecursiveGridBase13.digit i x.1 = (digitAt (k + d) (digitsEquiv (k + d) x) i).1 := by
        simpa using hdigit.symm
      _ = base - 1 := hval
  · intro ht
    intro i hi
    have hid : i < k + d := Nat.lt_of_lt_of_le hi (Nat.le_add_left d k)
    apply Fin.ext
    have hdigit :
        (digitAt (k + d) (digitsEquiv (k + d) x) i).1 = RecursiveGridBase13.digit i x.1 :=
      digitAt_digitsEquiv_val_eq_digit (k := k + d) (x := x) (d := i) hid
    have htail : RecursiveGridBase13.digit i x.1 = base - 1 := ht i hi
    calc
      (digitAt (k + d) (digitsEquiv (k + d) x) i).1 = RecursiveGridBase13.digit i x.1 := hdigit
      _ = base - 1 := htail

theorem basePow_mod_eq_pred_iff_tailReturnDigits (k d : Nat) (x : Fin (SL (k + d))) :
    (x.1 % base ^ d = base ^ d - 1) ↔ tailReturnDigits k d x := by
  have h0 : (x.1 % base ^ d = base ^ d - 1) ↔ tailReturn d x.1 :=
    basePow_mod_eq_pred_iff_tailReturn (d := d) (t := x.1)
  have h1 : tailReturnDigits k d x ↔ tailReturn d x.1 :=
    tailReturnDigits_iff_tailReturn (k := k) (d := d) (x := x)
  exact h0.trans h1.symm

def basePow_mod_eq_pred_iff_tailReturnDigits_stmt : Prop :=
  ∀ (k d : Nat) (x : Fin (SL (k + d))),
    (x.1 % base ^ d = base ^ d - 1) ↔ tailReturnDigits k d x

theorem basePow_mod_eq_pred_iff_tailReturnDigits_all :
    basePow_mod_eq_pred_iff_tailReturnDigits_stmt := by
  intro k d x
  exact basePow_mod_eq_pred_iff_tailReturnDigits (k := k) (d := d) (x := x)

/-!
## Carry-Chain Successor Lift (Coordinate Tail Form, Mechanism Only)

Restate the Step 297 carry-chain successor lift on prefixes using the canonical coordinate-tail
predicate `tailReturnDigits` instead of the numeric mod-power predicate.
-/

/--
Classical `ite` wrapper for the coordinate-tail predicate.

This keeps theorem statements free of `Decidable (tailReturnDigits ...)` obligations.
-/
noncomputable def iteTailReturnDigits (k d : Nat) (x : Fin (SL (k + d))) (a b : Fin (SL k)) :
    Fin (SL k) := by
  classical
  exact if tailReturnDigits k d x then a else b

theorem prefixFinPow_succSL_eq_ite_tailReturnDigits (k d : Nat) (x : Fin (SL (k + d))) :
    prefixFinPow k d (succSL (k + d) x) =
      iteTailReturnDigits k d x (succSL k (prefixFinPow k d x)) (prefixFinPow k d x) := by
  classical
  have h := prefixFinPow_succSL_eq_ite_mod (k := k) (d := d) (x := x)
  have hcond := basePow_mod_eq_pred_iff_tailReturnDigits (k := k) (d := d) (x := x)
  by_cases ht : tailReturnDigits k d x
  · have hmod : x.1 % base ^ d = base ^ d - 1 := (hcond).2 ht
    have h' : prefixFinPow k d (succSL (k + d) x) = succSL k (prefixFinPow k d x) := by
      simpa [hmod] using h
    simpa [iteTailReturnDigits, ht] using h'
  · have hmod : x.1 % base ^ d ≠ base ^ d - 1 := by
      intro hmod
      exact ht ((hcond).1 hmod)
    have h' : prefixFinPow k d (succSL (k + d) x) = prefixFinPow k d x := by
      simpa [hmod] using h
    simpa [iteTailReturnDigits, ht] using h'

def prefixFinPow_succSL_eq_ite_tailReturnDigits_stmt : Prop :=
  ∀ (k d : Nat) (x : Fin (SL (k + d))),
    prefixFinPow k d (succSL (k + d) x) =
      iteTailReturnDigits k d x (succSL k (prefixFinPow k d x)) (prefixFinPow k d x)

theorem prefixFinPow_succSL_eq_ite_tailReturnDigits_all :
    prefixFinPow_succSL_eq_ite_tailReturnDigits_stmt := by
  intro k d x
  exact prefixFinPow_succSL_eq_ite_tailReturnDigits (k := k) (d := d) (x := x)

end MultiAxisPhaseLift
