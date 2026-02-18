import Index_Of_Indexes_Theorem
import Index_Of_Indexes_Subcycle_Fiber_Theorem
import Index_Of_Indexes_Subintervals_Theorem
import Multidimensional_Ticks_Theorem

/-!
# UFRF Kernel Proof (Standalone, Certified Core)

This file extracts the **kernel-first** core of the repo into one Lean-checkable statement.

Scope:
- exact `0→1` refinement law in base 13 (index-of-indexes + rational addressing),
- explicit “a point contains 13 subpoints” fiber/image statements,
- one representative exact multi-axis tick invariant (base-10 scale tick + modular return).

This is not a “Monster/Moonshine” file. Those remain downstream anchors.
-/

namespace UFRFKernel

open IndexOfIndexes
open IndexOfIndexesSubcycle
open IndexOfIndexesSubintervals
open MultidimensionalTicks

/--
Canonical kernel bundle:

1. base-13 join/split refinement equations (exact rational addressing),
2. the interval containment bound for refinements,
3. the refinement fiber has cardinality 13 and its address-image is an explicit 13-point offset set,
4. one exact “log/mod concurrency” invariant for decimal ticks on coprime modular axes.
-/
theorem UFRF_Kernel_Synthesis :
    (∀ k (x : Fin (SL k)) (r : Fin base),
        addrQ (k + 1) (joinEquiv k (x, r)) =
          addrQ k x + (r.1 : ℚ) / (SL (k + 1) : ℚ))
    ∧
    (∀ k (y : Fin (SL (k + 1))),
        addrQ (k + 1) y =
          addrQ k (splitEquiv k y).1 + ((splitEquiv k y).2.1 : ℚ) / (SL (k + 1) : ℚ))
    ∧
    (∀ k (x : Fin (SL k)) (r : Fin base),
        addrQ k x ≤ addrQ (k + 1) (joinEquiv k (x, r))
          ∧ addrQ (k + 1) (joinEquiv k (x, r)) < addrQ k x + (1 : ℚ) / (SL k : ℚ))
    ∧
    (∀ k : Nat, Function.Injective (addrQ k))
    ∧
    (∀ k (x : Fin (SL k)),
        Fintype.card { y : Fin (SL (k + 1)) // (splitEquiv k y).1 = x } = base)
    ∧
    (∀ k (x : Fin (SL k)), fiberAddrImage k x = offsetAddrImage k x)
    ∧
    (∀ k (x : Fin (SL k)), fiberAddrImage k x ⊆ coarseInterval k x)
    ∧
    (∀ k (q : ℚ), 0 ≤ q → q < 1 → ∃ x : Fin (SL k), q ∈ coarseInterval k x)
    ∧
    (∀ k (q : ℚ), 0 ≤ q → q < 1 → ∃! x : Fin (SL k), q ∈ coarseInterval k x)
    ∧
    (∀ k (x : Fin (SL k)),
        coarseInterval k x = ⋃ r : Fin base, coarseInterval (k + 1) (joinEquiv k (x, r)))
    ∧
    (∀ k (x : Fin (SL k)) (r s : Fin base),
        r ≠ s →
          Disjoint (coarseInterval (k + 1) (joinEquiv k (x, r)))
            (coarseInterval (k + 1) (joinEquiv k (x, s))))
    ∧
    (∀ k (q : ℚ) (y : Fin (SL (k + 1))) (x : Fin (SL k)),
        q ∈ coarseInterval (k + 1) y → q ∈ coarseInterval k x → x = (splitEquiv k y).1)
    ∧
    (∀ k (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1),
        floorBin k q hq0 hq1 = (splitEquiv k (floorBin (k + 1) q hq0 hq1)).1)
    ∧
    (∀ k (q q' : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hq0' : 0 ≤ q') (hq1' : q' < 1),
        q ≤ q' → floorBin k q hq0 hq1 ≤ floorBin k q' hq0' hq1')
    ∧
    (∀ k (q q' : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hq0' : 0 ≤ q') (hq1' : q' < 1),
        q ≤ q' → resolveQ k q hq0 hq1 ≤ resolveQ k q' hq0' hq1')
    ∧
    (∀ k (q q' : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hq0' : 0 ≤ q') (hq1' : q' < 1),
        floorBin k q hq0 hq1 < floorBin k q' hq0' hq1' →
          ∃ n : Nat, n < SL k ∧ q < (n : ℚ) / (SL k : ℚ) ∧ (n : ℚ) / (SL k : ℚ) ≤ q')
    ∧
    (∀ k (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1),
        digitsEquiv k (floorBin k q hq0 hq1) = floorDigits k q hq0 hq1)
    ∧
    (∀ k (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1),
        q ∈ coarseInterval k ((digitsEquiv k).symm (floorDigits k q hq0 hq1)))
    ∧
    (∀ k (d : Digits k) (r : Fin base),
        digitAddrQ (k + 1) (d, r) = digitAddrQ k d + (r.1 : ℚ) / (SL (k + 1) : ℚ))
    ∧
    (∀ k (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1),
        digitAddrQ k (floorDigits k q hq0 hq1) =
          (Nat.floor (q * (SL k : ℚ)) : ℚ) / (SL k : ℚ))
    ∧
    (∀ k (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1),
        0 ≤ residualQ k q hq0 hq1 ∧ residualQ k q hq0 hq1 < (1 : ℚ) / (SL k : ℚ))
    ∧
    (∀ k (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1),
        q = resolveQ k q hq0 hq1 + residualQ k q hq0 hq1)
    ∧
    (∀ k (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1),
        resolveQ k
            (resolveQ k q hq0 hq1)
            (resolveQ_nonneg (k := k) (q := q) hq0 hq1)
            (resolveQ_lt_one (k := k) (q := q) hq0 hq1)
          = resolveQ k q hq0 hq1)
    ∧
    (∀ k (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1),
        resolveQ (k + 1) q hq0 hq1 =
          resolveQ k q hq0 hq1 + (floorDigit k q hq0 hq1).1 / (SL (k + 1) : ℚ))
    ∧
    (∀ k (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1),
        resolveQ k q hq0 hq1 = addrQ k (floorBin k q hq0 hq1))
    ∧
    (∀ k (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1),
        resolveQ k q hq0 hq1 ≤ resolveQ (k + 1) q hq0 hq1)
      ∧
      (∀ k (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1),
          resolveQ (k + 1) q hq0 hq1 < resolveQ k q hq0 hq1 + (1 : ℚ) / (SL k : ℚ))
      ∧
        (∀ k (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1),
            resolveQ k q hq0 hq1 = q ↔ ∃ n : Nat, n < SL k ∧ q = (n : ℚ) / (SL k : ℚ))
        ∧
        (∀ k (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1),
            residualQ k q hq0 hq1 = 0 ↔ ∃ n : Nat, n < SL k ∧ q = (n : ℚ) / (SL k : ℚ))
        ∧
        (∀ k (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1),
            resolveQ k q hq0 hq1 ≤ q)
        ∧
        (∀ k (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1),
            q < resolveQ k q hq0 hq1 + (1 : ℚ) / (SL k : ℚ))
        ∧
        (∀ k (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1) (x : Fin (SL k)),
            q ∈ coarseInterval k x → resolveQ k q hq0 hq1 = addrQ k x)
        ∧
        (∀ k (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1) (x : Fin (SL k)),
            resolveQ k q hq0 hq1 = addrQ k x → floorBin k q hq0 hq1 = x)
        ∧
        (∀ k (x : Fin (SL k)),
            Function.Injective (fun r : Fin base =>
              addrQ k x + (r.1 : ℚ) / (SL (k + 1) : ℚ)))
        ∧
    (∀ k (x : Fin (SL k)), (offsetAddrImage k x).ncard = base)
    ∧
    (∀ k (x : Fin (SL k)), (fiberAddrImage k x).ncard = base)
    ∧
    (∀ n m : Nat,
        n ≠ 0 → 1 < m → (10 : Nat).Coprime m →
          UniversalTicks.leadingBlock (tick10 (Nat.totient m) n) = UniversalTicks.leadingBlock n
            ∧ (tick10 (Nat.totient m) n) % m = n % m) := by
  refine And.intro (fun k x r => addrQ_join k x r) ?_
  refine And.intro (fun k y => addrQ_split k y) ?_
  refine And.intro (fun k x r => addrQ_join_bounds k x r) ?_
  refine And.intro (fun k => addrQ_injective k) ?_
  refine And.intro (fun k x => fiber_card_base k x) ?_
  refine And.intro (fun k x => fiberAddrImage_eq_offsetAddrImage k x) ?_
  refine And.intro (fun k x => fiberAddrImage_subset_coarseInterval (k := k) (x := x)) ?_
  refine And.intro (fun k q hq0 hq1 => exists_coarseInterval_of_mem_Icc (k := k) (q := q) hq0 hq1) ?_
  refine And.intro
    (fun k q hq0 hq1 => existsUnique_coarseInterval_of_mem_Icc (k := k) (q := q) hq0 hq1) ?_
  refine And.intro (fun k x => coarseInterval_eq_iUnion_succ (k := k) (x := x)) ?_
  refine And.intro (fun k x r s hrs => coarseInterval_succ_disjoint (k := k) (x := x) (r := r) (s := s) hrs) ?_
  refine And.intro
    (fun k q y x hy hx =>
      parent_eq_of_mem_child_and_mem_parent (k := k) (q := q) (y := y) (x := x) hy hx) ?_
  refine And.intro
    (fun k q hq0 hq1 => floorBin_parent (k := k) (q := q) hq0 hq1) ?_
  refine And.intro
    (fun k q q' hq0 hq1 hq0' hq1' hle =>
      floorBin_mono (k := k) (q := q) (q' := q') hq0 hq1 hq0' hq1' hle) ?_
  refine And.intro
    (fun k q q' hq0 hq1 hq0' hq1' hle =>
      resolveQ_mono (k := k) (q := q) (q' := q') hq0 hq1 hq0' hq1' hle) ?_
  refine And.intro
    (fun k q q' hq0 hq1 hq0' hq1' hlt =>
      floorBin_lt_imp_exists_gridpoint_between (k := k) (q := q) (q' := q') hq0 hq1 hq0' hq1' hlt) ?_
  refine And.intro
    (fun k q hq0 hq1 => digitsEquiv_floorBin_eq_floorDigits (k := k) (q := q) hq0 hq1) ?_
  refine And.intro
    (fun k q hq0 hq1 => mem_coarseInterval_digits (k := k) (q := q) hq0 hq1) ?_
  refine And.intro
    (fun k d r => digitAddrQ_succ (k := k) (d := d) (r := r)) ?_
  refine And.intro
    (fun k q hq0 hq1 => digitAddrQ_floorDigits_eq_floor (k := k) (q := q) hq0 hq1) ?_
  refine And.intro
    (fun k q hq0 hq1 => residualQ_bounds (k := k) (q := q) hq0 hq1) ?_
  refine And.intro
    (fun k q hq0 hq1 => resolveQ_add_residualQ (k := k) (q := q) hq0 hq1) ?_
  refine And.intro
    (fun k q hq0 hq1 => resolveQ_idempotent (k := k) (q := q) hq0 hq1) ?_
  refine And.intro
    (fun k q hq0 hq1 => resolveQ_succ (k := k) (q := q) hq0 hq1) ?_
  refine And.intro
    (fun k q hq0 hq1 => resolveQ_eq_addrQ_floorBin (k := k) (q := q) hq0 hq1) ?_
  refine And.intro
    (fun k q hq0 hq1 => resolveQ_le_succ (k := k) (q := q) hq0 hq1) ?_
  refine And.intro
    (fun k q hq0 hq1 => resolveQ_succ_lt_parent (k := k) (q := q) hq0 hq1) ?_
  refine And.intro
    (fun k q hq0 hq1 => resolveQ_fixed_point_iff_grid (k := k) (q := q) hq0 hq1) ?_
  refine And.intro
    (fun k q hq0 hq1 => residualQ_eq_zero_iff_grid (k := k) (q := q) hq0 hq1) ?_
  refine And.intro
    (fun k q hq0 hq1 => resolveQ_le (k := k) (q := q) hq0 hq1) ?_
  refine And.intro
    (fun k q hq0 hq1 => lt_resolveQ_add_invSL (k := k) (q := q) hq0 hq1) ?_
  refine And.intro
    (fun k q hq0 hq1 x hx => resolveQ_eq_addrQ_of_mem_coarseInterval (k := k) (q := q) hq0 hq1 hx) ?_
  refine And.intro
    (fun k q hq0 hq1 x hEq => floorBin_eq_of_resolveQ_eq_addrQ (k := k) (q := q) hq0 hq1 (x := x) hEq) ?_
  refine And.intro (fun k x => offsetAddr_injective (k := k) (x := x)) ?_
  refine And.intro (fun k x => offsetAddrImage_ncard (k := k) (x := x)) ?_
  refine And.intro (fun k x => fiberAddrImage_ncard (k := k) (x := x)) ?_
  intro n m hn hm hcop
  simpa [tick10] using tick10_totient_invariant_leadingBlock_and_mod (n := n) (m := m) hn hm hcop

end UFRFKernel
