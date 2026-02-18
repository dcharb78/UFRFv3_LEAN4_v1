/-
# Monster AP(12) Filter Theorem (Computational)

This file extracts a purely arithmetic "selection rule" inside the full
Level-2 Frobenius list built from the UFRF generators:

- compute `L2Full` from `FrobeniusEmergence`
- enumerate all triples from `L2Full`
- filter triples that form a 3-term arithmetic progression with common difference 12

Result: the unique such triple is `(47, 59, 71)`.
-/

import Frobenius_Emergence_Theorem

namespace MonsterAP12Filter

open FrobeniusEmergence

/-- Boolean predicate: `(a,b,c)` is an arithmetic progression with common difference 12. -/
def isAP12 (t : Nat × Nat × Nat) : Bool :=
  let (a, b, c) := t
  decide (b = a + 12) && decide (c = b + 12)

/--
Order-invariant AP(12) “start-point” predicate for a list:
`a` is a start iff `a, a+12, a+24` are all present.

This avoids dependence on triple-enumeration order and captures the same constraint
as a property of the underlying finite set.
-/
def isAP12Start (xs : List Nat) (a : Nat) : Bool :=
  decide (a ∈ xs) && decide (a + 12 ∈ xs) && decide (a + 24 ∈ xs)

/-- Deduplicated list of all AP(12) start-points present in `xs` (order inherits from `eraseDups`). -/
def ap12StartList (xs : List Nat) : List Nat :=
  (xs.eraseDups).filter (fun a => isAP12Start xs a)

/-- Order-invariant set of AP(12) start-points present in `xs`. -/
def ap12StartSet (xs : List Nat) : Finset Nat :=
  (xs.toFinset).filter (fun a => isAP12Start xs a = true)

/-- Canonical AP(12) triple determined by a start-point `a`. -/
def ap12TripleOf (a : Nat) : Nat × Nat × Nat :=
  (a, a + 12, a + 24)

/-- Enumerate all index-increasing triples from a list, in a deterministic order. -/
def allTriples (xs : List Nat) : List (Nat × Nat × Nat) :=
  let n := xs.length
  List.flatMap
    (fun i =>
      List.flatMap
        (fun j =>
          List.flatMap
            (fun k =>
              if i < j ∧ j < k then
                let a := xs.getD i 0
                let b := xs.getD j 0
                let c := xs.getD k 0
                [(a, b, c)]
              else
                [])
            (List.range n))
        (List.range n))
    (List.range n)

def ap12Triples (xs : List Nat) : List (Nat × Nat × Nat) :=
  (allTriples xs).filter (fun t => isAP12 t)

theorem mem_allTriples_exists_indices {xs : List Nat} {t : Nat × Nat × Nat}
    (ht : t ∈ allTriples xs) :
    ∃ i j k,
      i < j ∧ j < k ∧ i < xs.length ∧ j < xs.length ∧ k < xs.length ∧
        t = (xs.getD i 0, xs.getD j 0, xs.getD k 0) := by
  have ht' := ht
  -- `simp` expands the nested `flatMap` membership into an explicit witness triple.
  simp [allTriples] at ht'
  rcases ht' with ⟨i, hi, j, hj, k, hk, hij, ht_eq⟩
  have hi_get : xs[i]?.getD 0 = xs.getD i 0 := by
    simp
  have hj_get : xs[j]?.getD 0 = xs.getD j 0 := by
    simp
  have hk_get : xs[k]?.getD 0 = xs.getD k 0 := by
    simp
  have htriple :
      (xs[i]?.getD 0, xs[j]?.getD 0, xs[k]?.getD 0) = (xs.getD i 0, xs.getD j 0, xs.getD k 0) := by
    apply Prod.ext
    · exact hi_get
    · apply Prod.ext
      · exact hj_get
      · exact hk_get
  have ht_eq' : t = (xs.getD i 0, xs.getD j 0, xs.getD k 0) :=
    ht_eq.trans htriple
  exact ⟨i, j, k, hij.1, hij.2, hi, hj, hk, ht_eq'⟩

theorem mem_allTriples_components_mem {xs : List Nat} {t : Nat × Nat × Nat}
    (ht : t ∈ allTriples xs) :
    t.1 ∈ xs ∧ t.2.1 ∈ xs ∧ t.2.2 ∈ xs := by
  rcases mem_allTriples_exists_indices (xs := xs) (t := t) ht with
    ⟨i, j, k, _hij, _hjk, hi, hj, hk, rfl⟩
  have hi_mem : xs.getD i 0 ∈ xs := by
    have hget : xs.getD i 0 = xs[i] := by
      simpa using (List.getD_eq_getElem (l := xs) (d := 0) (n := i) hi)
    -- `xs[i]` is an element of `xs` by construction.
    have memi : xs[i] ∈ xs := List.getElem_mem (l := xs) (n := i) hi
    -- Rewrite the goal element to `xs[i]` and finish.
    rw [hget]
    exact memi
  have hj_mem : xs.getD j 0 ∈ xs := by
    have hget : xs.getD j 0 = xs[j] := by
      simpa using (List.getD_eq_getElem (l := xs) (d := 0) (n := j) hj)
    have memj : xs[j] ∈ xs := List.getElem_mem (l := xs) (n := j) hj
    rw [hget]
    exact memj
  have hk_mem : xs.getD k 0 ∈ xs := by
    have hget : xs.getD k 0 = xs[k] := by
      simpa using (List.getD_eq_getElem (l := xs) (d := 0) (n := k) hk)
    have memk : xs[k] ∈ xs := List.getElem_mem (l := xs) (n := k) hk
    rw [hget]
    exact memk
  exact ⟨hi_mem, hj_mem, hk_mem⟩

theorem mem_ap12Triples_start_mem {xs : List Nat} {t : Nat × Nat × Nat}
    (ht : t ∈ ap12Triples xs) : t.1 ∈ ap12StartSet xs := by
  rcases t with ⟨a, b, c⟩
  have ht' : (a, b, c) ∈ allTriples xs ∧ isAP12 (a, b, c) = true := by
    simpa [ap12Triples] using (List.mem_filter.1 ht)
  have ht_all : (a, b, c) ∈ allTriples xs := ht'.1
  have ht_ap : isAP12 (a, b, c) = true := ht'.2
  have hmem := mem_allTriples_components_mem (xs := xs) (t := (a, b, c)) ht_all
  have ha : a ∈ xs := hmem.1
  have hb_mem : b ∈ xs := hmem.2.1
  have hc_mem : c ∈ xs := hmem.2.2
  have hap : b = a + 12 ∧ c = b + 12 := by
    simpa [isAP12] using ht_ap
  have hb_eq : b = a + 12 := hap.1
  have hc_eq : c = b + 12 := hap.2
  have hb : a + 12 ∈ xs := by
    simpa [hb_eq] using hb_mem
  have hc : a + 24 ∈ xs := by
    have : c = a + 24 := by
      calc
        c = b + 12 := hc_eq
        _ = (a + 12) + 12 := by simp [hb_eq]
        _ = a + 24 := by simp [Nat.add_left_comm, Nat.add_comm]
    simpa [this] using hc_mem
  have ha_dec : decide (a ∈ xs) = true := by
    exact Eq.mpr (decide_eq_true_eq (p := a ∈ xs)) ha
  have hb_dec : decide (a + 12 ∈ xs) = true := by
    exact Eq.mpr (decide_eq_true_eq (p := a + 12 ∈ xs)) hb
  have hc_dec : decide (a + 24 ∈ xs) = true := by
    exact Eq.mpr (decide_eq_true_eq (p := a + 24 ∈ xs)) hc
  have hstart : isAP12Start xs a = true := by
    simp [isAP12Start, ha_dec, hb_dec, hc_dec]
  have ha_fin : a ∈ xs.toFinset := (List.mem_toFinset.2 ha)
  -- Membership in the order-invariant `Finset` filter.
  have ha_in_filter :
      a ∈ Finset.filter (fun x => isAP12Start xs x = true) xs.toFinset :=
    (Finset.mem_filter.2 ⟨ha_fin, hstart⟩)
  simpa [ap12StartSet] using ha_in_filter

theorem ap12Triple_eq_of_unique_start {xs : List Nat} {a0 : Nat} {t : Nat × Nat × Nat}
    (huniq : ap12StartSet xs = {a0}) (ht : t ∈ ap12Triples xs) :
    t = ap12TripleOf a0 := by
  rcases t with ⟨a, b, c⟩
  have ha_in : a ∈ ap12StartSet xs :=
    mem_ap12Triples_start_mem (xs := xs) (t := (a, b, c)) ht
  have ha0_in : a ∈ ({a0} : Finset Nat) := by simpa [huniq] using ha_in
  have ha_eq : a = a0 := by simpa using (Finset.mem_singleton.1 ha0_in)
  have ht_ap : isAP12 (a, b, c) = true := (by
    have ht' : (a, b, c) ∈ allTriples xs ∧ isAP12 (a, b, c) = true := by
      simpa [ap12Triples] using (List.mem_filter.1 ht)
    exact ht'.2)
  have hap : b = a + 12 ∧ c = b + 12 := by
    simpa [isAP12] using ht_ap
  have hb_eq : b = a + 12 := hap.1
  have hc_eq : c = b + 12 := hap.2
  -- The AP(12) equations fix the triple once the start point is fixed.
  apply Prod.ext
  · exact ha_eq
  · apply Prod.ext
    · calc
        b = a + 12 := hb_eq
        _ = a0 + 12 := by simp [ha_eq]
    · calc
        c = b + 12 := hc_eq
        _ = (a + 12) + 12 := by simp [hb_eq]
        _ = (a0 + 12) + 12 := by simp [ha_eq]
        _ = a0 + 24 := by simp [Nat.add_left_comm, Nat.add_comm]

theorem ap12Triples_L2Full :
  ap12Triples L2Full = [(47, 59, 71)] := by
  native_decide

theorem ap12StartSet_L2Full :
    ap12StartSet L2Full = {47} := by
  native_decide

end MonsterAP12Filter
