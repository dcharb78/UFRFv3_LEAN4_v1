import TwinPrime_AllowedCapacity_CRT_Theorem

/-!
# Twin-Prime Allowed-Capacity (Multi-Axis CRT, List Form)

This extends the 2-axis CRT multiplicativity mechanism to an arbitrary finite list of
pairwise-coprime moduli.

We keep the scope strictly at the **capacity** level (counting allowed residue channels),
not as an occupancy theorem about primes.

No placeholders.
-/

namespace TwinPrimeAllowedCapacityCRTList

open TwinPrimeAllowedCapacityCRT

/-! ## Nested axis product over a list of moduli -/

/-- Nested product type of residue axes: `Axis [m,n,k] = ZMod m × ZMod n × ZMod k × PUnit`. -/
def Axis : List Nat → Type
  | [] => PUnit
  | n :: ns => ZMod n × Axis ns

/-- Allowed predicate without any finiteness assumptions (we will only take cards for `n > 2`). -/
def allowed0 (n : Nat) (x : ZMod n) : Prop :=
  x ≠ 0 ∧ x ≠ (-2 : ZMod n)

noncomputable instance (n : Nat) [NeZero n] : DecidablePred (allowed0 n) := by
  classical
  infer_instance

/-- Pointwise allowed predicate across all axes. -/
def allowedAxis : (l : List Nat) → Axis l → Prop
  | [] => fun _ => True
  | n :: ns => fun x => allowed0 n x.1 ∧ allowedAxis ns x.2

noncomputable instance (l : List Nat) : DecidablePred (allowedAxis l) := by
  classical
  induction l with
  | nil =>
      -- `allowedAxis [] _ = True`
      simpa [allowedAxis] using (inferInstance : DecidablePred fun _ : Axis [] => True)
  | cons n ns ih =>
      -- `allowedAxis (n::ns) x = allowed0 n x.1 ∧ allowedAxis ns x.2`
      infer_instance

lemma card_allowed0 (n : Nat) [NeZero n] (hn : 2 < n) :
    Fintype.card ({x : ZMod n // allowed0 n x}) = n - 2 := by
  simpa [allowed0, TwinPrimeAllowedCapacityCRT.allowed] using
    TwinPrimeAllowedCapacityCRT.card_allowed (n := n) hn

lemma prod_ne_zero_of_all_gt_two {l : List Nat} (h : ∀ n ∈ l, 2 < n) : l.prod ≠ 0 := by
  induction l with
  | nil =>
      simp
  | cons n ns ih =>
      have hn : 2 < n := h n (by simp)
      have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_two hn)
      have htail : ∀ m ∈ ns, 2 < m := by
        intro m hm
        exact h m (by simp [hm])
      have hprod : ns.prod ≠ 0 := ih htail
      simpa [List.prod_cons] using Nat.mul_ne_zero hn0 hprod

noncomputable def fintypeAxis : (l : List Nat) → (∀ n ∈ l, n ≠ 0) → Fintype (Axis l)
  | [], _ => by
      -- `Axis [] = PUnit`
      simpa [Axis] using (inferInstance : Fintype PUnit)
  | n :: ns, h => by
      classical
      have hn0 : n ≠ 0 := h n (by simp)
      letI : NeZero n := ⟨hn0⟩
      have htail : ∀ m ∈ ns, m ≠ 0 := by
        intro m hm
        exact h m (by simp [hm])
      letI : Fintype (Axis ns) := fintypeAxis ns htail
      -- `Axis (n::ns) = ZMod n × Axis ns`
      simpa [Axis] using (inferInstance : Fintype (ZMod n × Axis ns))

/-! ## Cardinality of allowed axis tuples -/

theorem card_allowedAxis (l : List Nat) (h : ∀ n ∈ l, 2 < n) :
    (letI : Fintype (Axis l) := fintypeAxis l (fun n hn => Nat.ne_of_gt (lt_trans Nat.zero_lt_two (h n hn)));
      Fintype.card ({a : Axis l // allowedAxis l a}) = (l.map (fun n => n - 2)).prod) := by
  classical
  induction l with
  | nil =>
      simp [Axis, allowedAxis]
  | cons n ns ih =>
      have hn : 2 < n := h n (by simp)
      have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_two hn)
      letI : NeZero n := ⟨hn0⟩
      have hne0_tail : ∀ m ∈ ns, m ≠ 0 := by
        intro m hm
        exact Nat.ne_of_gt (lt_trans Nat.zero_lt_two (h m (by simp [hm])))
      letI : Fintype (Axis ns) := fintypeAxis ns hne0_tail
      letI : Fintype (Axis (n :: ns)) := by
        -- `Axis (n::ns) = ZMod n × Axis ns`
        simpa [Axis] using (inferInstance : Fintype (ZMod n × Axis ns))

      -- Split the subtype over a product into the product of subtypes (axis-wise independence).
      let A : Type := {a : ZMod n // allowed0 n a}
      let B : Type := {b : Axis ns // allowedAxis ns b}

      have h_equiv : ({x : Axis (n :: ns) // allowedAxis (n :: ns) x}) ≃ (A × B) := by
        refine
          { toFun := fun x => ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩⟩
            invFun := fun y => ⟨(y.1.1, y.2.1), y.1.2, y.2.2⟩
            left_inv := by intro x; (ext; rfl)
            right_inv := by
              intro y
              cases y with
              | mk a b =>
                simp }

      have htail : ∀ m ∈ ns, 2 < m := by
        intro m hm
        exact h m (by simp [hm])

      have hB : Fintype.card B = (ns.map (fun n => n - 2)).prod := by
        -- `ih` is the recursive card identity for the tail.
        -- Unwrap the tail's `letI` binder by reusing our `Fintype (Axis ns)` instance.
        simpa [B] using (by
          -- `ih htail` has the same `letI` wrapper; `simp` removes it under our instance.
          simpa using (ih htail))

      -- Main multiplicativity step.
      calc
        Fintype.card ({x : Axis (n :: ns) // allowedAxis (n :: ns) x})
            = Fintype.card (A × B) := Fintype.card_congr h_equiv
        _ = Fintype.card A * Fintype.card B := by simp
        _ = (n - 2) * (ns.map (fun n => n - 2)).prod := by
              simp [A, card_allowed0 (n := n) hn, hB]
        _ = ((n :: ns).map (fun n => n - 2)).prod := by simp

/-! ## List-CRT equivalence `ZMod (∏ nᵢ) ≃ Axis [nᵢ]` (pairwise coprime) -/

noncomputable def axisEquiv : (l : List Nat) → l.Pairwise Nat.Coprime → ZMod l.prod ≃ Axis l
  | [], _ => by
      classical
      refine
        { toFun := fun _ => PUnit.unit
          invFun := fun _ => 0
          left_inv := ?_
          right_inv := ?_ }
      · intro x
        -- `ZMod 1` is subsingleton
        have hs : Subsingleton (ZMod ([] : List Nat).prod) :=
          (ZMod.subsingleton_iff (n := ([] : List Nat).prod)).2 (by simp)
        simpa using (hs.elim 0 x)
      · intro x
        cases x
        rfl
  | n :: ns, co => by
      classical
      have hhead : ∀ m ∈ ns, Nat.Coprime n m := (List.pairwise_cons.mp co).1
      have coTail : ns.Pairwise Nat.Coprime := (List.pairwise_cons.mp co).2
      have hcop : Nat.Coprime n ns.prod := Nat.coprime_list_prod_right_iff.mpr hhead

      let e0 : ZMod (n * ns.prod) ≃ (ZMod n × ZMod ns.prod) :=
        (ZMod.chineseRemainder hcop).toEquiv
      let e1 : ZMod ns.prod ≃ Axis ns := axisEquiv ns coTail

      simpa [Axis, List.prod_cons] using
        (e0.trans (Equiv.prodCongr (Equiv.refl (ZMod n)) e1))

/-! ## Multi-axis allowed-capacity on the product modulus -/

theorem card_allowedList (l : List Nat) (co : l.Pairwise Nat.Coprime) (h : ∀ n ∈ l, 2 < n) :
    (letI : NeZero l.prod := ⟨prod_ne_zero_of_all_gt_two h⟩;
      Fintype.card ({x : ZMod l.prod // allowedAxis l (axisEquiv l co x)}) =
        (l.map (fun n => n - 2)).prod) := by
  classical

  have hprod0 : l.prod ≠ 0 := prod_ne_zero_of_all_gt_two h
  letI : NeZero l.prod := ⟨hprod0⟩

  have hne0 : ∀ n ∈ l, n ≠ 0 := by
    intro n hn
    exact Nat.ne_of_gt (lt_trans Nat.zero_lt_two (h n hn))

  letI : Fintype (Axis l) := fintypeAxis l hne0

  let e := axisEquiv l co
  let S : Type := {x : ZMod l.prod // allowedAxis l (e x)}
  let T : Type := {a : Axis l // allowedAxis l a}

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
    _ = (l.map (fun n => n - 2)).prod := card_allowedAxis l h

end TwinPrimeAllowedCapacityCRTList
