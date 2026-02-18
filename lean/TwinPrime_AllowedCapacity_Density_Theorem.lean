import Mathlib
import TwinPrime_AllowedCapacity_PrimePower_Product_Theorem
import Nat_Prime_Distinct_Coprime_Utilities

/-!
# Twin-Prime Allowed-Capacity Density (Scale-Invariant Ratios)

This layer converts the exact channel-count statements (Steps 221–225) into
**ratio / density** identities in `ℚ`.

Key point: for a prime-power axis `p^(k+1)`, the allowed-capacity is
`(p-2)·p^k`, so the density is

`((p-2)·p^k) / p^(k+1) = (p-2)/p`,

independent of the exponent `k`. This is the discrete "scale invariance"
in the twin-prime channel-counting mechanism.

No placeholders.
-/

namespace TwinPrimeAllowedCapacityDensity

open TwinPrimeAllowedCapacityPrimePowerProduct
open TwinPrimeAllowedCapacityCRTList

namespace PrimePow

/-- The per-axis density as a rational number. -/
noncomputable def axisDensity (pp : PrimePow) : ℚ :=
  (Fintype.card
        ({x : ZMod pp.modulus //
            TwinPrimeAllowedCapacityPrimePowerProduct.PrimePow.allowedPow pp x} : Type)
      : ℚ) /
    (pp.modulus : ℚ)

/--
Scale-invariant per-axis density:
`axisDensity = (p-2)/p` (independent of the exponent `k`).
-/
theorem axisDensity_eq (pp : PrimePow) :
    axisDensity pp = ((pp.p - 2 : ℚ) / (pp.p : ℚ)) := by
  classical
  unfold axisDensity

  -- Rewrite the numerator using the certified per-axis capacity count.
  have hcard :
      (Fintype.card
            ({x : ZMod pp.modulus //
                TwinPrimeAllowedCapacityPrimePowerProduct.PrimePow.allowedPow pp x} : Type)
          : ℚ) =
        (((pp.p - 2) * pp.p ^ pp.k : Nat) : ℚ) := by
    exact_mod_cast (TwinPrimeAllowedCapacityPrimePowerProduct.PrimePow.card_allowedPow pp)

  -- Cancel the common `p^k` factor against the modulus `p^(k+1) = p^k * p`.
  have hp0_nat : pp.p ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_two pp.hp)
  have hp0 : (pp.p : ℚ) ≠ 0 := by
    exact_mod_cast hp0_nat
  have hk0 : ((pp.p : ℚ) ^ pp.k) ≠ 0 := pow_ne_zero _ hp0
  have hp2 : (2 : Nat) ≤ pp.p := le_of_lt pp.hp

  -- Finish in the explicit closed form.
  calc
    (Fintype.card
          ({x : ZMod pp.modulus //
              TwinPrimeAllowedCapacityPrimePowerProduct.PrimePow.allowedPow pp x} : Type)
        : ℚ) /
        (pp.modulus : ℚ)
        = (((pp.p - 2) * pp.p ^ pp.k : Nat) : ℚ) / (pp.modulus : ℚ) := by
            simp [hcard]
    _ = (((pp.p - 2) * pp.p ^ pp.k : Nat) : ℚ) / ((pp.p ^ (pp.k + 1) : Nat) : ℚ) := by
          simp [PrimePow.modulus]
    _ = ((pp.p : ℚ) ^ pp.k * (pp.p - 2 : ℚ)) / ((pp.p : ℚ) ^ pp.k * (pp.p : ℚ)) := by
          -- Cast Nat expressions into `ℚ` and normalize to `c*a / (c*b)`.
          simp [pow_succ, Nat.cast_sub hp2, mul_comm]
    _ = ((pp.p - 2 : ℚ) / (pp.p : ℚ)) := by
          -- Cancel the common factor `c = p^k`.
          simpa using (mul_div_mul_left (pp.p - 2 : ℚ) (pp.p : ℚ) hk0)

/--
Closed-form axis density stated purely at the arithmetic level:
`((p-2)·p^k) / p^(k+1) = (p-2)/p`.
-/
theorem axisDensity_formula (pp : PrimePow) :
    (((pp.p - 2) * pp.p ^ pp.k : Nat) : ℚ) / ((pp.p ^ (pp.k + 1) : Nat) : ℚ) =
      ((pp.p - 2 : ℚ) / (pp.p : ℚ)) := by
  -- Derive from `axisDensity_eq` by unfolding and rewriting the numerator.
  have hp0 : (pp.modulus : ℚ) ≠ 0 := by
    -- `p>2` implies `p^(k+1) ≠ 0`.
    have hp0_nat : pp.p ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_two pp.hp)
    have hp0q : (pp.p : ℚ) ≠ 0 := by exact_mod_cast hp0_nat
    simpa [PrimePow.modulus] using (pow_ne_zero (pp.k + 1) hp0q)
  -- Use the already-proved cancellation shape in `axisDensity_eq`.
  -- (This lemma is intentionally redundant; it is convenient in list inductions.)
  have hk0 : ((pp.p : ℚ) ^ pp.k) ≠ 0 := by
    have hp0_nat : pp.p ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_two pp.hp)
    have hp0q : (pp.p : ℚ) ≠ 0 := by exact_mod_cast hp0_nat
    simpa using (pow_ne_zero pp.k hp0q)
  have hp2 : (2 : Nat) ≤ pp.p := le_of_lt pp.hp
  calc
    (((pp.p - 2) * pp.p ^ pp.k : Nat) : ℚ) / ((pp.p ^ (pp.k + 1) : Nat) : ℚ)
        = ((pp.p : ℚ) ^ pp.k * (pp.p - 2 : ℚ)) / ((pp.p : ℚ) ^ pp.k * (pp.p : ℚ)) := by
            simp [pow_succ, Nat.cast_sub hp2, mul_comm]
    _ = ((pp.p - 2 : ℚ) / (pp.p : ℚ)) := by
            simpa using (mul_div_mul_left (pp.p - 2 : ℚ) (pp.p : ℚ) hk0)

end PrimePow

/-! ## Product densities -/

/--
Pure arithmetic density identity for a list of prime-power axes:

`(∏ ((p-2)·p^k)) / (∏ p^(k+1)) = ∏ ((p-2)/p)`.

This statement is independent of CRT hypotheses; it is the ratio-level
scale invariance of the closed forms.
-/
theorem density_formula (pps : List PrimePow) :
    (((pps.map (fun pp => (pp.p - 2) * pp.p ^ pp.k)).prod : Nat) : ℚ) /
        (((mods pps).prod : Nat) : ℚ) =
      (pps.map (fun pp => ((pp.p - 2 : ℚ) / (pp.p : ℚ)))).prod := by
  induction pps with
  | nil =>
      simp [mods]
  | cons pp ps ih =>
      classical

      let headCap : Nat := (pp.p - 2) * pp.p ^ pp.k
      let tailCap : Nat := (ps.map (fun pp => (pp.p - 2) * pp.p ^ pp.k)).prod
      let headMod : Nat := pp.p ^ (pp.k + 1)
      let tailMod : Nat := (mods ps).prod

      have hsplit :
          ((headCap * tailCap : Nat) : ℚ) / ((headMod * tailMod : Nat) : ℚ) =
            ((headCap : Nat) : ℚ) / ((headMod : Nat) : ℚ) * (((tailCap : Nat) : ℚ) / ((tailMod : Nat) : ℚ)) := by
        -- LHS is `(a*b)/(c*d)` after casting; use `mul_div_mul_comm`.
        simpa [Nat.cast_mul] using
          (mul_div_mul_comm (a := (headCap : ℚ)) (b := (tailCap : ℚ)) (c := (headMod : ℚ)) (d := (tailMod : ℚ)))

      have hhead : ((headCap : Nat) : ℚ) / ((headMod : Nat) : ℚ) = ((pp.p - 2 : ℚ) / (pp.p : ℚ)) := by
        simpa [headCap, headMod] using (TwinPrimeAllowedCapacityDensity.PrimePow.axisDensity_formula pp)

      have htail :
          ((tailCap : Nat) : ℚ) / ((tailMod : Nat) : ℚ) =
            (ps.map (fun pp => ((pp.p - 2 : ℚ) / (pp.p : ℚ)))).prod := by
        -- IH is the tail ratio identity (unfolded).
        simpa [tailCap, tailMod] using ih

      have :
          (((((pp :: ps).map (fun pp => (pp.p - 2) * pp.p ^ pp.k)).prod : Nat) : ℚ) /
              (((mods (pp :: ps)).prod : Nat) : ℚ)) =
            ((pp.p - 2 : ℚ) / (pp.p : ℚ)) *
              (ps.map (fun pp => ((pp.p - 2 : ℚ) / (pp.p : ℚ)))).prod := by
        -- First rewrite the list products to `head * tail`, then apply `mul_div_mul_comm`.
        calc
          (((((pp :: ps).map (fun pp => (pp.p - 2) * pp.p ^ pp.k)).prod : Nat) : ℚ) /
                (((mods (pp :: ps)).prod : Nat) : ℚ))
              = ((headCap * tailCap : Nat) : ℚ) / ((headMod * tailMod : Nat) : ℚ) := by
                  simp [mods, List.prod_cons, PrimePow.modulus, headCap, tailCap, headMod, tailMod]
          _ = ((headCap : Nat) : ℚ) / ((headMod : Nat) : ℚ) * (((tailCap : Nat) : ℚ) / ((tailMod : Nat) : ℚ)) := by
                simpa using hsplit
          _ = ((pp.p - 2 : ℚ) / (pp.p : ℚ)) *
                (ps.map (fun pp => ((pp.p - 2 : ℚ) / (pp.p : ℚ)))).prod := by
                simp [hhead, htail]

      -- Fold the density list product back.
      simpa [List.prod_cons] using this

/--
Channel-density statement (requires CRT factorization to interpret the product formula as
the actual capacity count):

If base primes are pairwise coprime, then the global allowed-capacity density equals
`∏ ((p-2)/p)` and is independent of the exponents.
-/
theorem globalDensity_eq_of_p_pairwise_coprime (pps : List PrimePow)
    (hp : (pps.map PrimePow.p).Pairwise Nat.Coprime) :
    (letI : NeZero (mods pps).prod := ⟨mods_prod_ne_zero pps⟩;
      (Fintype.card
            ({x : ZMod (mods pps).prod //
                allowedAxisPow pps
                  (axisEquiv (mods pps) (mods_pairwise_coprime_of_p_pairwise_coprime pps hp) x)})
          : ℚ) / ((mods pps).prod : ℚ) =
        (pps.map (fun pp => ((pp.p - 2 : ℚ) / (pp.p : ℚ)))).prod) := by
  classical
  letI : NeZero (mods pps).prod := ⟨mods_prod_ne_zero pps⟩
  -- Use the certified global capacity count (Step 225 restatement), then reduce to `density_formula`.
  have hcardNat :
      Fintype.card
          ({x : ZMod (mods pps).prod //
              allowedAxisPow pps
                (axisEquiv (mods pps) (mods_pairwise_coprime_of_p_pairwise_coprime pps hp) x)}) =
        (pps.map (fun pp => (pp.p - 2) * pp.p ^ pp.k)).prod := by
    simpa using (card_allowedPrimePowerProduct_of_p_pairwise_coprime (pps := pps) hp)
  have hcardQ :
      (Fintype.card
            ({x : ZMod (mods pps).prod //
                allowedAxisPow pps
                  (axisEquiv (mods pps) (mods_pairwise_coprime_of_p_pairwise_coprime pps hp) x)})
          : ℚ) =
        (((pps.map (fun pp => (pp.p - 2) * pp.p ^ pp.k)).prod : Nat) : ℚ) := by
    exact_mod_cast hcardNat
  -- Now close with the arithmetic density identity.
  simpa [hcardQ] using density_formula pps

/-- User-facing wrapper: global density under `Nat.Prime` + `Nodup` on the base list. -/
theorem globalDensity_eq_of_prime_nodup (pps : List PrimePow)
    (hprime : ∀ p ∈ (pps.map PrimePow.p), Nat.Prime p) (hnodup : (pps.map PrimePow.p).Nodup) :
    (letI : NeZero (mods pps).prod := ⟨mods_prod_ne_zero pps⟩;
      (Fintype.card
            ({x : ZMod (mods pps).prod //
                allowedAxisPow pps
                  (axisEquiv (mods pps)
                    (mods_pairwise_coprime_of_p_pairwise_coprime pps
                      (List.pairwise_coprime_of_prime_nodup hprime hnodup)) x)})
          : ℚ) / ((mods pps).prod : ℚ) =
        (pps.map (fun pp => ((pp.p - 2 : ℚ) / (pp.p : ℚ)))).prod) := by
  simpa using
    (globalDensity_eq_of_p_pairwise_coprime (pps := pps)
      (hp := List.pairwise_coprime_of_prime_nodup hprime hnodup))

end TwinPrimeAllowedCapacityDensity
