import TwinPrime_AllowedCapacity_Density_Wrapper_Theorem

/-!
# Examples: Twin-Prime Prime/Exponent Wrapper API

These are small, auditable instantiations that exercise the user-facing wrapper layer:
- capacity + density theorems typecheck end-to-end,
- density is independent of the exponent list `ks` (for fixed base primes `ps`).

No placeholders.
-/

namespace TwinPrimeAllowedCapacityWrapperExamples

open TwinPrimeAllowedCapacityWrappers
open TwinPrimeAllowedCapacityPrimePowerProduct
open TwinPrimeAllowedCapacityCRTList

section PS357

def ps357 : List Nat := [3, 5, 7]
def ks000 : List Nat := [0, 0, 0]
def ks123 : List Nat := [1, 2, 3]

lemma ps357_hprime : ∀ p ∈ ps357, Nat.Prime p := by
  intro p hp
  simp [ps357] at hp
  rcases hp with rfl | rfl | rfl
  · decide
  · decide
  · decide

lemma ps357_hne2 : ∀ p ∈ ps357, p ≠ 2 := by
  intro p hp
  simp [ps357] at hp
  rcases hp with rfl | rfl | rfl
  · decide
  · decide
  · decide

lemma ps357_nodup : ps357.Nodup := by
  decide

lemma ps357_len_ks000 : ps357.length = ks000.length := by
  decide

lemma ps357_len_ks123 : ps357.length = ks123.length := by
  decide

noncomputable def densityExpr (ks : List Nat) (hlen : ps357.length = ks.length) : ℚ :=
  let pps := zipPrimePow ps357 ks ps357_hprime ps357_hne2 hlen
  (letI : NeZero (mods pps).prod := ⟨mods_prod_ne_zero pps⟩;
    (Fintype.card
          ({x : ZMod (mods pps).prod //
              allowedAxisPow pps
                (axisEquiv (mods pps)
                  (mods_pairwise_coprime_of_p_pairwise_coprime pps
                    (List.pairwise_coprime_of_prime_nodup
                      (by
                        intro p hp
                        have : p ∈ ps357 := by
                          simpa [pps, zipPrimePow_map_p ps357 ks ps357_hprime ps357_hne2 hlen] using hp
                        exact ps357_hprime p this)
                      (by
                        simpa [pps, zipPrimePow_map_p ps357 ks ps357_hprime ps357_hne2 hlen] using
                          ps357_nodup))) x)})
        : ℚ) / ((mods pps).prod : ℚ))

theorem density_ps357_eq_one_seventh (ks : List Nat) (hlen : ps357.length = ks.length) :
    densityExpr ks hlen = (1 / 7 : ℚ) := by
  -- Use the wrapper theorem to rewrite to the closed-form prime-only product, then evaluate.
  have h :=
    globalDensity_eq_of_prime_lists (ps := ps357) (ks := ks)
      ps357_hprime ps357_hne2 ps357_nodup hlen
  -- Unfold the LHS wrapper into `densityExpr`.
  have hform :
      densityExpr ks hlen = (ps357.map (fun p : Nat => ((p - 2 : ℚ) / (p : ℚ)))).prod := by
    dsimp [densityExpr]
    simpa using h
  have heval :
      (ps357.map (fun p : Nat => ((p - 2 : ℚ) / (p : ℚ)))).prod = (1 / 7 : ℚ) := by
    -- For [3,5,7], the product is (1/3)*(3/5)*(5/7) = 1/7.
    simp [ps357]
    norm_num
  exact hform.trans heval

theorem density_ps357_independent_of_ks :
    densityExpr ks000 ps357_len_ks000 = densityExpr ks123 ps357_len_ks123 := by
  -- Both sides equal the same prime-only product, so they are equal.
  have h0 := density_ps357_eq_one_seventh (ks := ks000) ps357_len_ks000
  have h1 := density_ps357_eq_one_seventh (ks := ks123) ps357_len_ks123
  simp [h0, h1]

end PS357

section PS31113

def ps31113 : List Nat := [3, 11, 13]
def ks102 : List Nat := [1, 0, 2]

lemma ps31113_hprime : ∀ p ∈ ps31113, Nat.Prime p := by
  intro p hp
  simp [ps31113] at hp
  rcases hp with rfl | rfl | rfl
  · decide
  · decide
  · decide

lemma ps31113_hne2 : ∀ p ∈ ps31113, p ≠ 2 := by
  intro p hp
  simp [ps31113] at hp
  rcases hp with rfl | rfl | rfl
  · decide
  · decide
  · decide

lemma ps31113_nodup : ps31113.Nodup := by
  decide

lemma ps31113_len_ks102 : ps31113.length = ks102.length := by
  decide

noncomputable def densityExpr31113 : ℚ :=
  let pps := zipPrimePow ps31113 ks102 ps31113_hprime ps31113_hne2 ps31113_len_ks102
  (letI : NeZero (mods pps).prod := ⟨mods_prod_ne_zero pps⟩;
    (Fintype.card
          ({x : ZMod (mods pps).prod //
              allowedAxisPow pps
                (axisEquiv (mods pps)
                  (mods_pairwise_coprime_of_p_pairwise_coprime pps
                    (List.pairwise_coprime_of_prime_nodup
                      (by
                        intro p hp
                        have : p ∈ ps31113 := by
                          simpa [zipPrimePow_map_p ps31113 ks102 ps31113_hprime ps31113_hne2
                            ps31113_len_ks102, pps] using hp
                        exact ps31113_hprime p this)
                      (by
                        simpa [zipPrimePow_map_p ps31113 ks102 ps31113_hprime ps31113_hne2
                          ps31113_len_ks102, pps] using ps31113_nodup))) x)})
        : ℚ) / ((mods pps).prod : ℚ))

theorem density_ps31113_eq_three_thirteenths :
    densityExpr31113 = (3 / 13 : ℚ) := by
  have h :=
    globalDensity_eq_of_prime_lists (ps := ps31113) (ks := ks102)
      ps31113_hprime ps31113_hne2 ps31113_nodup ps31113_len_ks102
  have hform :
      densityExpr31113 = (ps31113.map (fun p : Nat => ((p - 2 : ℚ) / (p : ℚ)))).prod := by
    dsimp [densityExpr31113]
    exact h
  have heval :
      (ps31113.map (fun p : Nat => ((p - 2 : ℚ) / (p : ℚ)))).prod = (3 / 13 : ℚ) := by
    -- Evaluate: (1/3)*(9/11)*(11/13) = 3/13.
    simp [ps31113]
    norm_num
  exact hform.trans heval

end PS31113

end TwinPrimeAllowedCapacityWrapperExamples
