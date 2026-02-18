import Mathlib

/-!
# Decimal / Mod-1001 Concurrency (1001 = 7*11*13)

Experiment notes in this repo highlight the integer `1001 = 7*11*13` as a high-skill
multiplier in some cross-domain datasets. We do **not** formalize any empirical claim here.

What we *can* formalize exactly (and cheaply) is the modular concurrency skeleton:

* `10^3 + 1 = 1001`, hence for every `n`, `n*10^3 + n` is divisible by `1001`.
* Consequently `10^6 ≡ 1 (mod 1001)` (a 6-decade return).
* Therefore scaling by `10^6` preserves residues mod `1001` for all `n`.

This mirrors the already-proved `mod 13` flip/return (`10^3 ≡ -1`, `10^6 ≡ 1`) but is
even stronger here because `10^3 + 1` is *literally* `1001`.

All proofs are no-placeholder and purely arithmetic (`native_decide` + `simp`).
-/

namespace DecimalMod1001

def M : Nat := 1001

theorem M_factor : M = 7 * 11 * 13 := by
  native_decide

theorem ten_pow_three_add_one : (10 ^ 3 : Nat) + 1 = M := by
  native_decide

theorem mul_ten_pow_three_add_self_mod (n : Nat) : ((n * 10 ^ 3) + n) % M = 0 := by
  -- `n*10^3 + n = n*(10^3 + 1)`, and `10^3 + 1 = 1001`.
  have hrewrite : n * 10 ^ 3 + n = n * (10 ^ 3 + 1) := by
    have : n * (10 ^ 3 + 1) = n * 10 ^ 3 + n := by
      -- `n*(a+1) = n*a + n*1`.
      simpa [Nat.mul_one] using (Nat.mul_add n (10 ^ 3) 1)
    simpa using this.symm
  calc
    ((n * 10 ^ 3) + n) % M = (n * (10 ^ 3 + 1)) % M := by
      simpa using congrArg (fun x => x % M) hrewrite
    _ = (n * M) % M := by
      -- Avoid `simp` here (it may reduce `(n*M) % M` to `0` and change the goal shape).
      rw [ten_pow_three_add_one]
    _ = 0 := by
      -- `M` divides `n*M`, so the remainder is `0`.
      simp

theorem ten_pow_six_mod : (10 ^ 6 : Nat) % M = 1 := by
  native_decide

/--
`1001 = 7*11*13` is not treated as a “magical modulus” here; it is a *composite system*.

This theorem shows the `10^6 ≡ 1 (mod 1001)` return as an *emergent concurrency* fact:
if the same return holds on each coprime prime axis (`7`, `11`, `13`), then it holds
on their product.

This is closer to the repo’s “systems become nodes of other systems” narrative than a
single closed-form `native_decide` computation on `1001`.
-/
theorem ten_pow_six_mod_emergent : (10 ^ 6 : Nat) % M = 1 := by
  -- Per-axis returns.
  have h7 : (10 ^ 6 : Nat) ≡ 1 [MOD 7] := by native_decide
  have h11 : (10 ^ 6 : Nat) ≡ 1 [MOD 11] := by native_decide
  have h13 : (10 ^ 6 : Nat) ≡ 1 [MOD 13] := by native_decide

  -- Concurrency: combine returns across coprime axes.
  have h7_11 : (10 ^ 6 : Nat) ≡ 1 [MOD 7 * 11] := by
    exact (Nat.modEq_and_modEq_iff_modEq_mul (by decide : Nat.Coprime 7 11)).1 ⟨h7, h11⟩
  have h7_11_13 : (10 ^ 6 : Nat) ≡ 1 [MOD (7 * 11) * 13] := by
    exact (Nat.modEq_and_modEq_iff_modEq_mul (by decide : Nat.Coprime (7 * 11) 13)).1 ⟨h7_11, h13⟩

  -- Re-express the product modulus as `M`.
  have hM : (10 ^ 6 : Nat) ≡ 1 [MOD M] := by
    -- `simp` rewrites the goal modulus `M` to `7*11*13`.
    simpa [M_factor, Nat.mul_assoc] using h7_11_13

  -- Unfold `ModEq` to a concrete `%` equality, then simplify `1 % M = 1`.
  have hmod : (10 ^ 6 : Nat) % M = 1 % M := by
    simpa [Nat.ModEq] using hM
  have h1 : (1 : Nat) % M = 1 := by
    have hlt : 1 < M := by native_decide
    simpa using (Nat.mod_eq_of_lt hlt)
  simpa [h1] using hmod

theorem mul_ten_pow_six_mod_all (n : Nat) : (n * 10 ^ 6) % M = n % M := by
  have hlt : n % M < M := Nat.mod_lt _ (by decide : 0 < M)
  calc
    (n * 10 ^ 6) % M = ((n % M) * ((10 ^ 6 : Nat) % M)) % M := by
      simp [Nat.mul_mod]
    _ = ((n % M) * 1) % M := by
      -- Use a targeted rewrite instead of `simp` to avoid numeric `pow` unfolding surprises.
      rw [ten_pow_six_mod]
    _ = (n % M) % M := by
      simp
    _ = n % M := by
      simp [Nat.mod_eq_of_lt hlt]

end DecimalMod1001
