# TwinPrimeIdea Alignment (p-adic Paper v3) vs Certified Lean Spine

Source folder:
- `twinprimeidea/`
  - `paper_v3_twin_primes_padic.md`
  - `independence_proof.py`
  - `observer_tracking.py`

This note is **not** an endorsement of every claim in the paper. It is a
mechanism/evidence alignment map so we can integrate only what is already
provable (Lean) or deterministically testable (Python protocol), without
handwaving.

## 1. What TwinPrimeIdea Is Saying (Decomposed)

The paper separates twin-prime residue behavior into two layers:

1. **Channel architecture (discrete mechanism)**:
   - For a modulus built from primes `p ≥ 3`, there are exactly two forbidden
     residues mod `p`: `0` and `p-2` (equivalently `-2`).
   - CRT means constraints at different primes are independent at the level of
     *allowed residue classes*.

2. **Occupancy by actual twin primes (empirical/equidistribution)**:
   - How many of those allowed residue classes actually contain a twin prime
     below some bound `N`.
   - Seed-vs-regular bookkeeping (small twins involving the prime `p` itself).

UFRF uses the same separation:
- Lean certifies the **architecture** (counts, equalities, invariants).
- Python protocols can certify finite **occupancy facts** for fixed cutoffs.

## 2. Direct Matches to What We Already Certified in Lean

### A. Prime-power allowed-channel count (paper: `(p-2)·p^k`)

Paper claim (regular channel capacity at prime `p`):
- `(p - 2)·p^k` classes mod `p^(k+1)` are available for twins.

Lean mechanism theorem:
- `lean/TwinPrime_AllowedCapacity_PrimePower_Product_Theorem.lean`
  - `PrimePow.card_allowedPow`:
    - `|{r : ZMod (p^(k+1)) // r ≠ 0 and r ≠ -2 }| = (p-2)·p^k`

Interpretation:
- This is **architecture**, not “occupied by primes”.

### B. Cross-tower independence of regular channels (paper: `∏(p_i-2)`)

Paper claim:
- For a finite prime set `P`, the number of regular (non-seed) occupied residue
  classes mod `∏P` equals `∏(p-2)`, and this “independence” is exact.

Lean mechanism theorem (stronger, purely structural):
- `lean/TwinPrime_AllowedCapacity_CRT_List_Theorem.lean`
  - `card_allowed_list_of_pairwise_coprime` (and wrappers)
  - shows *exact multiplicativity* of allowed channels for pairwise-coprime
    moduli.

This exactly matches the paper’s “regular channels are independent” statement,
but Lean makes it true **without data** (CRT, no probabilistic assumptions).

### C. Density + totient “lens” (paper: local factor interpretation)

Paper connects occupancy fractions to Hardy–Littlewood local factors.

Lean already has the deterministic local factors (architecture):
- `lean/TwinPrime_AllowedCapacity_Density_Theorem.lean`
  - `axisDensity = (p-2)/p` (exponent independent)
  - `globalDensity = ∏ (p-2)/p`
- `lean/TwinPrime_AllowedCapacity_Totient_Bridge_Theorem.lean`
  - `allowed(N)/φ(N) = ∏ (p-2)/(p-1)` (exponent independent)
- `lean/TwinPrime_AllowedCapacity_Totient_Bridge_Wrapper_Theorem.lean`
  - wrapper API from prime lists `ps,ks`
- `lean/TwinPrime_AllowedCapacity_Totient_Bridge_Examples.lean`
  - audited examples including `N=1001`

## 3. What Is NOT Proven in Lean (And What Category It Is)

### A. `occ_p(k) = (p-2)·p^k + c_p`

This is about **occupancy by actual twin primes below a bound**, not about
allowed-channel architecture. In our repo terms:
- **Architecture term**: `(p-2)·p^k` (Lean-proven).
- **Seed correction** `c_p`: bookkeeping about small twin pairs involving `p`,
  which live in forbidden classes (0 or `p-2`), so they are *outside* the
  allowed-channel model.

Status:
- Needs an evidence protocol (Python) if we want to keep it as a finite claim.
- Not a candidate for Lean “necessity” until we adopt strong number-theory
  assumptions (which we currently avoid).

### B. “Every allowed joint class is occupied (given enough data)”

This is a **distribution / equidistribution** assertion.
Status:
- Evidence lane only unless we add major analytic machinery.

### C. Defective cascade / unique survivor in the forbidden class

This is an occupancy statement about seed threads. Mechanism pieces (what is
forbidden, how lifts behave combinatorially) are formalizable, but the
“survivor is exactly `p-2` when `(p-2,p)` exists” is occupancy-by-primes.

## 4. What We Should Integrate Next (Low Risk, High Leverage)

1. Keep TwinPrimeIdea’s **seed/regular decomposition** as *terminology* in docs.
   - It explains why “coupling” ratios can look non-multiplicative when mixing
     architecture counts with seed bookkeeping.
2. Optional: add one small Lean lemma capturing the paper’s “universal
   tunneling” fact:
   - if `(n, n+2)` are twin primes with `n > 3`, then `n ≡ 2 (mod 3)`.
   - This is a clean, fully formal statement (no statistics).
3. Treat `twinprimeidea/*.py` as **offline evidence** unless we explicitly add a
   fast protocol version. The current scripts sieve to 50,000,000 and are not
   appropriate for `./scripts/verify.sh`.

## 5. Practical Mapping: Paper → Repo Lanes

- Channel architecture:
  - Lean (already done): Steps 222–231.
- Seed bookkeeping:
  - Doc-only unless we choose to model it formally as “exceptions outside the
    allowed-channel predicate”.
- Occupancy / equidistribution:
  - Python protocol (finite cutoff) if we want to record it as an anchor.
