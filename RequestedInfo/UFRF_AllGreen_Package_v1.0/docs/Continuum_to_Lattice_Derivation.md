# Continuum → Lattice (Wilson) in One Page

**Continuum YM.** S = (1/4g²) ∫ d⁴x F^a_{μν} F^{aμν}, F=dA + A∧A. Gauge invariance ⇒ local redundancy.

**Lattice discretization.** Put the theory on a hypercubic lattice with link variables U_μ(x) ∈ SU(N). The Wilson
plaquette is U_p = U_μ(x) U_ν(x+μ) U_μ(x+ν)^† U_ν(x)^†. Wilson action:
S_W = β Σ_p (1 − (1/N) Re Tr U_p), with β = 2N/g². As a → 0, expand U_μ(x) ≈ exp(i a A_μ) to recover the continuum
action. Wilson loops W(R,T) ≡ ⟨(1/N)Re Tr ∏ links⟩ test confinement (area law).

**What we implement here.** Minimal Metropolis updates for SU(2) and SU(3), small lattices for quick tests, average
plaquette, small Wilson loops, and a plaquette–plaquette correlator giving a crude correlation length (mass proxy).
UFRF mapping: the half‑step staggering and SU(2)×SU(2) ladder remain intact; SU(3) acts as a “container” for the
electromagnetic SU(2)×SU(2) structure when desired. fileciteturn0file11
