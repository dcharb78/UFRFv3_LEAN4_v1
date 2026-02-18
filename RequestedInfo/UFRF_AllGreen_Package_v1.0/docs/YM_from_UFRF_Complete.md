# Yang–Mills from the UFRF Lens — Complete Package Notes

**What “green” means here.** Beyond the Maxwell and Dirac layers, we include:
1) A working **SU(2)** lattice demonstration (Metropolis) with average plaquette, Wilson loops, and a crude mass proxy
   from a plaquette correlator; 2) a minimal **SU(3)** run; 3) BRST + matter‑coupling notes; 4) a concise continuum→lattice
   derivation. The **UFRF mapping**: the SU(2)×SU(2) half‑spin ladder provides the spinor/bundle structure; an SU(3) “container”
   can host U(1)×SU(2) structures without altering the U(1) Maxwell proof; projection and REST windows dictate how observed
   couplings “run” across techniques/scales. fileciteturn0file11 fileciteturn0file6

**Small‑lattice scope (fast checks).** We keep lattices small so that `python code/run_all.py` finishes quickly. This is not a
precision calculation; it’s a *health check* showing: (i) gauge‑invariant observables behave sensibly; (ii) area‑law trend for
small Wilson loops; (iii) a nonzero correlation length appears in a plaquette–plaquette correlator, usable as a mass scale proxy.

**How to interpret outputs.** See `results/ym_su2_summary.json` and `results/ym_su3_summary.json`. Extracted correlation length
(ξ) is in lattice units; a crude “mass” is 1/ξ. Increase volume/sweeps for stability.

**Where the rest lives (background).** For axioms (concurrency, projection, 13/26 ladder), geometry & scales, Fourier basis
rationale, cross‑domain validation and predictions, see the UFRF corpus pointers embedded throughout this package. 
fileciteturn0file9 fileciteturn0file12 fileciteturn0file8 fileciteturn0file10 fileciteturn0file5
