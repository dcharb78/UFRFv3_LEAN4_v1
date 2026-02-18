# UFRF All-Green Validation Package (Maxwell + Dirac + Yang–Mills)

**Purpose.** This is a *stand‑alone*, end‑to‑end validation bundle to review and reproduce the UFRF
(Maxwell, Dirac) results and to bring **Yang–Mills** to “green” by adding: (i) an SU(3) run,
(ii) matter coupling/BRST notes, (iii) a concise continuum→lattice derivation, and (iv) a small
gauge‑invariant correlator probe for a mass scale. It is designed for readers new to UFRF.

**Where each derivation lives (with cross‑refs into the UFRF corpus):**
- Maxwell (“Green”): docs/Maxwell_from_UFRF_Green.md. See the canonical Maxwell proof release. fileciteturn0file4
- Dirac (complete geometric proof): docs/Dirac_from_UFRF_Complete.md. fileciteturn0file3
- Yang–Mills (this package): docs/YM_from_UFRF_Complete.md (includes SU(2)/SU(3) code, BRST, and lattice notes).

**Run everything (quick validation):**
```bash
python code/run_all.py
```
Outputs appear in `results/` (JSON, logs, and small PNGs).

**What you should see (at a glance):**
- **Maxwell (FDTD 1D)**: Near‑null invariants for a plane‑wave class: ⟨E·B⟩≈0 and ⟨E²−c²B²⟩≈0. 
  (Half‑step staggering matches the 0.5/1.5 gates and Yee updates.) fileciteturn0file4 fileciteturn0file11
- **Dirac checks**: Clifford anticommutators {γ^μ,γ^ν}=2η^{μν}I and the square‑root factorization 
  (γ·p−m)(γ·p+m)=(p²−m²)I hold numerically. fileciteturn0file3
- **Yang–Mills (lattice SU(2)/SU(3))**: Average plaquette in a sensible range for β, a falling Wilson‑loop
  signal vs area (rough area law), and a tiny gauge‑invariant plaquette–plaquette correlator fit to extract 
  a correlation length (a mass scale proxy).

**Background reading (single‑source pointers):**
- Axioms/first principles and the 13/26 ladder (half‑spin): fileciteturn0file9 fileciteturn0file11
- SU(2)×SU(2) ladder, REST window (√φ efficiency), and projection law: fileciteturn0file11 fileciteturn0file14
- Integration summary / validation map / predictions: fileciteturn0file6 fileciteturn0file10 fileciteturn0file5
- Fourier rationale (why orthogonal modes are natural in UFRF): fileciteturn0file8

**Directory layout**
```
UFRF_AllGreen_Package_v1.0/
  docs/
    Maxwell_from_UFRF_Green.md
    Dirac_from_UFRF_Complete.md
    YM_from_UFRF_Complete.md
    BRST_and_Matter_Coupling_Notes.md
    Continuum_to_Lattice_Derivation.md
    Concurrent_Triple_Manifolds_and_Nodes.md
    Validation_Checklist.md
  code/
    maxwell_fdtd_1d.py
    dirac_spinor_checks.py
    ym_lattice_su2_demo.py
    ym_lattice_su3_demo.py
    run_all.py
  results/   (created by run_all.py)
  CITATIONS.txt
  VERSION.txt
  LICENSE.txt
```

*If you need a 5‑minute overview before running code*, scan `docs/Validation_Checklist.md` and then run the quick script.
