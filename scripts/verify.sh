#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

export MPLBACKEND=Agg

echo "== Python verification =="
if [[ ! -x "${ROOT_DIR}/.venv/bin/python" ]]; then
  echo "Missing venv at ${ROOT_DIR}/.venv (run: python3 -m venv .venv && .venv/bin/pip install -r requirements.txt)"
  exit 1
fi

"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/sigma1_theorem_verification.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/fine_structure_alpha_intrinsic_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/fine_structure_alpha_projection_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/dirac_clifford_anticommutator_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/dirac_factorization_scaled_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/pauli_quaternion_bridge_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/pauli_quaternion_q8_closure_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/pauli_quaternion_su2_commutator_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/pauli_quaternion_q8_gauge_invariance_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/q8_plaquette_wilson_loop_gauge_invariance_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/q8_wilson_loop_gauge_invariance_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/maxwell_poynting_identity_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/maxwell_field_tensor_duality_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/maxwell_invariants_from_tensor_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/maxwell_duality_invariants_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/maxwell_tensor_hodge_star_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/maxwell_tensor_duality_noether_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/tn_recurrence_universality.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/gap_set_prime_theorem.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/riemann_zero_exclusion_corrected.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/j_function_coefficient_theorem.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/j_qexp_from_delta_e4_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/boundary_overlap_prediction_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/network_optima_prediction_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/acoustic_n13_prediction_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/musical_harmony_13_over_n_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/prime_choreography_autocorr_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/prime_choreography_discriminant_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/prism_primitive_root_order_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/prism_complement_vs_inverse_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/prism_projection_compatibility_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/quantum_hall_n13_prediction_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/submagic_multiples13_prediction_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/shell_gap_projection_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/critical_positions_alignment_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/tc_sqrtphi_enhancement_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/dna_helix_rest_halfstep_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/network_137_threshold_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/anomaly_28k_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/phase_transition_144_scale_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/neural_oscillation_13x_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/dark_matter_projection_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/protein_folding_positions_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/binding_energy_oscillation_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/galaxy_rotation_mod13_residual_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/observer_composition_projection_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/tensor_projection_law_v3_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/projection_versions_reduction_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/moonshine_inevitability_chain_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/projection_tensor_rowsum_scalar_bridge_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/position_counted_scale_projection_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/decimal_nested_tick_projection_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/ppn_micro_oscillation_projection_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/projection_technique_variation_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/projection_zero_distance_identity_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/projection_distance_monotonicity_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/mod1001_composite_cycle_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/mod1001_inevitability_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/acoustic_critical_positions_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/mod1001_order_decomposition_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/monster_ap12_uniqueness_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/monster_pair_origin_uniqueness_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/monster_source_ap12_inevitability_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/moonshine_inevitability_from_source_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/monster_mod1001_order_classes_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/rest_anchor_cross_domain_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/network_scale_threshold_integration_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/critical_scale_7_14_28_integration_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/anchor_144_cross_domain_integration_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/twinprime_occupancy_boundary_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/observer_digits_cycle_position_protocol.py"
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/observer_digits_cycle_periodicity_protocol.py"

echo ""
echo "== Protocol coverage gate =="
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/scripts/protocol_coverage_gate.py"

echo ""
echo "== Lean build =="
if [[ ! -x "${HOME}/.elan/bin/lake" ]]; then
  echo "Missing elan/lake at ${HOME}/.elan/bin (install elan first)."
  exit 1
fi

"${HOME}/.elan/bin/lake" build

echo ""
echo "== Main transitive dependency coverage check =="
# Guardrail to avoid silent drift with layered imports:
# every root `lean/*.lean` (except Main) must be reachable via recursive imports.
queue=(Main)
seen="|Main|"

while [[ ${#queue[@]} -gt 0 ]]; do
  mod="${queue[0]}"
  queue=("${queue[@]:1}")
  file="${ROOT_DIR}/lean/${mod}.lean"
  if [[ ! -f "${file}" ]]; then
    continue
  fi

  while IFS= read -r dep; do
    [[ -z "${dep}" ]] && continue
    dep_file="${ROOT_DIR}/lean/${dep}.lean"
    if [[ -f "${dep_file}" ]] && [[ "${seen}" != *"|${dep}|"* ]]; then
      seen="${seen}${dep}|"
      queue+=("$dep")
    fi
  done < <(awk '/^import / { print $2 }' "${file}")
done

missing=0
while IFS= read -r -d '' f; do
  mod="$(basename "${f}" .lean)"
  if [[ "${mod}" == "Main" ]]; then
    continue
  fi
  if [[ "${seen}" != *"|${mod}|"* ]]; then
    echo "Missing transitive dependency from lean/Main.lean: ${mod}"
    missing=1
  fi
done < <(find "${ROOT_DIR}/lean" -maxdepth 1 -type f -name '*.lean' -print0)

if [[ "${missing}" -ne 0 ]]; then
  exit 1
fi
echo "All lean/*.lean files are reachable from lean/Main.lean (transitive)."

echo ""
echo "== Multi-view context gate =="
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/scripts/multiview_gate.py"

echo ""
echo "== Lean context check =="
"${HOME}/.elan/bin/lake" env lean "${ROOT_DIR}/context/UFRF_UNIFIED_PROOF.lean"
"${HOME}/.elan/bin/lake" env lean "${ROOT_DIR}/context/UFRF_KERNEL_PROOF.lean"
"${HOME}/.elan/bin/lake" env lean "${ROOT_DIR}/context/UFRF_START_HERE.lean"

echo ""
echo "== Sorry/admit check =="
# Note: `aristotle/` and `_refs/` contain archived / external materials and may include `sorry`.
# The canonical no-placeholder surface is `lean/` + `context/`.
if grep -RIn --include='*.lean' --exclude-dir='.lake' --exclude-dir='build' --exclude='lakefile.lean' -E "\\bsorry\\b|\\badmit\\b" "${ROOT_DIR}/lean" "${ROOT_DIR}/context" >/dev/null; then
  echo "Found sorry/admit in Lean sources:"
  grep -RIn --include='*.lean' --exclude-dir='.lake' --exclude-dir='build' --exclude='lakefile.lean' -E "\\bsorry\\b|\\badmit\\b" "${ROOT_DIR}/lean" "${ROOT_DIR}/context" || true
  exit 1
fi
echo "No sorry/admit found."

echo ""
echo "== Coherence checkpoint =="
# Keeps `context/.coherence_state.min.json` in sync with the canonical ledger + key pipeline hashes.
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/scripts/update_coherence_checkpoint.py"

echo ""
echo "== Session state =="
# Human-readable "where are we?" pointer file.
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/scripts/update_session_state.py"
