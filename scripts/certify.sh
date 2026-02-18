#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

MODE="incremental"
if [[ "${1:-}" == "--clean" ]]; then
  MODE="clean"
fi

TS="$(date -u +%Y%m%dT%H%M%SZ)"
LOG_DIR="${ROOT_DIR}/context/cert"
LOG_FILE="${LOG_DIR}/certify_${MODE}_${TS}.log"
mkdir -p "${LOG_DIR}"
completed=0

on_exit() {
  local code=$?
  if [[ "${code}" -eq 0 && "${completed}" -eq 1 ]]; then
    echo "CERT_STATUS=PASS"
  else
    echo "CERT_STATUS=FAIL"
  fi
  echo "CERT_LOG=${LOG_FILE}"
}
trap on_exit EXIT

# Use process substitution for logging so command failures are never masked.
exec > >(tee "${LOG_FILE}") 2>&1

echo "CERT_MODE=${MODE}"
echo "START_UTC=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
echo "ROOT_DIR=${ROOT_DIR}"
echo "LEAN_TOOLCHAIN=$(cat "${ROOT_DIR}/lean-toolchain")"

if [[ "${MODE}" == "clean" ]]; then
  echo ""
  echo "== Lean clean =="
  "${HOME}/.elan/bin/lake" clean
  echo ""
  echo "== Lean cache refresh =="
  "${HOME}/.elan/bin/lake" exe cache get
fi

echo ""
echo "== Full verify =="
"${ROOT_DIR}/scripts/verify.sh"

echo ""
echo "== Hardening audit snapshot =="
nd_count="$(rg -n "by\\s+native_decide" "${ROOT_DIR}/lean" --glob '*.lean' | wc -l | tr -d ' ')"
echo "NATIVE_DECIDE_BY_COUNT=${nd_count}"
echo "NATIVE_DECIDE_TOP_FILES:"
rg -n "by\\s+native_decide" "${ROOT_DIR}/lean" --glob '*.lean' \
  | cut -d: -f1 \
  | sort \
  | uniq -c \
  | sort -nr \
  | head -n 10

echo ""
echo "END_UTC=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
completed=1

# Emit final status lines inside the log body as well (not only via `EXIT` trap),
# so pointer files like `context/SESSION_STATE.md` can reliably detect PASS/FAIL.
echo "CERT_STATUS=PASS"
echo "CERT_LOG=${LOG_FILE}"
echo ""
echo "== Session state refresh =="
"${ROOT_DIR}/.venv/bin/python" "${ROOT_DIR}/scripts/update_session_state.py" || true
