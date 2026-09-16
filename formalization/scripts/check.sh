#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p validation/local
python3 scripts/static_audit.py | tee validation/local/static.log
python3 scripts/first_order_audit.py | tee validation/local/first-order.log
python3 scripts/manuscript_audit.py | tee validation/local/manuscript.log
python3 scripts/test_manuscript_audit.py 2>&1 | tee validation/local/manuscript-tests.log
python3 scripts/numeric_sanity.py | tee validation/local/numeric.log
if ! command -v lake >/dev/null 2>&1; then
  echo "BLOCKED: Lean/Lake not found. No kernel verification has been performed." >&2
  exit 2
fi
lake --version | tee validation/local/toolchain.log
lake build 2>&1 | tee validation/local/build.log
lake env lean UniformRandomMALA/AllResults.lean 2>&1 | tee validation/local/all-results.log
lake env lean UniformRandomMALA/DependencyAudit.lean 2>&1 | tee validation/local/axioms.log
python3 scripts/check_axioms.py validation/local/axioms.log | tee validation/local/axiom-gate.log
echo "FULL SOURCE BUILD AND AXIOM AUDIT PASSED"
