#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/static_audit.py
python3 scripts/numeric_sanity.py
if command -v lake >/dev/null 2>&1; then
  lake build
  lake env lean UniformRandomMALA/AllResults.lean
  lake env lean UniformRandomMALA/DependencyAudit.lean
else
  echo "Lean/Lake not found; kernel checking was skipped." >&2
  exit 2
fi
