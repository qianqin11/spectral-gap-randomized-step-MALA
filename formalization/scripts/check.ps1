$ErrorActionPreference = "Stop"

$projectRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot "..")).Path
Set-Location -LiteralPath $projectRoot

python scripts/static_audit.py
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }

python scripts/numeric_sanity.py
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }

lake build
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }

lake env lean UniformRandomMALA/AllResults.lean
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }

lake env lean UniformRandomMALA/DependencyAudit.lean
exit $LASTEXITCODE

