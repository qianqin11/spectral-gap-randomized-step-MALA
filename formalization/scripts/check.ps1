# A failed native command stops the audit; static success is not kernel success.
$ErrorActionPreference = 'Stop'
Push-Location -LiteralPath (Join-Path $PSScriptRoot '..')
try {
    New-Item -ItemType Directory -Force -Path 'validation/local' | Out-Null
    $PythonCommand = Get-Command python -ErrorAction SilentlyContinue
    $PythonArgs = @()
    if (-not $PythonCommand) {
        $PythonCommand = Get-Command py -ErrorAction SilentlyContinue
        $PythonArgs = @('-3')
    }
    if (-not $PythonCommand) {
        throw 'BLOCKED: Python 3 is unavailable; source audits were not run.'
    }
    $PythonExe = $PythonCommand.Source
    & $PythonExe @PythonArgs scripts/static_audit.py
    if ($LASTEXITCODE -ne 0) { throw 'Static audit failed.' }
    & $PythonExe @PythonArgs scripts/first_order_audit.py
    if ($LASTEXITCODE -ne 0) { throw 'First-order source audit failed.' }
    & $PythonExe @PythonArgs scripts/manuscript_audit.py
    if ($LASTEXITCODE -ne 0) { throw 'Manuscript and Lean-reference audit failed.' }
    & $PythonExe @PythonArgs scripts/test_manuscript_audit.py
    if ($LASTEXITCODE -ne 0) { throw 'Manuscript audit tests failed.' }
    & $PythonExe @PythonArgs scripts/numeric_sanity.py
    if ($LASTEXITCODE -ne 0) { throw 'Numerical sanity check failed.' }
    if (-not (Get-Command lake -ErrorAction SilentlyContinue)) {
        throw 'BLOCKED: Lean/Lake is unavailable; no kernel check was performed.'
    }
    lake --version
    if ($LASTEXITCODE -ne 0) { throw 'Pinned toolchain unavailable.' }
    lake build
    if ($LASTEXITCODE -ne 0) { throw 'Lean build failed.' }
    lake env lean UniformRandomMALA/AllResults.lean
    if ($LASTEXITCODE -ne 0) { throw 'Public entry-point check failed.' }
    $AuditOutput = & lake env lean UniformRandomMALA/DependencyAudit.lean 2>&1
    $AuditExit = $LASTEXITCODE
    $AuditOutput | ForEach-Object { $_.ToString() }
    $AuditOutput | ForEach-Object { $_.ToString() } |
        Set-Content -LiteralPath 'validation/local/axioms.log' -Encoding UTF8
    if ($AuditExit -ne 0) { throw 'Lean dependency audit failed.' }
    & $PythonExe @PythonArgs scripts/check_axioms.py validation/local/axioms.log
    if ($LASTEXITCODE -ne 0) { throw 'Axiom allow-list check failed.' }
    Write-Host 'FULL SOURCE BUILD AND AXIOM AUDIT PASSED'
}
finally { Pop-Location }
