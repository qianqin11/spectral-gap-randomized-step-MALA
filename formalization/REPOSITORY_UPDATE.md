# Updating the GitHub repository

Repository: [qianqin11/spectral-gap-randomized-step-MALA](https://github.com/qianqin11/spectral-gap-randomized-step-MALA).

The repository's default branch is `main`; the Lean package belongs in its
`formalization/` subdirectory. This supplied workspace is an extracted package
without Git metadata. Use a fresh clone to retain the repository's history.
The commands below prepare a branch, copy the package, and let you review the
changes before committing and pushing. They do not copy build caches.

Run the following in PowerShell, with Git installed. If the checkout directory
already exists, choose a different new directory or use your existing clean
clone instead of running `git clone` again.

```powershell
$ErrorActionPreference = 'Stop'
$packageSource = 'C:\Users\qianq\OneDrive\papers\RandomMALA\Repository\formalization'
$checkout = Join-Path $env:USERPROFILE 'source\spectral-gap-randomized-step-MALA'
if (Test-Path -LiteralPath $checkout) { throw 'Choose a new checkout directory.' }
New-Item -ItemType Directory -Force -Path (Split-Path -Parent $checkout) | Out-Null
git clone https://github.com/qianqin11/spectral-gap-randomized-step-MALA.git $checkout
if ($LASTEXITCODE -ne 0) { throw 'Clone failed.' }
Set-Location -LiteralPath $checkout
git switch -c sync-revised-draft
if ($LASTEXITCODE -ne 0) { throw 'Branch creation failed.' }

$packageDestination = Join-Path $checkout 'formalization'
robocopy $packageSource $packageDestination /E /R:2 /W:1 `
    /XD .lake .git tmp __pycache__ local `
    /XF *.olean *.ilean *.c *.o .DS_Store
if ($LASTEXITCODE -ge 8) { throw 'Package copy failed.' }

# Reconcile the tracked paper inventory with the PDF-only distribution.
$paperRoot = [IO.Path]::GetFullPath((Join-Path $checkout 'formalization\paper'))
$paperFiles = @(git ls-files -- 'formalization/paper/')
if ($LASTEXITCODE -ne 0) { throw 'Could not list tracked paper files.' }
foreach ($relative in $paperFiles) {
    if ($relative -eq 'formalization/paper/main.pdf') { continue }
    $absolute = [IO.Path]::GetFullPath((Join-Path $checkout $relative))
    if (-not $absolute.StartsWith($paperRoot + [IO.Path]::DirectorySeparatorChar,
        [StringComparison]::OrdinalIgnoreCase)) { throw 'Unexpected paper path.' }
    git rm -- $relative
    if ($LASTEXITCODE -ne 0) { throw 'Could not remove a superseded paper file.' }
}

# These old logs are now preserved under validation/historical/2026-09-12/.
git rm --ignore-unmatch -- `
    formalization/validation/manuscript-build.txt `
    formalization/validation/manuscript-source-audit.txt `
    formalization/validation/manuscript-latexmk.log
if ($LASTEXITCODE -ne 0) { throw 'Could not reconcile historical logs.' }

# GitHub Actions loads workflows only from the repository root.
# The supplied parent workflow already uses working-directory: formalization.
$workflowSource = Join-Path (Split-Path -Parent $packageSource) '.github\workflows\lean.yml'
if (Test-Path -LiteralPath $workflowSource) {
    $workflowDirectory = Join-Path $checkout '.github\workflows'
    New-Item -ItemType Directory -Force -Path $workflowDirectory | Out-Null
    Copy-Item -LiteralPath $workflowSource -Destination (Join-Path $workflowDirectory 'lean.yml')
}

git add -- formalization
if ($LASTEXITCODE -ne 0) { throw 'Staging the package failed.' }
if (Test-Path -LiteralPath '.github/workflows/lean.yml') {
    git add -- .github/workflows/lean.yml
    if ($LASTEXITCODE -ne 0) { throw 'Staging the workflow failed.' }
}
git status --short
git diff --cached --stat
git diff --cached -- formalization/UniformRandomMALA/Concrete/C1MainTheorem.lean
```

Review the full staged diff (`git diff --cached`). The intended changes are
the public existential range `A₀ ≥ 1`, the PDF-only manuscript inventory and
new checksum, the PDF packaging audit and tests, and refreshed documentation
and verification evidence. The internal universal constant still satisfies
`A₀ ≥ 2`. No simulation changes are needed. If the remote repository contains
newer independent changes, reconcile them before committing.

To check the copied package, install the pinned Lean toolchain through elan
and Python 3, then run:

```powershell
Set-Location -LiteralPath $packageDestination
lake exe cache get
if ($LASTEXITCODE -ne 0) { throw 'Cache retrieval failed.' }
powershell -ExecutionPolicy Bypass -File .\scripts\check.ps1
if ($LASTEXITCODE -ne 0) { throw 'Verification failed.' }
Set-Location -LiteralPath $checkout
```

After reviewing the staged changes and successful checks, commit and push:

```powershell
git commit -m "Match revised A0 range and PDF-only manuscript distribution"
if ($LASTEXITCODE -ne 0) { throw 'Commit failed.' }
git push -u origin sync-revised-draft
if ($LASTEXITCODE -ne 0) { throw 'Push failed.' }
```

Open a pull request from `sync-revised-draft` into `main` on GitHub, review
the verification workflow result, and merge it. GitHub sign-in is needed for
the push. No commit, push, or pull request was made by the local audit.
