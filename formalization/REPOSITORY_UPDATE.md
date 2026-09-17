# Maintaining the repository

Repository:
[qianqin11/spectral-gap-randomized-step-MALA](https://github.com/qianqin11/spectral-gap-randomized-step-MALA).
The Lean package and bundled manuscript are maintained in `formalization/`.
The following workflow is intended for contributors preparing a source or
manuscript update.

## Prepare a branch

Use a clean checkout with the repository's history. For a new checkout:

```powershell
git clone https://github.com/qianqin11/spectral-gap-randomized-step-MALA.git
if ($LASTEXITCODE -ne 0) { throw 'Clone failed.' }
Set-Location spectral-gap-randomized-step-MALA
git switch -c update-manuscript-formalization
if ($LASTEXITCODE -ne 0) { throw 'Branch creation failed.' }
```

For an existing checkout, review `git status` and bring the intended base
branch up to date before creating a working branch. Reconcile independent
changes before replacing files from a source snapshot.

## Update source and documentation together

Edit the package in `formalization/`. If importing a source snapshot, copy
its distributed contents into that directory, excluding `.lake/`, `.git/`,
compiled objects, Python bytecode, temporary files, and `validation/local/`.
Review removals individually against tracked files.

Keep the complete manuscript bundle: `main.tex`, `main.pdf`,
`uniform_random_mala.bib`, and the three figure PDFs named in
`PACKAGE_MANIFEST.md`. When changing the paper, update the source and PDF
together, and refresh `validation/manuscript-pdf.sha256` to identify the
intended PDF. Preserve existing TeX labels when possible; update Lean paper
references and `THEOREM_MAP.md` if labels or numbering change.

Keep reader documentation focused on assumptions, coverage, theorem
navigation, and reproducibility. Record current validation in
`BUILD_STATUS.md` and the curated files under `validation/`; retain older
records under `validation/historical/` with their original scope identified.
Regenerate `validation/SHA256SUMS.txt` after the distributed files are final,
using its existing path and exclusion conventions.

The repository-level workflow belongs in `.github/workflows/`. Changes to
the package layout or check commands should be reflected in that workflow
and in the reader instructions.

## Verify and review

Install Git, Python 3, and `elan`, then run the package gate:

```powershell
Push-Location formalization
try {
    lake exe cache get
    if ($LASTEXITCODE -ne 0) { throw 'Cache retrieval failed.' }
    powershell -ExecutionPolicy Bypass -File .\scripts\check.ps1
    if ($LASTEXITCODE -ne 0) { throw 'Verification failed.' }
}
finally { Pop-Location }
```

The Bash equivalent is described in `formalization/README.md`. If the
manuscript changed, typeset it from `formalization/paper/` with
`latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex`, and review
warnings and the resulting PDF. Keep typesetting evidence separate from
Lean kernel and source-audit results.

Inspect the complete diff before committing:

```powershell
git status --short
git diff --stat
git diff -- formalization
```

Confirm that manuscript source assets are present, paper references match
the TeX labels, documented mathematical scope matches the declarations,
and generated caches or local logs are absent from the staged changes.
Stage the intended package changes with `git add -- formalization`; stage
any repository-level documentation or workflow changes separately.
Review `git diff --cached` and `git diff --cached --check`.

## Submit the update

After successful checks and review:

```powershell
git commit -m "Synchronize manuscript source and formalization documentation"
if ($LASTEXITCODE -ne 0) { throw 'Commit failed.' }
git push -u origin HEAD
if ($LASTEXITCODE -ne 0) { throw 'Push failed.' }
```

Open a pull request against the intended base branch. Describe the
mathematical or documentation changes, the checks performed, and any scope
limitations. Review the repository's verification workflow before merging.
