# Distribution package manifest

Package name: `UniformRandomMALA-Lean-Complete-2026-08-30`

`Complete` refers to all manuscript-facing results recorded in
`COMPLETION_REPORT.md`, including the randomized-step lower bound and the
fixed-step minimax upper bound.

## Included

- `UniformRandomMALA.lean`: complete project import;
- `UniformRandomMALA/`: every Lean source module, including the content-named
  public entry files;
- `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain`: reproducible
  Lean/mathlib configuration;
- `scripts/`: Unix, Windows, static, and numerical checks;
- `.github/workflows/lean.yml`: CI build workflow;
- `paper/`: the current manuscript (`main.pdf`, `main.tex`, compiled
  bibliography, and `uniform_random_mala.bib`), plus `paper/legacy/`, whose
  README identifies the retained unique companion note as background rather
  than a competing manuscript draft;
- `README.md`: installation, verification, and usage instructions;
- `PAPER_READER_GUIDE.md`: mathematical conventions, paper-to-Lean proof
  differences, and suggested reading paths;
- `REUSABLE_RESULTS.md`: scope, imports, and examples for the general
  Gaussian, Bakry--Ledoux, weak-limit, and transfer theorems;
- `PROOF_STRATEGY_LEDGER.md`: concise current proof ledger;
- `THEOREM_MAP.md`: detailed source-to-declaration cross-reference;
- `FORMALIZATION_STATUS.md`, `FORMALIZATION_REPORT.md`, `BUILD_STATUS.md`, and
  `TRUST_BOUNDARY.md`: validation and trust-boundary reports;
- `COMPLETION_REPORT.md`: exact paper-result declarations, changed files,
  reusable additions, build and axiom results, manuscript audit, and scope;
- `LEAN_FRIENDLY_PROOF_LEDGER.md` and
  `BAKRY_LEDOUX_DISCRETE_LANGEVIN_PROOF.md`: clearly marked archival
  development and design records;
- `MALA_OVERLAP_FORMALIZATION.md`: local-overlap source cross-reference;
- `.gitignore` and the recorded audit summaries.

## Public Lean entry files

```text
UniformRandomMALA/MALAOverlap.lean
UniformRandomMALA/WeakLimitStability.lean
UniformRandomMALA/GaussianBobkov.lean
UniformRandomMALA/BakryLedoux.lean
UniformRandomMALA/SpectralGap.lean
UniformRandomMALA/AllResults.lean
```

The first five names describe mathematical content rather than paper section
or proposition numbers.  `AllResults.lean` is the convenient aggregate import.

## Intentionally excluded from the archive

- `.lake/`: locally generated build products and downloaded dependencies;
- `work/`: scratch experiments and external-library investigations;
- editor metadata, temporary files, and Python bytecode caches.

Reviewers should reconstruct `.lake/` with `lake exe cache get` and then run
`lake build`.  Excluding local build products keeps the archive small and
makes the verification process independent of the originating machine.
