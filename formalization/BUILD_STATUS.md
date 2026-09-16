# Build status — revised draft and PDF-only distribution

Validation date: **2026-09-15** (local time, America/Chicago).

| Check | Result |
|---|---|
| Pinned toolchain | Lean 4.33.0; Lake 5.0.0; mathlib 4.33.0 |
| Static source audit | Passed: 155 Lean files; 2,069 top-level declarations; no placeholders |
| First-order/import audit | Passed: acyclic graph; mathlib is the only direct external library |
| Manuscript PDF audit | Passed: recorded SHA-256, basic header/end marker, and PDF-only inventory |
| PDF audit regression tests | Passed: seven tests, including missing/altered inputs and extra paper files |
| Numerical sanity audit | Passed: 2,000 deterministic trials |
| Full kernel build | Passed: `Build completed successfully (3439 jobs).` |
| Public entry point | `lake env lean UniformRandomMALA/AllResults.lean` passed |
| Dependency audit | Passed for all 266 requested declarations |
| Allowed axioms | `propext`, `Classical.choice`, `Quot.sound` only |
| PowerShell wrapper | Passed with final line `FULL SOURCE BUILD AND AXIOM AUDIT PASSED` |
| Script/instruction syntax | Python and PowerShell syntax checks passed |

The public existential statements in `C1MainTheorem.lean`,
`HessianMainTheorem.lean`, and `LazyKernel.lean` now state `A₀ ≥ 1`.
Their existing universal witness satisfies `A₀ ≥ 2`, and the stronger internal
moment assumptions are preserved. All three modified modules were included
in the fresh full build and the existing axiom audit.

`paper/` contains only the revised 47-page `main.pdf`, with SHA-256
`eb3ec374502cbc7b01a2552164f8d64693f64fef333f9948173f575d09a6c4f9`.
TeX, bibliography, and separate figures are not bundled. The PDF audit is an
identity/inventory check; no current LaTeX build or source-reference/citation
audit is claimed. Earlier manuscript build records are preserved under
`validation/historical/2026-09-12/`.

`validation/local/full-gate.log` contains the complete fresh gate output;
`validation/local/axioms.log` contains the actual axiom declarations.
`CHECK_OUTPUT.txt` and `validation/kernel-gate-passed.txt` are compact summaries.
The 2,069 declaration count is a source-regex count, not the full elaborated
Lean environment. The build emitted linter/style warnings but no errors.

The check used the pinned mathlib cache and built all project modules from
source. On this Windows host, `ELAN_HOME` was set to the existing elan
installation and command-local Git `safe.directory` entries named the cached
dependency directories. No global Git configuration was changed.

To reproduce, fetch dependencies with `lake exe cache get`, then run
`scripts/check.ps1` or `bash scripts/check.sh`. Local logs and `.lake/` are
excluded from the distributed package.
