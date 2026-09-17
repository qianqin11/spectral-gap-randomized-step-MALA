# Package manifest

The distribution contains Lean source, the accompanying manuscript and its
source assets, documentation, and reproducibility scripts. Current build
and audit results are recorded in [BUILD_STATUS.md](BUILD_STATUS.md).

## Lean development

| Path | Contents |
|---|---|
| `UniformRandomMALA/` | Library modules, organized by mathematical construction |
| `UniformRandomMALA.lean` | Aggregate library root |
| `UniformRandomMALA/AllResults.lean` | Public import surface |
| `UniformRandomMALA/Concrete/C1ToFirstOrder.lean` | First-order assumptions and derived upper Taylor inequality |
| `UniformRandomMALA/Concrete/C1MainTheorem.lean` | Paper-facing theorem, corollary, isoperimetry, rejection/overlap, and flow endpoints |
| `UniformRandomMALA/DependencyAudit.lean` | Selected declarations for the actual axiom dependency audit |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | Pinned Lean and mathlib dependency configuration |

## Manuscript files

All of the following are included in `paper/`:

| File | Role |
|---|---|
| `main.pdf` | Typeset manuscript |
| `main.tex` | Manuscript source, including theorem labels |
| `uniform_random_mala.bib` | Bibliography database |
| `hard_target_origin_acceptance.pdf` | Origin-acceptance figure |
| `hard_target_first_coordinate_trace.pdf` | First-coordinate trace figure |
| `hard_target_stationary_comparison.pdf` | Stationary comparison figure |

The manuscript PDF identity is recorded in
[validation/manuscript-pdf.sha256](validation/manuscript-pdf.sha256).
The TeX source uses the bundled bibliography and figure files. Instructions
for typesetting and verification are in [README.md](README.md).

## Documentation and validation

`PAPER_READER_GUIDE.md` introduces the formalization; `THEOREM_MAP.md` maps
paper numbers and TeX labels to declarations. `FORMALIZATION_STATUS.md` and
`TRUST_BOUNDARY.md` describe coverage and assumptions.
`PROOF_STRATEGY_LEDGER.md` and `REUSABLE_RESULTS.md` describe the proof route
and general lemmas.

`scripts/` contains source, first-order-interface, manuscript, numerical,
build, public-import, and axiom gates for Bash and PowerShell, together with
regression tests for the manuscript audit. `validation/` contains curated
validation evidence and checksums. Records under `validation/historical/`
are retained for provenance; `FIRST_ORDER_REVISION.md` describes the
historical transition to the first-order interface.

The companion `../simulation/` directory contains the numerical experiment
code, data, and figures at the repository level. It is separate from the
Lean source distribution and its checksum manifest.

The source distribution excludes `.lake/`, dependency caches, compiled Lean
objects, Git data, Python bytecode, `tmp/`, and `validation/local/`. Local
checks regenerate caches and logs. `validation/SHA256SUMS.txt` covers the
distributed files under `formalization/` except itself; it does not cover the
sibling simulation directory or repository-level documentation and workflow.
[REPOSITORY_UPDATE.md](REPOSITORY_UPDATE.md) describes the update workflow.
