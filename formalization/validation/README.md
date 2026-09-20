# Validation records

Current verification scope and results are summarized in
[BUILD_STATUS.md](../BUILD_STATUS.md). `kernel-gate-passed.txt` records the
last complete Lean gate. The root `CHECK_OUTPUT.txt` and `CHECK_STATUS.txt`
combine that verified proof version with the current manuscript and
documentation checks, identifying which checks were refreshed.

| Record | Contents |
|---|---|
| `static-audit.txt`, `first-order-audit.txt` | Lean source and interface checks |
| `manuscript-audit.txt` | PDF checksum, source references, citations, figures, and Lean paper references |
| `manuscript-tests.txt` | Manuscript-audit regression tests |
| `lean-reference-audit.txt` | Theorem-number and label concordance |
| `manuscript-labels.json` | Labels extracted from the compiled TeX, with source hash |
| `manuscript-build.txt` | LaTeX build and bundled/rebuilt PDF text comparison |
| `manuscript-pdf.sha256` | Identity of the bundled manuscript PDF |
| `numeric-sanity.txt` | Supporting numerical checks |
| `integrity.txt`, `SHA256SUMS.txt` | Package scope and distributed-file checksums |

`validation/local/` contains full local build and axiom logs and is excluded
from distribution. The public scripts reproduce the Lean verification gate;
LaTeX is a separate build as described in the package README.

`historical/` preserves earlier snapshots, including the first-order revision
and previous manuscript distributions. Candidate patches and old build logs
describe their recorded stages, not the current manuscript. `source-changes.json`
records the scope of the latest manuscript comparison and documentation
review, together with the source identity of the checked Lean development.

`SHA256SUMS.txt` uses repository-relative paths under `formalization/` and
excludes itself, `.lake/`, `tmp/`, `validation/local/`, Git metadata, and
compiled/bytecode artifacts. It does not cover the sibling simulation package.
