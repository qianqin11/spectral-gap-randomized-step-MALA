# Validation records

Current release evidence is in `kernel-gate-passed.txt`, `static-audit.txt`,
`first-order-audit.txt`, `manuscript-pdf-audit.txt`, `manuscript-tests.txt`,
`numeric-sanity.txt`, `integrity.txt`, and the root
`CHECK_OUTPUT.txt`/`CHECK_STATUS.txt`. The full build and machine-generated
axiom logs are under `validation/local/`, which is excluded from releases.

`manuscript-pdf.sha256` records the identity of the revised `paper/main.pdf`.
The manuscript audit checks this checksum and that `paper/` contains only
that PDF. It does not rebuild LaTeX or audit source labels or citations.

`historical/2026-09-12/` preserves the superseded kernel-status snapshot,
TeX build, LaTeX log, and manuscript-source audit. Those records describe
an earlier distribution and do not verify the revised PDF. The candidate
`source-changes.patch` and `manuscript-changes.patch` also remain historical
records; they are not the diff for the current update. `source-changes.json`
records the current reconciliation. `historical/pre-first-order/` preserves
the older Hessian-facing documentation.

`SHA256SUMS.txt` covers the distributed files under `formalization/` except
itself, with repository-relative paths. It excludes `.lake/`, `tmp/`,
`validation/local/`, Git data, and compiled/bytecode artifacts.
