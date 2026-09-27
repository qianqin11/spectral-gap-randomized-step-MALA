# Verification evidence

The current package passed the full verification gate on **2026-09-26**,
using pinned Lean 4.33.0 and mathlib v4.33.0. It covers every requested
paper result except Lemmas B.2–B.5, including the CLTs from arbitrary
initial distributions and the full nonconvex rejection estimate.

## Lean verification

| Check | Result |
|---|---|
| Source audit | 275 Lean files; 3234 declarations counted by source regex; no proof placeholders |
| Interface and imports | Acyclic local imports; mathlib is the sole direct external Lean library |
| Full library build | Passed; 4,131 jobs |
| Public `AllResults` import | Passed |
| Dependency audit | 318 selected declarations; only `propext`, `Classical.choice`, and `Quot.sound` |
| Manuscript-audit regression tests | 21 passed |
| Supporting numerical checks | 2,000 deterministic trials passed |

The full gate ended with `FULL SOURCE BUILD AND AXIOM AUDIT PASSED`.
The library build covers every source module. The dependency audit checks
the declarations selected in
[DependencyAudit.lean](UniformRandomMALA/DependencyAudit.lean), including
the main endpoints, aggregation, variance comparison, MSE, rejection, and CLT.
Nonfatal linter warnings concern source style, such as unused variables or
tactics; they do not leave proofs unverified.

## Manuscript and reader documentation

| Check | Result |
|---|---|
| Manuscript references | 122 labels, 299 reference uses, 145 citation-key uses, 76 bibliography entries, three figures |
| Lean manuscript references | 185 label uses and 135 numbered theorem/label pairs |
| Compiled result numbers | All 25 labeled result numbers agree with the source parser |
| Paper statement review | All 21 in-scope numbered results and Remark 2.4 have formalized endpoints |
| Documentation declarations | 69 theorem-map names located; 83 Lean inspection commands compile |
| Reader-guide example | 22 commands compile through `AllResults`, with standard axiom dependencies |
| Documentation navigation | 284 local links and heading anchors checked across 13 reader documents |
| Fresh LaTeX/BibTeX build | 55 pages; no unresolved references or citations |
| Supplied/rebuilt PDF comparison | Normalized extracted text agrees on all 55 pages |

The supplied manuscript assets were preserved. Typesetting warnings are
recorded in [manuscript-build.txt](validation/manuscript-build.txt); text
equality does not assert byte or pixel equality. The manuscript's own
verification narrative still describes an older, narrower formalization
scope and an earlier audit count. Current coverage is recorded in
[FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md).

## Reproduce and inspect

Use the commands in [README.md](README.md#reproduce-the-verification).
The [reader guide](PAPER_READER_GUIDE.md) explains how to compare the actual
definitions with the paper and follow the complete proof routes.

- [Combined verification record](CHECK_OUTPUT.txt)
- [Kernel gate](validation/kernel-gate-passed.txt)
- [Statement and documentation review](validation/lean-reference-audit.txt)
- [Manuscript source audit](validation/manuscript-audit.txt)
- [Compiled labels](validation/manuscript-labels.json)
- [Package checksums](validation/SHA256SUMS.txt)

Full local logs are in `validation/local/current-full-gate.log`,
`validation/local/axioms.log`, `validation/local/reader-doc-checks.log`,
and `validation/local/reader-guide-review.log`. Earlier evidence is preserved
under `validation/historical/` and describes its own snapshots.
