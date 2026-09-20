# Verification evidence

The package uses pinned Lean 4.33.0 and mathlib 4.33.0. The full Lean gate
passed on **2026-09-19**. All 165 Lean source files and the three dependency
configuration files still match that verified version. The manuscript and
documentation were checked again after the revision to Corollary 2.4;
no Lean statement or proof needed to change.

## Lean verification

| Check | Result from the full gate |
|---|---|
| Source audit | 165 files; 2,161 declarations counted by source regex; no placeholders |
| Interface and imports | Acyclic local imports; mathlib is the sole direct external Lean library |
| Library build | `Build completed successfully (3976 jobs).` |
| Public import | `lake env lean UniformRandomMALA/AllResults.lean` passed |
| Axiom audit | All 281 selected declarations use only `propext`, `Classical.choice`, and `Quot.sound` |
| Supporting numerical checks | 2,000 deterministic trials passed |

These checks cover the development containing the randomized MALA gap and
mixing results, the fixed-step obstruction, and the general aggregation
lemma and theorem. The source audit and library build cover the complete
development; the axiom audit covers the declarations selected in
[DependencyAudit.lean](UniformRandomMALA/DependencyAudit.lean).

## Paper correspondence and documentation

| Check | Result |
|---|---|
| Corollary 2.4 | The assumptions, definitions, and both bounds match `C1Potential.mixingTimeCorollary`; the constant depends only on the tuning parameter |
| Manuscript source | 110 labels, 257 reference uses, 132 citation-key uses, 65 bibliography entries, and three figures checked |
| Lean manuscript references | 134 label uses and 90 numbered theorem/label pairs checked |
| Theorem numbers | All 20 theorem-level labels match the compiled paper; the unlabeled Mills lemma completes the 21 theorem environments in the map |
| Manuscript-audit regression tests | 21 tests passed |
| Theorem-map declarations | All 56 named declarations compile through `AllResults` |
| Reader-guide example | Compiles through `AllResults`; printed logical dependencies are standard |
| Documentation links | Local files and section anchors checked across the current package documentation |
| LaTeX and PDF comparison | 48 pages; normalized extracted text agrees on every page of the supplied and rebuilt PDFs |

The manuscript files were preserved as supplied. The PDF identity is in
[manuscript-pdf.sha256](validation/manuscript-pdf.sha256). Typesetting has no
unresolved references, citations, or overfull boxes. Seven bibliography
underfull-box warnings and eight duplicate PDF-destination warnings remain;
see [manuscript-build.txt](validation/manuscript-build.txt). Text equality
is not a claim of byte-identical or pixel-identical PDFs.

The [reader guide](PAPER_READER_GUIDE.md) explains how to inspect definitions
and trace the complete proofs. [THEOREM_MAP.md](THEOREM_MAP.md) and
[FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) describe coverage and proof
differences, including the unformalized additional scope of Appendix B.
Compilation and an axiom audit complement that comparison; neither alone
establishes that the definitions express the paper's intended mathematics.

## Reproduce and inspect the checks

Use the commands in [README.md](README.md#reproduce-the-verification).
The full gate checks source, manuscript references, regression tests,
numerics, the Lean build, the public import, and actual axiom output.
LaTeX is a separate check.

- [CHECK_OUTPUT.txt](CHECK_OUTPUT.txt): combined verification summary, identifying retained and refreshed checks.
- [Kernel verification](validation/kernel-gate-passed.txt): the full Lean build and dependency audit.
- [Manuscript audit](validation/manuscript-audit.txt): current source and reference checks.
- [Reference audit](validation/lean-reference-audit.txt): statement comparison and documentation checks.
- [Manuscript build](validation/manuscript-build.txt): typesetting and PDF comparison.
- [Compiled labels](validation/manuscript-labels.json): label numbers, page locations, and source hash.

Full local logs include `validation/local/mixing-corollary-gate.log`,
`validation/local/axioms.log`, and `validation/local/reader-guide-review.log`.
Generated files are excluded from distribution. Earlier records under
`validation/historical/` document their own snapshots.
