# Verification evidence

Validation date: **2026-09-16**. The development uses pinned Lean 4.33.0 and
mathlib 4.33.0. The full verification gate completed successfully.

| Check | Result |
|---|---|
| Lean source audit | Passed: 155 files; 2,069 top-level declarations counted by source regex; no placeholders |
| First-order interface and imports | Passed; acyclic local imports; mathlib is the sole direct external Lean library |
| Manuscript source | Passed: 108 labels, 252 reference uses, 117 citation-key uses, 58 bibliography entries, three figures |
| Lean manuscript references | Passed: 122 label uses and 78 numbered theorem/label pairs |
| Manuscript regression tests | Passed: 21 tests for missing/changed assets and invalid references |
| Numerical sanity checks | Passed: 2,000 deterministic trials |
| Lean build | Passed: `Build completed successfully (3439 jobs).` |
| Public import | `lake env lean UniformRandomMALA/AllResults.lean` passed |
| Axiom dependencies | All 266 selected declarations passed; only `propext`, `Classical.choice`, and `Quot.sound` |
| LaTeX build | Passed: 47 pages; no unresolved references or citations; no overfull boxes |
| Source/PDF correspondence | Bundled and rebuilt PDFs have equal normalized extracted text on all 47 pages |

The recent Lean edits add stable manuscript labels and correct two location
references in comments. The theorem statements and proofs are unchanged.
The public existential constant range remains `A₀ ≥ 1`, proved with the
existing witness satisfying `A₀ ≥ 2`.

## Manuscript and theorem references

`paper/` contains `main.tex`, `main.pdf`, `uniform_random_mala.bib`, and the
three figure PDFs used by the source. The PDF checksum is recorded in
[manuscript-pdf.sha256](validation/manuscript-pdf.sha256).
The source-label audit checks active labels, references, citations, figure
inputs, and the labels and numbers written in Lean comments.

All 19 theorem-level labels agree with the fresh LaTeX build. The Mills-ratio
lemma has no theorem-level label; its equation labels identify Lemma C.1.
[THEOREM_MAP.md](THEOREM_MAP.md) covers all 20 theorem environments and
distinguishes direct formalizations from alternative proofs and scope limits.

The bundled PDF was produced with MiKTeX and retained unchanged. A separate
TeX Live 2025 build produced the same page count and normalized extracted
text. PDF bytes and exact rendering can differ across TeX distributions.
Four underfull-box warnings remain; the LaTeX build has no overfull boxes.
LaTeX also reports four duplicate PDF-destination warnings for `equation.18`.
Source labels and theorem numbers are unique and resolved; the duplicate
destination may affect the PDF equation hyperlink. Details are recorded in
`validation/manuscript-build.txt`; the manuscript source and PDF were preserved.

## Reproduction and records

Run `lake exe cache get`, then `scripts/check.ps1` on Windows or
`bash scripts/check.sh` on Linux/macOS. The gate checks source, manuscript
references, regression tests, numerics, the full Lean build, the public
import, and the actual axiom output. It does not invoke LaTeX automatically.
Typesetting instructions are in [README.md](README.md).

- [CHECK_OUTPUT.txt](CHECK_OUTPUT.txt): compact gate summary.
- [Manuscript audit](validation/manuscript-audit.txt): source and reference checks.
- [Reference audit](validation/lean-reference-audit.txt): concordance details.
- [Manuscript build](validation/manuscript-build.txt): typesetting and PDF comparison.
- [Compiled labels](validation/manuscript-labels.json): label numbers and page locations.

Full local logs are `validation/local/restored-source-gate.log` and
`validation/local/axioms.log`; generated files are excluded from distribution.
Earlier records under `validation/historical/` document their own snapshots.
Static and numerical audits are supporting checks, distinct from Lean kernel
verification. The axiom audit covers a selected set of declarations; the
source audit and library build cover the complete development.
