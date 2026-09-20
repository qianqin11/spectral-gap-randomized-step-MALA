# Verification evidence

Validation date: **2026-09-19**. The development uses pinned Lean 4.33.0 and
mathlib 4.33.0. The full verification gate completed successfully, including
the new tuned spectral-gap bound and mixing-time corollary.

| Check | Result |
|---|---|
| Lean source audit | Passed: 165 files; 2,161 top-level declarations counted by source regex; no placeholders |
| First-order interface and imports | Passed; acyclic local imports; mathlib is the sole direct external Lean library |
| Manuscript source | Passed: 110 labels, 257 reference uses, 132 citation-key uses, 65 bibliography entries, three figures |
| Lean manuscript references | Passed: 134 label uses and 90 numbered theorem/label pairs |
| Manuscript regression tests | Passed: 21 tests for missing/changed assets and invalid references |
| Numerical sanity checks | Passed: 2,000 deterministic trials |
| Lean build | Passed: `Build completed successfully (3976 jobs).` |
| Public import | `lake env lean UniformRandomMALA/AllResults.lean` passed |
| Axiom dependencies | All 281 selected declarations passed; only `propext`, `Classical.choice`, and `Quot.sound` |
| Theorem-map declarations | All 56 named declarations compile through `AllResults` |
| Documentation links | 242 local links and 17 Markdown anchors resolve across 18 documents |
| LaTeX build | Passed: 48 pages; no unresolved references or citations; no overfull boxes |
| Source/PDF correspondence | Supplied and rebuilt PDFs have equal normalized extracted text on all 48 pages |

## New proof scope

[TunedSpectralGap.lean](UniformRandomMALA/Concrete/TunedSpectralGap.lean)
proves the new third display of Corollary 2.2 from the existing master bound.
[MixingTime.lean](UniformRandomMALA/Concrete/MixingTime.lean) proves both
ceiling inequalities in Corollary 2.4 for the actual half-lazy kernel,
using the proved initial-density, reversible contraction, and TV estimates.
The initial law has precisely the probability, absolute-continuity, and
square-integrable density assumptions in the manuscript.

For arbitrary positive tuning, the second ceiling has explicit prefactor
`C(c) = 2/[c₀ min{c,b₀²/(2c)}]`. A separate theorem fixes a universal tuning
and proves a universal prefactor. This qualifies the manuscript's use of
“universal” with arbitrary `c`; see the
[reader guide](PAPER_READER_GUIDE.md#tuned-gap-and-mixing-time-corollaries).
The manuscript files were preserved as supplied. Existing aggregation
endpoints remain exported and included in the dependency audit.

## Manuscript and theorem references

`paper/` contains `main.tex`, `main.pdf`, `uniform_random_mala.bib`, and the
three figure PDFs. The supplied PDF checksum is recorded in
[manuscript-pdf.sha256](validation/manuscript-pdf.sha256).
All 20 theorem-level labels agree with the fresh LaTeX build. The unlabeled
Mills-ratio lemma is identified by its equation labels, giving 21 theorem
environments covered by [THEOREM_MAP.md](THEOREM_MAP.md).

A separate TeX Live 2025 build produced the same page count and normalized
extracted text as the supplied PDF. Text equality does not assert byte or
pixel equality. Seven bibliography underfull-box warnings and eight duplicate
PDF-destination warnings remain; they do not affect Lean verification.
Details and the limited visual inspection are recorded in
[manuscript-build.txt](validation/manuscript-build.txt).

## Reproduction and records

Run `lake exe cache get`, then `scripts/check.ps1` on Windows or
`bash scripts/check.sh` on Linux/macOS. The gate checks source, manuscript
references, regression tests, numerics, the full Lean build, the public
import, and the actual axiom output. LaTeX is a separate check; typesetting
instructions are in [README.md](README.md).

- [CHECK_OUTPUT.txt](CHECK_OUTPUT.txt): compact gate summary.
- [Manuscript audit](validation/manuscript-audit.txt): source and reference checks.
- [Reference audit](validation/lean-reference-audit.txt): concordance details.
- [Manuscript build](validation/manuscript-build.txt): typesetting and PDF comparison.
- [Compiled labels](validation/manuscript-labels.json): label numbers and page locations.

Full local logs are `validation/local/mixing-corollary-gate.log` and
`validation/local/axioms.log`; generated files are excluded from distribution.
Earlier records under `validation/historical/` document their own snapshots.
Static and numerical audits are supporting checks, distinct from Lean kernel
verification. The axiom audit covers a selected set of declarations; the
source audit and library build cover the complete development.
