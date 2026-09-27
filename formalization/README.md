# Uniform-random MALA: Lean verification

This package accompanies Qian Qin's *A spectral gap for
Metropolis-adjusted Langevin algorithm with a uniformly randomized step size*.
It contains Lean proofs, definitions of the
algorithms and quantities they concern, and reusable results about Markov
kernels. The [paper PDF](paper/main.pdf), [LaTeX source](paper/main.tex),
bibliography, and figures are included.

## What is formalized

| Part of the paper | Main source files |
|---|---|
| Randomized-step spectral-gap bound and its corollary: Theorem 2.1 and Corollary 2.2 | [PaperNormalizedGap.lean](UniformRandomMALA/Concrete/PaperNormalizedGap.lean) |
| Fixed-step minimax obstruction: Proposition 2.3 | [FixedStepMinimax.lean](UniformRandomMALA/Concrete/FixedStepMinimax.lean) |
| Mixing-time bound: Corollary 2.5 | [PaperNormalizedMixing.lean](UniformRandomMALA/Concrete/PaperNormalizedMixing.lean) |
| Central limit theorem from every initial distribution, with stationary variance limits and bounds: Corollary 2.6 | [PaperCentralLimit.lean](UniformRandomMALA/Concrete/PaperCentralLimit.lean), [PaperAsymptoticVariance.lean](UniformRandomMALA/Concrete/PaperAsymptoticVariance.lean) |
| Randomized versus fixed-step variance comparison: Corollary 2.7 | [VarianceSeparationCorollary.lean](UniformRandomMALA/Concrete/VarianceSeparationCorollary.lean) |
| Nonstationary mean-square error: Corollary 2.8 | [PaperNonstationaryMSE.lean](UniformRandomMALA/Concrete/PaperNonstationaryMSE.lean) |
| Small-step fixed-MALA gap: Proposition G.1 and Remark 2.4 | [SmallFixedStepGap.lean](UniformRandomMALA/Concrete/SmallFixedStepGap.lean) |
| Fractional aggregation lemma and component-aggregation theorem: Lemma 3.5 and Theorem 3.6 | [FractionalAggregation.lean](UniformRandomMALA/Concrete/FractionalAggregation.lean) |
| Stationary rejection under the nonconvex appendix assumptions: Proposition B.1 | [StationaryRejection.lean](UniformRandomMALA/Nonconvex/StationaryRejection.lean) |

To check a result, start at its public declaration in the table, compare
the definitions in the reader guide, then follow the linked proof path.
The MALA proofs start from the paper's assumptions on the potential. The
target distribution, transition kernels, rejection and isoperimetric
estimates, and final gap and mixing bounds are constructed or proved within
the development. The general aggregation results are also formalized under
their stated energy and flow hypotheses and can be reused independently of
MALA.

The [theorem map](THEOREM_MAP.md) covers the supporting results and their
scope. All results in the requested scope have formalized endpoints.
The explicit exclusions are Lemmas B.2–B.5: their continuous-time route is
bypassed by the proved finite-chain rejection argument.
[FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) describes the mathematical
coverage; [BUILD_STATUS.md](BUILD_STATUS.md) records the separate package
verification result.

## Where to start

The [paper reader guide](PAPER_READER_GUIDE.md) provides a structured route
through the whole package: locate a result, compare the algorithm and
quantity definitions, follow the complete proof, and check its dependencies.
It is the best starting point for readers reviewing the formalization
alongside the paper.

| Your task | Documentation |
|---|---|
| Understand the package and its reading routes | [PAPER_READER_GUIDE.md](PAPER_READER_GUIDE.md) |
| Find a paper statement in Lean | [THEOREM_MAP.md](THEOREM_MAP.md) |
| Understand the proof architecture | [PROOF_STRATEGY_LEDGER.md](PROOF_STRATEGY_LEDGER.md) |
| Check assumptions, scope, and logical dependencies | [TRUST_BOUNDARY.md](TRUST_BOUNDARY.md) |
| Reuse general mathematics | [REUSABLE_RESULTS.md](REUSABLE_RESULTS.md) |
| Inspect verification results | [BUILD_STATUS.md](BUILD_STATUS.md) |

The public import is:

```lean
import UniformRandomMALA.AllResults
```

## Package layout

| Location | Contents |
|---|---|
| `UniformRandomMALA/Concrete/` | Target and MALA definitions, public statements, and their proofs |
| `UniformRandomMALA/DiscreteTime/` | Probability and finite-chain arguments supporting the analysis |
| `UniformRandomMALA/Nonconvex/` | Rejection proof under the weaker appendix assumptions, reusing the finite-chain foundations |
| Other `UniformRandomMALA/` modules | General kernel, energy, arithmetic, and assembly results |
| `paper/` | Manuscript source, PDF, bibliography, and figures |
| `scripts/` | Reproducible build and audit commands |
| `validation/` | Verification summaries and checksums; earlier records are under `historical/` |

[PACKAGE_MANIFEST.md](PACKAGE_MANIFEST.md) gives a fuller file index.
The companion [simulation package](../simulation/README.md) is maintained
separately from the Lean development.

## Reproduce the verification

Install Git, Python 3, and `elan`. The Lean and mathlib versions are pinned
by `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`. Run from the
`formalization/` directory. On Windows:

```powershell
lake exe cache get
if ($LASTEXITCODE -ne 0) { throw 'Cache retrieval failed.' }
powershell -ExecutionPolicy Bypass -File .\scripts\check.ps1
```

On Linux or macOS:

```bash
lake exe cache get
bash scripts/check.sh
```

The gate builds the library, checks the public import, and audits the actual
logical dependencies of selected results, including the main theorems and
aggregation results. It also checks source imports, manuscript references,
and supporting numerical and regression tests. Success ends with:

```text
FULL SOURCE BUILD AND AXIOM AUDIT PASSED
```

[BUILD_STATUS.md](BUILD_STATUS.md) links the verification evidence.
Compilation checks the formal proofs; correspondence with the paper also
requires reading the statements and definitions. The reader guide explains
how to carry out both checks.

For maintenance instructions, see [REPOSITORY_UPDATE.md](REPOSITORY_UPDATE.md).
Generated caches and logs live in `.lake/`, `tmp/`, and `validation/local/`
and are excluded from the distributed package.

To typeset the manuscript, run
`latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex` from `paper/`
with a LaTeX distribution installed. Typesetting is separate from the Lean
verification gate; its evidence is linked from `BUILD_STATUS.md`.
