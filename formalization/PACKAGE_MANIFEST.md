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
| `UniformRandomMALA/Concrete/C1MainTheorem.lean` | First-order analytic endpoints and original constant convention |
| `UniformRandomMALA/Concrete/PaperNormalizedGap.lean` | Current main theorem and all three gap-corollary bounds |
| `UniformRandomMALA/Concrete/PaperNormalizedMixing.lean` | Current mixing-time corollary and explicit tuning dependence |
| `UniformRandomMALA/Concrete/PaperAsymptoticVariance.lean` | Actual stationary variance limits and bounds for randomized MALA |
| `UniformRandomMALA/Concrete/PaperCentralLimit.lean` | Nonlazy and half-lazy CLTs for measurable L² observables from every initial distribution |
| `UniformRandomMALA/Concrete/PaperNonstationaryMSE.lean` | Both nonstationary mean-square error bounds of Corollary 2.8 |
| `UniformRandomMALA/Concrete/StationaryPath*.lean`, `StationaryVariance*.lean` | Finite-path moments, centered kernel operator, Poisson equation, and stationary variance limits |
| `UniformRandomMALA/Concrete/KernelLp*.lean`, `L2DensityEvolution.lean` | Actual Lp kernel integration, L²/L⁴ contraction, and Radon–Nikodym density evolution |
| `UniformRandomMALA/Concrete/NonstationaryMSE*.lean` | Actual sample-average MSE, pair bounds, and covariance summation |
| `UniformRandomMALA/Concrete/VarianceSeparation*.lean` | Extended variance, observable witnesses, and both assertions of the variance comparison |
| `UniformRandomMALA/Concrete/MarkovInfinite*.lean`, `MarkovFiniteExtension.lean` | Actual infinite trajectory kernel, finite-prefix correspondence, time shifts, conditional expectations, and initial-law domination |
| `UniformRandomMALA/Concrete/MartingaleCLT*.lean`, `MarkovErgodic*.lean` | Proved triangular martingale CLT and the L¹ ergodic estimates used to discharge its hypotheses |
| `UniformRandomMALA/Concrete/MarkovCLT*.lean`, `MarkovBounded*.lean`, `MarkovGaussianCLT.lean` | Poisson boundary, normalized rows, Gaussian convergence, and bounded-density, absolutely continuous, and arbitrary-start transfer |
| `UniformRandomMALA/Concrete/SmallFixedStepGap.lean` | Fixed-step lower bound and its dimension endpoint |
| `UniformRandomMALA/Concrete/NonconvexPotential.lean`, `NonconvexGradientMoments.lean` | Nonconvex Boltzmann interface and proved Gaussian-convolution gradient moments |
| `UniformRandomMALA/Concrete/NonconvexGradientMGF.lean`, `NonconvexMALA.lean` | Subcritical gradient moments and actual reversible MALA in the nonconvex setting |
| `UniformRandomMALA/Nonconvex/` | Full Proposition B.1 through finite likelihoods, Lipschitz Euler/RWM comparison, weak limits, and real-moment interpolation |
| `UniformRandomMALA/Concrete/FractionalAggregation.lean` | General fractional aggregation lemma and component-aggregation theorem, independently reusable from MALA |
| `UniformRandomMALA/Concrete/TunedSpectralGap.lean`, `MixingTime.lean` | Compatibility constant convention, mixing-time definition, and general ceiling arguments |
| `UniformRandomMALA/Concrete/L2Mixing*.lean`, `L2DensityTV.lean`, `PositiveContraction.lean` | Proved gap-to-TV connection for the actual iterated half-lazy kernel |
| `UniformRandomMALA/Concrete/MixingTimeArithmetic.lean`, `TargetGapRange.lean` | Logarithm/ceiling estimates and the concrete finite-gap range |
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
