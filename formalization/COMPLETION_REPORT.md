# Completion report

Formalization-completion record: **2026-08-30**

Documentation/PDF synchronization: **2026-09-05**; no new Lean build.

This report covers the Lean 4 package accompanying Qian Qin's
*A global spectral gap for Metropolis-adjusted Langevin algorithm
with a uniformly randomized step size*. The current
canonical manuscript is the author-supplied `paper/main.pdf`, synchronized
on 2026-09-05. The `paper/` directory contains only that PDF.

The outcomes and build/axiom checks below are retained historical records of
the 2026-08-30 formalization, not fresh verification results. The
2026-09-05 revision only synchronizes documentation with the time-reversal
proof and replaces the paper materials; it leaves all Lean sources and build
inputs unchanged. The new checks are in `DOCUMENTATION_UPDATE_2026-09-05.md`.

## Outcome

All five requested formalization milestones are complete.  The public results
are kernel-checked with Lean 4.33.0 and mathlib 4.33.0.  The project contains
no `sorry`, `admit`, or project-specific axiom declaration.

The recommended reviewer import is:

```lean
import UniformRandomMALA.AllResults
```

## Paper results and exact Lean declarations

All names below are in the namespace `UniformRandomMALA`.

| Manuscript result | Principal Lean declaration | File |
|---|---|---|
| Actual-Hessian calculus bridge | `Concrete.HessianBoundedPotential.toFirstOrderPotential` | `UniformRandomMALA/Concrete/HessianToFirstOrder.lean` |
| Lower and upper line-Taylor inequalities | `Concrete.HessianBoundedPotential.lowerTaylor`, `Concrete.HessianBoundedPotential.upperTaylor` | `UniformRandomMALA/Concrete/HessianToFirstOrder.lean` |
| Lipschitz Riesz gradient from the Hessian bounds | `Concrete.HessianBoundedPotential.gradient_lipschitz` | `UniformRandomMALA/Concrete/HessianToFirstOrder.lean` |
| Poincaré/Rayleigh equivalence at the manuscript's `L²` scope | `Concrete.l2PoincareLower_iff_le_rayleighSpectralGap`, `Concrete.l2SpectralGap_eq_rayleighSpectralGap` | `UniformRandomMALA/Concrete/RayleighSpectralGap.lean` |
| Theorem 2.1, exact non-lazy paper form | `Concrete.exists_universal_nonlazy_paperMasterRHS_lower` | `UniformRandomMALA/Concrete/HessianMainTheorem.lean` |
| Concrete half-lazy MALA kernel | `Concrete.FirstOrderPotential.lazyUniformMALA` | `UniformRandomMALA/Concrete/LazyKernel.lean` |
| Exact half-energy and half-gap identities | `Concrete.Dirichlet.energy_halfLazyKernel`, `Concrete.rayleighSpectralGap_halfLazyKernel` | `UniformRandomMALA/Concrete/LazyKernel.lean` |
| Theorem 2.1, exact lazy paper form | `Concrete.exists_universal_lazy_paperMasterRHS_lower` | `UniformRandomMALA/Concrete/LazyKernel.lean` |
| Corollary 2.2, first displayed inequality | `Concrete.HessianBoundedPotential.sqrtDimensionCorollary_rayleighSpectralGap_lower` | `UniformRandomMALA/Concrete/SqrtDimensionCorollary.lean` |
| Corollary 2.2, simplified displayed inequality | `Concrete.HessianBoundedPotential.sqrtDimensionCorollarySimplified_rayleighSpectralGap_lower` | `UniformRandomMALA/Concrete/SqrtDimensionCorollary.lean` |
| Assumption-free scalar simplification used in Corollary 2.2 | `Concrete.Parameters.min_sqrtDimensionDenominator_le_two_pStar` | `UniformRandomMALA/Concrete/SqrtDimensionCorollary.lean` |
| Lemma 3.5, fractional finite-component aggregation | `Concrete.fractionalAggregation_poincareLower`, `Concrete.fractionalAggregation_le_spectralGap` | `UniformRandomMALA/Concrete/FractionalAggregation.lean` |
| Weighted Cauchy--Schwarz input | `Concrete.fractional_weighted_sqrt_sum_le` | `UniformRandomMALA/Concrete/FractionalAggregation.lean` |
| Hard-assignment aggregation corollary | `Concrete.hardAssignmentAggregation_poincareLower`, `Concrete.hardAssignmentAggregation_le_spectralGap` | `UniformRandomMALA/Concrete/FractionalAggregation.lean` |
| Proposition 3.4, local arbitrary-parameter clause | `Concrete.FirstOrderPotential.local_dyadicMALA_boundaryFlow_allParameters` | `UniformRandomMALA/Concrete/AllParameterMALAFlow.lean` |
| Proposition 3.4, safe small-step clause | `Concrete.FirstOrderPotential.safe_dyadicMALA_boundaryFlow_allParameters` | `UniformRandomMALA/Concrete/AllParameterMALAFlow.lean` |
| Proposition 3.4, two-clause package | `Concrete.FirstOrderPotential.allParameterMALAFlowBounds` | `UniformRandomMALA/Concrete/AllParameterMALAFlow.lean` |
| Generic Rayleigh-test and cut upper bounds | `Concrete.rayleighSpectralGap_le_energy_div_evariance`, `Concrete.rayleighSpectralGap_le_boundaryFlow_div_cutVariance` | `UniformRandomMALA/Concrete/SpectralGapUpperBounds.lean` |
| Explicit `C∞` hard potential and actual Hessian bounds | `Concrete.contDiff_infty_fixedStepHardPotential`, `Concrete.fixedStepHardPotential_hessian_lower`, `Concrete.fixedStepHardPotential_hessian_upper` | `UniformRandomMALA/Concrete/FixedStepHardPotential.lean` |
| Fixed-step local obstruction | `Concrete.fixedStepHardMALA_rayleighSpectralGap_le_local` | `UniformRandomMALA/Concrete/HardPotentialLocalObstruction.lean` |
| Exact hard-potential log-ratio estimate | `Concrete.hard_malaLogRatio_zero_le_shape_sum` | `UniformRandomMALA/Concrete/HardPotentialLogRatio.lean` |
| Gaussian trigonometric identities | `Concrete.integral_cos_gaussianReal_zero_two`, `Concrete.integral_mul_sin_gaussianReal_zero_two` | `UniformRandomMALA/Concrete/GaussianTrigonometricConcentration.lean` |
| Negative-threshold finite-product Chernoff estimate | `Concrete.exists_universal_contraction_factor_for_pi_scaledGaussian_tail` | `UniformRandomMALA/Concrete/HardPotentialShiftedConcentration.lean` |
| Continuity of the pointwise MALA acceptance probability | `Concrete.FirstOrderPotential.continuous_malaAcceptanceProfile` | `UniformRandomMALA/Concrete/StickyRegionCut.lean` |
| Positive target-mass sticky-ball cut bound | `Concrete.FirstOrderPotential.exists_target_ball_rayleighSpectralGap_le_two_mul` | `UniformRandomMALA/Concrete/StickyRegionCut.lean` |
| Fixed-step sticky obstruction | `Concrete.exists_universal_fixedStepHard_sticky_rayleighSpectralGap_upper` | `UniformRandomMALA/Concrete/HardPotentialStickyObstruction.lean` |
| Generic two-branch hard-potential obstruction | `Concrete.exists_universal_fixedStepHardPotential_obstruction_allDimensions` | `UniformRandomMALA/Concrete/FixedStepHardPotentialObstruction.lean` |
| Scalar fixed-step envelope optimization | `Concrete.iSup_fixedStepTwoBranchEnvelope_le_log_max_exp` | `UniformRandomMALA/Concrete/FixedStepObstructionOptimization.lean` |
| Exact `C∞` potential class, fixed-step infimum, and minimax supremum | `Concrete.smoothHessianPotentialGapValues`, `Concrete.fixedStepWorstPotentialGap`, `Concrete.fixedStepMinimaxGap` | `UniformRandomMALA/Concrete/FixedStepMinimax.lean` |
| Proposition 2.3, explicit pre-absorption bound | `Concrete.exists_universal_fixedStepMinimaxGap_explicit_upper` | `UniformRandomMALA/Concrete/FixedStepMinimax.lean` |
| Proposition 2.3, paper form with universal `c` and `C=C(κ₀)` | `Concrete.exists_universal_fixedStepMinimaxGap_paper_upper` | `UniformRandomMALA/Concrete/FixedStepMinimax.lean` |

The unconditional target Bakry--Ledoux input remains available as
`DiscreteTime.target_bakryLedoux`.  Its proof uses finite Gaussian Euler
images and weak-limit stability.  It does not assume an isoperimetric
certificate.

## Reusable additions

- A coordinate-free finite-dimensional bridge from an actual `ContDiff ℝ 2`
  Hessian bound to strong-convexity Taylor inequalities and an
  `L`-Lipschitz Riesz gradient.
- An extended-valued `L²` Rayleigh spectral gap and exact equivalence with the
  corresponding Poincaré lower-bound supremum, including zero variance,
  infinite energy, and empty-test-family cases.
- Fair lazification for arbitrary Markov kernels, preserving reversibility
  and exactly halving energy, Rayleigh quotients, and the Rayleigh gap.
- Fractional finite-component aggregation for arbitrary finite reversible
  kernel families with the manuscript's `L²` energy-domination premise.
- Spectral-gap upper bounds from arbitrary admissible tests and measurable
  indicator cuts, with exact indicator variance/flow identities.
- A dominated-convergence continuity theorem for proposal-averaged MALA
  acceptance and a general positive-mass sticky-ball cut construction.
- Exact Gaussian trigonometric moments and direct fixed-parameter MGF/Chernoff
  bounds for finite independent products.
- Complete-lattice definitions and scalar optimization tools for
  supremum--infimum fixed-step obstruction statements.

## New Lean modules

The following content-named modules were added relative to the attached
checkpoint:

```text
UniformRandomMALA/Concrete/HessianToFirstOrder.lean
UniformRandomMALA/Concrete/RayleighSpectralGap.lean
UniformRandomMALA/Concrete/HessianMainTheorem.lean
UniformRandomMALA/Concrete/LazyKernel.lean
UniformRandomMALA/Concrete/SqrtDimensionCorollary.lean
UniformRandomMALA/Concrete/FractionalAggregation.lean
UniformRandomMALA/Concrete/AllParameterMALAFlow.lean
UniformRandomMALA/Concrete/SpectralGapUpperBounds.lean
UniformRandomMALA/Concrete/FixedStepHardPotential.lean
UniformRandomMALA/Concrete/HardPotentialLogRatio.lean
UniformRandomMALA/Concrete/GaussianTrigonometricConcentration.lean
UniformRandomMALA/Concrete/HardPotentialShiftedConcentration.lean
UniformRandomMALA/Concrete/StickyRegionCut.lean
UniformRandomMALA/Concrete/HardPotentialLocalObstruction.lean
UniformRandomMALA/Concrete/HardPotentialStickyObstruction.lean
UniformRandomMALA/Concrete/FixedStepHardPotentialObstruction.lean
UniformRandomMALA/Concrete/FixedStepObstructionOptimization.lean
UniformRandomMALA/Concrete/FixedStepMinimax.lean
```

Public import and audit surfaces changed in
`UniformRandomMALA.lean`, `UniformRandomMALA/AllResults.lean`, and
`UniformRandomMALA/DependencyAudit.lean`.  Reader documentation changed in
`README.md`, `FORMALIZATION_STATUS.md`, `REUSABLE_RESULTS.md`,
`PAPER_READER_GUIDE.md`, `THEOREM_MAP.md`, `PROOF_STRATEGY_LEDGER.md`,
`TRUST_BOUNDARY.md`, `BUILD_STATUS.md`, and `WORKLOG.md`.  The Lean
verification section of `paper/main.tex` was synchronized with the checked
results.  The bibliography remains the canonical attached bibliography.

At the 2026-08-30 checkpoint, the unique Davies companion note was retained
under `paper/legacy/` as background. In the 2026-09-05 distribution, that
legacy directory and all manuscript source/bibliography files have been
removed: `paper/` now contains only the author-supplied PDF. The historical
source-synchronization and compilation statements in this report do not
describe files included in the current distribution.

## Verification recorded on 2026-08-30

Pinned tools:

```text
Lean 4.33.0, commit d8b18978322de05a8f3dba51ef03cf5461676c17
Lake 5.0.0
mathlib v4.33.0
```

The complete project audit was run from the package root with the bundled
Python runtime on `PATH`:

```powershell
$env:ELAN_HOME='C:\Users\qianq\.elan'
powershell -ExecutionPolicy Bypass -File scripts\check.ps1
```

Result:

```text
STATIC AUDIT PASSED
NUMERIC SANITY PASSED (2,000 deterministic trials)
Build completed successfully (3435 jobs).
UniformRandomMALA/AllResults.lean elaborated successfully.
UniformRandomMALA/DependencyAudit.lean elaborated successfully.
```

The static audit counted 151 Lean files and 2,036 declarations and found no
placeholder or project axiom.

## Axiom audit

`UniformRandomMALA/DependencyAudit.lean` contains `#print axioms` commands for
the principal endpoints, including all five milestones and the final
fixed-step minimax result.  Every new principal endpoint reports exactly the
ordinary Lean/mathlib logical dependencies:

```text
[propext, Classical.choice, Quot.sound]
```

In particular this was checked for:

```text
Concrete.exists_universal_nonlazy_paperMasterRHS_lower
Concrete.exists_universal_lazy_paperMasterRHS_lower
Concrete.HessianBoundedPotential.sqrtDimensionCorollarySimplified_rayleighSpectralGap_lower
Concrete.fractionalAggregation_poincareLower
Concrete.FirstOrderPotential.allParameterMALAFlowBounds
Concrete.exists_universal_fixedStepHardPotential_obstruction_allDimensions
Concrete.exists_universal_fixedStepMinimaxGap_explicit_upper
Concrete.exists_universal_fixedStepMinimaxGap_paper_upper
```

No new axiom is introduced by any of them.

## Historical manuscript audit (2026-08-30)

This section concerns the earlier manuscript, not the 46-page PDF supplied
for the 2026-09-05 update. The new PDF was copied without alteration and was
not recompiled; no LaTeX-source or bibliography audit is claimed for it.

The earlier manuscript and bibliography were compiled with:

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

Result: success, including BibTeX; `paper/main.pdf` has 43 pages.  The final
LaTeX log had no undefined citation, undefined reference, or multiply-defined
label warning.  A separate source audit found 96 active labels, no duplicate
active label, no undefined `\ref`/`\eqref`/`\cref`, and no unreferenced
equation label.

## Remaining omissions and blockers

There is no remaining omission among the requested Milestones 1--5 and no
mathematical, library, or engineering blocker to the stated completion
criteria.

The package deliberately does **not** claim a line-by-line formalization of
the manuscript's continuous-time SDE derivation in Appendix B.  It proves the
same stationary-rejection and overlap conclusions by the already documented
finite discrete-time Gaussian/Euler/RWM argument.  This is a proof-route
difference, not an unproved hypothesis of any endpoint above.

The package also keeps its older all-measurable-function spectral-gap API for
compatibility.  The exact equality proved for the manuscript is between the
new `L²` Poincaré gap and `rayleighSpectralGap`; no unnecessary abstract
equality with the older, stronger-scope definition is asserted.
