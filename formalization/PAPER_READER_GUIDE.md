# A reader's guide to the Lean formalization

This package develops Lean proofs of the [paper](paper/main.pdf)
and the supporting mathematics needed to prove them. Completed results include the
randomized MALA spectral-gap and mixing-time bounds, the fixed-step
obstruction, the small-step fixed-MALA gap, and the general aggregation
lemma and theorem. It also proves the central limit theorem from every
initial distribution, the stationary variance limit and bounds, the
variance comparison, the nonstationary MSE bounds, and the full nonconvex
stationary-rejection theorem. The explicit exclusions are Lemmas B.2–B.5;
see [coverage status](FORMALIZATION_STATUS.md) and the separate
[verification evidence](BUILD_STATUS.md).

The guide answers two questions: **do the Lean statements describe the
paper's mathematics, and do their proofs reach the stated assumptions?**
You can check the first by comparing statements and definitions, and the
second by following the proof dependencies and running Lean.

## 1. Choose a reading route

| Your purpose | Suggested route |
|---|---|
| Get an overview | Read the [package README](README.md), then the main results below. |
| Review a particular paper statement | Find its number in [THEOREM_MAP.md](THEOREM_MAP.md), open the linked declaration, and compare its assumptions and conclusion. |
| Check that the algorithms and quantities agree | Use the [definition map](#3-compare-definitions-with-the-paper), starting with the target and transition kernels. |
| Check that the formalization is end-to-end | Follow the [proof paths](#4-follow-the-complete-proofs), then inspect the build and dependency evidence. |
| Reuse a theorem or contribute | Start with [REUSABLE_RESULTS.md](REUSABLE_RESULTS.md) and the [package manifest](PACKAGE_MANIFEST.md). |

Most paper-facing results are in `UniformRandomMALA/Concrete/`.
`DiscreteTime/` supplies probability and finite-chain arguments used by
those proofs. The public import
[AllResults.lean](UniformRandomMALA/AllResults.lean) exposes the completed
results; you do not need to read the source files in directory order.

In the tables below, abbreviated names are relative to
`UniformRandomMALA.Concrete`, unless stated otherwise; grouped names share
the namespace of the first name. A Lean `def` introduces
a mathematical object; a `theorem` or `lemma` states a proved result.
Read each declaration's inputs as its assumptions, then compare its
conclusion with the paper.

## 2. Find the paper's results

### Main results

| Paper result | Where to start |
|---|---|
| Theorem 2.1: randomized-step spectral-gap bound and exact half-lazy gap | [PaperNormalizedGap.lean](UniformRandomMALA/Concrete/PaperNormalizedGap.lean): `C1Potential.exists_universal_normalizedMasterRHS_bounds` |
| Corollary 2.2: all three dimension-dependent gap bounds | [PaperNormalizedGap.lean](UniformRandomMALA/Concrete/PaperNormalizedGap.lean): `C1Potential.normalizedSquareRootCorollary_rayleighSpectralGap_lower`, `normalizedSimplifiedCorollary_rayleighSpectralGap_lower`, and `normalizedTunedCorollary_rayleighSpectralGap_lower` |
| Proposition 2.3: fixed-step minimax obstruction | [FixedStepMinimax.lean](UniformRandomMALA/Concrete/FixedStepMinimax.lean): `exists_universal_fixedStepMinimaxGap_paper_upper` |
| Corollary 2.5: mixing time of half-lazy randomized MALA | [PaperNormalizedMixing.lean](UniformRandomMALA/Concrete/PaperNormalizedMixing.lean): `C1Potential.normalizedMixingTimeCorollary` |
| Proposition G.1 and Remark 2.4: small-step fixed-MALA gap | [SmallFixedStepGap.lean](UniformRandomMALA/Concrete/SmallFixedStepGap.lean): `C1Potential.exists_universal_smallFixedStep_gap_constant` |
| Corollary 2.6: actual stationary variance limits and bounds | [PaperAsymptoticVariance.lean](UniformRandomMALA/Concrete/PaperAsymptoticVariance.lean): `C1Potential.stationaryAsymptoticVariance_nonlazy_bounds` and `stationaryAsymptoticVariance_lazy_bounds` |
| Corollary 2.7: randomized versus fixed-step variance comparison | [VarianceSeparationCorollary.lean](UniformRandomMALA/Concrete/VarianceSeparationCorollary.lean): `exists_universal_varianceSeparation_randomized_upper`; [VarianceSeparationFixedStep.lean](UniformRandomMALA/Concrete/VarianceSeparationFixedStep.lean): `exists_universal_fixedStep_variance_separation` |
| Corollary 2.8: nonstationary finite-sample mean-square error | [PaperNonstationaryMSE.lean](UniformRandomMALA/Concrete/PaperNonstationaryMSE.lean): `C1Potential.nonstationaryMSE_corollary` |
| Proposition B.1: rejection moments under the nonconvex appendix assumptions | [StationaryRejection.lean](UniformRandomMALA/Nonconvex/StationaryRejection.lean): `NonconvexPotential.exists_universal_stationary_rejection_moments` |
| Corollary 2.6: central limit theorem, including every initial distribution | [PaperCentralLimit.lean](UniformRandomMALA/Concrete/PaperCentralLimit.lean): `C1Potential.central_limit_nonlazy` and `central_limit_lazy` |

The randomized MALA results start from `C1Potential` in
[C1ToFirstOrder.lean](UniformRandomMALA/Concrete/C1ToFirstOrder.lean).
This record expresses the paper's continuously differentiable, strongly
convex potential with Lipschitz gradient. Its adapter uses the actual
gradient of that potential and proves the upper Taylor bound needed by
the internal development. For the fixed-step obstruction,
[FixedStepMinimax.lean](UniformRandomMALA/Concrete/FixedStepMinimax.lean)
specifies the smooth potential class, using the Hessian-bounded record in
[HessianToFirstOrder.lean](UniformRandomMALA/Concrete/HessianToFirstOrder.lean).

For the mixing corollary, the initial distribution has the paper's
absolute-continuity and square-integrable density assumptions. The theorem
proves both ceiling bounds with `normalizedMixingConstant c`, a universal
multiple of `max c (1/c)`. The universal coefficient is chosen before the
tuning parameter, dimension, target, initial law, and accuracy.

[THEOREM_MAP.md](THEOREM_MAP.md) gives the full index, including the
Section 3 ingredients and appendix results. Use it for exact declaration
names and scope details without working through every proof file.

### Aggregation: Lemma 3.5 and Theorem 3.6

Both results are formalized in
[FractionalAggregation.lean](UniformRandomMALA/Concrete/FractionalAggregation.lean)
as general theorems for finite families of Markov kernels. They can be
used independently of MALA.

| Paper result | Declarations |
|---|---|
| Lemma 3.5: fractional aggregation | `fractionalAggregation_poincareLower` and `fractionalAggregation_le_spectralGap` |
| Theorem 3.6: component aggregation | `hardAssignmentAggregation_poincareLower` and `hardAssignmentAggregation_le_spectralGap` |

Compare the energy-domination and flow hypotheses with the paper. The
component theorem follows from the fractional lemma by choosing its weights.
The file contains both the general statements and their proofs; all four
declarations are exported by `AllResults` and included in the dependency
audit. Their internal gap formulation connects to the paper's Rayleigh gap
through `spectralGap_le_rayleighSpectralGap`.

## 3. Compare definitions with the paper

A compiled theorem proves a statement about its Lean definitions. To check
that it concerns the intended algorithm, start with those definitions.
For a public input `V : C1Potential d`, the kernels are constructed from
`W := V.toFirstOrderPotential`; most kernel definitions below belong to
`FirstOrderPotential` and take this `W` as an argument.

### Target and algorithm

| What to compare | Definitions and files |
|---|---|
| Euclidean state space and normalized target distribution | `State`, `target`, and `targetDensity` in [EuclideanTarget.lean](UniformRandomMALA/Concrete/EuclideanTarget.lean) |
| Gaussian proposal and its gradient drift | `proposalMean`, `proposalMap`, and `gaussianProposal` in [GaussianProposal.lean](UniformRandomMALA/Concrete/GaussianProposal.lean) |
| Acceptance rule and the stay-put transition on rejection | `malaAcceptance` and `malaKernel` in [MALA.lean](UniformRandomMALA/Concrete/MALA.lean), using [MetropolisHastings.lean](UniformRandomMALA/Concrete/MetropolisHastings.lean) |
| Uniformly randomized step and dyadic component kernels | `uniformStepMeasure`, `uniformMALA`, and `dyadicMALA` in [MALAFamily.lean](UniformRandomMALA/Concrete/MALAFamily.lean) |
| Averaging transition kernels | `UniformRandomMALA.Kernel.parameterMixture` in [KernelMixture.lean](UniformRandomMALA/KernelMixture.lean) |
| Half-lazy randomized chain | `halfLazyKernel` and `FirstOrderPotential.lazyUniformMALA` in [LazyKernel.lean](UniformRandomMALA/Concrete/LazyKernel.lean) |

[GaussianLawBridge.lean](UniformRandomMALA/DiscreteTime/GaussianLawBridge.lean)
proves that the sampling construction of the proposal equals its density
construction. `uniformMALA` then averages the Metropolis-corrected kernels,
representing a fresh step-size draw at each transition. These connections
are useful places to check that the definitions describe the paper's algorithm.

### Quantities in the statements

| What to compare | Definitions and files |
|---|---|
| Dirichlet form | `UniformRandomMALA.Dirichlet.energy` in [KernelMixture.lean](UniformRandomMALA/KernelMixture.lean) |
| Rayleigh spectral gap and admissible test functions | `L2RayleighTest`, `rayleighQuotient`, and `rayleighSpectralGap` in [RayleighSpectralGap.lean](UniformRandomMALA/Concrete/RayleighSpectralGap.lean) |
| Total variation | `UniformRandomMALA.setwiseTV` in [SetwiseTV.lean](UniformRandomMALA/Concrete/SetwiseTV.lean) |
| Mixing time, density discrepancy, and logarithmic factor | `mixingTime` in [MixingTime.lean](UniformRandomMALA/Concrete/MixingTime.lean), `centeredDensityL2Norm` in [L2DensityTV.lean](UniformRandomMALA/Concrete/L2DensityTV.lean), and `mixingLog` in [MixingTimeArithmetic.lean](UniformRandomMALA/Concrete/MixingTimeArithmetic.lean) |
| Moment threshold, gap expressions, and tuned endpoint | `C1Potential.normalizedMomentThreshold`, `normalizedMasterRHS`, `normalizedTunedStep`, and `normalizedTunedGapRHS` in [PaperNormalizedGap.lean](UniformRandomMALA/Concrete/PaperNormalizedGap.lean) |
| Actual finite Markov paths and sample mean | `finiteMarkovPathLaw` and `finiteMarkovSampleMean` in [NonstationaryMSEPath.lean](UniformRandomMALA/Concrete/NonstationaryMSEPath.lean); coordinate laws are proved in [StationaryPath.lean](UniformRandomMALA/Concrete/StationaryPath.lean) |
| Infinite Markov trajectory and its relation to finite samples | `infiniteMarkovPathLaw` in [MarkovInfinitePath.lean](UniformRandomMALA/Concrete/MarkovInfinitePath.lean); `infiniteMarkovPathLaw_map_prefix` in [MarkovInfinitePrefix.lean](UniformRandomMALA/Concrete/MarkovInfinitePrefix.lean) proves that each prefix has the finite Markov law |
| CLT normalization and Gaussian law | `normalizedMarkovSum` in [MarkovCLTBoundary.lean](UniformRandomMALA/Concrete/MarkovCLTBoundary.lean), applied to `f - π(f)`; `TendstoInDistribution` and `gaussianReal` in the [paper-facing CLT](UniformRandomMALA/Concrete/PaperCentralLimit.lean) |
| Nonstationary mean-square error | `finiteMarkovMSE` in [NonstationaryMSEPath.lean](UniformRandomMALA/Concrete/NonstationaryMSEPath.lean), the integral of the squared centered sample mean under the actual path law |
| Asymptotic variance | `scaledMarkovSampleVariance` in [StationaryVarianceLimit.lean](UniformRandomMALA/Concrete/StationaryVarianceLimit.lean); `stationaryAsymptoticVariance` and its proved limit specification in [StationaryVarianceGeneral.lean](UniformRandomMALA/Concrete/StationaryVarianceGeneral.lean) |
| Extended asymptotic variance, allowing infinity | `asymptoticVarianceExtended` and its proved convergence in [VarianceSeparationExtended.lean](UniformRandomMALA/Concrete/VarianceSeparationExtended.lean); it agrees with the real variance when the gap is positive |
| Optimization over potentials and fixed steps | `smoothHessianPotentialGapValues`, `fixedStepWorstPotentialGap`, and `fixedStepMinimaxGap` in [FixedStepMinimax.lean](UniformRandomMALA/Concrete/FixedStepMinimax.lean) |
| Stationary flow and rejection quantities used in the proof | `flow` and `boundaryFlow` in [Conductance.lean](UniformRandomMALA/Concrete/Conductance.lean); [MALARejectionGoodSet.lean](UniformRandomMALA/Concrete/MALARejectionGoodSet.lean) and [RejectionMomentsOne.lean](UniformRandomMALA/Concrete/RejectionMomentsOne.lean) |

Some internal proofs express the gap as a Poincaré inequality. The
[Rayleigh gap module](UniformRandomMALA/Concrete/RayleighSpectralGap.lean)
proves the transfer and equivalence results used to return to the paper's
convention. The mixing-time definition uses the actual iterated transition
kernel and includes time zero. Finite sample means use the observations
`X₀,…,Xₙ₋₁` and divide by `n`; `finiteMarkovMSE` integrates the squared error
under their actual joint law. The CLT uses the same centered sum divided by
`√n`, and its Gaussian variance is the proved stationary scaled-variance
limit. These are useful normalization and indexing checks when comparing
the statements with the paper.

## 4. Follow the complete proofs

Start at the public theorem and follow the results it invokes. In
particular, check where each analytic input is proved. The main MALA
endpoints construct the target and kernels and establish rejection,
isoperimetry, and convergence bounds internally from their stated inputs.

### Randomized spectral gap

| Proof stage | Files to follow |
|---|---|
| Translate the paper's assumptions | [C1ToFirstOrder.lean](UniformRandomMALA/Concrete/C1ToFirstOrder.lean) supplies the internal potential and its derived bounds. |
| Obtain rejection estimates and local overlap | [MALAFullPathAssembly.lean](UniformRandomMALA/Concrete/MALAFullPathAssembly.lean), [MALAOverlapBounds.lean](UniformRandomMALA/Concrete/MALAOverlapBounds.lean), and [RejectionMomentsOne.lean](UniformRandomMALA/Concrete/RejectionMomentsOne.lean) connect the finite-chain estimates to the MALA kernel. |
| Prove target isoperimetry | [GaussianRampCanonicalInterpolation.lean](UniformRandomMALA/Concrete/GaussianRampCanonicalInterpolation.lean): `UniformRandomMALA.DiscreteTime.target_bakryLedoux` completes the Gaussian, finite-Euler, and weak-limit argument. |
| Build component flow estimates and aggregate them | [AllParameterMALAFlow.lean](UniformRandomMALA/Concrete/AllParameterMALAFlow.lean), [LadderComponents.lean](UniformRandomMALA/Concrete/LadderComponents.lean), and [ComponentAggregationFinal.lean](UniformRandomMALA/Concrete/ComponentAggregationFinal.lean) assemble local bounds into a global estimate. |
| Supply the proved inputs and return to the paper's statement | `FirstOrderPotential.universal_masterRHS_spectralGap_lower` in [GaussianRampCanonicalInterpolation.lean](UniformRandomMALA/Concrete/GaussianRampCanonicalInterpolation.lean) supplies isoperimetry; [C1MainTheorem.lean](UniformRandomMALA/Concrete/C1MainTheorem.lean) supplies the first-order interface; [PaperNormalizedGap.lean](UniformRandomMALA/Concrete/PaperNormalizedGap.lean) proves the current normalization and all three corollary bounds. |

Conditional interfaces, such as theorems ending in `_of_bakryLedoux`, are
reusable intermediate results. To verify the complete argument, continue
to the public theorem that supplies their hypotheses with proved results.
[PROOF_STRATEGY_LEDGER.md](PROOF_STRATEGY_LEDGER.md) expands this proof path.

### Mixing time and fixed-step obstruction

For mixing, [KernelLpContraction.lean](UniformRandomMALA/Concrete/KernelLpContraction.lean)
derives full `L²` contraction from positivity and the reversible kernel's
gap. [L2DensityEvolution.lean](UniformRandomMALA/Concrete/L2DensityEvolution.lean)
identifies the actual evolved Radon–Nikodym density and proves both the
density and total-variation inequalities. Half-lazy positivity is proved
internally. The earlier bounded-observable argument remains available in
`L2Mixing.lean` and `L2MixingTV.lean`.
[MixingTime.lean](UniformRandomMALA/Concrete/MixingTime.lean) supplies the
ceiling argument; [PaperNormalizedMixing.lean](UniformRandomMALA/Concrete/PaperNormalizedMixing.lean)
combines it with the current gap corollary and its tuning dependence.

For the fixed-step obstruction, follow the explicit smooth witness in
[FixedStepHardPotential.lean](UniformRandomMALA/Concrete/FixedStepHardPotential.lean),
its gap bound in
[FixedStepHardPotentialObstruction.lean](UniformRandomMALA/Concrete/FixedStepHardPotentialObstruction.lean),
and its use in the minimax optimization in
[FixedStepMinimax.lean](UniformRandomMALA/Concrete/FixedStepMinimax.lean).

For the small-step fixed-MALA lower bound, follow
[SmallFixedStepGap.lean](UniformRandomMALA/Concrete/SmallFixedStepGap.lean).
It applies the proved acceptance and proposal-overlap estimates to the
fixed-step kernel, obtains a conductance bound from separated sets, and
uses the aggregation theorem with one component.

### Sample averages and variance

For stationary asymptotic variance, start at
[PaperAsymptoticVariance.lean](UniformRandomMALA/Concrete/PaperAsymptoticVariance.lean).
[StationaryVarianceGeneral.lean](UniformRandomMALA/Concrete/StationaryVarianceGeneral.lean)
proves convergence of the scaled variance of the actual sample mean.
The proof uses the centered kernel operator and a Poisson equation;
[StationaryPathMoments.lean](UniformRandomMALA/Concrete/StationaryPathMoments.lean)
connects the operator expressions to finite-path expectations.

For the variance comparison, follow
[VarianceSeparationFixedStep.lean](UniformRandomMALA/Concrete/VarianceSeparationFixedStep.lean)
from the fixed-step gap obstruction to an actual observable with large
variance. The Rayleigh, covariance, and extended-limit modules supply the
witness and cover the zero-gap case. The randomized upper bound uses the
same extended variance definition.

For nonstationary MSE, start at
[PaperNonstationaryMSE.lean](UniformRandomMALA/Concrete/PaperNonstationaryMSE.lean).
[NonstationaryMSE.lean](UniformRandomMALA/Concrete/NonstationaryMSE.lean)
assembles the general kernel theorem from density evolution, proved L⁴
contraction, path-coordinate moments, and a finite covariance sum. The
paper-facing theorem supplies the randomized MALA gap internally. Compare
the initial-law assumptions and sample indices with the paper, then follow
the norm and path-law definitions if reviewing the expectation itself.

### Central limit theorem and arbitrary initial laws

Start at [PaperCentralLimit.lean](UniformRandomMALA/Concrete/PaperCentralLimit.lean).
Its nonlazy and half-lazy theorems take the actual randomized MALA kernel,
an arbitrary initial probability measure, and a measurable `L²(π)` observable.
There is no initial-density or initial-moment assumption. The limiting
Gaussian uses the same `stationaryAsymptoticVariance` as the variance bounds.

| Proof stage | Files to follow |
|---|---|
| Construct the chain and identify its observations | [MarkovInfinitePath.lean](UniformRandomMALA/Concrete/MarkovInfinitePath.lean), [MarkovInfinitePrefix.lean](UniformRandomMALA/Concrete/MarkovInfinitePrefix.lean), and [MarkovInfiniteInitial.lean](UniformRandomMALA/Concrete/MarkovInfiniteInitial.lean) construct the trajectory kernel, prove finite-prefix laws, and prove the law after a time shift. |
| Construct actual martingale increments | [MarkovInfiniteMartingale.lean](UniformRandomMALA/Concrete/MarkovInfiniteMartingale.lean) proves conditional expectation identities for the Poisson increments, using the trajectory's natural filtration. |
| Discharge the limit theorem's hypotheses | [MarkovInfiniteRow.lean](UniformRandomMALA/Concrete/MarkovInfiniteRow.lean) proves the expected Lindeberg-tail limit; [MarkovInfiniteCLTInputs.lean](UniformRandomMALA/Concrete/MarkovInfiniteCLTInputs.lean) proves conditional-variance convergence from the `L¹` ergodic theorem. |
| Obtain a Gaussian limit for sample sums | [MartingaleCLTLimit.lean](UniformRandomMALA/Concrete/MartingaleCLTLimit.lean) proves the general martingale characteristic-function limit. [MarkovGaussianCLT.lean](UniformRandomMALA/Concrete/MarkovGaussianCLT.lean) applies it and removes the Poisson boundary; [MarkovCLTDistribution.lean](UniformRandomMALA/Concrete/MarkovCLTDistribution.lean) converts it to convergence in distribution. |
| Allow every initial distribution | [MarkovCLTAbsolutelyContinuous.lean](UniformRandomMALA/Concrete/MarkovCLTAbsolutelyContinuous.lean) removes the bounded-density restriction. [MarkovCLTArbitraryStart.lean](UniformRandomMALA/Concrete/MarkovCLTArbitraryStart.lean) uses acceptance, a vanishing rejection remainder, the actual shifted path law, and a negligible finite prefix. The paper wrapper proves the required acceptance facts for MALA. |

The generic martingale theorem has explicit Lindeberg and variance
hypotheses. Following these connections verifies that they are proved for
the chain rather than left as assumptions of the paper corollary.

### Scope and proof differences

The package uses independent proofs for two analytic ingredients:
Gaussian interpolation and finite-Euler weak limits for isoperimetry, and
a discrete-time argument for rejection. Lemmas B.2–B.5 are excluded from
the requested scope. The full nonconvex Proposition B.1 is proved in
`Nonconvex/StationaryRejection.lean`. Start with `NonconvexPotential.lean`
for its assumptions and `NonconvexMALA.lean` for the actual proposal,
acceptance, and rejection definitions. The `Nonconvex/` proof modules
reuse the generic finite Gaussian and weak-limit arguments with the
weaker drift stability and target-moment estimates.

The requested coverage is complete outside the explicit B.2–B.5 exclusions.
[FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) describes that coverage;
[TRUST_BOUNDARY.md](TRUST_BOUNDARY.md) distinguishes mathematical inputs,
proof dependencies, and manuscript correspondence.

## 5. Verify and reuse the package

Run the commands in the [README](README.md#reproduce-the-verification).
The full gate builds the library, checks the public import, and audits the
axioms used by the declarations selected in
[DependencyAudit.lean](UniformRandomMALA/DependencyAudit.lean), including
the main results and both aggregation theorems.
[BUILD_STATUS.md](BUILD_STATUS.md) records the results and links the evidence.

For a focused inspection, save this example under `tmp/Review.lean` in the
package directory and run `lake env lean tmp/Review.lean` after building:

```lean
import UniformRandomMALA.AllResults

open UniformRandomMALA.Concrete

#print C1Potential
#check C1Potential.exists_universal_normalizedMasterRHS_bounds
#check C1Potential.normalizedTunedCorollary_rayleighSpectralGap_lower
#check exists_universal_fixedStepMinimaxGap_paper_upper
#check C1Potential.normalizedMixingTimeCorollary
#check C1Potential.exists_universal_smallFixedStep_gap_constant
#check C1Potential.central_limit_nonlazy
#check C1Potential.central_limit_lazy
#check C1Potential.nonstationaryMSE_corollary
#check exists_universal_fixedStep_variance_separation
#check NonconvexPotential.exists_universal_stationary_rejection_moments
#check fractionalAggregation_le_spectralGap
#check hardAssignmentAggregation_le_spectralGap
#print axioms C1Potential.exists_universal_normalizedMasterRHS_bounds
#print axioms C1Potential.normalizedMixingTimeCorollary
#print axioms C1Potential.exists_universal_smallFixedStep_gap_constant
#print axioms C1Potential.central_limit_nonlazy
#print axioms C1Potential.central_limit_lazy
#print axioms C1Potential.nonstationaryMSE_corollary
#print axioms NonconvexPotential.exists_universal_stationary_rejection_moments
#print axioms fractionalAggregation_le_spectralGap
#print axioms hardAssignmentAggregation_le_spectralGap
```

`#check` displays a statement, `#print` shows a definition or declaration,
and `#print axioms` reports its logical dependencies. The package permits
only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.
Reading the assumptions and definitions remains necessary: the axiom list
alone does not establish correspondence with the paper.

For reuse, import `UniformRandomMALA.AllResults` or the narrower module
listed in [REUSABLE_RESULTS.md](REUSABLE_RESULTS.md). For package layout and
maintenance, see [PACKAGE_MANIFEST.md](PACKAGE_MANIFEST.md) and
[REPOSITORY_UPDATE.md](REPOSITORY_UPDATE.md). Records under
`validation/historical/` describe earlier snapshots.
