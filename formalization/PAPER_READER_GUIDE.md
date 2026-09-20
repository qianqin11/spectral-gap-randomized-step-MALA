# A reader's guide to the Lean formalization

This package formalizes the principal results of the [paper](paper/main.pdf)
and the supporting mathematics needed to prove them. It includes the
randomized MALA spectral-gap and mixing-time bounds, the fixed-step
obstruction, and the general aggregation lemma and theorem.

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
| Theorem 2.1: randomized-step spectral-gap bound, including the half-lazy chain | [C1MainTheorem.lean](UniformRandomMALA/Concrete/C1MainTheorem.lean): `C1Potential.exists_universal_paperMasterRHS_bounds` |
| Corollary 2.2: dimension-dependent gap bounds | [C1MainTheorem.lean](UniformRandomMALA/Concrete/C1MainTheorem.lean): `C1Potential.sqrtDimensionCorollary_rayleighSpectralGap_lower` and `sqrtDimensionCorollarySimplified_rayleighSpectralGap_lower`; [TunedSpectralGap.lean](UniformRandomMALA/Concrete/TunedSpectralGap.lean): `C1Potential.tunedSqrtDimensionCorollary_rayleighSpectralGap_lower` |
| Proposition 2.3: fixed-step minimax obstruction | [FixedStepMinimax.lean](UniformRandomMALA/Concrete/FixedStepMinimax.lean): `exists_universal_fixedStepMinimaxGap_paper_upper` |
| Corollary 2.4: mixing time of half-lazy randomized MALA | [MixingTime.lean](UniformRandomMALA/Concrete/MixingTime.lean): `C1Potential.mixingTimeCorollary` |

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
proves both ceiling bounds with `paperMixingConstant c`, which depends only
on the tuning parameter `c`, as stated in the manuscript. The additional
`C1Potential.exists_universal_mixingTimeCorollary` specializes to a fixed
universal tuning.

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
| Moment threshold, gap expressions, and tuned endpoint | `C1Potential.paperMomentThreshold` and `paperMasterRHS` in [C1MainTheorem.lean](UniformRandomMALA/Concrete/C1MainTheorem.lean); `paperTunedStep` and `paperTunedGapRHS` in [TunedSpectralGap.lean](UniformRandomMALA/Concrete/TunedSpectralGap.lean) |
| Optimization over potentials and fixed steps | `smoothHessianPotentialGapValues`, `fixedStepWorstPotentialGap`, and `fixedStepMinimaxGap` in [FixedStepMinimax.lean](UniformRandomMALA/Concrete/FixedStepMinimax.lean) |
| Stationary flow and rejection quantities used in the proof | `flow` and `boundaryFlow` in [Conductance.lean](UniformRandomMALA/Concrete/Conductance.lean); [MALARejectionGoodSet.lean](UniformRandomMALA/Concrete/MALARejectionGoodSet.lean) and [RejectionMomentsOne.lean](UniformRandomMALA/Concrete/RejectionMomentsOne.lean) |

Some internal proofs express the gap as a Poincaré inequality. The
[Rayleigh gap module](UniformRandomMALA/Concrete/RayleighSpectralGap.lean)
proves the transfer and equivalence results used to return to the paper's
convention. The mixing-time definition uses the actual iterated transition
kernel and includes time zero.

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
| Supply the proved inputs and return to the paper's statement | `FirstOrderPotential.universal_masterRHS_spectralGap_lower` in [GaussianRampCanonicalInterpolation.lean](UniformRandomMALA/Concrete/GaussianRampCanonicalInterpolation.lean) supplies isoperimetry; [C1MainTheorem.lean](UniformRandomMALA/Concrete/C1MainTheorem.lean) provides the public result and [TunedSpectralGap.lean](UniformRandomMALA/Concrete/TunedSpectralGap.lean) its tuned specialization. |

Conditional interfaces, such as theorems ending in `_of_bakryLedoux`, are
reusable intermediate results. To verify the complete argument, continue
to the public theorem that supplies their hypotheses with proved results.
[PROOF_STRATEGY_LEDGER.md](PROOF_STRATEGY_LEDGER.md) expands this proof path.

### Mixing time and fixed-step obstruction

For mixing, [L2Mixing.lean](UniformRandomMALA/Concrete/L2Mixing.lean) derives
contraction from the reversible half-lazy kernel's gap.
[L2MixingTV.lean](UniformRandomMALA/Concrete/L2MixingTV.lean) connects it to
total variation for the actual kernel iterates and the initial density.
[MixingTime.lean](UniformRandomMALA/Concrete/MixingTime.lean) combines that
estimate with the gap corollary to obtain the paper's mixing-time bound.

For the fixed-step obstruction, follow the explicit smooth witness in
[FixedStepHardPotential.lean](UniformRandomMALA/Concrete/FixedStepHardPotential.lean),
its gap bound in
[FixedStepHardPotentialObstruction.lean](UniformRandomMALA/Concrete/FixedStepHardPotentialObstruction.lean),
and its use in the minimax optimization in
[FixedStepMinimax.lean](UniformRandomMALA/Concrete/FixedStepMinimax.lean).

### Scope and proof differences

The package uses independent proofs for two analytic ingredients:
Gaussian interpolation and finite-Euler weak limits for isoperimetry, and
a discrete-time argument for rejection. Appendix B's continuous-time
lemmas and additional nonconvex generalization are outside the formalized
scope. The strongly convex rejection result needed by the main theorem is
proved internally. [FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) and
[TRUST_BOUNDARY.md](TRUST_BOUNDARY.md) explain these boundaries.

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
#check C1Potential.exists_universal_paperMasterRHS_bounds
#check C1Potential.tunedSqrtDimensionCorollary_rayleighSpectralGap_lower
#check exists_universal_fixedStepMinimaxGap_paper_upper
#check C1Potential.mixingTimeCorollary
#check fractionalAggregation_le_spectralGap
#check hardAssignmentAggregation_le_spectralGap
#print axioms C1Potential.exists_universal_paperMasterRHS_bounds
#print axioms C1Potential.mixingTimeCorollary
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
