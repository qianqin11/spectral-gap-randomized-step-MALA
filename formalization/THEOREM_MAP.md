# Paper-to-Lean theorem map

This map connects the statements in [the manuscript](paper/main.pdf) to their
Lean declarations. Stable labels refer to [the LaTeX source](paper/main.tex);
the displayed numbers agree with the supplied manuscript. The `paper/`
directory contains the PDF, TeX source, bibliography, and figures used by
the source.

Start with [the reader guide](PAPER_READER_GUIDE.md) to compare assumptions,
algorithm and quantity definitions, and the complete proof route. Its
[definition map](PAPER_READER_GUIDE.md#3-compare-definitions-with-the-paper)
locates the target, proposal, acceptance rule, mixtures, energy, gap, and
rejection quantities used by the statements below. See
[the build status](BUILD_STATUS.md) for verification evidence. The public
import is `UniformRandomMALA.AllResults`. Unless a namespace is written in
full below, declaration names have the prefix `UniformRandomMALA.Concrete.`.

## Main results

| Manuscript statement and TeX label | Lean declaration | Source |
|---|---|---|
| Theorem 2.1 (`thm:main`), non-lazy bound `eq:master-gap` | `C1Potential.normalized_masterRHS_rayleighSpectralGap_lower` | [PaperNormalizedGap.lean](UniformRandomMALA/Concrete/PaperNormalizedGap.lean) |
| Theorem 2.1 (`thm:main`), lazy clause | `FirstOrderPotential.rayleighSpectralGap_lazyUniformMALA` (exact halving) | [LazyKernel.lean](UniformRandomMALA/Concrete/LazyKernel.lean) |
| Theorem 2.1 (`thm:main`), both clauses with the same universal constants | `C1Potential.exists_universal_normalizedMasterRHS_bounds` | [PaperNormalizedGap.lean](UniformRandomMALA/Concrete/PaperNormalizedGap.lean) |
| Corollary 2.2 (`cor:sqrt-d-endpoint`), first display | `C1Potential.normalizedSquareRootCorollary_rayleighSpectralGap_lower` | [PaperNormalizedGap.lean](UniformRandomMALA/Concrete/PaperNormalizedGap.lean) |
| Corollary 2.2 (`cor:sqrt-d-endpoint`), simplified display | `C1Potential.normalizedSimplifiedCorollary_rayleighSpectralGap_lower` | [PaperNormalizedGap.lean](UniformRandomMALA/Concrete/PaperNormalizedGap.lean) |
| Corollary 2.2 (`cor:sqrt-d-endpoint`), tuned third display | `C1Potential.normalizedTunedCorollary_rayleighSpectralGap_lower` | [PaperNormalizedGap.lean](UniformRandomMALA/Concrete/PaperNormalizedGap.lean) |
| Proposition 2.3 (`prop:minimax-fixed-step-ceiling`), fixed-step minimax upper bound | `exists_universal_fixedStepMinimaxGap_paper_upper` | [FixedStepMinimax.lean](UniformRandomMALA/Concrete/FixedStepMinimax.lean) |
| Corollary 2.5 (`cor:mixing`), both ceiling bounds with explicit tuning dependence | `C1Potential.normalizedMixingTimeCorollary` | [PaperNormalizedMixing.lean](UniformRandomMALA/Concrete/PaperNormalizedMixing.lean) |
| Corollary 2.5, universal coefficient before all tuning parameters | `C1Potential.exists_universal_normalizedMixingTimeCorollary` | [PaperNormalizedMixing.lean](UniformRandomMALA/Concrete/PaperNormalizedMixing.lean) |
| Both density and TV inequalities `eq:TVbound`, for positive or half-lazy reversible kernels | `densityTV_iterate_of_positive_actualGap`; `densityTV_iterate_halfLazy_actualGap` | [L2DensityEvolution.lean](UniformRandomMALA/Concrete/L2DensityEvolution.lean) |
| `eq:TVbound` for the actual randomized MALA law | `C1Potential.densityTVConvergence` | [PaperDensityConvergence.lean](UniformRandomMALA/Concrete/PaperDensityConvergence.lean) |
| Remark 2.4 (`rem:minimax-fixed-step-ceiling`), fixed-step lower bound | `C1Potential.dimensionStep_rayleighSpectralGap_lower` | [SmallFixedStepGap.lean](UniformRandomMALA/Concrete/SmallFixedStepGap.lean) |
| Corollary 2.6 (`cor:asymptotic-variance`), actual variance limits and bounds | `C1Potential.stationaryAsymptoticVariance_nonlazy_bounds`; `C1Potential.stationaryAsymptoticVariance_lazy_bounds` | [PaperAsymptoticVariance.lean](UniformRandomMALA/Concrete/PaperAsymptoticVariance.lean) |
| Corollary 2.6, nonlazy and half-lazy CLT from every initial distribution | `C1Potential.central_limit_nonlazy`; `C1Potential.central_limit_lazy` | [PaperCentralLimit.lean](UniformRandomMALA/Concrete/PaperCentralLimit.lean) |
| Corollary 2.7 (`cor:variance-separation`), both variance-comparison assertions | `exists_universal_varianceSeparation_randomized_upper`; `exists_universal_fixedStep_variance_separation` | [VarianceSeparationCorollary.lean](UniformRandomMALA/Concrete/VarianceSeparationCorollary.lean), [VarianceSeparationFixedStep.lean](UniformRandomMALA/Concrete/VarianceSeparationFixedStep.lean) |
| Corollary 2.8 (`cor:nonstationary-variance`), both mean-square error bounds | `C1Potential.nonstationaryMSE_corollary`; `C1Potential.nonstationaryMSE_actualGap_bound` | [PaperNonstationaryMSE.lean](UniformRandomMALA/Concrete/PaperNonstationaryMSE.lean) |

The main theorem chooses its universal constants before the dimension,
potential, and endpoint. The definitions `C1Potential.normalizedMomentThreshold`
and `C1Potential.normalizedMasterRHS` spell out `p⋆` and the right-hand side of
`eq:master-gap`.

The first two gap-corollary declarations use `H = c/(L√d)`. The simplified
bound does not require `p⋆ ≤ d`; the third substitutes `c/√p⋆`, yielding
the endpoint `H = c/(L√(d p⋆))` used by the mixing corollary.

For arbitrary positive `c`, `normalizedMixingConstant c` is exactly a
universal positive coefficient multiplied by `max c (1/c)`. The normalized
threshold is `1 + log d + log (L/m)`, as in the current manuscript. Older
constant conventions remain available in internal and compatibility APIs.
The [definition map in the reader guide](PAPER_READER_GUIDE.md#3-compare-definitions-with-the-paper)
locates the initial-density norm, logarithm, kernel iterates, and mixing-time
definition and explains the proved spectral-gap-to-TV connection.

The fixed-step upper bound ranges over the smooth,
Hessian-bounded class specified in Proposition 2.3; this smoothness requirement
belongs to the obstruction result, not to the lower bound in Theorem 2.1.
The definitions `smoothHessianPotentialGapValues`,
`fixedStepWorstPotentialGap`, and `fixedStepMinimaxGap` at the start of
[FixedStepMinimax.lean](UniformRandomMALA/Concrete/FixedStepMinimax.lean)
specify that class and the order of the infimum and supremum.

The CLT wrappers allow every initial probability distribution and every
measurable `L²(π)` observable. Their actual trajectory law is
`infiniteMarkovPathLaw`, their normalized sum is `normalizedMarkovSum`, and
their Gaussian variance is `stationaryAsymptoticVariance`. The variance
bounds use this same proved limit. The MSE theorem instead assumes the
paper's `L²` initial density and `L⁴` observable and integrates the squared
error under `finiteMarkovPathLaw`; the [definition map](PAPER_READER_GUIDE.md#3-compare-definitions-with-the-paper)
locates these objects.

## Assumptions and spectral-gap convention

| Manuscript object | Lean declaration | Source |
|---|---|---|
| `C¹` potential with first-order strong convexity and a Lipschitz gradient, `eq:first-order-assumptions` | `C1Potential` | [C1ToFirstOrder.lean](UniformRandomMALA/Concrete/C1ToFirstOrder.lean) |
| Descent inequality derived from those assumptions | `C1Potential.upperTaylor` | [C1ToFirstOrder.lean](UniformRandomMALA/Concrete/C1ToFirstOrder.lean) |
| Adapter whose gradient field is the actual gradient of `U` | `C1Potential.toFirstOrderPotential` | [C1ToFirstOrder.lean](UniformRandomMALA/Concrete/C1ToFirstOrder.lean) |
| Admissible `L²` test, Rayleigh quotient, and right spectral gap | `L2RayleighTest`; `rayleighQuotient`; `rayleighSpectralGap` | [RayleighSpectralGap.lean](UniformRandomMALA/Concrete/RayleighSpectralGap.lean) |
| Equivalence with the `L²` Poincaré formulation | `l2PoincareLower_iff_le_rayleighSpectralGap`; `l2SpectralGap_eq_rayleighSpectralGap` | [RayleighSpectralGap.lean](UniformRandomMALA/Concrete/RayleighSpectralGap.lean) |
| Transfer from the internal all-measurable Poincaré gap | `spectralGap_le_rayleighSpectralGap` | [RayleighSpectralGap.lean](UniformRandomMALA/Concrete/RayleighSpectralGap.lean) |

The public main theorem uses the manuscript's `L²` Rayleigh gap. Some
intermediate results prove a stronger Poincaré inequality for all measurable
functions. Their lower bounds transfer to the manuscript's gap through
`spectralGap_le_rayleighSpectralGap`; the definitions are not silently identified.

## Ingredients in Section 3

| Manuscript statement and TeX label | Lean declaration | Source |
|---|---|---|
| Lemma 3.1 (`lem:Kt`), disjoint-component energy comparison | `UniformRandomMALA.Dirichlet.sum_energy_parameterMixture_restrict_le` | [KernelMixture.lean](UniformRandomMALA/KernelMixture.lean) |
| Lemma 3.1 (`lem:Kt`), dyadic restrictions and ladder instance | `FirstOrderPotential.energy_restricted_uniformStep_eq_weight_dyadic`; `FirstOrderPotential.ladder_energy_domination` | [Ladder.lean](UniformRandomMALA/Concrete/Ladder.lean) |
| Proposition 3.2 (`prop:overlap`), both overlap bounds, every real `p ≥ 1` | `C1Potential.mala_overlap_bounds` | [C1MainTheorem.lean](UniformRandomMALA/Concrete/C1MainTheorem.lean) |
| Proposition 3.3 (`prop:separated`), separated-set bound `eq:separated` | `C1Potential.separatedSets` | [C1MainTheorem.lean](UniformRandomMALA/Concrete/C1MainTheorem.lean) |
| Proposition 3.4 (`prop:flow`), local and globally safe flow | `C1Potential.allParameterMALAFlowBounds`, with conclusion `FirstOrderPotential.AllParameterMALAFlowBounds` | [C1MainTheorem.lean](UniformRandomMALA/Concrete/C1MainTheorem.lean); [AllParameterMALAFlow.lean](UniformRandomMALA/Concrete/AllParameterMALAFlow.lean) |
| Lemma 3.5 (`lem:fractional`), fractional aggregation | `fractionalAggregation_poincareLower`; `fractionalAggregation_le_spectralGap` | [FractionalAggregation.lean](UniformRandomMALA/Concrete/FractionalAggregation.lean) |
| Theorem 3.6 (`thm:aggregation`), hard-assignment aggregation | `hardAssignmentAggregation_poincareLower`; `hardAssignmentAggregation_le_spectralGap` | [FractionalAggregation.lean](UniformRandomMALA/Concrete/FractionalAggregation.lean) |

Proposition 3.2 is exported with constants `1/(32e)` and `12288e³`. Its
internal `p ≥ 2` proof uses `1/(16e)` and `6144e³`; the range `1 ≤ p ≤ 2`
follows by second-moment interpolation in
[MomentInterpolation.lean](UniformRandomMALA/DiscreteTime/MomentInterpolation.lean)
and [RejectionMomentsOne.lean](UniformRandomMALA/Concrete/RejectionMomentsOne.lean).
Proposition 3.4 uses the same chosen `A₀,b₀` as the main theorem and covers
every admissible moment and multiplier, beyond the finite ladder instances.

Lemma 3.5 and Theorem 3.6 are formalized as general results for finite
families of Markov kernels, independently of the MALA application. The
aggregation declarations use precisely the manuscript's `L²`
energy-domination premise. Their conclusions use the stronger internal
Poincaré gap; the transfer theorem above gives the Rayleigh-gap inequalities.
Both the Poincaré and spectral-gap forms are exported by `AllResults` and
selected in `DependencyAudit`. The
[aggregation reader guide](PAPER_READER_GUIDE.md#aggregation-lemma-35-and-theorem-36)
compares the flow hypotheses, cost formulas, and the specialization from
the fractional lemma to the component-aggregation theorem.

## Appendix results and proof correspondence

| Manuscript statement and TeX label | Formalization and scope | Source |
|---|---|---|
| Proposition A.1 (`prop:generic-fixed-step-obstruction`), potential `eq:generic-hard-potential` and curvature `eq:generic-hard-curvature` | `fixedStepHardPotential`; `contDiff_infty_fixedStepHardPotential`; `fixedStepHardPotential_hessian_lower`; `fixedStepHardPotential_hessian_upper` | [FixedStepHardPotential.lean](UniformRandomMALA/Concrete/FixedStepHardPotential.lean) |
| Proposition A.1 (`prop:generic-fixed-step-obstruction`), bound `eq:generic-fixed-step-gap-upper` | `exists_universal_fixedStepHardPotential_obstruction_allDimensions`, for the same witness and every `d ≥ 2` | [FixedStepHardPotentialObstruction.lean](UniformRandomMALA/Concrete/FixedStepHardPotentialObstruction.lean) |
| Proposition A.1, condition-number form `eq:generic-fixed-step-gap-upper-kappa` | The same obstruction composed with `hardObstructionScalar_le_twoBranchEnvelope` | [FixedStepMinimax.lean](UniformRandomMALA/Concrete/FixedStepMinimax.lean) |
| Proposition B.1 (`prop:stationary-rejection`), estimate `eq:stationary-rejection` | `NonconvexPotential.exists_universal_stationary_rejection_moments`, every real `p ≥ 1` under the full nonconvex appendix assumptions | [StationaryRejection.lean](UniformRandomMALA/Nonconvex/StationaryRejection.lean) |
| Lemma B.2 (`lem:linear-increment`) and Lemma B.3 (`lem:integrated-increments`) | Explicitly excluded; their continuous-time statements are not formalized. Finite Gaussian maximal and Euler-energy estimates supply the corresponding inputs to the discrete proof. | [GaussianMaximum.lean](UniformRandomMALA/DiscreteTime/GaussianMaximum.lean); [FiniteEulerEnergyMGF.lean](UniformRandomMALA/Concrete/FiniteEulerEnergyMGF.lean) |
| Lemma B.4 (`lem:frozen-endpoint-law`) | Explicitly excluded; the continuous frozen-drift path statement is bypassed by finite Gaussian change-of-measure and endpoint-law identities. | [FiniteGaussianLikelihood.lean](UniformRandomMALA/DiscreteTime/FiniteGaussianLikelihood.lean); [FiniteGaussianEndpointLaw.lean](UniformRandomMALA/DiscreteTime/FiniteGaussianEndpointLaw.lean) |
| Lemma B.5 (`lem:path-likelihood`) | Explicitly excluded; the continuous likelihood-moment statement is bypassed by finite-product likelihood bounds followed by a weak-limit argument. | [FiniteEulerRealMoments.lean](UniformRandomMALA/Concrete/FiniteEulerRealMoments.lean); [MALAFullPathAssembly.lean](UniformRandomMALA/Concrete/MALAFullPathAssembly.lean) |
| Lemma C.1, Mills bounds `eq:mills-two-sided` and log-tail bound `eq:log-tail-simple` | `mills_lower`; `mills_upper`; `log_one_div_normalTailReal_le` | [GaussianMills.lean](UniformRandomMALA/Concrete/GaussianMills.lean); [StandardGaussianShift.lean](UniformRandomMALA/Concrete/StandardGaussianShift.lean) |
| Lemma C.2 (`lem:gaussian-shift`) | `standardGaussianShift` | [StandardGaussianShift.lean](UniformRandomMALA/Concrete/StandardGaussianShift.lean) |
| Lemma D.1 (`lem:defective`), defective conductance | `defectiveConductance_of_separatedSets` | [DefectiveConductance.lean](UniformRandomMALA/Concrete/DefectiveConductance.lean) |
| Lemma D.2 (`lem:exceptional-budget`), exceptional-set arithmetic and universal parameters | `UniformRandomMALA.exceptional_budget_unsaturated`; `UniformRandomMALA.exceptional_budget_endpoint_of_log_condition`; `FirstOrderPotential.concreteA0_exceptional_choice` | [ExceptionalBudgetArithmetic.lean](UniformRandomMALA/ExceptionalBudgetArithmetic.lean); [UniversalConstants.lean](UniformRandomMALA/Concrete/UniversalConstants.lean) |
| Lemma F.1 (`lem:ladder-sum`), harmonic sum for the chosen universal parameters | `ladderHarmonicReal_le`; `ladder_harmonicCost_le` | [LadderComponents.lean](UniformRandomMALA/Concrete/LadderComponents.lean) |
| Proposition G.1 (`prop:small-fixed-step-gap`), small-step fixed-MALA bound and dimension endpoint | `C1Potential.exists_universal_smallFixedStep_gap_constant` | [SmallFixedStepGap.lean](UniformRandomMALA/Concrete/SmallFixedStepGap.lean) |

Lemma C.1 has no theorem-level `\label` in the source. Its two equation
labels identify it unambiguously; `lem:gaussian-shift` belongs to Lemma C.2.
Appendix E (`app:fractional`) proves Lemma 3.5 and introduces no additional
numbered theorem. The final overlap argument is in Appendix B.4, within
`app:rejection-overlap`; Lemma B.4 is a different reference.

Proposition B.1 is proved under the full nonconvex assumptions. The interface
`NonconvexPotential` records a continuously differentiable potential, a
Lipschitz actual gradient, and an integrable Boltzmann weight. The final
theorem supplies every analytic input internally. It uses the gradient
moment theorem, finite Gaussian likelihoods, Euler/RWM comparison, and weak
limits in place of the excluded continuous-time Lemmas B.2–B.5. The earlier
strongly convex rejection theorem remains available for the main proof.

## Isoperimetry, the ladder, and lazification

| Manuscript role or label | Lean declaration | Source |
|---|---|---|
| Target enlargement `eq:bakry-ledoux-enlargement` | `C1Potential.target_bakryLedoux` | [C1MainTheorem.lean](UniformRandomMALA/Concrete/C1MainTheorem.lean) |
| Gaussian finite-dimensional enlargement | `bakryLedouxEnlargement_stdGaussian_finiteIndex` | [GaussianRampCanonicalInterpolation.lean](UniformRandomMALA/Concrete/GaussianRampCanonicalInterpolation.lean) |
| Gaussian interpolation and distance-ramp specialization | `gaussianBobkovSmoothInterpolation_of_boundedThirdJet`; `gaussianRampMollified_bobkov` | [GaussianOUCanonicalInterpolation.lean](UniformRandomMALA/Concrete/GaussianOUCanonicalInterpolation.lean); [GaussianRampCanonicalInterpolation.lean](UniformRandomMALA/Concrete/GaussianRampCanonicalInterpolation.lean) |
| Enlargement transported to finite Euler endpoints | `finiteEulerEuclideanEndpoint_enlargement` | [FiniteEulerEnlargement.lean](UniformRandomMALA/Concrete/FiniteEulerEnlargement.lean) |
| Enlargement passed to the target limit | `UniformRandomMALA.DiscreteTime.target_bakryLedoux` | [GaussianRampCanonicalInterpolation.lean](UniformRandomMALA/Concrete/GaussianRampCanonicalInterpolation.lean) |
| Geometric moments `eq:pj` and terminal range `eq:pJ-range` | `ladderMoment`; `ladderMoment_top_range` | [Ladder.lean](UniformRandomMALA/Concrete/Ladder.lean) |
| Exact half-lazy energy and gap scaling | `Dirichlet.energy_halfLazyKernel`; `rayleighSpectralGap_halfLazyKernel` | [LazyKernel.lean](UniformRandomMALA/Concrete/LazyKernel.lean) |

For target enlargement, the manuscript invokes the Caffarelli/Kim–Milman
contraction theorem as a literature result. Lean proves the required
enlargement independently through Gaussian OU/Bobkov interpolation, finite
Euler endpoint contraction, and weak limits. The labels G3, G4, and G5 in
some source comments denote internal construction stages, not manuscript
theorems. Nesterov's Theorem 2.1.5 in `C1ToFirstOrder.lean` is an external
literature reference.

`HessianBoundedPotential.toFirstOrderPotential` and the wrappers in
`HessianMainTheorem.lean`, `LazyKernel.lean`, and
`SqrtDimensionCorollary.lean` provide smooth special cases. The public
first-order statements are the `C1Potential` declarations listed above.
The abstract records in `AnalyticInterfaces.lean` and
`DiscreteTime/StationaryRejection.lean` describe conditional proof interfaces;
they are not additional hypotheses of the public main theorem.
