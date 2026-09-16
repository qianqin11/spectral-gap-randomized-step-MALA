# Revised paper-to-Lean theorem map

Manuscript: revised `paper/main.pdf`, distributed without TeX source.
The public existential statements use the revised range `A₀ ≥ 1`, with
the same internal witness `concreteA0 ≥ 2`. See `BUILD_STATUS.md` for the
current Lean/mathlib 4.33.0 kernel-check evidence. Unless stated otherwise, prefix
names with `UniformRandomMALA.Concrete.`.

## Standing setup and main theorem

| Paper content | Lean declaration | Source |
|---|---|---|
| `C¹` potential, first-order `m`-strong convexity, `L`-Lipschitz actual gradient | `C1Potential` | `Concrete/C1ToFirstOrder.lean` |
| Descent/upper-Taylor inequality | `C1Potential.upperTaylor` | `Concrete/C1ToFirstOrder.lean` |
| Adapter to the internal proof interface, with `gradU = ∇ U` | `C1Potential.toFirstOrderPotential` | `Concrete/C1ToFirstOrder.lean` |
| Paper Rayleigh quotient and gap | `L2RayleighTest`; `rayleighQuotient`; `rayleighSpectralGap` | `Concrete/RayleighSpectralGap.lean` |
| Exact `L²` Poincaré/Rayleigh equivalence | `l2PoincareLower_iff_le_rayleighSpectralGap`; `l2SpectralGap_eq_rayleighSpectralGap` | `Concrete/RayleighSpectralGap.lean` |
| Transfer from the stronger original package gap | `spectralGap_le_rayleighSpectralGap` | `Concrete/RayleighSpectralGap.lean` |
| Theorem 2.1, non-lazy clause | `C1Potential.universal_masterRHS_rayleighSpectralGap_lower` | `Concrete/C1MainTheorem.lean` |
| Theorem 2.1, concrete lazy clause | `C1Potential.universal_half_masterRHS_lazy_rayleighSpectralGap_lower` | `Concrete/C1MainTheorem.lean` |
| Both clauses with the same universal `A₀,b₀,c₀` | `C1Potential.exists_universal_paperMasterRHS_bounds` | `Concrete/C1MainTheorem.lean` |
| Displayed `p⋆` and master right-hand side | `C1Potential.paperMomentThreshold`; `C1Potential.paperMasterRHS` | `Concrete/C1MainTheorem.lean` |
| Corollary 2.2, first display | `C1Potential.sqrtDimensionCorollary_rayleighSpectralGap_lower` | `Concrete/C1MainTheorem.lean` |
| Corollary 2.2, simplified display | `C1Potential.sqrtDimensionCorollarySimplified_rayleighSpectralGap_lower` | `Concrete/C1MainTheorem.lean` |

The two corollary declarations use `H = c/(L√d)`. The simplified theorem does
not assume `p⋆ ≤ d`.

## Ingredients in Section 3

| Paper item | Lean declaration | Source |
|---|---|---|
| Lemma 3.1, finite disjoint-component energy comparison | `Dirichlet.sum_energy_parameterMixture_restrict_le`, specialized by `FirstOrderPotential.energy_restricted_uniformStep_eq_weight_dyadic`; the paper's ladder instance is `FirstOrderPotential.ladder_energy_domination` | `KernelMixture.lean`; `Concrete/Ladder.lean` |
| Proposition 3.2, rejection/overlap for every `p ≥ 1` | `C1Potential.mala_overlap_bounds` | `Concrete/C1MainTheorem.lean` |
| Stationary rejection family used by Proposition 3.2 | `C1Potential.stationary_rejection_moments` | `Concrete/C1MainTheorem.lean` |
| `1 ≤ p ≤ 2` moment interpolation | `UniformRandomMALA.DiscreteTime.integral_rpow_le_of_second_moment` | `DiscreteTime/MomentInterpolation.lean` |
| Proposition 3.3, separated-set conclusion | `C1Potential.separatedSets` | `Concrete/C1MainTheorem.lean` |
| Proposition 3.4, both clauses and full parameter range | `C1Potential.allParameterMALAFlowBounds` | `Concrete/C1MainTheorem.lean` |
| Proposition 3.4's bundled conclusion type | `FirstOrderPotential.AllParameterMALAFlowBounds` | `Concrete/AllParameterMALAFlow.lean` |
| Lemma 3.5, fractional Poincaré conclusion | `fractionalAggregation_poincareLower` | `Concrete/FractionalAggregation.lean` |
| Lemma 3.5 as a gap inequality | `fractionalAggregation_le_spectralGap` | `Concrete/FractionalAggregation.lean` |
| Theorem 3.6, hard-assignment aggregation | `hardAssignmentAggregation_poincareLower`; `hardAssignmentAggregation_le_spectralGap` | `Concrete/FractionalAggregation.lean` |

The public `p ≥ 1` wrapper uses constants `1/(32e)` and `12288 e³`. The
sharper `p ≥ 2` core at `1/(16e)` and `6144 e³` remains checked and is used by
the established multiscale proof.

The aggregation theorems bound the package's stronger, all-measurable
Poincaré spectral gap. Composing `hardAssignmentAggregation_le_spectralGap`
(or its fractional analogue) with `spectralGap_le_rayleighSpectralGap` gives
the corresponding lower bound for the manuscript's `L²` Rayleigh gap.

## Isoperimetry and weak-limit route

| Mathematical role | Lean declaration | Source |
|---|---|---|
| First-order target enlargement | `C1Potential.target_bakryLedoux` | `Concrete/C1MainTheorem.lean` |
| Gaussian finite-dimensional enlargement | `bakryLedouxEnlargement_stdGaussian_finiteIndex` | `Concrete/GaussianRampCanonicalInterpolation.lean` |
| Canonical Gaussian interpolation | `gaussianBobkovSmoothInterpolation_of_boundedThirdJet`; `gaussianRampMollified_bobkov` | `Concrete/GaussianOUCanonicalInterpolation.lean`; `Concrete/GaussianRampCanonicalInterpolation.lean` |
| Finite-Euler endpoint transport | `finiteEulerEuclideanEndpoint_enlargement` | `Concrete/FiniteEulerEnlargement.lean` |
| Weak-limit target theorem | `UniformRandomMALA.DiscreteTime.target_bakryLedoux` | Declared in `Concrete/GaussianRampCanonicalInterpolation.lean`, using target convergence from `Concrete/FiniteEulerTargetIdentification.lean` |

The manuscript invokes the Caffarelli/Kim--Milman contraction theorem as a
literature result. Lean does not assume that theorem: this is an independent,
internal discrete proof of the required target enlargement.

## Concrete lazification

| Paper content | Lean declaration | Source |
|---|---|---|
| Identity branch and reversibility | `Kernel.id`; `kernelId_isReversible` | `Concrete/LazyKernel.lean` |
| Half-lazy kernel and reversibility | `halfLazyKernel`; `halfLazyKernel_isReversible` | `Concrete/LazyKernel.lean` |
| Exact energy scaling | `Dirichlet.energy_halfLazyKernel` | `Concrete/LazyKernel.lean` |
| Exact Rayleigh-gap scaling | `rayleighSpectralGap_halfLazyKernel` | `Concrete/LazyKernel.lean` |

## Fixed-step obstruction (Proposition 2.3)

| Mathematical component | Lean declaration | Source |
|---|---|---|
| Generic Rayleigh test/cut upper bounds | `rayleighSpectralGap_le_quotient`; `rayleighSpectralGap_le_boundaryFlow_div_cutVariance` | `Concrete/SpectralGapUpperBounds.lean` |
| Smooth hard potential | `fixedStepHardPotential`; `contDiff_infty_fixedStepHardPotential` | `Concrete/FixedStepHardPotential.lean` |
| Actual Hessian bounds | `fixedStepHardPotential_hessian_lower`; `fixedStepHardPotential_hessian_upper` | `Concrete/FixedStepHardPotential.lean` |
| Local test-function branch | `fixedStepHardMALA_rayleighSpectralGap_le_local` | `Concrete/HardPotentialLocalObstruction.lean` |
| Gaussian trigonometric identities | `integral_cos_gaussianReal_zero_two`; `integral_mul_sin_gaussianReal_zero_two` | `Concrete/GaussianTrigonometricConcentration.lean` |
| Sticky-region branch | `exists_universal_fixedStepHard_sticky_rayleighSpectralGap_upper` | `Concrete/HardPotentialStickyObstruction.lean` |
| Proposition A.1, generic two-branch smooth-witness obstruction | `exists_universal_fixedStepHardPotential_obstruction_allDimensions`, together with the smoothness and Hessian-bound declarations above | `Concrete/FixedStepHardPotentialObstruction.lean`; `Concrete/FixedStepHardPotential.lean` |
| Exact minimax paper statement | `exists_universal_fixedStepMinimaxGap_paper_upper` | `Concrete/FixedStepMinimax.lean` |

The hard witness is deliberately `C∞` and Hessian bounded, as required for the
smooth subclass in Proposition 2.3. This does not reinstate a smoothness
assumption in Theorem 2.1.

## Compatibility and non-goals

`HessianBoundedPotential.toFirstOrderPotential` and the theorem wrappers in
`HessianMainTheorem.lean`, `LazyKernel.lean`, and
`SqrtDimensionCorollary.lean` remain verified smooth special cases. They are
not the current paper-facing route.

The independent Appendix B extension of the rejection lemmas to possibly
nonconvex `C¹` potentials is not formalized. The declared
`C1Potential.stationary_rejection_moments` retains strong convexity and is the
exact input needed by the end-to-end main-theorem proof. The manuscript's
continuous-time SDE proof is replaced by the discrete route described above.
