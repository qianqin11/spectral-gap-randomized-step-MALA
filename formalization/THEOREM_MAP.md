# Paper-to-Lean theorem map

This table maps Qian Qin's **A global spectral gap for Metropolis-adjusted Langevin algorithm
with a uniformly randomized step size**
(`paper/main.pdf`, synchronized on 2026-09-05) to Lean declarations.
Labels such as `thm:main` are retained manuscript source identifiers, not
paths to bundled LaTeX files; only the manuscript PDF is distributed.

The paper's stationary-rejection appendix uses stationary time reversal
for the linear-increment estimate, following the Lyons--Zheng
forward--backward decomposition (1988, Section 1, equation (1.7)). Gaussian
randomization and Jensen's inequality give integrated-increment bounds;
Girsanov and martingale inequalities then give rejection control.

The rows described as finite-discrete-time replacements concern the role
of these ingredients in establishing stationary rejection and overlap.
They do not assert that the finite-Euler estimates formalize the exact
continuous-time increment inequalities. The implemented route uses finite
Gaussian likelihoods, an Euler/RWM coupling, and weak-limit closure. See
`PAPER_READER_GUIDE.md` for its scope; this manuscript revision changes no
Lean proof or assumption.

The internal development labels G3, G4, and G5 mean the local OU residual
argument, functional Bobkov closure, and the ramp-to-enlargement passage,
respectively. They are not paper theorem numbers.

| Paper result | Lean declaration(s) | Status |
|---|---|---|
| Appendix B, Lemmas B.2--B.3 (`lem:linear-increment`, `lem:integrated-increments`) | Their role in the stationary-rejection argument is replaced by `finiteEulerEnergy_le_frozenGradient_add_partialSums` and `integral_exp_finiteEulerEnergy_le_exp` | Alternative finite-Euler estimates; not a formalization of the stationary time-reversal identity or the exact continuous-time increment inequalities |
| Appendix B, Lemma B.5 (`lem:path-likelihood`) | `finiteGaussianDRec_centered_rpow_root_le_paper_scale`; `fixedHorizonOffsetFullPathMomentBound_paperScale` | Concrete finite-product replacement, with full-path constant `1024 e^3` |
| Endpoint conditional likelihood contraction | `finiteEulerLikelihoodTiltedEdgeLaw_eq_finiteFrozenLikelihoodEdgeLaw`; `finiteFrozenLikelihoodEdge_rnDeriv_centered_rpow_integrable_and_root_le`; `finiteEulerLikelihoodEdgeLaw_eq_finiteEulerEdgeMeasure` | Concrete and formalized |
| Gaussian RWM proposal and detailed balance | `randomWalkProposal`; `rwmKernel`; `rwmKernel_isReversible`; `rwmKernel_invariant` | Concrete and formalized |
| Euler/RWM endpoint coalescence | `iteratedIntegral_pair_difference_sq_delta_le`; `stationaryEulerRWMPairChain_energy_step`; `tendsto_stationaryEulerRWMPairChain_energy_fixedHorizon` | Concrete and formalized by finite pair-kernel iteration |
| Moving-reference likelihood lemma | `centeredRNDeriv_memLp_of_weakLimit`; supporting declarations in `DiscreteTime/MovingReference.lean` | Concrete and formalized |
| Retained-initial edge coupling and vanishing cost | `lintegral_retainedInitial_pairCost_eq_ofReal_energy`; `exists_positive_vanishing_fixedHorizonOffsetSchedule` | Concrete and formalized |
| Tight endpoint limit and preservation of symmetry | `exists_common_tendsto_subseq_fixedHorizonEulerRWMEdgeLaws_with_structure` | Concrete and formalized; common Euler/RWM limit is swap invariant with both target marginals |
| MH accepted-flow meet and rejection marginal | `malaAcceptedEdge_eq_rnMeet`; `malaRejection_eq_rejectionMarginal`; `stationaryMALARejectionMomentBound_of_moving_reference_family` | Concrete and formalized |
| Proposition B.1 stationary rejection | `stationaryMALARejectionMomentBound_paperScale` | Concrete and formalized with `cr=1/(16e)`, `Cr=6144 e^3` |
| Scalar probability averaging/Jensen | `rpow_integral_le_integral_rpow` | Concrete and formalized |
| `lem:Kt` (Lemma 3.1), common mixture kernel | `Kernel.parameterMixture`; `Kernel.parameterMixture_apply`; `Kernel.parameterMixture_isMarkovKernel` | Concrete and formalized |
| `lem:Kt`, reversibility | `Kernel.isReversible_parameterMixture` | Concrete and formalized |
| `lem:Kt`, Tonelli identity and dyadic-component inequality | `Dirichlet.energy_parameterMixture`; `Measure.finsetSum_restrict_le_of_pairwiseDisjoint`; `energy_parameterMixture_restrict_le`; `sum_energy_parameterMixture_le`; `sum_energy_parameterMixture_restrict_le`; `energy_restricted_uniformStep_eq_weight_dyadic` | Concrete, including exact interval normalization |
| Target `π(dx) ∝ exp(-U(x))dx` | `boltzmannFiniteMeasure`; `target`; `targetDensity`; `target_toMeasure_eq_withDensity` | Concrete and formalized from `FirstOrderPotential` |
| Paper's `C²` Hessian assumptions and gradient | `HessianBoundedPotential`; `HessianBoundedPotential.toFirstOrderPotential`; `gradient_fixedStepHardPotential` for the explicit hard witness | The Hessian is the actual second Fréchet derivative, the gradient is mathlib's Riesz gradient, and the exact Taylor and Lipschitz consequences are kernel-checked in `Concrete/HessianToFirstOrder.lean` |
| Gaussian proposal `Q_h` | `proposalDensityReal`; `proposalDensity`; `gaussianDensityProposal`; normalization/apply theorems | Concrete and formalized |
| Metropolis correction and fixed-step `P_h` | `MetropolisHastings.densityKernel_isReversible`; `accepted_densityKernel_isReversible`; `malaKernel`; `malaKernel_isReversible` | Concrete and formalized |
| Joint measurability and uniform mixture `P̄_H` | `malaKernelFamily`; `uniformStepMeasure`; `uniformMALA`; Markov/reversibility/energy theorems | Concrete and formalized |
| Dyadic component `K_t` | `dyadicStepMeasure`; `dyadicMALA`; `energy_dyadicMALA` | Concrete and formalized |
| Proposition 3.2, moment part | First conjunct of `FirstOrderPotential.proposition32_discreteTime`; `exists_dyadicMALALocalOverlap_goodSet` | Concrete and formalized, including the measurable good set and exceptional-mass bound |
| Proposition 3.2, globally safe part | Second conjunct of `FirstOrderPotential.proposition32_discreteTime`; `setwiseTV_dyadicMALA_le_seventeen_div_32` | Concrete and formalized; the stronger intermediate constant is `17/32` |
| MALA local overlap (both assertions of Proposition 3.2) | `FirstOrderPotential.mala_overlap_bounds` in `MALAOverlap.lean`; compatibility theorem `proposition32_discreteTime` in `Concrete/MALAOverlapBounds.lean` | **Unconditional and kernel-checked**, with `cr=1/(16e)` and `Cr=6144 e^3` |
| BH1 in safe-step proof | `one_sided_bh_safe_log_lower` | Formalized from the scalar BH1 premise |
| Cocoercivity/nonexpansive proposal means | `proposal_mean_nonexpansive_sq` | Formalized from the scalar cocoercivity premise |
| Standard `φ`, `Φ`, and upper tail | `normalDensity`; `normalCDF`; `normalTail`; integral, symmetry, and zero-mass theorems | Concrete foundation formalized |
| Lemma C.1 (Gaussian Mills bounds) | `Concrete.mills_lower`; `Concrete.mills_upper` | Concrete and checked |
| `lem:gaussian-shift` | `Concrete.standardGaussianShift` | Concrete and checked |
| Weak-limit stability of enlargement profiles | `Concrete.enlargement_profile_of_weakLimit`; `Concrete.bakryLedouxEnlargement_of_weakLimit` | Abstract profile theorem and direct endpoint-safe Gaussian specialization checked by the open/closed Portmanteau sandwich with `c_n → c > 0` |
| Gaussian normal profile | `Concrete.normalProfile`; `normalProfile_one_sub`; `normalProfile_mul_secondDeriv`; `strictConcaveOn_normalProfile`; `normalProfile_tendsto_zero_right`; `normalProfile_tendsto_one_left`; `normalProfileClosed`; `continuous_normalProfileClosed` | Interior calculus plus the canonical continuous endpoint extension checked |
| Explicit Gaussian OU/Mehler semigroup | `Concrete.gaussianOUSemigroup`; `map_gaussianOUMap_prod_stdGaussian`; `gaussianOUSemigroup_comp`; `integral_gaussianOUSemigroup`; `tendsto_gaussianOUSemigroup_atTop`; `hasFDerivAt_gaussianOUSemigroup` | Time zero, Gaussian invariance, composition, invariant integration, long-time convergence, and bounded-`C¹` Fréchet-derivative commutation checked |
| Local Bobkov OU interpolation (internal stage G3) | `gaussianBobkovSmoothInterpolation_of_boundedThirdJet`; `canonicalGaussianBobkovQ_time_add_generator_eq_residual` | **Complete**: canonical field, higher derivatives, backward PDE, residual identity/sign, integrable time-dependent Mehler differentiation, and endpoint monotonicity |
| Functional Gaussian Bobkov closure (internal stage G4) | `Concrete.tendsto_gaussianBobkovOUIntegral_atTop`; `gaussianBobkov_functionalClosed_of_truncations`; `gaussianBobkov_functionalClosed_of_localTruncations`; `gaussianBobkov_functionalClosed_of_smoothInterpolations` | Long-time dominated convergence, closed-profile passage, and endpoint truncation checked and connected directly to smooth interpolation certificates |
| Gaussian ramps and enlargement (internal stage G5) | `gaussianRamp`; `concreteGaussianRampSmoothApproximation`; `gaussianRampSmoothApproximationProperty`; `continuousWithinAt_closedEnlargementMass_right`; `bakryLedouxEnlargement_of_canonicalInterpolations` | Concrete mollification, strip/perimeter, intrinsic right-continuity, Dini/quantile, closed-set, and Radon steps checked; no external ramp-approximation or enlargement-continuity premise remains |
| Finite Euler enlargement and weak limit | `finiteEulerEndpointLimit_bakryLedoux`; `tendsto_finiteEulerTargetDiagonalEndpointLaw` | **Complete**: finite Gaussian-image transfer, sharp coefficient limit, and explicit target identification |
| Bakry–Ledoux enlargement `(2.10)–(2.12)` | `bakryLedouxEnlargement_stdGaussian_finiteIndex`; `DiscreteTime.target_bakryLedoux` | **Unconditional and checked** |
| `prop:separated` | `Concrete.separatedSets_of_bakryLedoux` | Concrete and checked from Bakry--Ledoux |
| `prop:flow` (Proposition 3.4), full parameter range | `FirstOrderPotential.local_dyadicMALA_boundaryFlow_allParameters`; `safe_dyadicMALA_boundaryFlow_allParameters`; `allParameterMALAFlowBounds` | Both clauses are checked for arbitrary admissible `p,θ,t`, including the mass interval, exact step, constants, and `m t log(1/π(S)) ≤ 1` assertion |
| Stationary edge measure and cut flow | `edgeMeasure`; `flow`; `boundaryFlow`; `edgeMeasure_map_swap`; `lintegral_edgeMeasure_fst`; `lintegral_edgeMeasure_snd`; `energy_indicatorReal` | Concrete and checked |
| Squared-superlevel coarea identity used in `lem:fractional` and `thm:aggregation` | `lintegral_boundaryFlow_sqSuperlevel`; `half_lintegral_abs_sqDiff_eq_lintegral_pos_sqDiff`; `coarea_sqSuperlevel`; `coarea_sqSuperlevel_le_energy_secondMoment` | Concrete and checked in `[0,∞]` |
| `lem:fractional` (Lemma 3.5) | `fractionalCost`; `fractional_weighted_sqrt_sum_le`; `fractionalAggregation_evariance_le`; `fractionalAggregation_poincareLower`; `fractionalAggregation_le_spectralGap` | Full fractional theorem checked with the manuscript's `L²` energy-domination scope, zero weights, bounded truncations, and ENNReal edge cases |
| Quantile/median infrastructure for `thm:aggregation` | `lowerQuantile_le_iff`; `exists_isMedian`; `evariance_le_lintegral_sq_sub`; `energy_medianParts_le` | Concrete and checked |
| Finite component flow aggregation | `measure_le_sum_inv_mul_boundaryFlow`; `lintegral_measure_sqSuperlevel_le_sum_normalizedFlow`; `lintegral_sq_le_sum_component_coareaBounds`; `medianParts_lintegral_le_sum_component_coareaBounds` | Concrete and checked without measurable selection |
| `thm:aggregation` (Theorem 3.6), hard-assignment corollary | `hardAssignmentAggregation_poincareLower`; `hardAssignmentAggregation_le_spectralGap`; retained MALA-specific declarations `componentAggregation_poincareLower` and `componentAggregation_le_spectralGap` | The exact `L²` theorem is checked as a corollary of fractional aggregation; the older stronger-scope MALA interface remains available |
| Safe component, equation `safe-gap-bound` | `FirstOrderPotential.safe_spectralGap_lower_of_bakryLedoux`; `safe_truncated_spectralGap_lower_of_bakryLedoux` | Concrete and checked from Bakry--Ledoux |
| Ladder moments, endpoints, and disjoint intervals | `ladderMoment`; `ladderTopIndex`; `ladderMoment_top_range`; `ladderEndpoint_succ_lt_half`; `ladderIntervals_pairwiseDisjoint` | Concrete and formalized |
| Ladder Dirichlet domination | `uniformStepMeasure_restrict_dyadic`; `energy_restricted_uniformStep_eq_weight_dyadic`; `ladder_energy_domination` | Concrete and formalized with exact weights |
| Ladder flow assignment | `FirstOrderPotential.ladder_flowAssignment_of_bakryLedoux` | Concrete and checked from Bakry--Ledoux |
| `lem:exceptional-budget` | `ladderExceptionalBudget_of_parameterChoice`; `universalParameters_exceptionalChoice` | Concrete and checked; explicit `A₀` discharges the condition |
| `lem:ladder-sum` | `ladderHarmonicReal_le`; `ladder_harmonicCost_le` | Concrete and checked with constant `6·2^30` |
| Equation `ladder-gap-bound` | `FirstOrderPotential.ladder_truncated_spectralGap_lower_of_bakryLedoux` | Concrete and checked from Bakry--Ledoux |
| Final identity `max{min(H,a)^2,min(H,b)^2}` | `max_sq_min_eq_min_max_sq` | Formalized |
| Paper and Poincaré/Rayleigh spectral-gap definitions | `l2PoincareLower_iff_le_rayleighSpectralGap`; `l2SpectralGap_eq_rayleighSpectralGap`; `spectralGap_le_rayleighSpectralGap` | Measurable `L²` tests, zero variance, constant functions, and infinite energy are handled formally |
| `thm:main`, exact non-lazy lower bound | `HessianBoundedPotential.universal_masterRHS_rayleighSpectralGap_lower`; `exists_universal_nonlazy_paperMasterRHS_lower` | **Concrete and checked from the manuscript's actual `C²` Hessian assumptions**, with the exact displayed `pStar`, universal constants, and paper Rayleigh gap |
| Concrete lazification in `thm:main` | `halfLazyKernel`; `halfLazyKernel_isReversible`; `Dirichlet.energy_halfLazyKernel`; `rayleighSpectralGap_halfLazyKernel`; `FirstOrderPotential.lazyUniformMALA`; `exists_universal_lazy_paperMasterRHS_lower` | Exact identity-kernel mixture, reversibility, half-energy, half-gap, and paper-form lazy lower bound checked |
| Corollary 2.2, `H=c/(L√d)` | `HessianBoundedPotential.sqrtDimensionCorollary_rayleighSpectralGap_lower` | First displayed inequality checked under the manuscript's Hessian assumptions |
| Corollary 2.2, final simplified logarithmic bound | `min_sqrtDimensionDenominator_le_two_pStar`; `sqrtDimensionCorollarySimplifiedRHS_le_gap`; `HessianBoundedPotential.sqrtDimensionCorollarySimplified_rayleighSpectralGap_lower` | Current assumption-free simplification checked without assuming `pStar ≤ d` |
| Additional adapted-endpoint corollary retained in Lean | `adapted_endpoint_identity`; `adapted_endpoint`; `paper_interfaces_imply_adapted_endpoint` | Formalized; useful but not stated separately in the current manuscript |
| Proposition 2.3, generic test/cut upper bounds | `rayleighSpectralGap_le_quotient`; `rayleighSpectralGap_le_energy_div_evariance`; `rayleighSpectralGap_le_boundaryFlow_div_cutVariance` | Reusable Rayleigh upper-bound and exact indicator-flow API checked |
| Proposition 2.3, explicit `C∞` hard potential | `fixedStepHardPotential`; `contDiff_infty_fixedStepHardPotential`; `fixedStepHardPotential_hessian_lower`; `fixedStepHardPotential_hessian_upper`; `fixedStepHardHessianPotential` | Literal cosine-perturbed potential checked against the actual Hessian bounds |
| Proposition 2.3, local and sticky branches | `fixedStepHardMALA_rayleighSpectralGap_le_local`; `exists_universal_fixedStepHard_sticky_rayleighSpectralGap_upper`; `exists_universal_fixedStepHardPotential_obstruction_allDimensions` | Gaussian first marginal/test function, exact MALA log ratio, Gaussian trigonometric concentration, continuity/small-ball cut, and the combined obstruction are checked |
| Proposition 2.3, scalar optimization and minimax | `fixedStepTwoBranchEnvelope_le_log_max_exp`; `fixedStepMinimaxGap`; `exists_universal_fixedStepMinimaxGap_explicit_upper`; `exists_universal_fixedStepMinimaxGap_paper_upper` | Full supremum–infimum statement over positive step sizes and the exact `C∞` Hessian-bounded potential class is checked; the final constant depends only on `κ₀` |

## Exact paper-form entry theorems

```lean
theorem exists_universal_nonlazy_paperMasterRHS_lower :
    ∃ A₀ b₀ c₀ : ℝ, ...

theorem exists_universal_lazy_paperMasterRHS_lower :
    ∃ A₀ b₀ c₀ : ℝ, ...

theorem exists_universal_fixedStepMinimaxGap_paper_upper :
    ∃ c : ℝ, 0 < c ∧
      ∀ {κ₀ : ℝ}, 1 < κ₀ → ∃ C : ℝ, 0 < C ∧ ...
```

The ellipses abbreviate the quantified dimensions, Hessian-bounded
potentials, and positive step parameters printed in
`Concrete/HessianMainTheorem.lean`, `Concrete/LazyKernel.lean`, and
`Concrete/FixedStepMinimax.lean`. The older
`FirstOrderPotential.universal_masterRHS_spectralGap_lower` remains the main
internal assembly theorem.

## Legacy abstract assembly

The following theorem belongs to an early API in which the paper's analytic
ingredients were fields of `PaperAnalyticInterfaces`. It remains useful for
testing alternate inputs and for compatibility with old imports, but it is
not the verification endpoint and is not used by the concrete theorem above.

```lean
theorem paper_interfaces_imply_expanded_main_theorem
    (p : Parameters) (a : PaperAnalyticInterfaces p) :
    p.c0 * (p.m / p.H) *
        (min p.H
          ((p.b0 / p.L) *
            max
              (1 / Real.sqrt (p.pStar * (p.d + p.pStar)))
              (1 / p.d))) ^ 2 ≤
      a.kernelObjects.spectralGap
        (a.kernelObjects.uniformMALA p.H)
```

The argument is intentionally conditional on `a` because that is the purpose
of this modular interface. The concrete route proves and supplies the
corresponding inputs internally.
