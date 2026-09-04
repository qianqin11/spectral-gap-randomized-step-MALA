# Formalization status

Status date: **2026-08-30**

“Checked” means that the relevant module has elaborated with Lean `v4.33.0`
and mathlib `v4.33.0`; principal endpoints are also listed in
`DependencyAudit.lean` for `#print axioms`.

## Reader summary

The lower-bound side of the paper is formalized from the manuscript's actual
`C²` Hessian assumptions through the non-lazy and lazy conclusions of the
main theorem. The package also contains the square-root-dimension corollary,
the exact `L²` fractional aggregation lemma, the one-step MALA flow result
over its full parameter range, and the fixed-step minimax upper bound over
the exact `C∞` Hessian-bounded potential class.

The principal paper-form declarations are:

```lean
UniformRandomMALA.Concrete.
  exists_universal_nonlazy_paperMasterRHS_lower
UniformRandomMALA.Concrete.
  exists_universal_lazy_paperMasterRHS_lower
UniformRandomMALA.Concrete.HessianBoundedPotential.
  sqrtDimensionCorollary_rayleighSpectralGap_lower
UniformRandomMALA.Concrete.fractionalAggregation_poincareLower
UniformRandomMALA.Concrete.FirstOrderPotential.
  allParameterMALAFlowBounds
UniformRandomMALA.Concrete.
  exists_universal_fixedStepMinimaxGap_paper_upper
```

For Proposition 2.3, `fixedStepWorstPotentialGap` is an `sInf` over gaps
attained by infinitely differentiable potentials whose actual second
Fréchet derivatives lie in `[mI,LI]`; `fixedStepMinimaxGap` is an `iSup` over
every positive step size. The explicit cosine-perturbed potential is proved
to belong to this class. The final theorem supplies a universal exponential
rate and, for each lower condition-number cutoff `κ₀ > 1`, a positive
multiplicative constant depending only on `κ₀`.

## Paper-result status

| Paper result | Status | Principal declaration | Main module |
|---|---|---|---|
| MALA overlap proposition, both clauses | Checked | `Concrete.FirstOrderPotential.mala_overlap_bounds` | `MALAOverlap.lean` |
| Bakry--Ledoux enlargement for the target | Checked | `DiscreteTime.target_bakryLedoux` | `BakryLedoux.lean` |
| Hessian assumptions imply the first-order interface | Checked | `Concrete.HessianBoundedPotential.toFirstOrderPotential` | `Concrete/HessianToFirstOrder.lean` |
| Equivalence of Rayleigh and `L²` Poincaré gaps | Checked | `Concrete.l2SpectralGap_eq_rayleighSpectralGap` | `Concrete/RayleighSpectralGap.lean` |
| Theorem 2.1, non-lazy clause | Checked | `Concrete.exists_universal_nonlazy_paperMasterRHS_lower` | `Concrete/HessianMainTheorem.lean` |
| Theorem 2.1, concrete half-lazy clause | Checked | `Concrete.exists_universal_lazy_paperMasterRHS_lower` | `Concrete/LazyKernel.lean` |
| Corollary 2.2, both displays | Checked | `Concrete.HessianBoundedPotential.sqrtDimensionCorollary_rayleighSpectralGap_lower`; `...sqrtDimensionCorollarySimplified_rayleighSpectralGap_lower` | `Concrete/SqrtDimensionCorollary.lean` |
| Lemma 3.5, fractional aggregation | Checked | `Concrete.fractionalAggregation_poincareLower` | `Concrete/FractionalAggregation.lean` |
| Hard-assignment aggregation theorem at exact `L²` scope | Checked | `Concrete.hardAssignmentAggregation_poincareLower` | `Concrete/FractionalAggregation.lean` |
| Proposition 3.4, full admissible parameter range | Checked | `Concrete.FirstOrderPotential.allParameterMALAFlowBounds` | `Concrete/AllParameterMALAFlow.lean` |
| Proposition 2.3, fixed-step minimax upper bound | Checked | `Concrete.exists_universal_fixedStepMinimaxGap_paper_upper` | `Concrete/FixedStepMinimax.lean` |

## The manuscript-assumption bridge

`Concrete.HessianBoundedPotential d` contains:

- a function `U : State d → ℝ` with `ContDiff ℝ 2 U`;
- a positive dimension and constants `0 < m ≤ L`;
- lower and upper quadratic-form bounds on the actual second Fréchet
  derivative `iteratedFDeriv ℝ 2 U x v v`.

The bridge restricts `U` to affine lines and proves the exact strong-convexity
and smoothness Taylor inequalities. An elementary Baillon--Haddad argument
then proves cocoercivity and `L`-Lipschitz continuity of mathlib's Riesz
gradient. `toFirstOrderPotential.gradU` is definitionally `∇ U`, so the MALA
drift in the endpoint is the derivative of the stated potential.

This closes the former mismatch between the paper's Hessian hypothesis and
the package's downstream `FirstOrderPotential` interface.

## Spectral-gap definitions

`Concrete.RayleighSpectralGap.lean` defines:

- `L2RayleighTest π`: a measurable `L²(π)` real function with nonzero
  extended variance;
- `rayleighQuotient π K f = E_K(f,f) / Var_π(f)`;
- `rayleighSpectralGap`: the infimum of those quotients;
- `L2PoincareLower` and `l2SpectralGap`: the corresponding `L²` Poincaré
  formulations.

`l2PoincareLower_iff_le_rayleighSpectralGap` proves the exact order
equivalence, and `l2SpectralGap_eq_rayleighSpectralGap` identifies the two
gaps. The proof treats constant functions, zero variance, infinite energy,
and an empty Rayleigh-test family explicitly. `PoincareLower.toL2` and
`spectralGap_le_rayleighSpectralGap` connect the older all-measurable
Poincaré API to the manuscript's quantity. The paper-form endpoints are
stated directly with `rayleighSpectralGap`.

## Concrete lazification

`Concrete.halfLazyKernel K` is a fair mixture of `Kernel.id` and `K`, not a
scalar stand-in. The checked results include:

```lean
Concrete.halfLazyKernel_isReversible
Concrete.Dirichlet.energy_halfLazyKernel
Concrete.rayleighQuotient_halfLazyKernel
Concrete.rayleighSpectralGap_halfLazyKernel
```

The last theorem proves exact multiplication by `1/2`, including infinite-gap
and empty-test cases. `Concrete.FirstOrderPotential.lazyUniformMALA` applies
this construction to the concrete uniformly randomized MALA kernel and is
proved Markov and reversible with respect to the constructed target.

## Fractional aggregation

The paper's finite-component lemma is formalized with coefficients in
`ℝ≥0∞`. The energy weights `γ j` are finite and positive; the cut weights
`β j` are finite, nonnegative, and may be zero. The cost is

```lean
Concrete.fractionalCost γ β = ∑ j, (β j)^2 / γ j.
```

The main theorem assumes the energy domination only for measurable
`L²(π)` functions. Internally, median positive and negative parts are capped,
proved to lie in `L²`, passed through that hypothesis, and uncapped by
monotone convergence. Thus the formal statement does not strengthen the
manuscript's premise to all measurable functions.

The resulting Poincaré constant is
`(2 * fractionalCost γ β)⁻¹`. Setting `β j = (φ j)⁻¹` gives the exact
hard-assignment theorem and identifies the cost with the existing harmonic
cost.

## Full-parameter one-step flow

`Concrete.FirstOrderPotential.allParameterMALAFlowBounds` packages both
clauses of Proposition 3.4 with the concrete universal constants:

- for every real `p` above `malaFlowMomentThreshold` and
  `0 < θ ≤ 1`, at
  `t = θ b₀/(L sqrt(p(d+p)))`, the local flow bound holds whenever
  `exp(-p/2) ≤ π(S) ≤ 1/2`, together with
  `m t log(1/π(S)) ≤ 1`;
- for every `0 < t ≤ 1/(2Ld)`, the safe flow bound holds for every measurable
  `S` with `0 < π(S) ≤ 1/2`.

The theorem invokes the already checked overlap and target Bakry--Ledoux
results; it does not merely assume the two special ladder cases used later
in the main theorem.

## Lower-bound dependency status

| Layer | Status | Main modules |
|---|---|---|
| Normalized target and concrete MALA kernels | Checked | `Concrete/EuclideanTarget.lean`, `Concrete/MALA.lean`, `Concrete/MALAFamily.lean` |
| Finite Gaussian likelihood and Euler/RWM comparison | Checked | `DiscreteTime/FiniteGaussianLikelihood.lean`, `DiscreteTime/EulerRWM*.lean`, `DiscreteTime/MovingReference.lean` |
| MALA local overlap | Checked | `MALAOverlap.lean`, `Concrete/MALAOverlapBounds.lean` |
| Gaussian normal profile and OU semigroup | Checked | `Concrete/GaussianNormalProfile.lean`, `Concrete/GaussianOU*.lean` |
| Bobkov interpolation residual and functional closure | Checked | `Concrete/GaussianOUCanonical*.lean`, `Concrete/GaussianBobkovFunctional.lean` |
| Smooth ramps and finite Gaussian enlargement | Checked | `Concrete/GaussianRampMollification.lean`, `Concrete/GaussianEnlargement.lean` |
| Weak-limit stability | Checked | `Concrete/WeakLimitEnlargement.lean`, `Concrete/GaussianWeakLimit.lean` |
| Finite Euler transfer and target identification | Checked | `Concrete/FiniteEulerEnlargement.lean`, `Concrete/FiniteEulerTargetIdentification.lean` |
| Separated sets and defective conductance | Checked | `Concrete/SeparatedSets.lean`, `Concrete/MALADefectiveConductance.lean` |
| Safe/ladder components and harmonic aggregation | Checked | `Concrete/SafeComponent.lean`, `Concrete/LadderComponents.lean`, `Concrete/ComponentAggregationFinal.lean` |
| Universal constants and master lower bound | Checked | `Concrete/UniversalConstants.lean`, `Concrete/GlobalFromBakryLedoux.lean` |
| Hessian and Rayleigh paper-form endpoint | Checked | `Concrete/HessianToFirstOrder.lean`, `Concrete/HessianMainTheorem.lean` |

The Gaussian isoperimetry proof is finite dimensional and explicit. The
target transfer uses contractive finite Euler maps and weak convergence. The
development does not formalize a general SDE existence theory, Girsanov's
theorem, or the paper's continuous-time Appendix B derivation.

## Fixed-step proof status

| Component | Status | Principal declarations |
|---|---|---|
| Generic Rayleigh test upper bounds | Checked | `rayleighSpectralGap_le_quotient`, `rayleighSpectralGap_le_energy_div_evariance` |
| Indicator variance and cut upper bound | Checked | `evariance_indicatorReal`, `rayleighSpectralGap_le_boundaryFlow_div_cutVariance` |
| Explicit `C^∞` hard potential | Checked | `contDiff_infty_fixedStepHardPotential`, `fixedStepHardPotential_hessian_lower`, `fixedStepHardPotential_hessian_upper` |
| Genuine gradient/Hessian packaging | Checked | `gradient_fixedStepHardPotential`, `fixedStepHardHessianPotential`, `fixedStepHardFirstOrderPotential` |
| Local first-coordinate obstruction | Checked | `fixedStepHardMALA_rayleighSpectralGap_le_local` |
| Exact origin log-ratio algebra | Checked | `hardCoordinateLogRatio_eq`, `hard_malaLogRatio_zero_eq_sum` |
| Gaussian trigonometric moments | Checked | `integral_cos_gaussianReal_zero_two`, `integral_mul_sin_gaussianReal_zero_two` |
| Negative-threshold product concentration | Checked | `exists_universal_contraction_factor_for_pi_scaledGaussian_tail` |
| Acceptance-profile continuity | Checked | `FirstOrderPotential.continuous_malaAcceptanceProfile` |
| Positive-mass centered sticky ball and cut bound | Checked | `FirstOrderPotential.exists_target_ball_rayleighSpectralGap_le_two_mul` |
| Exponential sticky branch | Checked | `exists_universal_fixedStepHard_sticky_rayleighSpectralGap_upper` |
| Combined generic hard-potential obstruction | Checked | `exists_universal_fixedStepHardPotential_obstruction_allDimensions` |
| Scalar compression and step-size optimization | Checked | `iSup_fixedStepTwoBranchEnvelope_le_log_max_exp` |
| `sInf`/`iSup` minimax endpoint | Checked | `exists_universal_fixedStepMinimaxGap_paper_upper` |

The generic sticky-cut theorem deserves separate emphasis. For an arbitrary
`FirstOrderPotential`, `malaAcceptanceProfile h x` integrates the real
Metropolis acceptance over one fixed standard-Gaussian innovation law.
`continuous_malaAcceptanceProfile` proves continuity by dominated convergence.
Strict positivity of the target density and absence of atoms then produce a
centered open ball with positive target mass below one half. If the origin
acceptance is strictly below `b`,
`exists_target_ball_rayleighSpectralGap_le_two_mul` gives both the outgoing
flow estimate and `Gap ≤ 2b`.

For the hard potential, the local branch gives
`Gap ≤ mh+(mh)²/2`. The sticky branch shifts the exact trigonometric increment
by half the magnitude of its negative mean and proves a fixed-parameter
Chernoff contraction at the required negative linear threshold. Combining
that estimate with the generic ball theorem yields an exponential upper
bound. `exists_universal_fixedStepHardPotential_obstruction_allDimensions`
compresses the two branches to

```text
Gap(P_h) ≤ 8 min(
  mh + (mh)²/2,
  exp(-c(d-1) min((L-m)h,1))).
```

Finally, `smoothHessianPotentialGapValues` defines the exact admissible
`C∞` class; `fixedStepWorstPotentialGap` is its `sInf`; and
`fixedStepMinimaxGap` is the `iSup` over all positive `h`. The final theorem
proves

```text
fixedStepMinimaxGap d m L ≤
  C(κ₀) max(log(κd)/(κd), exp(-c d)),   κ=L/m,
```

for `κ ≥ κ₀ > 1`, where `c>0` is universal and `C(κ₀)>0` depends only on
the cutoff.

## Validation record and trust boundary

The complete active package built successfully with:

```text
lake build
```

and reported `Build completed successfully (3435 jobs).`

The completed endpoint audits expose only the standard logical dependencies
already used by Lean/mathlib, such as propositional extensionality,
`Classical.choice`, and quotient soundness. No project-specific axiom is used.

No requested mathematical milestone remains open. The package deliberately
does not formalize the paper's continuous-time Appendix B derivation: the
corresponding lower-bound input is proved by the documented finite,
discrete-time alternative. This is a proof-route difference, not an assumed
lemma or an omission from the stated Lean endpoints.
