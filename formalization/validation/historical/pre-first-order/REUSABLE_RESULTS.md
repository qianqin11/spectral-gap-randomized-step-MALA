# Reusable mathematical results

This guide describes results that can be imported independently of the final
uniform-random-MALA theorem. All names below begin with the namespace
`UniformRandomMALA`; code blocks omit that common prefix when space is tight.

“Checked” means that the theorem has elaborated with the pinned Lean/mathlib
toolchain and contains no placeholder proof. Ordinary mathematical hypotheses
remain visible in its type.

## A coordinate-free Hessian calculus bridge

Import:

```lean
import UniformRandomMALA.Concrete.HessianToFirstOrder
```

The reusable input structure is:

```lean
#check Concrete.HessianBoundedPotential
```

For `State d = EuclideanSpace ℝ (Fin d)`, it records:

```text
U : State d → ℝ
ContDiff ℝ 2 U
0 < d,  0 < m ≤ L
m ‖v‖² ≤ iteratedFDeriv ℝ 2 U x v v
iteratedFDeriv ℝ 2 U x v v ≤ L ‖v‖².
```

The Hessian in these inequalities is the actual second Fréchet derivative of
`U`. The gradient used below is mathlib's Riesz representative `∇ U`.

The main results are:

```lean
#check Concrete.HessianBoundedPotential.lowerTaylor
#check Concrete.HessianBoundedPotential.upperTaylor
#check Concrete.HessianBoundedPotential.gradient_cocoercive
#check Concrete.HessianBoundedPotential.norm_gradient_sub_le
#check Concrete.HessianBoundedPotential.gradient_lipschitz
#check Concrete.HessianBoundedPotential.toFirstOrderPotential
```

In mathematical notation, `lowerTaylor` and `upperTaylor` prove

```text
U(y) ≥ U(x) + ⟪∇U(x), y-x⟫ + (m/2) ‖y-x‖²,
U(y) ≤ U(x) + ⟪∇U(x), y-x⟫ + (L/2) ‖y-x‖².
```

The proof restricts `U` to the affine line `x+s(y-x)`, differentiates that
one-dimensional function twice, and applies convexity of the lower and upper
Taylor residuals. The gradient Lipschitz estimate is then derived from those
Taylor inequalities through a Baillon--Haddad/cocoercivity argument; it is
not assumed as an additional operator-norm hypothesis.

`toFirstOrderPotential` is useful whenever a later development is phrased in
terms of strong convexity and a Lipschitz gradient. Its recorded `gradU` is
definitionally `∇ U`, which prevents accidental use of an unrelated vector
field. The bridge is finite dimensional because it relies on the Riesz
gradient and the Euclidean MALA state type, but its statement is
coordinate-free.

## Rayleigh and Poincaré formulations of spectral gap

Import:

```lean
import UniformRandomMALA.Concrete.RayleighSpectralGap
```

The definitions are:

```lean
#check Concrete.L2RayleighTest
#check Concrete.rayleighQuotient
#check Concrete.rayleighSpectralGap
#check Concrete.L2PoincareLower
#check Concrete.l2SpectralGap
```

`L2RayleighTest π` bundles a measurable real `L²(π)` function with nonzero
extended variance. The quotient and gap take values in `ℝ≥0∞`, so infinite
Dirichlet energy does not require a separate side condition.

The equivalence API is:

```lean
#check Concrete.l2PoincareLower_iff_le_rayleighSpectralGap
#check Concrete.l2SpectralGap_eq_rayleighSpectralGap
```

The first theorem says exactly that `c` is an `L²` Poincaré lower bound if
and only if `c ≤ rayleighSpectralGap π K`. The second identifies the supremum
of such lower bounds with the infimum of Rayleigh quotients.

The proof covers the cases that are easy to lose in paper calculations:

- measurable `L²` functions of zero variance;
- constant functions;
- infinite energy;
- the empty family of nonconstant tests, where the infimum is `∞`.

The older package definition `PoincareLower` quantifies over every measurable
real function, not only `L²` functions. The bridge

```lean
#check Concrete.PoincareLower.toL2
#check Concrete.spectralGap_le_rayleighSpectralGap
```

shows that a bound proved with this stronger scope is a valid lower bound for
the paper's Rayleigh gap. The package does not claim that the older
all-measurable supremum equals the Rayleigh gap in complete abstraction;
the exact equality is between `l2SpectralGap` and `rayleighSpectralGap`.

## Fair lazification of arbitrary Markov kernels

Import:

```lean
import UniformRandomMALA.Concrete.LazyKernel
```

The generic construction is:

```lean
#check Concrete.halfLazyKernel
```

It uses a fair measure on `Bool` and a measurable kernel family selecting
either `Kernel.id` or `K`. This realizes `(I+K)/2` as a genuine kernel on any
measurable state space.

The reusable theorems are:

```lean
#check Concrete.halfLazyKernel_apply
#check Concrete.halfLazyKernel_isReversible
#check Concrete.Dirichlet.energy_halfLazyKernel
#check Concrete.rayleighQuotient_halfLazyKernel
#check Concrete.rayleighSpectralGap_halfLazyKernel
```

For a Markov kernel `K` and measurable `f`, they prove

```text
E_{(I+K)/2}(f,f) = (1/2) E_K(f,f)
```

and hence exact halving of every Rayleigh quotient and of the Rayleigh gap.
The gap theorem is stated in `ℝ≥0∞` and handles an empty test family or an
infinite original gap without an auxiliary finiteness assumption.

The same module specializes the construction to the paper's concrete kernel:

```lean
#check Concrete.FirstOrderPotential.lazyUniformMALA
#check Concrete.FirstOrderPotential.lazyUniformMALA_isMarkovKernel
#check Concrete.FirstOrderPotential.lazyUniformMALA_isReversible
#check Concrete.FirstOrderPotential.energy_lazyUniformMALA
#check Concrete.FirstOrderPotential.rayleighSpectralGap_lazyUniformMALA
```

## Fractional aggregation for finite reversible families

Import:

```lean
import UniformRandomMALA.Concrete.FractionalAggregation
```

This module is independent of MALA. Let `P` be a Markov kernel on a
probability space and let `K j`, `j : Fin N`, be reversible Markov kernels.
Let `γ j` be finite and strictly positive and let `β j` be finite and
nonnegative; `β j = 0` is allowed. Define

```lean
#check Concrete.fractionalCost
-- fractionalCost γ β = ∑ j, (β j)^2 / γ j
```

Assume, for every measurable `f ∈ L²(π)`,

```text
∑ j, γ_j E_{K_j}(f,f) ≤ E_P(f,f),
```

and, for every measurable `S` with `0 < π(S) ≤ 1/2`,

```text
π(S) ≤ ∑ j, β_j J_{K_j}(S,Sᶜ).
```

If `fractionalCost γ β > 0`, then:

```lean
#check Concrete.fractionalAggregation_evariance_le
#check Concrete.fractionalAggregation_poincareLower
#check Concrete.fractionalAggregation_le_spectralGap
```

The variance theorem states

```text
Var_π(f) ≤ 2 (∑ j β_j²/γ_j) E_P(f,f),
```

and the Poincaré theorem gives the reciprocal constant. The proof formalizes
a weighted Cauchy--Schwarz inequality in `ℝ≥0∞`:

```lean
#check Concrete.fractional_weighted_sqrt_sum_le
```

It then combines reversible edge-measure coarea, layer cake, median splitting,
bounded capping, and monotone convergence. Crucially, the energy-domination
hypothesis is invoked only on the capped functions, after those functions
have been proved `L²`. This is why the theorem has the manuscript's exact
`L²` premise instead of the stronger all-measurable premise used by an older
component-aggregation interface.

The hard-assignment specialization is:

```lean
#check Concrete.fractionalCost_inv_eq_harmonicCost
#check Concrete.hardAssignmentAggregation_poincareLower
#check Concrete.hardAssignmentAggregation_le_spectralGap
```

It sets `β j = (φ j)⁻¹`, where a cut is assigned a component satisfying
`φ_j π(S) ≤ J_{K_j}(S,Sᶜ)`, and recovers the harmonic cost
`∑ j (γ_j φ_j²)⁻¹`.

## Spectral-gap upper bounds from tests and cuts

Import:

```lean
import UniformRandomMALA.Concrete.SpectralGapUpperBounds
```

The lower-bound proof uses Poincaré inequalities; upper-bound arguments use
the dual fact that each admissible test gives an upper bound. The generic API
contains:

```lean
#check Concrete.rayleighSpectralGap_le_quotient
#check Concrete.rayleighSpectralGap_le_energy_div_evariance
#check Concrete.rayleighSpectralGap_mul_evariance_le_energy
```

For measurable cuts it proves the exact identities and consequences:

```lean
#check Concrete.memLp_indicatorReal
#check Concrete.integral_indicatorReal
#check Concrete.variance_indicatorReal
#check Concrete.evariance_indicatorReal
#check Concrete.rayleighSpectralGap_le_boundaryFlow_div_evariance_indicator
#check Concrete.rayleighSpectralGap_le_boundaryFlow_div_cutVariance
#check Concrete.rayleighSpectralGap_mul_indicatorVariance_le_boundaryFlow
```

On a probability space, the real indicator has variance
`π(S)(1-π(S))`. Thus every measurable nontrivial cut gives the familiar
upper bound by outgoing stationary flow divided by cut variance. The
division-free form is useful when working in `ℝ≥0∞`.

## Continuous acceptance profiles and sticky cuts

Import:

```lean
import UniformRandomMALA.Concrete.StickyRegionCut
```

For any `FirstOrderPotential`, define the proposal-averaged Metropolis
acceptance by integrating against one fixed standard-Gaussian innovation:

```lean
#check Concrete.FirstOrderPotential.malaAcceptanceIntegrand
#check Concrete.FirstOrderPotential.malaAcceptanceProfile
```

The principal regularity theorem is:

```lean
#check Concrete.FirstOrderPotential.continuous_malaAcceptanceProfile
```

The integrand is continuous in the state and innovation and lies in `[0,1]`.
Dominated convergence therefore makes the integrated profile continuous in
the state. The identity

```lean
#check Concrete.FirstOrderPotential.
  ofReal_malaAcceptanceProfile_eq_acceptanceMass
```

connects this real integral to the extended-valued accepted mass of the
concrete Metropolis--Hastings kernel.

The target constructed from a `FirstOrderPotential` has strictly positive
density on every point and no atoms. Using outer regularity, the module proves
that every open neighborhood of the origin contains a positive-target-mass
open cut, and indeed a centered metric ball, whose mass is below one half:

```lean
#check Concrete.FirstOrderPotential.target_isOpen_measure_pos
#check Concrete.FirstOrderPotential.target_singleton_zero
#check Concrete.FirstOrderPotential.exists_target_ball_inside
```

Combining continuity with the indicator-cut Rayleigh bound gives:

```lean
#check Concrete.FirstOrderPotential.
  exists_target_ball_rayleighSpectralGap_le_two_mul
```

If `malaAcceptanceProfile h 0 < b`, it returns `r>0` such that the centered
ball has positive target mass below one half, its outgoing flow is at most
`b` times its mass, and the Rayleigh gap of the MALA kernel is at most `2b`.
This theorem is generic: it does not mention the cosine hard potential and
can be reused whenever a pointwise low-acceptance estimate is available.

## Full-parameter MALA boundary flow

Import:

```lean
import UniformRandomMALA.Concrete.AllParameterMALAFlow
```

The definitions

```lean
#check Concrete.FirstOrderPotential.malaFlowMomentThreshold
#check Concrete.FirstOrderPotential.malaFlowStep
```

encode the paper's

```text
p ≥ A₀(1+log(d+1)+log(L/m)),
t = θ b₀/(L sqrt(p(d+p))).
```

The reusable unbundled results are:

```lean
#check Concrete.FirstOrderPotential.
  local_dyadicMALA_boundaryFlow_allParameters
#check Concrete.FirstOrderPotential.
  safe_dyadicMALA_boundaryFlow_allParameters
```

and the two-clause bundle is:

```lean
#check Concrete.FirstOrderPotential.AllParameterMALAFlowBounds
#check Concrete.FirstOrderPotential.allParameterMALAFlowBounds
```

The local theorem accepts every real `p` above the threshold and every
`0 < θ ≤ 1`; it is not restricted to the dyadic ladder chosen in the main
proof. It covers `exp(-p/2) ≤ π(S) ≤ 1/2` and also proves the unsaturated
inequality `m t log(1/π(S)) ≤ 1`. The safe theorem covers every
`0 < t ≤ 1/(2Ld)` and every nontrivial cut of mass at most one half.

## Finite-dimensional Gaussian isoperimetry

Import:

```lean
import UniformRandomMALA.BakryLedoux
```

The common predicate is:

```lean
#check Concrete.BakryLedouxEnlargement
```

It states, for every measurable `A` with `0 < π.real A < 1` and every
`r > 0`,

```text
Φ(Φ⁻¹(π(A)) + sqrt(m) r) ≤ π(A^r),
```

where `A^r` is the open metric enlargement. The profile functions are
parameters. The paper uses the standard Gaussian CDF and lower quantile.

The sharp finite-Gaussian theorem is:

```lean
#check Concrete.bakryLedouxEnlargement_stdGaussian_finiteIndex
```

For every finite coordinate type `ι`, it proves curvature-one enlargement
for `stdGaussian (EuclideanSpace ℝ ι)`. The theorem does not ask its caller
for a Bobkov or isoperimetric certificate. Its proof formalizes the normal
profile, the Mehler Ornstein--Uhlenbeck semigroup, the nonnegative Bobkov
interpolation residual, endpoint closure, mollified distance ramps, Gaussian
perimeter, inverse-CDF comparison, and Radon inner approximation. The
zero-dimensional case is included.

For the normalized density proportional to `exp(-U)`, use:

```lean
#check DiscreteTime.target_bakryLedoux
```

It takes a `FirstOrderPotential d` and returns curvature-`m` enlargement of
its concrete target. A downstream user starting from actual Hessian bounds
can compose it with `HessianBoundedPotential.toFirstOrderPotential`.

The proof uses finite Gaussian innovation spaces and contractive Euler
endpoint maps, followed by an explicit weak-limit identification. It does
not depend on an SDE library or a continuous-time invariance theorem.

## Weak-limit stability of enlargement inequalities

Import:

```lean
import UniformRandomMALA.WeakLimitStability
```

The Gaussian-profile specialization is:

```lean
#check Concrete.bakryLedouxEnlargement_of_weakLimit
```

Suppose probability measures `μ n` converge weakly to `μ`, positive scale
coefficients `c n` converge to `c > 0`, and every approximation satisfies a
Gaussian-profile enlargement inequality with radius `r/(c n)`. Under the
stated regularity assumptions on the ambient Borel pseudometric space, the
limit satisfies the corresponding inequality with curvature `c⁻²`.

The more general profile theorem is:

```lean
#check Concrete.enlargement_profile_of_weakLimit
```

It works with an `ℝ≥0∞`-valued profile `J(mass,shift)` that is monotone in
mass and shift, continuous in mass, and lower-continuous at the relevant
profile boundary. Compact inner approximation and the open/closed
Portmanteau inequalities handle the moving set. No continuity-in-radius
hypothesis on enlargement masses is required.

## Lipschitz images and finite-Euler transfer

The map theorem

```lean
#check Concrete.enlargement_map_of_lipschitzWith
```

says that if `μ` satisfies a Bakry--Ledoux inequality and `F` is
`C`-Lipschitz with `C > 0`, then `Measure.map F μ` satisfies the same profile
with source radius `r/C`. This form is especially convenient when `C` varies
along an approximating sequence.

The higher-level theorem

```lean
#check Concrete.finiteEulerEndpointLimit_bakryLedoux
```

accepts positive mesh sizes tending to zero, stable Euler schemes with
`L² δ < 2m`, sharp enlargement of every finite Gaussian innovation space,
and weak convergence of the endpoint laws. It concludes curvature-`m`
Bakry--Ledoux enlargement of the limit. The endpoint map has checked squared
sensitivity

```text
2 / (2m - L²δ),
```

which converges to `1/m`. The theorem can therefore be reused with a different
weak-limit identification.

## Gaussian Bobkov interpolation

Import:

```lean
import UniformRandomMALA.GaussianBobkov
```

The concrete functional result used for enlargement is:

```lean
#check Concrete.gaussianRampMollified_bobkov
```

It proves the closed-profile Gaussian Bobkov inequality for each smooth
mollification of a distance ramp. The reusable local constructor is:

```lean
#check Concrete.gaussianBobkovSmoothInterpolation_of_boundedThirdJet
```

For an interior-valued bounded function on finite-dimensional Euclidean
space, it accepts bounded continuous first, Riesz-Hessian, and third
derivative fields with their Fréchet derivative identities. It constructs
the time-dependent Mehler interpolation and proves the residual identity and
nonnegativity rather than assuming them.

The closure API is:

```lean
#check Concrete.gaussianBobkov_local_of_smoothInterpolation
#check Concrete.gaussianBobkov_functional_of_local
#check Concrete.gaussianBobkov_functionalClosed_of_truncations
#check Concrete.gaussianBobkov_functionalClosed_of_localTruncations
```

The package currently exposes the unconditional production theorem for the
mollified distance ramps used in isoperimetry. It does not claim a single
theorem for every abstract smooth `[0,1]`-valued function under only a
`ContDiff` hypothesis; the more general constructor intentionally exposes a
bounded-third-jet interface.

## Explicit smooth hard potential for fixed-step MALA

Import:

```lean
import UniformRandomMALA.Concrete.FixedStepHardPotential
```

The potential is defined literally as

```text
U_{d,h}(x) = (m/2)x₀²
  + ∑_{i≠0} [(L+m)xᵢ²/4 - (L-m)h cos(xᵢ/sqrt h)/2].
```

The module provides:

```lean
#check Concrete.contDiff_infty_fixedStepHardPotential
#check Concrete.gradient_fixedStepHardPotential
#check Concrete.iteratedFDeriv_two_fixedStepHardPotential
#check Concrete.fixedStepHardPotential_hessian_lower
#check Concrete.fixedStepHardPotential_hessian_upper
#check Concrete.fixedStepHardHessianPotential
#check Concrete.fixedStepHardFirstOrderPotential
```

Thus the witness is `C^∞`, its gradient is computed from the derivative, and
its second Fréchet derivative is a diagonal quadratic form with curvature in
`[m,L]`. The final packaging uses the general Hessian bridge; it does not
weaken the smoothness statement to a first-order certificate.

## Gaussian trigonometric concentration

Import:

```lean
import UniformRandomMALA.Concrete.GaussianTrigonometricConcentration
```

For

```text
A(v) = cos v - 1 + (v sin v)/2,
V ~ N(0,2),
```

the module proves:

```lean
#check Concrete.integral_cos_gaussianReal_zero_two
#check Concrete.integral_mul_sin_gaussianReal_zero_two
#check Concrete.integral_gaussianTrigonometricIncrement
#check Concrete.integral_gaussianTrigonometricIncrement_neg
```

These give `E cos V = exp(-1)`, `E[V sin V] = 2 exp(-1)`, and
`E A(V) = 2/e - 1 < 0`.

Rather than relying on an abstract sub-Gaussian-norm/MGF equivalence, the
proof establishes the elementary envelope

```text
|A(v)| ≤ 2 + |v|/2,
```

deduces integrability of `exp(t A(V))` for every real `t`, and uses
differentiability of the MGF at zero to choose a fixed `t > 0` with MGF less
than one. The finite-product API is:

```lean
#check Concrete.finite_iid_sum_nonnegative_le_mgf_pow
#check Concrete.independent_gaussianTrigonometric_sum_nonnegative_le_mgf_pow
#check Concrete.
  exists_contraction_factor_for_independent_gaussianTrigonometric_sum
```

The last theorem produces universal `t > 0` and `0 ≤ ρ < 1` such that the
probability of a nonnegative sum of independent variance-two Gaussian
increments is at most `ρ` to the number of coordinates.

## Negative-threshold Gaussian product concentration

Import:

```lean
import UniformRandomMALA.Concrete.HardPotentialShiftedConcentration
```

The sticky argument needs a bound at a negative linear threshold, not merely
at zero. The module defines

```text
δ = hardAcceptanceDrift = (1-2/e)/2 > 0
A_shift(v) = A(v) + δ.
```

Since `E A(V) = -2δ`, the shifted increment still has exact mean `-δ`.
The relevant declarations are:

```lean
#check Concrete.hardAcceptanceDrift_pos
#check Concrete.integral_halfShiftedGaussianTrigonometricIncrement
#check Concrete.exists_pos_mgf_halfShiftedGaussianTrigonometricIncrement_lt_one
#check Concrete.
  independent_gaussianTrigonometric_sum_ge_negativeDrift_le_mgf_pow
#check Concrete.
  exists_universal_contraction_factor_for_pi_scaledGaussian_tail
```

The last theorem chooses one pair `t>0`, `0≤ρ<1` for all finite dimensions
and proves, for the non-first coordinates of a product standard Gaussian,

```text
P(-δ n ≤ ∑_{j=1}^n A(sqrt(2) Z_j)) ≤ ρ^n.
```

The proof again uses a direct fixed-parameter Chernoff argument. No general
equivalence between sub-Gaussian norms and MGF estimates is assumed.

## Local and sticky obstructions for the hard potential

Imports:

```lean
import UniformRandomMALA.Concrete.HardPotentialLocalObstruction
import UniformRandomMALA.Concrete.HardPotentialStickyObstruction
import UniformRandomMALA.Concrete.FixedStepHardPotentialObstruction
```

The local branch proves that the first marginal of the hard target is
`N(0,m⁻¹)`. With `f(x)=x₀`, the Metropolis step has no more coordinate energy
than its Gaussian proposal, giving:

```lean
#check Concrete.fixedStepHardTarget_map_firstCoordinate
#check Concrete.fixedStepHardFirstCoordinate_evariance
#check Concrete.fixedStepHardMALA_rayleighSpectralGap_le_local
```

The endpoint is

```text
Gap(P_h) ≤ mh + (mh)²/2.
```

For the sticky branch, `hard_malaLogRatio_zero_at_piInnovation_le` combines
the exact Hastings-ratio algebra with the oscillatory sum. Splitting the mean
acceptance over the negative-threshold exceptional event gives:

```lean
#check Concrete.fixedStepHard_malaAcceptanceProfile_zero_le_mgf_pow
#check Concrete.exists_universal_fixedStepHard_sticky_rayleighSpectralGap_upper
```

One universal `ρ<1` works for every dimension and every admissible `m,L,h`;
the sticky gap is bounded by

```text
4 [ρ^(d-1) + exp(-((L-m)/2) h δ (d-1))].
```

The generic two-branch package is:

```lean
#check Concrete.exists_universal_fixedStepHardPotential_raw_obstruction
#check Concrete.exists_universal_fixedStepHardPotential_obstruction_allDimensions
```

The second theorem chooses a universal `c>0` and, for every `d≥2`, proves

```text
Gap(P_h) ≤ 8 min(
  mh + (mh)²/2,
  exp(-c(d-1) min((L-m)h,1))).
```

This theorem concerns one explicit witness potential. The next section
inserts that witness into the full smooth potential class and optimizes over
the step size.

## Complete-lattice minimax definitions and scalar optimization

Import:

```lean
import UniformRandomMALA.Concrete.FixedStepMinimax
```

The class and minimax quantities are literal complete-lattice definitions:

```lean
#check Concrete.smoothHessianPotentialGapValues
#check Concrete.fixedStepWorstPotentialGap
#check Concrete.fixedStepMinimaxGap
```

`smoothHessianPotentialGapValues d m L h` consists of Rayleigh gaps attained
by potentials `V` satisfying all of the following:

- `V` is a `HessianBoundedPotential d`, so its actual second Fréchet
  derivative is bounded between `mI` and `LI`;
- the stored constants are exactly `V.m = m` and `V.L = L`;
- `V.U` is `ContDiff ℝ ⊤`;
- the target and fixed-step MALA kernel are constructed from
  `V.toFirstOrderPotential`, hence from the genuine Riesz gradient.

`fixedStepWorstPotentialGap d m L h` is the `sInf` of this set.
`fixedStepMinimaxGap d m L` is the `iSup` of those infima over the subtype of
all real `h>0`. The explicit hard witness is inserted by:

```lean
#check Concrete.fixedStepHardPotential_mem_smoothHessianPotentialGapValues
#check Concrete.fixedStepWorstPotentialGap_le_hardWitness
```

`Concrete/FixedStepObstructionOptimization.lean` isolates reusable scalar
facts. `exists_exponential_compression_rate` compresses a geometric term and
an exponential penalty into `2 exp(-c n min(s,1))`.
`fixedStepTwoBranchEnvelope_le_log_max_exp` balances the local and sticky
branches, and `iSup_fixedStepTwoBranchEnvelope_le_log_max_exp` carries the
bound through an extended-valued supremum over all nonnegative step
parameters.

The final endpoints are:

```lean
#check Concrete.exists_universal_fixedStepMinimaxGap_explicit_upper
#check Concrete.exists_universal_fixedStepMinimaxGap_paper_upper
```

The paper-form theorem states:

```text
∃ c>0, ∀ κ₀>1, ∃ C(κ₀)>0,
  ∀ d≥2, 0<m<L, κ₀≤L/m,
  sup_{h>0} inf_{U∈C∞, mI≤D²U≤LI} Gap(P_{U,h})
    ≤ C(κ₀) max(log((L/m)d)/((L/m)d), exp(-c d)).
```

The rate `c` is universal. Once that rate is fixed, the multiplicative
constant `C` depends only on the cutoff `κ₀`, not on the dimension,
curvatures, potential, or step size.

## Other probability infrastructure

The following declarations may also be useful independently:

- `DiscreteTime.centeredRNDeriv_memLp_of_weakLimit` transfers centered
  Radon--Nikodym `Lᵖ` control when numerator and reference measures both vary
  weakly;
- `Kernel.parameterMixture_isMarkovKernel` and
  `Kernel.isReversible_parameterMixture` construct measurable mixtures and
  preserve Markovness and reversibility;
- `Dirichlet.energy_parameterMixture` computes the energy of a parameter
  mixture;
- the reversible edge-measure, coarea, layer-cake, median, and truncation
  lemmas below `Concrete/ComponentAggregation*.lean` form a reusable toolkit
  for conductance-to-Poincaré arguments in extended-real measure theory.

## Minimal audit example

```lean
import UniformRandomMALA.AllResults

open UniformRandomMALA

#check Concrete.HessianBoundedPotential.toFirstOrderPotential
#check Concrete.l2SpectralGap_eq_rayleighSpectralGap
#check Concrete.rayleighSpectralGap_halfLazyKernel
#check Concrete.fractionalAggregation_poincareLower
#check Concrete.bakryLedouxEnlargement_stdGaussian_finiteIndex
#check DiscreteTime.target_bakryLedoux
#check Concrete.exists_universal_fixedStepMinimaxGap_paper_upper

#print axioms Concrete.fractionalAggregation_poincareLower
#print axioms DiscreteTime.target_bakryLedoux
#print axioms Concrete.exists_universal_fixedStepMinimaxGap_paper_upper
```

Compile the file with `lake env lean YourExample.lean`. When minimizing
dependencies, import the narrow module named at the start of the relevant
section instead of `AllResults`.
