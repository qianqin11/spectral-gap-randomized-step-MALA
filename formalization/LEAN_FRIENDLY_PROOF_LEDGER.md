# Archival development ledger for MALA local overlap

Last updated during development: 2026-08-28

> **Reader note.** This is a chronological engineering record, not the
> current package guide. It preserves intermediate proof plans, provisional
> names, and status language from the construction of the moment-indexed
> local-overlap result (`prop:overlap`, Proposition 3.2 in the included paper
> draft). Some items described below as “planned” were subsequently completed.
> For current status, use `README.md`, `PROOF_STRATEGY_LEDGER.md`, and
> `MALA_OVERLAP_FORMALIZATION.md`.

An item marked **checked** had a compiled theorem at the point recorded. An
item marked **planned** records the design at that historical point and must
not be read as a current project obligation.

## 1. Moving-reference likelihood bound - checked

### Mathematical statement

Let `mu n` and `nu n` be probability measures on a Borel pseudometric space,
converging weakly to `muLimit` and `nuLimit`.  Let `p >= 2`, `q >= 1`, and

```text
1 / p + 1 / q = 1.
```

Suppose that for every bounded continuous real function `f` and every `n`,

```text
|integral f d(mu n) - integral f d(nu n)|
  <= C * (integral |f|^q d(nu n))^(1/q).
```

If `C >= 0`, then `muLimit << nuLimit`, and, with

```text
u = d(muLimit)/d(nuLimit) - 1,
```

one has `u in L^p(nuLimit)` and

```text
(integral |u|^p d(nuLimit))^(1/p) <= C.
```

The compiled endpoint is

```lean
UniformRandomMALA.DiscreteTime.centeredRNDeriv_memLp_of_weakLimit
```

in `UniformRandomMALA/DiscreteTime/MovingReference.lean`.

### Lean-friendly proof

1. For a fixed bounded continuous `f`, weak convergence transfers
   `integral f`.  The function `|f|^q` is again bounded continuous, so weak
   convergence also transfers its integral and hence its `q`-root.  Taking
   limits in the finite-`n` inequality gives the same inequality for
   `muLimit` and `nuLimit` on bounded continuous tests.

2. To extend the inequality to a measurable test `phi` in
   `L^q(muLimit + nuLimit)`, approximate `phi` by bounded continuous `g n` in
   that single `L^q` space.  Monotonicity of `eLpNorm` under measure
   domination gives convergence in both `L^q(muLimit)` and `L^q(nuLimit)`.
   Since both measures are probabilities and `q >= 1`, this also gives the
   two `L^1` convergences needed for the linear integrals.  Continuity of the
   norm in Mathlib's ordinary `Lp` space gives convergence of the right-hand
   `L^q(nuLimit)` scale.

   This simultaneous approximation is the key simplification.  It avoids
   both a Lusin theorem with uniform bounds and surjectivity of the duality
   map `(L^q)* = L^p`.

3. Apply the measurable-test inequality to the indicator of a measurable
   `nuLimit`-null set.  Its right-hand norm is zero, so its `muLimit` mass is
   zero.  Thus `muLimit << nuLimit`.

4. Set `F = d(muLimit)/d(nuLimit)` and `u = F - 1`.  For `R >= 0`, use the
   bounded measurable test

   ```text
   phi_R = u * |u|^(p-2) * 1_{|u| <= R}.
   ```

   This form is preferable to `sign(u) * |u|^(p-1)`: when `p >= 2`, all its
   operations are continuous except the explicitly measurable truncation.
   It is bounded by `R^(p-1)`, hence belongs to every finite-measure `L^q`.

5. The Radon--Nikodym integral identity and elementary pointwise algebra give

   ```text
   integral phi_R d(muLimit) - integral phi_R d(nuLimit)
     = A_R,

   integral |phi_R|^q d(nuLimit) = A_R,

   A_R = integral |u|^p * 1_{|u| <= R} d(nuLimit).
   ```

   The second identity uses `(p - 1) * q = p`.  Therefore

   ```text
   A_R <= C * A_R^(1/q),
   ```

   and the conjugate-exponent calculation gives `A_R^(1/p) <= C`, including
   the separate zero case so no illegal division occurs.

6. Take `R = n` and let `n` tend to infinity.  The truncated nonnegative
   integrands increase pointwise to `|u|^p`.  Monotone convergence, applied
   to their `ENNReal.ofReal` forms, gives a finite full `p`-moment bounded by
   `C^p`.  The definition of `MemLp` then gives `u in L^p`, and taking the
   `p`-root recovers the bound by `C`.

### Supporting checked declarations

- `boundedContinuous_integral_tendsto`
- `boundedContinuous_integral_abs_rpow_tendsto`
- `boundedContinuous_holder_bound_of_weakLimit`
- `exists_boundedContinuous_eLpNorm_approximants`
- `exists_boundedContinuous_integral_approximants`
- `holder_bound_of_memLp`
- `absolutelyContinuous_of_boundedContinuous_holder`
- `truncatedDualPower`
- `mul_truncatedDualPower`
- `abs_truncatedDualPower_rpow`
- `truncated_rnDeriv_moment_bound`
- `full_rnDeriv_moment_bound`
- `centeredRNDeriv_memLp_of_weakLimit`

### Finite density input and the moving-reference wrapper - checked

`UniformRandomMALA/DiscreteTime/DensityTestHolder.lean` now supplies the
finite step that was previously only implicit.  If

```text
mu = nu.withDensity (ofReal F),
```

`F` is measurable and nonnegative, and `F - 1` has `L^p(nu)` root at most
`C`, then Hölder gives, for every bounded continuous `f`,

```text
|integral f dmu - integral f dnu|
  <= C * (integral |f|^q dnu)^(1/q).
```

The compiled declarations are
`boundedContinuous_holder_of_withDensity_memLp` and
`boundedContinuous_holder_of_withDensity_moment`.  The second version asks
explicitly for integrability of `|F-1|^p`.  This is not bookkeeping noise:
Mathlib defines the Bochner integral of a nonintegrable function to be zero,
so a bare inequality between real integral values cannot safely serve as an
`L^p` hypothesis.

`UniformRandomMALA/DiscreteTime/MovingDensityClosure.lean` packages the
whole moving-reference composition.  The theorem
`rnDeriv_memLp_of_moving_withDensity` takes a constant probability `mu`,
references `nu n -> sigma`, exact finite density identities, and uniform
centered moment/root bounds.  It returns

```text
mu << sigma,
sigma.withDensity (rnDeriv mu sigma) = mu,
toReal (rnDeriv mu sigma) - 1 in L^p(sigma),
||toReal (rnDeriv mu sigma) - 1||_p <= C.
```

Thus the abstract varying-reference analytic closure is fully checked.  The
concrete finite density family and its paper-scale uniform moment bound are
now supplied by the endpoint and full-path assembly recorded below.

## 2. Probability averaging by scalar Jensen - checked

For a probability measure `rho`, a nonnegative integrable real function `f`,
and `p >= 1`, convexity of `x |-> x^p` gives

```text
(integral f d rho)^p <= integral f^p d rho.
```

The compiled theorem is

```lean
UniformRandomMALA.DiscreteTime.rpow_integral_le_integral_rpow
```

in `UniformRandomMALA/DiscreteTime/Averaging.lean`.  This scalar statement is
the intended replacement whenever the paper invokes Minkowski only to show
that probability averaging contracts a moment.  It should be applied
pointwise and then integrated, rather than formalizing a more general
Bochner-valued Minkowski theorem.

## 3. Paper-scale likelihood and endpoint contraction - checked

The finite-product likelihood is contracted to the endpoint likelihood by
disintegrating the joint law with respect to the retained endpoint and
applying scalar Jensen on each conditional fiber.  No conditional-expectation
API is used.  The generic compiled theorem is

```lean
UniformRandomMALA.DiscreteTime.integral_centered_rnDeriv_fst_rpow_le
```

in `UniformRandomMALA/DiscreteTime/EndpointContraction.lean`.  Its hypotheses
are the standard Borel/countable-generation assumptions needed by Mathlib's
disintegration theorem.  The forgotten coordinate may be an arbitrary
finite path coordinate.

The quantitative full-path input is now unconditional and checked in
`Concrete/FiniteEulerRealMoments.lean`.  The theorem
`finiteGaussianDRec_centered_rpow_root_le_paper_scale` proves, under

```text
n * delta = h,
L * h <= 1,
256 * e^2 * L^2 * h^2 * p * (d + p) <= 1,
```

that `|D-1|^p` is integrable and

```text
(integral |D-1|^p)^(1/p)
  <= 1024 * e^3 * L * h * sqrt(p * (d+p)).
```

`Concrete/FiniteEulerEndpointContraction.lean` then transfers any such
full-path bound verbatim to the canonical endpoint Radon--Nikodym density in
`finiteFrozenLikelihoodEdge_rnDeriv_centered_rpow_integrable_and_root_le`.
Together with the concrete edge-law identifications in
`DiscreteTime/FiniteEulerEdgeBridge.lean`, this is exactly the finite
real-valued density moment required by the moving-reference theorem.  Thus
both the paper-scale moment coarsening and endpoint data-processing steps are
complete.

## 4. Finite Gaussian likelihood - explicit finite product checked

Three formerly missing primitives now compile.

1. `UniformRandomMALA/DiscreteTime/GaussianMGF.lean` proves the exact
   finite-dimensional identity

   ```text
   E exp(t L(Z)) = exp(t^2 ||L||^2 / 2)
   ```

   and the exact powered moment of the normalized one-step Gaussian shift
   likelihood.

2. `UniformRandomMALA/DiscreteTime/FiniteProduct.lean` defines a recursive
   finite-kernel product moment and proves by induction that a one-step
   Lyapunov estimate `T_p W <= B W` propagates to
   `T_p^n W <= B^n W`.

3. `UniformRandomMALA/DiscreteTime/KernelAveraging.lean` proves the
   fiberwise Jensen/Fubini inequality needed when one coordinate is averaged
   by a probability kernel.

The application-specific construction is now checked in
`UniformRandomMALA/DiscreteTime/FiniteGaussianLikelihood.lean`.
It defines the Euler recursion on the literal finite innovation space
`Fin n → State d`, proves measurability of every state and of the whole path,
and defines the adapted shifts `theta`, their sums `M`, `V`, and
`D = exp(M - V/2)`.

For normalization, the likelihood is also written as a chronological
recursive product.  The identity

```text
integral D(x,z) d(pi stdGaussian)(z) = 1
```

is proved by induction after splitting `Fin (n+1)` into its zeroth coordinate
and tail with `piFinSuccAbove`.  Each induction step is ordinary Tonelli plus
the one-step Gaussian square-completion identity.  The theorem
`integral_finiteGaussianDRec_initial` further integrates the initial state
against an arbitrary probability measure, so normalization is fully
unconditioned and uses no filtration or conditional expectation.

The same file defines `finiteEulerEnergy` and proves the checked deterministic
bridge

```text
finiteEulerV ≤ (L^2 / 2) * finiteEulerEnergy.
```

The quantitative likelihood bridge is also checked.  The elementary
pointwise Young inequality

```text
D_1^2 ≤ (D_4 + exp(6 V))/2
```

together with exact normalization at exponents `1` and `4` gives, from
`E exp(3 L^2 J) ≤ B`,

```text
E (D-1)^2 ≤ (B-1)/2,
E |D-1| ≤ eta + (B-1)/(8 eta),
P(|D-1| ≥ r) ≤ (B-1)/(2 r^2).
```

These are the compiled theorems
`finiteGaussianDRec_centered_sq_integrable_and_integral_le_of_energy_exp`,
`finiteGaussianDRec_centered_abs_integrable_and_integral_le_of_energy_exp`,
and `finiteGaussianDRec_centered_tail_le_of_energy_exp`.  Their only analytic
hypothesis is the explicit energy exponential moment now supplied in exact
product form by `FiniteEulerEnergyMGF.lean`.

The chronological and path-indexed energies have now been identified by the
checked theorem `finiteEulerEnergyRec_initial_eq_finiteEulerEnergy`.
Consequently `Concrete/FiniteEulerLikelihoodBounds.lean` composes the
likelihood theorem with the explicit energy MGF without any residual
integrability hypothesis.  Under

    192 * exp(1)^2 * L^2 * h^2 <= 1

and (ndelta=h), it proves concrete centered (L^2), (L^1), and tail
bounds with

    B = exp(192 * exp(1)^2 * L^2 * h^2 * d).

For the low-moment fallback, the same module now linearizes (B-1) under
the dimension-aware condition

    192 * exp(1)^2 * L^2 * h^2 * d <= 1.

It proves the explicit checked estimates

    E (D-1)^2 <= 96 * exp(1)^3 * L^2 * h^2 * d,
    P(|D-1| >= t) <= 96 * exp(1)^3 * L^2 * h^2 * d / t^2,
    E |D-1| <= 8 * exp(1)^2 * L * h * sqrt(d).

These do not replace the real-(p) estimate in Proposition 3.2, but they
are useful end-to-end tests of the finite energy/likelihood composition and
give unconditional quantitative control at (p=1,2).

The finite tilted-law identity is now structurally checked.  The
one-coordinate theorem
`stdGaussian_withDensity_finiteGaussianStepLikelihood` identifies the
weighted Gaussian coordinate with its translate.  The triangular map
`finiteCenteredInnovations` then subtracts each adapted shift using only
earlier uncentered coordinates.  A literal Tonelli induction proves
`lintegral_finiteGaussianLikelihoodRec_centered`; its pushforward
corollaries
`map_finiteCenteredInnovations_likelihood_withDensity`,
`map_finiteEulerEndpointRec_likelihood_withDensity`, and
`map_finiteEulerEndpointRec_DRec_withDensity` identify the weighted Euler
endpoint with the frozen-drift recursion.  Finally,
`finiteFrozenEndpointRec_initial_eq_closedForm` evaluates that recursion as
the initial point minus (ndelta) times the frozen gradient plus the finite
Gaussian sum.

The last representation equality is now checked in
`DiscreteTime/FiniteGaussianEndpointLaw.lean`.  The finite sum of independent
standard Gaussian vectors is identified by characteristic functions,
`finiteFrozenEndpointRec_initial_eq_closedForm` supplies the affine formula,
and `map_finiteEulerTiltedEdge_eq_compProd_gaussianDensityProposal` proves the
fully unconditioned measure identity

    tilted finite Euler edge = target(dx) Q_h(x,dy)

whenever `(n : Real) * delta = h`.  This is an equality of explicit finite
pushforward measures, not an invocation of finite-dimensional Girsanov.

The generic MGF-to-real-moment infrastructure for this last estimate is now
checked in `DiscreteTime/ElementaryMGFTail.lean`.  A
`TwoSidedMGFBound` supplies ordinary integral bounds for
(exp(pm sX)) on a finite interval.  The module proves Chernoff bounds and,
more importantly for formalization, bypasses layer-cake integration using
the pointwise calculus estimate

    |x|^r <= (r / s)^r * exp(s * |x|).

The optimized theorem
`TwoSidedMGFBound.realMomentRoot_le_subgamma_scale` gives

    (E |X|^r)^(1/r)
      <= 2 * A * exp(1) * (sqrt(B*r) + r/s0)

from `E exp(±sX) <= A exp(B*s^2)` for `0 <= s <= s0`.
This is exactly the scalar tool needed for (M_{h,n}); no layer-cake,
stopping-time, or abstract (L^p) infrastructure remains at that point.

The application is now checked in
`Concrete/FiniteEulerRealMoments.lean`.  It derives the two-sided MGF

    E exp(a * M)
      <= exp(64 * exp(1)^2 * L^2 * h^2 * d * a^2)

through a single Young inequality, exact normalization of the likelihood at
parameter `2*a`, and the finite Euler energy MGF.  The theorem
`finiteGaussianMRec_twoSidedMGFBound` packages this for both signs, and
`finiteGaussianMRec_realMomentRoot_le` applies the elementary optimizer to
obtain a real-order moment bound.  The same module proves real-order moment
bounds for the path energy and for the recursive compensator `V`, again
from a single exponential moment and a pointwise power/exponential
inequality.  It now also proves the powered-likelihood estimate
`finiteGaussianDRec_rpow_integrable_and_integral_le`, the uniform
`L^(2p)` root bound `finiteGaussianDRec_two_p_root_le`, and the final scalar
Cauchy--Schwarz assembly
`finiteGaussianDRec_centered_rpow_root_le_of_moments`.  The latter uses only

    |exp(w)-1| <= (1+exp(w))*|w|

and two applications of the elementary two-term powered-sum inequality.
Thus the full real-`p` centered likelihood is structurally checked.  The
explicit MGF parameter choices and coarsening to the universal paper scale
are now checked by
`finiteGaussianDRec_centered_rpow_root_le_paper_scale`, as recorded in
Section 3.

`Concrete/FiniteEulerEndpointContraction.lean` now instantiates the generic
data-processing theorem without conditional expectation: it embeds a finite
joint sample as `(edge,sample)`, contracts the RN moment along the first
projection, and erases the auxiliary sample.  The same file proves that its
tilted edge is the frozen-drift edge and provides both the earlier `p=2`
endpoint test and the general real-`p` endpoint contraction used by the final
assembly.

The identification between the likelihood construction and the coupling
construction is checked in
`DiscreteTime/FiniteEulerEdgeBridge.lean`.  A finite Tonelli induction proves
that the explicit `Fin n` Euler recursion has the same endpoint law as the
finite iterate of the Euler kernel, hence

```text
finiteEulerLikelihoodEdgeLaw = finiteEulerEdgeMeasure.
```

Under `(n : Real) * delta = h`, the likelihood-tilted edge is exactly the
stationary concrete MALA proposal edge.  The module proves its absolute
continuity with respect to the finite Euler edge and reconstructs it using
both the canonical `rnDeriv` and the existing finite endpoint density.  In
particular,

```text
target ⊗ gaussianDensityProposal h
  = finiteEulerEdgeMeasure.withDensity
      (ofReal (toReal finiteEulerLikelihoodEndpointRNDensity)).
```

The density appearing in the checked finite likelihood moment estimates is
therefore literally the real-valued density required by the moving-reference
wrapper; no conditional expectation or endpoint-density choice remains.

## 5. Metropolis meet and rejection marginal - checked

`UniformRandomMALA/DiscreteTime/MetropolisMeet.lean` proves the density-level
accepted-flow meet estimate with respect to a swap-invariant reference and
then disintegrates to the rejection marginal.  It uses the elementary bound

```text
(a + b)^p <= 2^(p-1) (a^p + b^p)
```

instead of importing an abstract `L^p` Minkowski theorem.  The compiled final
declaration is

```lean
UniformRandomMALA.DiscreteTime.integral_rejectionMarginal_rpow_le
```

Thus the general measure-theoretic meet/marginal block is complete; only the
identification of the paper's concrete limiting endpoint density with the
arguments of this theorem remains.

The common-reference issue is now fully elementary and checked.
`DiscreteTime/MeasureMeet.lean` proves `withDensity_min_invariant` by
splitting each measurable-set integral over `{f <= g}` and its complement.
`Concrete/MALAAcceptedMeet.lean` first proves the concrete MALA accepted-flow
identity relative to product Lebesgue measure and then transports the
pointwise minimum to any swap-invariant RN reference.  Its endpoint is
`malaAcceptedEdge_eq_rnMeet`.

`Concrete/MALAMetropolisMeet.lean` supplies the concrete downstream wrapper.
A `MALAProposalMeetCertificate` now records only a symmetric probability
reference, its target marginals, a nonnegative measurable proposal RN
density, and the centered moment bound.  It contains no accepted-meet or
rejection-identification hypothesis.  The file derives the concrete
target-a.e. rejection marginal by disintegration and subtraction.  The
checked theorem
`stationaryMALARejectionMomentBound_of_meetCertificates` converts a family
of such endpoint certificates directly into the sole hypothesis of
`Concrete/MALAOverlapFromRejection.lean`, with the correct factor two in the
stationary rejection bound.  Therefore this block has no remaining
measure-theoretic meet obstacle.

## 6. Euler/RWM one-step coupling - checked

### Exact Gaussian cancellation

`UniformRandomMALA/DiscreteTime/GaussianPositivePart.lean` proves, by
Gaussian sign symmetry plus the covariance identity,

```text
E[Z max(L Z, 0)] = (1/2) Riesz(L),
E[s max(<g,s>,0)] = delta g,  s = sqrt(2 delta) Z.
```

This replaces the informal Gaussian integration-by-parts line in the paper.

### Acceptance expansion

`UniformRandomMALA/DiscreteTime/AcceptanceExpansion.lean` proves globally

```text
|rho(u) - q_+| <= |u-q| + (|q| + |u-q|)^2,
rho(u) = 1 - min(1, exp(-u)).
```

The constant in front of the quadratic remainder is deliberately coarse;
the proof splits `u <= 1` and `u >= 1`, so it needs no probabilistic Taylor
theorem.  Polynomial simplification lemmas for the scaled first and second
moments are also checked.

### Concrete potential and moment bounds

`UniformRandomMALA/Concrete/RWMExpansion.lean` proves the exact smoothness
sandwich

```text
0 <= U(x+s)-U(x)-<grad U(x),s> <= (L/2)||s||^2,
```

defines the actual one-step RWM rejected displacement, and proves:

```text
E_Z[rho(U(x+s)-U(x)) s]
  = delta grad U(x) + E_Z[explicit error],

||E_Z[explicit error]||
  <= (sqrt(2 delta))^3 * an explicit finite Gaussian-moment polynomial,

E_Z[rho(U(x+s)-U(x)) ||s||^2]
  <= (sqrt(2 delta))^3 * an explicit finite Gaussian-moment polynomial.
```

`UniformRandomMALA/DiscreteTime/BernoulliUniform.lean` constructs a Bernoulli
decision from a unit-interval coordinate and proves its exact vector mean and
second moment.  The concrete file then checks the corresponding iterated
Gaussian--uniform integrals.  Consequently the local conditional bias and
variance estimates are no longer an interface.

The already checked recursion lemmas in
`UniformRandomMALA/DiscreteTime/Recursion.lean` convert an affine one-step
mean-square recursion into the required fixed-horizon `sqrt(delta)` endpoint
error.

## 7. Finite Euler energy estimate - deterministic and Gaussian blocks checked

The target-centering input is also checked in
`UniformRandomMALA/Concrete/PotentialCentering.lean`.  It constructs a global
minimizer without importing a convex-optimization framework, proves the
gradient vanishes there by one descent step, and establishes

```text
||gradU(x)||^2 <= 2 L (U(x)-U(x_star)),
E_target exp(s (U(X)-U(x_star))) <= (1-s)^(-d),  0 <= s < 1.
```

The final declarations are `gradU_norm_sq_le_potentialGap`,
`integral_exp_potentialGap_le`, `integral_exp_gradU_norm_sq_le`, and
`integrable_gradU_norm_fourth`.  The third theorem is the exact target MGF
needed for the frozen-gradient term of the Euler energy, while the fourth
closes the finite fourth-gradient-moment input needed when the local Euler/RWM
coupling is averaged under stationarity.  These results use only convexity,
translation, positive scalar change of variables for Lebesgue measure,
normalization of the target, and the elementary second Taylor term of the
exponential.

The maximal-process route has been removed.  Let

```text
a_k = ||X_k-X_0||,
b_k = ||-k delta gradU(X_0) + sqrt(2) S_k||,
S_k = sqrt(delta) * sum_{j<=k} Z_j.
```

The Euler recursion gives the scalar Volterra inequality

```text
a_k <= b_k + L delta * sum_{j<k} a_j.
```

The new file `UniformRandomMALA/DiscreteTime/FiniteEnergy.lean` proves two
fully finite alternatives.

1. Under `L*h <= 1/2`, Cauchy--Schwarz gives

   ```text
   delta * sum_k (delta * sum_{j<k} a_j)^2
     <= h^2 * delta * sum_k a_k^2,
   ```

   and absorption yields the clean factor-four bound.

2. Under the paper's full hypothesis `L*h <= 1`, an explicit convolution
   formula and a finite Schur estimate give

   ```text
   delta * sum_{k<n} a_k^2
     <= 8 * exp(1)^2 * h^3 * G^2
        + 16 * exp(1)^2 * delta * sum_{k<n} s_k^2.
   ```

The principal checked declarations are:

- `cumulative_sum_sq_energy_le`;
- `finite_energy_absorption`;
- `frozen_forcing_energy_le`;
- `finite_euler_path_energy_le`;
- `finite_euler_path_energy_le_full_horizon`;
- `euler_deviation_le_of_telescoping`.

Thus no filtration, conditional expectation, Doob inequality, reflection
principle, or maximum of a Gaussian walk is needed.

The complementary finite Gaussian block is checked in
`UniformRandomMALA/DiscreteTime/GaussianMaximum.lean`:

- `integral_exp_mul_sq_gaussianReal` proves the one-dimensional quadratic
  Gaussian integral;
- `integral_exp_mul_norm_sq_stdGaussian` and its scaled form prove the exact
  finite-dimensional radial MGF;
- `map_finsetSum_eq_map_sqrt_card_smul_stdGaussian` proves the law of a finite
  sum of independent standard Gaussians by characteristic functions;
- `map_sqrt_smul_finsetSum_eq_scaled_stdGaussian` adds the `sqrt(delta)`
  scaling;
- `integral_exp_norm_sq_sqrt_smul_finsetSum` gives the exact partial-sum MGF;
- `integral_exp_mul_step_sum_norm_sq_le_of_scaledGaussian_marginals` is the
  finite-grid Jensen step.

The application-level composition is now checked in
`UniformRandomMALA/Concrete/FiniteEulerEnergyMGF.lean`.  Its theorem
`integral_exp_finiteEulerEnergy_le` combines the deterministic path estimate,
target gradient-square MGF, finite partial-sum Gaussian MGF, and product
factorization into one explicit bound.  With `A = 8 exp(1)^2 h^3` and
`B = 16 exp(1)^2`, the right side is the target factor

```text
(1 - 2 L lambda A)^(-d)
```

times the finite Jensen average of exact Gaussian quadratic-MGF factors.
Its assumptions are explicit scalar positivity/smallness inequalities only.
Thus the previously identified "finite Euler maximal estimate" and its
product-space exponential moment are no longer infrastructure obstacles.
The exact factors have also been coarsened in the paper-readable theorem
`integral_exp_finiteEulerEnergy_le_exp`.  It assumes

    64 * exp(1)^2 * lambda * h^2 <= 1

and proves

    E exp(lambda * finiteEulerEnergy)
      <= exp(64 * exp(1)^2 * lambda * h^2 * d).

The companion theorem `integrable_exp_finiteEulerEnergy` discharges the
actual Bochner-integrability hypothesis under the same assumptions.  This
distinction matters in Lean: a numerical integral bound alone cannot be used
where the likelihood argument asks for `Integrable`.

The independence/factorization part of that composition is checked in
`UniformRandomMALA/DiscreteTime/ProductEnergyMGF.lean`.  Its theorem
`integral_exp_productEnergy_le` says that a pathwise bound

```text
J(x,z) <= A f(x) + B g(z)
```

under the explicit product measure `mu.prod nu` gives the product of the two
one-coordinate MGFs.  This replaces all abstract independence and conditional
expectation bookkeeping in the energy estimate by ordinary Fubini.

## 8. Gaussian map-versus-density bridge - checked

`UniformRandomMALA/DiscreteTime/GaussianLawBridge.lean` proves the exact
identity between the innovation and Lebesgue-density descriptions.  The proof
computes both characteristic functions using Mathlib's finite-dimensional
Gaussian Fourier integral, proves equality at zero by
`Measure.ext_of_charFun`, and transfers it to arbitrary means by translation.

The checked application declarations are:

- `randomWalkProposal_eq_map_stdGaussian`;
- `gaussianDensityProposal_apply_eq_randomWalkProposal`;
- `gaussianProposal_apply_eq_map_stdGaussian`;
- `gaussianProposal_eq_gaussianDensityProposal`;
- `gaussianDensityProposal_eq_randomWalkProposal`;
- `gaussianDensityProposal_eq_map_stdGaussian`.

This removes the representation boundary that formerly separated the
explicit Gaussian/uniform coupling from the already constructed density-based
RWM and MALA kernels.

There is now a second, independent bypass in
`UniformRandomMALA/DiscreteTime/ExplicitRWMBalance.lean`.  It defines the RWM
proposal directly as the pushforward of a standard Gaussian, proves symmetry
of the accepted edge flow by the finite coordinate involution

```text
(x,z) |-> (x + sqrt(2 delta) z, -z),
```

and then proves `explicitRWMKernel_isReversible`,
`explicitRWMKernel_isMarkovKernel`, and `explicitRWMKernel_invariant`.
Consequently the coupling proof can use an explicit innovation kernel and
stationarity without going through a Gaussian density at all; the checked
map-versus-density bridge remains available later for identification with the
paper's existing concrete kernel.

## 9. Finite pair chain and weak-limit closure - checked plumbing

`UniformRandomMALA/DiscreteTime/EulerRWMPairChain.lean` now constructs the
shared standard-Gaussian/unit-uniform update as an actual Markov kernel.  The
RWM coordinate uses the rejection-threshold form, and a pointwise theorem
identifies it with the `bernoulliRWMRejectedIncrement` used by the earlier
expansion estimates.  The file proves:

- the exact Gaussian--uniform pushforward formula for `explicitRWMKernel`;
- the second marginal of one pair step;
- the second marginal after an arbitrary finite kernel iterate; and
- stationarity of every finite RWM iterate under the concrete target.

It also proves the exact unit-interval measure of threshold disagreement, a
common-uniform tail bound, and the same-start identity

```text
Euler - RWM = rejectedIncrement - delta * gradU.
```

After integrating the uniform coordinate, the squared discrepancy is bounded
by the already checked RWM rejection second-moment integrand plus the explicit
gradient term.  The outer Gaussian and stationary-target integrations are now
also checked.  The theorem
`target_iteratedIntegral_norm_explicitEuler_sub_rwm_sq_le` gives the literal
product-integral estimate

    E ||Euler(x,z) - RWM(x,z,u)||^2
      <= (sqrt(2*delta))^3 * C_V
           + 2 * delta^2 * E_target ||gradU||^2,

with `C_V` an explicit polynomial in finite Gaussian norm moments and the
first two target gradient moments.  All measurability and integrability
requirements in this statement are discharged.  The remaining pair-chain
estimate is therefore the unequal-start recurrence and its finite iteration,
not another Gaussian/uniform integration.

`DiscreteTime/EulerRWMRecurrence.lean` now proves the unequal-start
one-step recurrence itself.  It expands the Gaussian--uniform integral
exactly, isolates the vector bias, uses cocoercive contraction, and applies
Young only to the cross term.  Its theorem
`integral_pairOneStepSquaredDistance_le` says that for any current pair law
whose RWM marginal is the target,

    E distance_next^2
      <= (1 + delta) * E distance_current^2
           + stationaryEulerRWMRecurrenceError(delta).

All local error terms are integrated explicitly and are finite.
`DiscreteTime/EulerRWMFiniteRecurrence.lean` lifts the estimate to the actual
finite pair-chain law started from the diagonal target measure, proves that
the RWM second marginal stays stationary, and iterates the affine recurrence.
`DiscreteTime/EulerRWMVanishingStep.lean` then bounds the stationary local
error by

    C_V * delta * sqrt(delta)

and obtains

    E ||X_n-Y_n||^2 <= C_V * h * sqrt(delta) * exp(h)

when `n*delta=h`.  In particular,
`tendsto_stationaryEulerRWMPairChain_energy_fixedHorizon` proves convergence
to zero for the explicit sequence `delta_n=h/(n+1)`, `steps_n=n+1`.

The general tightness/weak-limit part is now checked in
`UniformRandomMALA/DiscreteTime/ProkhorovBridge.lean`.  In particular it
proves:

- tightness of joint laws from tight first and second marginals, including
  the fixed-probability-marginal case;
- `levyProkhorovEDist_le_of_coupling_lintegral_sq_le_cube`, converting a
  squared endpoint coupling bound to Levy--Prokhorov distance by a single
  Markov inequality;
- preservation of first marginal, second marginal, and swap invariance under
  weak convergence; and
- `exists_tendsto_subseq_of_tight_marginals`, an actual sequential
  Prokhorov extraction obtained through Mathlib's Levy--Prokhorov
  homeomorphism.

Thus no new topology or compactness infrastructure is needed.

`UniformRandomMALA/DiscreteTime/CouplingClosure.lean` now records the exact
Portmanteau form needed at the limit: fixed marginals and distance-tail bounds
pass to a weak limit with arbitrary threshold slack.  It also records
probability-one support on a closed relation.  A same-threshold upper bound on
a closed set is deliberately *not* asserted: it is false in general (for
example, `delta_(1/n) → delta_0` and the closed set `{0}`).  This makes the
small threshold enlargement in the elementary limit proof explicit.
The composition theorem
`weak_limit_symmetric_coupling_of_fixed_marginals_with_sq_control` packages
fixed first and second marginals, swap symmetry, the threshold-slack tail,
and the resulting Levy--Prokhorov bound.  Its only limit hypothesis is the
selected weak convergence itself; the existing Prokhorov extraction theorem
supplies that hypothesis once the concrete finite endpoint laws are inserted.

The concrete edge laws are now constructed in
`DiscreteTime/EulerRWMEdgeCoupling.lean`.  Crucially, this wrapper retains
the common initial point: it constructs a law of
`(x0,(Xn,Yn))` and pushes it forward to a literal coupling of the two edge
laws `(x0,Xn)` and `(x0,Yn)`.  Both marginal identities are checked.  The
RWM edge law has both marginals equal to the target, and
`exists_tendsto_subseq_finiteRWMEdgeLaw` gives a concrete Prokhorov
subsequence for arbitrary vanishing step sizes and iteration counts.
Swap invariance of every finite RWM edge is also checked: the module proves
reversibility of finite kernel iterates by an elementary commuting-kernel
induction and then converts detailed balance to
`map Prod.swap eta = eta`.  Finally, the retained-edge squared-distance
integral is proved equal to the terminal pair-chain norm-squared integral,
and
`levyProkhorovEDist_finiteEulerEdgeMeasure_finiteRWMEdgeMeasure_le`
turns any terminal second-moment estimate directly into the required
edge-law Levy--Prokhorov bound.  The module additionally proves that weak
convergence transfers across vanishing Levy--Prokhorov distance and packages
a common subsequence of RWM and Euler edge laws with one common limit.  The
one-shot theorem
`exists_common_tendsto_subseq_finiteEulerEdgeLaw_finiteRWMEdgeLaw_with_structure`
also records swap invariance and both target marginals of that limit.  The
coupling integration needed by this wrapper is now checked as well.

`DiscreteTime/EulerRWMEdgeVanishing.lean` proves that forgetting the retained
initial point recovers the stationary pair-chain law and that the retained
`ENNReal` squared-distance cost is exactly `ofReal` of the compiled real
pair-chain energy.  To avoid an eventual-only small-step statement, it uses
the offset schedule

```text
delta_n = h / (n + N),       steps_n = n + N,
```

with an elementary Archimedean choice of `N`.  The schedule has exact horizon
`steps_n * delta_n = h`.  A strictly positive `epsilon_n -> 0` is constructed
so that the retained cost is at most `epsilon_n^3` at every index.  The final
compiled theorem
`exists_common_tendsto_subseq_fixedHorizonEulerRWMEdgeLaws_with_structure`
then returns one subsequence along which the finite Euler and finite RWM edge
laws converge to the same `sigma`, together with

```text
map swap sigma = sigma,
sigma.fst = target,
sigma.snd = target.
```

Consequently the fixed-horizon vanishing-cost, Prokhorov extraction, common
subsequence, symmetry, and marginal package is complete.  No coupling or
weak-topology lemma remains pending in this block.

## 10. Proposition 3.2 assembly - unconditional theorem checked

The numerical assembly and abstract interfaces compile.  The leanest
unconditional statement should first use setwise total variation:

```text
forall measurable A, |K x A - K y A| <= c.
```

Only after the setwise inequalities are proved should total variation be
packaged as their supremum.  This avoids building signed-measure Jordan
decomposition infrastructure that the proposition does not use.

All six Appendix B.4 inputs and their final numerical assembly are now
concrete and checked.

1. the averaged-rejection good-set estimate, using the already checked scalar
   Jensen theorem followed by Markov;
2. proposal-mean nonexpansiveness from the checked Baillon--Haddad estimate;
3. a specific equal-covariance Gaussian proposal TV bound through Hellinger
   affinity, without KL/Pinsker;
4. the elementary bound `|P_h(x,A)-Q_h(x,A)| <= r_h(x)` for every measurable
   set `A`;
5. convexity of that setwise discrepancy under the dyadic step-size mixture;
   and
6. a global safe acceptance bound from the exact log-ratio identity and the
   checked Gaussian quadratic MGF.

`UniformRandomMALA/DiscreteTime/RejectionGoodSet.lean` checks item 1 at the
correct level of generality.  From a product-space (p)-moment bound for a
nonnegative rejection function, it constructs a measurable good set, proves
that the step-averaged rejection is at most (1/3) there, and bounds the
exceptional mass by ((3B)^p).  The final corollary is
`exists_averagedRejection_goodSet_one_third`.  Thus this stage needs no
Minkowski theorem, conditional expectation, or separate Markov API.  Its
concrete stationary rejection `L^p` input is now supplied by the compiled
finite-likelihood/weak-limit chain below.

The concrete specialization is checked in
`Concrete/MALARejectionGoodSet.lean`, including joint measurability in the
step size and state and bounded integrability of the rejection mass.
`exists_dyadicMALARejection_goodSet_one_third` assumes only a uniform
fixed-step (p)-moment bound on (hin(t/2,t]).  Finally,
`Concrete/MALALocalOverlap.lean` performs the entire accept/reject triangle
under the dyadic parameter measure and proves

    1/3 + 1/32 + 1/3 = 67/96 < 3/4.

Its endpoint `exists_dyadicMALALocalOverlap_goodSet` packages the measurable
good set, exceptional mass, and actual `setwiseTV <= 3/4`.  Its uniform
fixed-step stationary rejection moment hypothesis is discharged by
`stationaryMALARejectionMomentBound_paperScale` below.

`Concrete/MALAOverlapFromRejection.lean` makes this boundary literal.  The predicate
`StationaryMALARejectionMomentBound cr Cr` is the exact fixed-step input, and
`proposition32_of_stationaryMALARejectionMomentBound` proves both clauses of
Proposition 3.2, including the paper's exceptional-mass expression.  The
predicate is now proved unconditionally with explicit constants.

The generic weak-limit-to-rejection assembly is checked in
`Concrete/MALAWeakLimitAssembly.lean`.  Its theorem
`stationaryMALARejectionMomentBound_of_moving_reference_family` accepts, for
each admissible `(p,h)`, a finite reference sequence `nu n`, exact real
densities of the fixed MALA proposal edge, uniform centered moment bounds,
and a weak limit with swap symmetry and target marginals.  It applies
`rnDeriv_memLp_of_moving_withDensity` with the canonical conjugate exponent
and then invokes the already checked MALA meet theorem.  The result is the
full predicate `StationaryMALARejectionMomentBound cr Cr`.

The concrete instantiation is checked in
`Concrete/MALAFullPathAssembly.lean`.  The theorem
`stationaryMALARejectionMomentBound_of_fixedHorizonOffsetFullPath` internally
chooses the offset fixed-horizon schedule, extracts the structured common
Euler/RWM subsequence, identifies the finite Euler endpoint density, contracts
the full-path moment to that endpoint, applies the moving-reference closure,
and finishes with the Metropolis meet.  The theorem
`fixedHorizonOffsetFullPathMomentBound_paperScale` supplies its sole numerical
hypothesis from the paper-scale finite Gaussian estimate, with

```text
cr = 1 / (16 * e),
Cr = 6144 * e^3.
```

Here the full-path density constant is `1024 * e^3`; the factor six is the
endpoint/meet budget encoded by the downstream certificate.  The compiled
endpoint is
`stationaryMALARejectionMomentBound_paperScale`.

Finally, `Concrete/MALAOverlapBounds.lean` names these constants as
`proposition32CrSmall` and `proposition32CrLarge`, proves their required sign
and size facts, and exposes the unconditional theorem

```lean
UniformRandomMALA.Concrete.FirstOrderPotential.proposition32_discreteTime
```

The exact compiled chain is:

1. `finiteGaussianDRec_centered_rpow_root_le_paper_scale`;
2. `fixedHorizonOffsetFullPathMomentBound_paperScale`;
3. `stationaryMALARejectionMomentBound_of_fixedHorizonOffsetFullPath` and
   `stationaryMALARejectionMomentBound_paperScale`;
4. `stationaryMALARejectionMomentBound_proposition32`; and
5. `proposition32_discreteTime`.

The final theorem gives both Proposition 3.2 clauses: the measurable local
good set with the explicit exceptional-mass bound and `setwiseTV <= 3/4`, and
the unconditional global `setwiseTV <= 3/4` clause under
`t <= 1 / (2 * L * d)`.  Proposition 3.2 is therefore fully formalized by
the discrete-time route.

For completeness, the remaining global-clause ingredients used by this final
theorem are also concrete.  Proposal nonexpansiveness is checked in
`UniformRandomMALA/Concrete/Cocoercivity.lean`.  The file derives the
one-sided Bregman lower bound and gradient cocoercivity directly from one
upper-Taylor and one lower-Taylor estimate, then proves

```text
||(x-h gradU(x))-(y-h gradU(y))|| <= ||x-y||,  0 <= h <= 2/L.
```

No abstract convex-analysis Baillon--Haddad theorem is imported.

`UniformRandomMALA/Concrete/GaussianProposalTV.lean` evaluates the exact
equal-covariance Gaussian Hellinger affinity and proves the paper-ready
setwise proposal bound `1/32` when `t/2 ≤ h`, `h ≤ 2/L`, and
`||x-y|| ≤ sqrt(t)/16`.

`UniformRandomMALA/Concrete/SafeAcceptance.lean` rewrites the exact MALA
log-ratio at a Gaussian innovation and proves globally, for `h ≤ 1/L`,

```text
acceptanceMass(x) ≥ (1 + L h)^(-d/2) ≥ exp(-L h d / 2).
```

`UniformRandomMALA/DiscreteTime/SetwiseAcceptReject.lean` decomposes proposal
mass on a set into accepted and rejected proposal mass and proves the generic
setwise rejection comparison.  Finally,
`UniformRandomMALA/Concrete/MALASetwiseTV.lean` combines the three terms and
integrates them over the explicit dyadic step law.  The checked endpoint is

```text
abs_dyadicMALA_apply_toReal_sub_le_three_quarters
```

under `0<t≤1/(2Ld)` and the paper's distance condition, for every measurable
set.  In fact the proof gives the stronger constant `17/32`.  Thus the
global “moreover” clause of Proposition 3.2 is unconditional.  Mathlib does
not provide the paper's probability-measure convention as a ready-made
distance, so `Concrete/SetwiseTV.lean` defines the lightweight supremum

    setwiseTV mu nu =
      sSup {|mu.real A - nu.real A| : A measurable}

and proves the generic setwise-to-supremum bridge.  The final compiled theorem
is `setwiseTV_dyadicMALA_le_three_quarters`, with the stronger intermediate
bound `17/32`.  This avoids irrelevant signed-measure/Jordan infrastructure
while still formalizing the literal total-variation conclusion.

## 11. Feasibility assessment - formalization achieved

The feasibility question is now answered affirmatively: the unconditional
discrete-time formalization of Proposition 3.2 has been achieved.  The
compiled theorem `proposition32_discreteTime` includes both the local good-set
clause and the global total-variation clause, with explicit constants

```text
cr = 1 / (16e),
Cr = 6144 e^3.
```

Every mathematical block that had been identified as a possible
infrastructure obstacle is discharged in Lean:

- finite Gaussian likelihood normalization and real-`p` moments;
- endpoint likelihood contraction;
- the concrete Euler-edge/RN-density identification;
- the Euler/RWM pair recurrence and fixed-horizon vanishing cost;
- Levy--Prokhorov subsequence extraction and transfer of symmetry/marginals;
- the finite density-to-test Hölder inequality and moving-reference RN
  closure;
- the MALA meet and stationary rejection estimate; and
- the rejection good set and setwise total-variation assembly.

The resulting proof is genuinely discrete time.  It uses finite products,
finite kernel iteration, elementary integral inequalities, and weak
convergence of probability measures.  It does not use Euler--Maruyama
convergence, Ethier--Kurtz, an SDE, continuous-time stochastic calculus,
Doob/BDG, or a diffusion approximation.  This confirms that the elementary
route is amenable to Lean formalization, rather than merely suggesting that
it might be.

There is no remaining mathematical obligation for Proposition 3.2.  Future
work is engineering and maintenance only:

1. expose the final module through the preferred project import surface and
   keep the full dependency build green;
2. refactor repeated measure/kernel conversion lemmas and stabilize names as
   the paper's numbering changes;
3. run dependency and declaration audits, documentation checks, and theorem
   statement comparisons against later paper revisions; and
4. optionally sharpen the deliberately generous constants without changing
   the proof architecture.

## 12. Paper-wide component aggregation - routine infrastructure implemented

Status: **source-complete, compiler recheck pending**.  The declarations in
this section contain no `sorry` or `admit`, but they were added in a runtime
where the Lean executable cannot resolve its own application path.  They must
not be relabelled **checked** until `lake build` succeeds in an unrestricted
Lean process.  The earlier Proposition 3.2 modules retain their previous
checked status.

### Concrete interface replacement

The abstract `KernelObjects` interface stores arbitrary real-valued `mass`,
`flow`, `dirichlet`, and `spectralGap` functions.  That statement is useful
for paper assembly, but is too weak for a formal proof: it does not say that
sets are measurable, that kernels are Markov, or that flow and energy are the
actual Mathlib integrals.

The new aggregation modules therefore use the existing concrete objects
directly:

```lean
π : Measure α
K : Fin N → Kernel α α
boundaryFlow π (K j) A : ℝ≥0∞
Dirichlet.energy π (K j) f : ℝ≥0∞
Concrete.spectralGap π P : ℝ≥0∞
```

All set hypotheses now include `MeasurableSet`; all function hypotheses
include `Measurable`; every component has `IsMarkovKernel`; reversibility is
`Kernel.IsReversible`; and infinite values remain visible in `ℝ≥0∞`.

### Quantile and measurable median

`Concrete/Quantile.lean` defines

```lean
lowerQuantile μ u = sInf {x | u ≤ cdf μ x}
```

and proves the Galois equivalence

```text
lowerQuantile μ u ≤ x  iff  u ≤ cdf μ x,       0 < u < 1.
```

The easy implication is the defining property of `sInf`; the converse uses
only right-continuity of the CDF.  `Concrete/Median.lean` applies this at
`u=1/2` to the pushforward `π.map f`.  The upper strict tail is controlled by
`1-F(q)`.  The lower strict tail is controlled by `leftLim F q`: every
`y<q` has `F(y)<1/2`, so `leftLim F q≤1/2`; Mathlib's Stieltjes formula then
identifies this left limit with the mass of `Iio q`.  This correctly handles
atoms at the median.

The resulting endpoint is

```lean
exists_isMedian (π : Measure α) [IsProbabilityMeasure π]
  (f : α → ℝ) (hf : Measurable f) :
  ∃ b, IsMedian π f b
```

where `IsMedian` records both strict-tail `ℝ≥0∞` bounds.

### Extended variance without an `L²` side condition

`Concrete/Variance.lean` proves

```text
evariance f π ≤ ∫⁻ x, ofReal ((f x-b)^2) ∂π
```

for every measurable `f`, not merely `f∈L²`.  The proof first establishes
shift invariance of `evariance`.  In the `L²` case this follows by converting
to ordinary variance; in the non-`L²` case both shifted and unshifted
extended variances are `∞`.  Mathlib's identity

```text
evariance g π = (∫⁻ ‖g‖ₑ² dπ) - ofReal ((∫g dπ)²)
```

then gives the second-moment upper bound by `tsub_le_self`.  This explicit
case split is necessary because `PoincareLower` quantifies over all
measurable functions.

### Layer cake and median parts

`Concrete/LayerCake.lean` specializes Mathlib's layer-cake theorem to
`g²` and the project's strict squared superlevels.  The only conversion is
from `(0,∞)` to `[0,∞)`, using that Lebesgue measure has no atom at zero.

`Concrete/MedianDecomposition.lean` lifts the previously checked scalar
arithmetic to measures and kernels:

```text
∫(f-b)² = ∫((f-b)⁺)² + ∫((f-b)⁻)²,

E_K((f-b)⁺) + E_K((f-b)⁻) ≤ E_K(f).
```

It also proves that every positive squared superlevel of either median part
has mass at most `1/2`.  The energy inequality is a pointwise application of
`median_parts_edge_energy` under the concrete stationary edge measure.

### Coarea--Cauchy--Schwarz block

`Concrete/Conductance.lean` now exposes three reusable facts that had been
implicit in the earlier coarea proof:

1. integration against the first edge marginal equals integration under
   `π`;
2. reversibility gives the same identity for the second edge marginal; and
3. `∫(g(x)+g(y))² dQ ≤ 4∫g² dπ`.

It also proves measurability of
`r ↦ boundaryFlow π K (sqSuperlevel g r)` by writing it as the measure of a
measurable section.

`Concrete/CoareaCauchySchwarz.lean` then proves, in extended values,

```text
∫₀∞ boundaryFlow π K {g²>r} dr
  ≤ 1/2 * (2 E_K(g))^(1/2) * (4 ∫g² dπ)^(1/2).
```

The proof factors `|a²-b²|`, applies Mathlib's ENNReal Hölder theorem with
exponents `(2,2)`, identifies the difference factor with twice the
Dirichlet energy, and bounds the sum factor by the two edge marginals.

### Avoiding measurable finite selection

The most important proof rewrite is in `Concrete/ComponentFlow.lean`.
Suppose every small measurable cut `S` has *some* successful component:

```text
∃ j, φ_j π(S) ≤ Q_j(S,Sᶜ).
```

Rather than choosing `j=j(r)` for the superlevel `S_r`, use the pointwise
inequality

```text
π(S_r) ≤ ∑ j φ_j⁻¹ Q_j(S_r,S_rᶜ).
```

The successful summand proves the inequality and every other summand is
nonnegative.  Finite-sum linearity then gives

```text
∫π(S_r)dr ≤ ∑ j φ_j⁻¹ ∫Q_j(S_r,S_rᶜ)dr.
```

Thus there is no measurable-selection theorem, no tie-breaking definition,
and no partition of the level axis.  `Concrete/ComponentAggregation.lean`
combines this estimate with layer cake and the componentwise coarea bound,
first for any nonnegative small-support function and then for both parts of
an actual median.

### Aggregation arithmetic subsequently closed

The finite-dimensional ENNReal arithmetic described below has now been
implemented in `Concrete/ComponentArithmetic.lean` and connected to bounded
truncations in `Concrete/ComponentAggregationFinal.lean`.  The original
planned reduction was: for each median part, rewrite the component sum in
the form

```text
sqrt(2 I) * ∑ j sqrt(E_j) / φ_j
```

and apply weighted Cauchy--Schwarz:

```text
(∑ j sqrt(E_j)/φ_j)^2
  ≤ (∑ j γ_j E_j) * (∑ j 1/(γ_j φ_j²)).
```

The audit exposed an important correction to that plan: there is no valid
“infinity case” in which one cancels an infinite second moment.  The proof
must first cap the median part, cancel its finite squared moment, and only
then use monotone convergence.  Section 13 records the implemented proof.

## 13. Component aggregation closure by bounded caps - checked

Status: **kernel-checked**.  The declarations contain no `sorry`, `admit`,
or project-specific axiom.

### Why a direct ENNReal cancellation is invalid

The raw coarea inequality for a nonnegative median part has the schematic
form

```text
I <= sqrt(I) * sqrt(E * H).
```

If `I=∞`, this inequality can be true without implying `I <= E*H`; one may
not cancel `sqrt(I)` in `ℝ≥0∞`.  This is not merely a Lean API inconvenience.
It is a genuine gap in an over-compressed extended-valued proof.

The formalization-friendly repair is to define

```text
g_n(x) = min(g(x), n).
```

Every `I_n = ∫ g_n² dπ` is finite on a probability space.  Apply coarea and
cancel at level `n`, obtain a bound independent of `n`, and then take the
supremum.

### Truncation infrastructure

`Concrete/Truncation.lean` implements the following elementary statements.

1. `capAt R g = min g R` is measurable when `g` is measurable.
2. For nonnegative `g`, every natural cap is nonnegative and bounded by its
   cap level.
3. Capping contracts edge increments:

   ```text
   (min(a,R)-min(b,R))² <= (a-b)².
   ```

   This follows from the scalar min-contraction inequality for absolute
   differences, followed by squaring.  Integrating pointwise gives

   ```text
   E_K(min(g,R)) <= E_K(g).
   ```

4. Pointwise, a nonnegative scalar is recovered exactly from its natural
   caps:

   ```text
   sup_n ofReal(min(a,n)²) = ofReal(a²).
   ```

   The proof avoids topology: every cap is at most `a`, and the Archimedean
   property supplies one natural `n >= a`, where the cap equals `a`.
5. Mathlib's `lintegral_iSup` then gives the exact monotone-convergence
   identity

   ```text
   ∫ g² dπ = sup_n ∫ min(g,n)² dπ.
   ```

The main declarations are `energy_capAt_le`,
`lintegral_sq_eq_iSup_lintegral_sq_capAt_nat`, and
`lintegral_sq_capAt_nat_ne_top`.

### Harmonic weighted Cauchy--Schwarz without square-root division

A direct substitution with factors `sqrt(γ_j)` creates unnecessary
square-root cancellation.  `Concrete/ComponentArithmetic.lean` instead uses
Mathlib's weighted Hölder theorem with

```text
w_j = 1 / (γ_j φ_j²),
F_j = γ_j φ_j sqrt(E_j).
```

Two finite-denominator identities give

```text
w_j F_j    = sqrt(E_j) / φ_j,
w_j F_j²   = γ_j E_j.
```

Weighted Hölder at exponent two therefore yields directly

```text
sum_j sqrt(E_j)/φ_j
  <= sqrt(sum_j γ_j E_j) * sqrt(sum_j 1/(γ_j φ_j²)).
```

This is `weighted_sqrt_sum_le`.  It avoids introducing `sqrt(γ_j)⁻¹`
altogether and reduces the denominator algebra to ordinary finite products.

### Safe square-root cancellation

`le_of_le_rpow_half_self_mul` proves

```text
I != ∞  and  I <= sqrt(I*C)  imply  I <= C.
```

The proof separates `I=0`.  Otherwise it squares the inequality, obtaining
`I*I <= I*C`, left-multiplies by `I⁻¹`, and uses the explicit nonzero and
non-top hypotheses in `ENNReal.inv_mul_cancel`.  Thus the theorem's type
prevents its use at infinity.

`coarea_component_sum_cancel` combines this cancellation with the raw
componentwise coarea estimate and `weighted_sqrt_sum_le`, producing

```text
I <= 2 * harmonicCost γ φ * E_total
```

for a finite `I` whenever `sum_j γ_j E_j <= E_total`.

### Concrete Poincare endpoint

`Concrete/ComponentAggregationFinal.lean` applies the preceding arithmetic
to every natural cap of a nonnegative small-support function.  Component
energy domination and cap contraction give

```text
sum_j γ_j E_{K_j}(g_n) <= E_P(g_n) <= E_P(g),
```

so the capped estimates have a common upper bound.  Taking their supremum
proves `lintegral_sq_le_two_harmonic_mul_energy`.

For an arbitrary measurable `f`, choose an actual median `b` and apply the
one-sided result to `(f-b)⁺` and `(f-b)⁻`.  Their supports have mass at most
one half, their squared moments sum to `∫(f-b)²`, and their energies sum to
at most `E_P(f)`.  The result is

```text
evariance f π <= 2 * harmonicCost γ φ * E_P(f).
```

Finally, for a nonempty component family, the harmonic cost is both nonzero
and finite.  Multiplication by its reciprocal is therefore legitimate.
`componentAggregation_poincareLower` records the resulting variational
inequality, and `Concrete.le_spectralGap` yields the endpoint

```lean
componentAggregation_le_spectralGap :
  ((2 : ℝ≥0∞) * harmonicCost γ φ)⁻¹ <= spectralGap π P
```

under the concrete Markov-kernel, reversibility, component-energy, and
small-cut flow hypotheses.  This removes measurable selection, implicit
`L²` assumptions, and invalid infinity cancellation from the aggregation
route.

## 14. Gaussian shift, separation, and defective conductance - checked

The Gaussian bridge after Bakry--Ledoux is now concrete.  The standard
Gaussian Mills bounds are proved by elementary integration estimates in
`Concrete/GaussianMills.lean`; inverse-CDF bookkeeping and the quantitative
shift bound are checked in `Concrete/Quantile.lean` and
`Concrete/StandardGaussianShift.lean`.  Consequently

```lean
separatedSets_of_bakryLedoux
```

derives the separated-set inequality from the single enlargement premise.
`Concrete/MALADefectiveConductance.lean` then instantiates the already
checked defective-conductance argument for the dyadic MALA kernels.  There
is no remaining Gaussian-shift, quantile, or defective-conductance interface
in the concrete chain.

## 15. Safe component from Bakry--Ledoux - checked

`Concrete/SafeComponent.lean` constructs the globally safe dyadic component,
proves its exact selection weight and conductance, invokes concrete component
aggregation, and obtains

```text
ofReal (m * t_safe^2 * log 2 / (2^28 * H))
  <= spectralGap(pi, uniformMALA(H)).
```

The compiled endpoint is

```lean
FirstOrderPotential.safe_spectralGap_lower_of_bakryLedoux
```

and its sole analytic premise is Bakry--Ledoux.

## 16. Ladder assignment and exceptional budget - checked

`Concrete/LadderComponents.lean` now contains the full finite component
construction.  For a cut of mass `q`, put `u=log(1/q)`.  The proof chooses
the least ladder index whose upper logarithmic endpoint reaches `u`; this
gives the lower-quarter and upper-half inequalities needed by the local
conductance estimate.  Cuts above the final band use the terminal globally
safe component.  This `Nat.find` construction is pointwise and finite, so no
measurable selection is introduced.

The exceptional budget is reduced to the endpoint comparison

```text
(theta/16)^p_j
  <= 2^-13 exp(-p_j/2) sqrt(m t_j p_j/2).
```

Monotonicity of `exp(-u) sqrt(u)` on `u >= 1/2` fills each logarithmic band.
The endpoint inequality is proved by taking logarithms and applying the
explicit coefficient-wise condition `ExceptionalBudgetParameterChoice`.
`Concrete/UniversalConstants.lean` subsequently chooses an explicit `A₀`
and proves this condition, so it is not part of the final trust boundary.

## 17. Elementary harmonic sum and concrete master theorem - checked

The remaining harmonic estimate was rewritten as finite real algebra.
For the initial component the exact summand is

```text
2^27 H L^2 pStar(d+pStar)
  / (m theta^2 b0^2 log 2),
```

and for every noninitial component it is

```text
2^30 H L^2 (d+p_j) / (m theta^2 b0^2).
```

The proof uses only

```text
p_J < 4d,       J <= pStar,       log 2 > 0.69.
```

Thus the entire harmonic cost is at most

```text
6 * 2^30 * H * L^2 * pStar * (d+pStar)
  / (m * theta^2 * b0^2).
```

This is `ladderHarmonicReal_le`; `ladder_harmonicCost_le` is its ENNReal
form.  Inverting twice the bound and applying concrete aggregation gives
`ladder_truncated_spectralGap_lower_of_bakryLedoux`.

`Concrete/GlobalFromBakryLedoux.lean` combines the safe and ladder estimates
by comparing the two certified scales.  `Concrete/UniversalConstants.lean`
fixes explicit positive values of `b₀`, `A₀`, and `c₀` and discharges every
numerical side condition.  The final compiled declaration is

```lean
FirstOrderPotential.universal_masterRHS_spectralGap_lower
```

It has no additional mathematical hypothesis apart from positivity of the
requested endpoint `H`.  All steps from
Proposition 3.2 through conductance, component aggregation, exceptional-set
assignment, harmonic summation, and the final min/max assembly are now
kernel-checked.

## 18. Bakry--Ledoux route analysis and elementary entrance - checked

The formerly remaining premise was compared along three proof routes.  The
important conclusion is that ordinary Gaussian log-Sobolev inequality is not
by itself a sufficient replacement.  Herbst's argument gives Gaussian
concentration, but applying it to a cutoff between two separated sets loses
the first-order small-distance scale.  It produces a bound of quadratic type

```text
q * m * r² * log(1/q),
```

whereas the completed conductance argument needs, up to universal constants,

```text
q * min(1, r * sqrt(m * log(1/q))).
```

Thus a successful route must retain the normal isoperimetric profile, not just
entropy dissipation.

### Common elementary entrance

`Concrete/BakryLedouxReduction.lean` introduces

```lean
gaussianResidual V x := V.U x - (V.m / 2) * ‖x‖^2
gaussianResidualGrad V x := V.gradU x - V.m • x.
```

Using only the already recorded lower Taylor inequality, the file proves

```lean
gaussianResidual_firstOrderConvex :
  FirstOrderConvexCertificate V.gaussianResidual V.gaussianResidualGrad
```

and the exact factorization

```text
exp(-U(x)) = exp(-(m/2)‖x‖²) * exp(-gaussianResidual(x)).
```

This is the hypothesis required by Bobkov's localization route, expressed
without Hessians or a differentiability-heavy convex-analysis interface.

The same file proves the strong monotonicity inequality

```text
m ‖x-y‖² <= <gradU(x)-gradU(y), x-y>
```

and the one-step Euler contraction

```text
‖(x-h gradU(x))-(y-h gradU(y))‖²
  <= (1 - 2mh + L²h²) ‖x-y‖²                 (h >= 0).
```

All four declarations are kernel-checked.  The last inequality is the entrance
to a third, discrete Gaussian-image route described below.

### Route A: Bobkov localization

Bobkov's proof has a genuinely Lean-friendly one-dimensional core:

1. Scale to `m=1` and write the measure as a log-concave perturbation of the
   standard Gaussian.
2. In one dimension, let `T = F_mu^{-1} o Phi` be monotone transport from the
   Gaussian to the target.
3. Prove `T` is one-Lipschitz.  Bobkov obtains the needed density comparison
   at a quantile from a supporting affine function to the residual convex
   potential, reducing the estimate to an exponentially tilted Gaussian.
4. A one-Lipschitz pushforward transfers Gaussian enlargement directly:
   `(T^{-1} A)_r` is contained in `T^{-1}(A_r)`.

This core uses ordered real analysis, quantiles, affine support, and elementary
Gaussian estimates.  Much of the scalar Gaussian and quantile infrastructure
already exists in this project.  It is a realistic medium-sized Lean task.

The obstacle is the Lovasz--Simonovits localization lemma needed to pass from
`R^d` to one-dimensional needles.  A self-contained formalization would need
at least:

* repeated hyperplane bisection/ham-sandwich separation;
* compact convex bodies and nested-limit arguments;
* the cone-volume limit that produces the affine needle weight
  `ell(t)^(d-1)`;
* preservation of log-concavity on the needle; and
* truncation plus lower-semicontinuous/measurable-set approximation.

Mathlib does not presently provide this localization package.  The needle
weight is benign once constructed: its logarithm is concave and combines with
the residual density to leave a one-dimensional strongly log-concave measure.
Constructing the needle is the difficult part.  Consequently, Bobkov's route
is feasible in principle, but it is not currently the shortest route to this
paper's theorem.  It would be attractive only if a reusable convex-geometric
localization library were itself a desired output.

Primary reference: S. G. Bobkov, *Localization Proof of the Bakry--Ledoux
Isoperimetric Inequality and Some Applications*, Theory Probab. Appl. 47
(2003), 308--314,
<https://epubs.siam.org/doi/abs/10.1137/TPRBAU000047000002000308000001>.

### Route B: target diffusion semigroup

The right analogue of the standard Gaussian LSI proof is not the entropy
identity.  Put

```text
I(s) = phi(Phi^{-1}(s)),     I(s) I''(s) = -1.
```

For the Langevin semigroup with generator

```text
L f = Delta f - <gradU, grad f>
```

and curvature at least `m`, the Bakry--Ledoux interpolation is

```text
sqrt(I(P_t f)^2 + alpha |grad P_t f|^2)
  <= P_t sqrt(I(f)^2 + c_alpha(t) |grad f|^2),

c_alpha(t) = (1-exp(-2mt))/m + alpha exp(-2mt).
```

Taking `alpha=1/m` and `t -> infinity` gives the functional Bobkov inequality

```text
sqrt(m) I(integral f dπ)
  <= integral sqrt(m I(f)^2 + |grad f|^2) dπ.
```

Distance cutoffs and integration of the resulting boundary-profile inequality
give the desired global enlargement statement.

This proof graph is coherent and highly reusable, but for the present project
it requires a large analytic block before the displayed interpolation can even
be stated unconditionally:

* construction, positivity, invariance, and ergodicity of the target Langevin
  semigroup;
* differentiation and chain rules for the semigroup;
* weighted integration by parts;
* the Bochner/`Gamma_2` identity and its curvature lower bound;
* smoothing of a merely `C^{1,1}` potential while preserving `m` and `L`;
* passage from smooth functions to distance cutoffs and from boundary measure
  to measurable-set enlargement.

The explicit Ornstein--Uhlenbeck architecture used for standard Gaussian LSI
does help with proof organization--invariance, derivative commutation,
monotonicity, and endpoint limits--but it cannot be copied directly to the
target: the Mehler formula disappears.  A source audit of Statlean's
`Gaussian/OrnsteinUhlenbeck.lean` found useful templates for the explicit
one-dimensional Gaussian steps, but no target Langevin semigroup or
Bakry--Ledoux normal-profile development.  The repository was not imported as
a dependency; any reused lemma will be locally rebuilt and kernel-audited.

Semigroup reference: D. Bakry and M. Ledoux, *Levy--Gromov's isoperimetric
inequality for an infinite dimensional diffusion generator*, Invent. Math.
123 (1996), 259--281, <https://doi.org/10.1007/s002220050026>.  A particularly
clear statement of the interpolation and its endpoint argument is S. Ohta,
*A semigroup approach to Finsler geometry: Bakry--Ledoux's isoperimetric
inequality*, <https://arxiv.org/abs/1602.00390>.

### Route C: finite Gaussian images and a discrete Langevin limit

This is now the recommended route.  It uses the Gaussian semigroup only where
it is explicit and keeps the target-side proof discrete.

For step size `h`, start at a deterministic point and iterate

```text
X_(k+1) = X_k - h gradU(X_k) + sqrt(2h) Z_(k+1),
```

where the `Z_j` form a finite standard Gaussian vector.  Put

```text
rho_h² = 1 - 2mh + L²h².
```

The checked one-step contraction implies, by a finite induction and
Cauchy--Schwarz, that the endpoint map

```text
(Z_1,...,Z_n) |-> X_n
```

is Lipschitz with squared constant at most

```text
C_(h,n)²
  = 2h * sum_(j=0)^(n-1) rho_h^(2j)
  <= (1-rho_h^(2n)) / (m-L²h/2).
```

Hence finite-dimensional Gaussian isoperimetry transfers to the Euler
endpoint law.  If `nh -> t` and `h -> 0`, then

```text
C_(h,n)² -> (1-exp(-2mt))/m.
```

Letting `t -> infinity` gives exactly `1/m`, hence the sharp shift
`sqrt(m) r` in Bakry--Ledoux.

At this planning stage the proof was organized as two explicit limits rather
than an abstract diffusion theorem:

1. Construct the fixed-time law as the limit of coupled finite Euler schemes.
2. Prove that the limiting transition preserves `π`.  For smooth compactly
   supported tests, expand one Euler step, divide by `h`, and use the elementary
   weighted integration-by-parts identity
   `integral (Delta f - <gradU,grad f>) dπ = 0`; then close by tightness.
3. Use the same synchronous-coupling contraction to show convergence of the
   fixed-time law to `π` as `t -> infinity`.
4. Pass enlargement through weak convergence first for closed inner
   approximations and open thickenings, then use Radon regularity for arbitrary
   measurable sets.

At that stage this route still had two substantial tasks: sharp Gaussian
isoperimetry and the discrete-limit stationarity argument.  It was better aligned
with the existing code than Routes A or B.  The project already contains
finite Gaussian product laws, Euler recursions, tightness/weak-limit tools,
target moment bounds, and extensive discrete coupling infrastructure.

For sharp Gaussian isoperimetry, adapt the explicit Gaussian OU proof to the
normal profile `I`, rather than importing Gaussian LSI as a black box.  The
Gaussian-only development needs Mehler invariance, derivative commutation,
the scalar identity `I I''=-1`, the functional Bobkov inequality, and the
cutoff-to-enlargement passage.  This is much narrower than constructing the
target diffusion semigroup.  The existing sorry-free Gaussian LSI development
at <https://github.com/YuanheZ/lean-stat-learning-theory> is useful for entropy,
integration, and approximation conventions, but its LSI theorem alone does
not supply the sharp isoperimetric profile.

### Decision

The implementation order is therefore:

1. finish the finite Euler endpoint Lipschitz theorem from the checked
   one-step contraction;
2. build sharp finite-dimensional Gaussian isoperimetry using the explicit OU
   normal-profile argument;
3. transfer enlargement to every Euler endpoint law;
4. build the two discrete limits and the weighted integration-by-parts
   stationarity certificate;
5. discharge `BakryLedouxEnlargement` for `V.target`.

The one-dimensional part of Bobkov localization remains a useful fallback and
may be formalized independently, but the Lovasz--Simonovits lemma is not on the
critical path.  The full target `Gamma_2` semigroup is also no longer on the
critical path.

## 19. Gaussian OU plus finite Langevin limits - proof audit and first code

**Completion note.** This section records the obstacle analysis that preceded
the final implementation.  The current code does not assume either SDE
convergence or a Fokker--Planck uniqueness theorem.  The obstacle described
below was subsequently bypassed by the explicit diagonal stationary
Euler--RWM coupling in `Concrete/FiniteEulerTargetIdentification.lean`; the
Gaussian OU certificate and finite-index transfer were completed in
`Concrete/GaussianOUCanonicalInterpolation.lean` and
`Concrete/GaussianRampCanonicalInterpolation.lean`.

The recommended Route C has now been written out in
`BAKRY_LEDOUX_DISCRETE_LANGEVIN_PROOF.md` and stress-tested at the two places
where an informal limit argument can easily be wrong.

### 19.1 Corrected analytic boundary

The route considered at that stage was a correct standard probabilistic proof,
but was not yet a purely discrete proof.  Finite Euler estimates determine concentration of
every fixed-time Langevin transition after passage to the mesh limit.  They
do **not**, by themselves, identify that limit or prove that its invariant
law is `exp(-U) dx`.

For that route, the missing implication had to be stated explicitly as one of:

```text
globally-Lipschitz Euler schemes converge strongly to the Langevin SDE,
and exp(-U) dx is invariant for that SDE;
```

or

```text
weak limits of invariant ULA laws solve L*mu=0,
and the probability solution of L*mu=0 is uniquely exp(-U) dx.
```

The second formulation sounds more discrete, but its uniqueness clause is
elliptic PDE or martingale-problem infrastructure in disguise.  Weighted
integration by parts only proves infinitesimal invariance; an additional core
or uniqueness theorem is required to deduce invariance of the transition
law.  The completed formalization uses neither formulation: it replaces
endpoint identification with a fully discrete diagonal coupling argument.

### 19.2 Weak convergence is used in the correct direction

Enlargement is stable under weak convergence, but not by applying
Portmanteau directly to the open output thickening.  The correct proof is:

1. choose a compact inner approximation `K subset A`;
2. use the open input `B=thickening epsilon K` so that
   `liminf mu_n(B) >= mu(B)`;
3. dominate `thickening s B` by the closed neighborhood
   `{x | dist(x,K) <= epsilon+s}`;
4. use Portmanteau's closed-set `limsup` inequality on that neighborhood;
5. send the mass error and the two radius errors to zero.

This open-input/closed-output sandwich is recorded as W1--W3 in the proof
document and will be a standalone Lean theorem.

### 19.3 Formalization-friendly coefficient simplification

`Concrete/FiniteEulerGaussianImage.lean` now contains a fully finite proof of
the innovation sensitivity bound.  In addition to the previously checked
one-step contraction, the following pieces compile:

```text
reverseGeometricAccum_eq_sum
reverseGeometricAccum_sq_le
reverseGeometricAccum_one_eq_geomSum
sum_reverse_pow_sq_eq_geomSum
finiteEulerState_innovationSensitivity
finiteEulerState_innovationSensitivity_sq
finiteEuler_geometricCoefficient_le
finiteEulerState_innovationSensitivity_sq_le
tendsto_finiteEulerSensitivityCoefficient_zero
tendsto_finiteEulerSensitivityCoefficient_fixedTime
eventually_finiteEuler_fixedTime_smallStep
sum_norm_euclideanInnovationBlocks_sub_sq
finiteEulerEuclideanEndpoint_sq_le
finiteEulerEuclideanEndpoint_lipschitzWith
```

The final finite estimate is

```text
|X_k(z)-X_k(w)|^2
 <= [2/(2m-L^2 delta)] * sum_(j<k)|z_j-w_j|^2,
```

valid when `delta>0` and `L^2 delta<2m`.  The proof uses the finite product
identity

```text
(sum_(j<k) q^j)(1-q)=1-q^k
```

rather than an infinite series.

For fixed physical time, it is unnecessary to retain the sharper factor
`1-rho^(2k)`.  The coarser coefficient satisfies

```text
2/(2m-L^2 T/(N+1)) -> 1/m.
```

This gives the sharp final Bakry--Ledoux constant and removes the separate
limit `rho_N^(2N)->exp(-2mT)` from the Lean dependency graph.

### 19.4 Radius-zero convention corrected

`BakryLedouxEnlargement` now assumes `r>0`, because Mathlib's open
`Metric.thickening 0 A` is empty.  The paper theorem is normally stated for
positive open-enlargement radius, or for nonnegative radius with a closed
enlargement.  The downstream separated-set argument already handles `r=0`
separately, so this is a representation correction and does not weaken any
paper consequence.

### 19.5 Completed declarations

The finite-dimensional innovation tuple is packaged as
`EuclideanSpace R (Fin N x Fin d)` and its block norm-square identity and
endpoint `LipschitzWith` theorem are checked.  The normal profile, Mehler
semigroup, canonical residual identity, bounded-third-jet interpolation
certificate, mollified-ramp Bobkov inequality, finite-index Gaussian
enlargement, and diagonal target transfer now compile.  The endpoint is
`DiscreteTime.target_bakryLedoux`; the unconditional paper-scale conclusion is
`Concrete.FirstOrderPotential.universal_masterRHS_spectralGap_lower`.
