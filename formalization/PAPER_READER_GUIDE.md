# Guide for readers of the paper

This guide connects the mathematical narrative of the August 2026 paper by
Qian Qin and Guanyang Wang, **A Global Spectral Gap for MALA with a Uniformly
Randomized Step Size**, to the Lean 4 source tree. The current paper is
`paper/main.pdf`, generated from `paper/main.tex`.

## The main claim

The paper studies the target

```text
pi(dx) proportional to exp(-U(x)) dx on R^d,
```

under `m I <= Hess U <= L I`, with condition number `kappa = L/m`. At each
step the algorithm samples `h` uniformly from `(0,H)` and applies one MALA
transition with proposal

```text
Y = x - h grad U(x) + sqrt(2h) Z,       Z standard Gaussian.
```

The paper's theorem `thm:main` says that there are universal constants
`A0,b0,c0 > 0` for which

```text
Gap(P_bar_H) >= c0 * (m/H) * min(H, certifiedScale)^2,

certifiedScale =
  (b0/L) * max(1/sqrt(pStar*(d+pStar)), 1/d),

pStar = A0 * (1 + log(d+1) + log(L/m)).
```

The exact checked non-lazy endpoint is

```lean
UniformRandomMALA.Concrete.exists_universal_nonlazy_paperMasterRHS_lower
```

in `Concrete/HessianMainTheorem.lean`. It starts from the paper's actual
`C²` Hessian hypotheses, uses the paper's `L²` Rayleigh spectral gap, and
chooses the universal constants before the dimension and potential. The
concrete lazy clause is
`exists_universal_lazy_paperMasterRHS_lower` in
`Concrete/LazyKernel.lean`.

The fixed-step minimax upper bound (Proposition 2.3), the fractional
aggregation lemma (Lemma 3.5), the all-parameter flow proposition
(Proposition 3.4), and both displays of Corollary 2.2 are also formalized.
The main lower-bound chain still uses `FirstOrderPotential` internally, but
`HessianBoundedPotential.toFirstOrderPotential` now proves the calculus
bridge from the manuscript assumptions.

## Translation of notation

| Paper notation | Lean representation | Where defined |
|---|---|---|
| `R^d` | `State d`, definitionally a finite Euclidean space | `Concrete/EuclideanTarget.lean` |
| paper's `U`, `m`, `L`, and Hessian bounds | fields of `HessianBoundedPotential d`; the Hessian is `iteratedFDeriv ℝ 2 U` | `Concrete/HessianToFirstOrder.lean` |
| derived `grad U` | mathlib's Riesz gradient, stored by `HessianBoundedPotential.toFirstOrderPotential` | `Concrete/HessianToFirstOrder.lean` |
| normalized `pi` | `V.target` | `Concrete/EuclideanTarget.lean` |
| fixed-step MALA `P_h` | `V.malaKernel h` | `Concrete/MALA.lean` |
| uniform mixture `P_bar_H` | `V.uniformMALA H hH` | `Concrete/MALAFamily.lean` |
| dyadic step-size component | `V.dyadicMALA t ht` | `Concrete/MALAFamily.lean` |
| paper's `L²` Rayleigh spectral gap | `rayleighSpectralGap V.target K` | `Concrete/RayleighSpectralGap.lean` |
| standard normal CDF `Phi` | `cdf standardGaussianMeasure`, or `normalCDFReal` after simplification | `Concrete/GaussianNormalProfile.lean` |
| normal quantile `PhiInv` | `lowerQuantile standardGaussianMeasure` | mathlib plus `Concrete/Quantile.lean` |
| open enlargement `A^r` | `Metric.thickening r A` | mathlib |
| real-valued probability `pi(A)` | `pi.real A` | mathlib's `Measure.real` |

The formal definition

```lean
BakryLedouxEnlargement pi m Phi PhiInv
```

means, for every measurable `A` with `0 < pi(A) < 1` and every `r > 0`,

```text
Phi(PhiInv(pi(A)) + sqrt(m) * r) <= pi(thickening r A).
```

The restriction `r > 0` is intentional: mathlib's open thickening at radius
zero is empty. The zero- and full-mass cases are excluded from the predicate
because the normal quantile is singular at the endpoints and those cases are
trivial in applications.

## Target assumptions

The paper's coordinate-free assumptions are represented by
`HessianBoundedPotential d`. Its fields include `ContDiff ℝ 2 U` and the
quadratic-form inequalities on the actual second Fréchet derivative
`iteratedFDeriv ℝ 2 U x ![v,v]`.

`Concrete/HessianToFirstOrder.lean` proves, rather than assumes, the
consequences used by the randomized-MALA argument:

- positive dimension and constants `0 < m <= L`;
- global lower and upper first-order Taylor inequalities for `U` and `gradU`;
- continuity of `U` and `gradU`;
- an `L`-Lipschitz bound on `gradU`.

The proof restricts `U` to affine lines, derives the two Taylor inequalities
from one-dimensional second-derivative bounds, and obtains gradient
Lipschitzness through a Baillon--Haddad argument. The resulting `gradU` is
definitionally mathlib's Riesz gradient of `U`, not a separately supplied
vector field. `FirstOrderPotential` remains useful as a reusable internal
interface, while the public paper-form theorem no longer assumes it.

## Paper-to-Lean proof route

The main paper chain and its Lean entry points are:

1. The dyadic-mixture Dirichlet domination (`lem:Kt`, Lemma 3.1) is implemented by
   `Kernel.parameterMixture` and `Dirichlet.energy_parameterMixture`.
2. The moment-indexed local-overlap result (`prop:overlap`, Proposition 3.2
   in the current PDF) is exposed as
   `Concrete.FirstOrderPotential.mala_overlap_bounds`.
3. Gaussian isoperimetry and a finite Euler transfer prove the target
   Bakry--Ledoux inequality
   `DiscreteTime.target_bakryLedoux`.
4. `Concrete.separatedSets_of_bakryLedoux` formalizes the paper's
   separated-set step (`prop:separated`).
5. `FirstOrderPotential.allParameterMALAFlowBounds` verifies both clauses of
   Proposition 3.4 (`prop:flow`) for the full admissible parameter range,
   using the generic defective-flow Lemma D.1 (`lem:defective`).
6. `Concrete/FractionalAggregation.lean` proves Lemma 3.5 with its exact
   `L²` energy-domination premise. Bounded `L²` truncations justify applying
   the premise before monotone convergence. The paper's hard-assignment
   aggregation theorem is exported as
   `hardAssignmentAggregation_le_spectralGap`.
7. The safe interval and geometric ladder are assembled into
   `FirstOrderPotential.universal_masterRHS_spectralGap_lower`; the Hessian
   and Rayleigh-gap bridges then yield
   `exists_universal_nonlazy_paperMasterRHS_lower`.
8. `halfLazyKernel` gives the literal kernel `(I+P)/2`; its Dirichlet energy
   and Rayleigh gap are exactly half those of `P`. The two Corollary 2.2
   displays are in `Concrete/SqrtDimensionCorollary.lean`, including the
   assumption-free estimate
   `min_sqrtDimensionDenominator_le_two_pStar`.

`THEOREM_MAP.md` gives the declaration-level cross-reference for every one of
these steps.

## Why the Lean appendix looks different

The paper's stationary rejection appendix uses stationary Langevin
diffusion, Davies perturbation, Girsanov, and martingale estimates. A suitable
general SDE and perturbation library was not available in the pinned Lean
ecosystem. The formalization therefore proves the same rejection-moment and
overlap conclusions through elementary finite objects:

```text
finite Gaussian likelihood recursion
  -> moment estimates on a finite product space
  -> shared Euler/random-walk-Metropolis pair chain
  -> fixed-horizon coalescence
  -> weak closure of moving Radon--Nikodym densities
  -> stationary MALA rejection estimate.
```

This is a proof replacement, not an extra assumption. Its public conclusion
uses the formalization's explicit constants `cr = 1/(16e)` and
`Cr = 6144 e^3`, which instantiate the paper's universal constants.

The target Bakry--Ledoux transfer is also discrete. Every finite Euler
endpoint is a Lipschitz image of a finite standard-Gaussian innovation
vector. Its enlargement coefficient is controlled explicitly. A diagonal
choice of vanishing mesh and growing horizon is then proved to converge to
the normalized target by Euler/RWM comparison and contraction. This avoids
asserting an unidentified diffusion limit.

The continuous-time SDE proof in Appendix B itself is therefore **not** a
claimed Lean result. What is kernel-checked is the discrete-time proof of the
same rejection-moment and overlap statements used by the rest of the paper.

## The fixed-step minimax obstruction

Proposition 2.3 is organized as a separate reusable chain:

1. `Concrete/SpectralGapUpperBounds.lean` proves Rayleigh upper bounds from
   arbitrary admissible tests and from indicator cuts.
2. `fixedStepHardPotential` is the manuscript's literal cosine-perturbed
   Gaussian. `contDiff_infty_fixedStepHardPotential` and the two
   `fixedStepHardPotential_hessian_*` declarations prove `C∞` regularity and
   the actual `[mI,LI]` Hessian bounds.
3. `Concrete/HardPotentialLocalObstruction.lean` identifies the first target
   marginal and proves the `x₁` test-function branch.
4. `Concrete/HardPotentialLogRatio.lean`,
   `GaussianTrigonometricConcentration.lean`,
   `HardPotentialShiftedConcentration.lean`, and
   `StickyRegionCut.lean` prove the exact Hastings-ratio formula, Gaussian
   trigonometric identities and concentration, acceptance continuity, and
   the positive small-ball cut used by the sticky branch.
5. `Concrete/FixedStepObstructionOptimization.lean` carries out the scalar
   balance uniformly over the step size. `Concrete/FixedStepMinimax.lean`
   defines the literal infimum over smooth Hessian-bounded potentials and
   supremum over positive steps, ending at
   `exists_universal_fixedStepMinimaxGap_paper_upper`.

## The Gaussian isoperimetric subproof

Some development notes use the internal labels G1--G5. They mean:

1. normal-profile calculus, including `I I'' = -1`;
2. Mehler's Ornstein--Uhlenbeck semigroup and Gaussian invariance;
3. the local Bobkov interpolation residual identity and its nonnegativity;
4. long-time and endpoint closure to the functional Bobkov inequality;
5. smooth distance ramps, Gaussian perimeter, and enlargement.

They are stages of the construction, not theorem numbers that a reader is
expected to know. The current public imports use mathematical names:
`GaussianBobkov.lean`, `WeakLimitStability.lean`, and `BakryLedoux.lean`.

## Suggested reading paths

To check only the main result:

1. read `Concrete/HessianMainTheorem.lean` and `Concrete/LazyKernel.lean`;
2. inspect the calculus bridge in `Concrete/HessianToFirstOrder.lean` and
   the gap equivalence in `Concrete/RayleighSpectralGap.lean`;
3. follow `PROOF_STRATEGY_LEDGER.md` backward through the lower-bound
   dependencies;
4. run `lake build` and the dependency audit.

To study the Gaussian/Bakry--Ledoux formalization for reuse:

1. read `REUSABLE_RESULTS.md`;
2. import `UniformRandomMALA.BakryLedoux`;
3. inspect `Concrete/GaussianNormalProfile.lean`,
   `Concrete/GaussianOUCanonicalInterpolation.lean`,
   `Concrete/GaussianEnlargement.lean`, and
   `Concrete/GaussianWeakLimit.lean` in that order.

To study the rejection and overlap argument:

1. begin with `MALA_OVERLAP_FORMALIZATION.md`;
2. inspect the public theorem in `Concrete/MALAOverlapBounds.lean`;
3. use the first part of `PROOF_STRATEGY_LEDGER.md` to trace the finite
   likelihood, pair-chain, and moving-density modules.

## Scope and compatibility files

Names ending in `_of_bakryLedoux` expose downstream implications under an
abstract enlargement hypothesis. They let future users combine a different
isoperimetric theorem with this package's conductance and aggregation code.
The completed target proof supplies that hypothesis with
`target_bakryLedoux`; the paper's final theorem does not assume it.

`PaperAnalyticInterfaces` is a legacy record from an earlier development
stage that represented several paper inputs as fields. It remains for old
imports and modular experiments. It is not on the recommended dependency
path, and no instance of it is required by the final concrete theorem.

The project does not claim a general infinite-dimensional Bakry--Ledoux
theorem or a general `Gamma_2`/SDE diffusion theory. It proves the
finite-dimensional standard-Gaussian theorem, the strongly log-concave
target theorem, exact half-lazification for the concrete reversible-kernel
setting, fractional finite-component aggregation, and the fixed-step
minimax obstruction needed here. General reusable lemmas are catalogued in
`REUSABLE_RESULTS.md`.
