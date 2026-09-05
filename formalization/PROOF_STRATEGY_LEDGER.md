# Lean proof-strategy ledger

This ledger gives a reviewer-oriented path through the completed formalization
of the main lower-bound theorem in Qian Qin's **A global spectral gap for Metropolis-adjusted Langevin algorithm
with a uniformly randomized step size**. Each row records the mathematical result, its public
Lean entry point, the principal implementation modules, and the proof
mechanism. Paper labels are cross-referenced in `THEOREM_MAP.md`; mathematical
content, rather than provisional numbering, is used here.

Last recorded Lean validation: **2026-08-30**.

Documentation/PDF synchronization: **2026-09-05**; no new Lean build.

## Result dependency graph

```text
MALA finite likelihood and coupling --------------------+
                                                        |
                                                        v
                                               MALA local overlap
                                                        |
                                                        v
Gaussian normal profile -> OU interpolation -> Bobkov functional inequality
                                                        |
                                                        v
smooth distance ramps -> finite Gaussian Bakry--Ledoux  |
                          |                             |
                          v                             |
finite Euler Gaussian image -> weak-limit stability     |
                          |                             |
                          v                             |
discrete target identification -> target Bakry--Ledoux-+
                                                        |
                                                        v
separated sets -> defective conductance -> component aggregation
                                                        |
                                                        v
                                  universal spectral-gap lower bound
```

## Foundations and target model

| Mathematical content | Public entry | Implementation | Strategy and output | Status |
|---|---|---|---|---|
| Strongly convex smooth target | `SpectralGap.lean` | `Concrete/EuclideanTarget.lean` | Define `FirstOrderPotential`, prove integrability of `exp (-U)`, normalize the target, and install probability-measure facts. | Checked |
| MALA and RWM kernels | `MALAOverlap.lean` | `Concrete/GaussianProposal.lean`, `MetropolisHastings.lean`, `MALA.lean`, `RandomWalkMetropolis.lean`, `MALAFamily.lean` | Construct measurable Gaussian proposals, MH correction, fixed-step kernels, dyadic mixtures, uniform mixtures, reversibility, and stationary edge measures. | Checked |
| Spectral gap and conductance | `SpectralGap.lean` | `Concrete/SpectralGap.lean`, `Conductance.lean` | Define the variational spectral gap and Dirichlet energy; prove indicator-energy, symmetry, layer-cake, and coarea identities. | Checked |

## Finite discrete-time MALA overlap

The manuscript now proves its stationary linear-increment estimate by
stationary time reversal, following Lyons--Zheng (1988). The finite
discrete-time route below, and its assumptions, are unchanged. It proves
the stationary-rejection and overlap conclusions without formalizing the
continuous-time increment identities.

| Mathematical content | Public entry | Implementation | Strategy and output | Status |
|---|---|---|---|---|
| Finite Gaussian likelihood | `MALAOverlap.lean` | `DiscreteTime/FiniteGaussianLikelihood.lean`, `Concrete/FiniteEulerLikelihoodBounds.lean`, `FiniteEulerRealMoments.lean` | Use an explicit finite product likelihood recursion.  Bound its centered moments through scalar Gaussian MGFs and finite energy rather than conditional-expectation infrastructure. | Checked |
| Euler/RWM comparison | `MALAOverlap.lean` | `DiscreteTime/EulerRWMPairChain.lean`, `EulerRWMFiniteRecurrence.lean`, `EulerRWMEdgeCoupling.lean`, `EulerRWMEdgeVanishing.lean` | Couple Euler and stationary RWM chains, iterate a finite recurrence, and construct a common symmetric fixed-horizon weak limit with the target as both marginals. | Checked |
| Moving-density closure | `MALAOverlap.lean` | `DiscreteTime/MovingReference.lean`, `MovingDensityClosure.lean`, `MetropolisMeet.lean` | Transfer `L^p` control under simultaneous weak convergence using bounded-continuous approximation and truncated Radon--Nikodym duality; identify the accepted-flow meet. | Checked |
| Stationary rejection moments | `MALAOverlap.lean` | `Concrete/MALAFullPathAssembly.lean`, `Concrete/MALAOverlapBounds.lean` | Assemble the finite likelihood and coupling bounds into the stationary MALA rejection estimate with explicit constants. | Checked |
| MALA local-overlap bounds | `MALAOverlap.lean` | `Concrete/MALALocalOverlap.lean`, `Concrete/MALAOverlapBounds.lean` | Combine rejection good sets with equal-covariance Gaussian proposal TV and accept/reject discrepancy.  Public declaration: `mala_overlap_bounds`. | **Unconditional** |

The public overlap theorem uses

```text
cr = 1/(16e),       Cr = 6144 e^3,
```

and proves both a high-probability local statement and a global sufficiently
small-step statement.

## Gaussian Bobkov inequality

The development originally called the next three rows G3, G4, and G5. They
mean, respectively, the local OU residual argument, closure to a functional
inequality, and passage from smooth distance ramps to Gaussian enlargement.
They are internal construction-stage names rather than paper theorem labels.

| Mathematical content | Public entry | Implementation | Strategy and output | Status |
|---|---|---|---|---|
| Normal profile | `GaussianBobkov.lean` | `Concrete/GaussianNormalProfile.lean` | Develop the standard Gaussian CDF/quantile profile, endpoint extension, symmetry, concavity, and `I * I'' = -1`. | Checked |
| Ornstein--Uhlenbeck semigroup | `GaussianBobkov.lean` | `Concrete/GaussianOU.lean`, `GaussianOUGenerator.lean` | Prove Mehler invariance, semigroup composition, invariant integration, long-time convergence, spatial derivative commutation, Gaussian integration by parts, and time differentiation. | Checked |
| Canonical interpolation fields | `GaussianBobkov.lean` | `Concrete/GaussianOUCanonicalFields.lean`, `GaussianOUHigherFields.lean`, `GaussianOUCoordinateFields.lean` | Define the backward value, gradient, Hessian, third derivative, and canonical square-root field; establish range, endpoints, continuity, and norm bounds. | Checked |
| OU residual identity and sign | `GaussianBobkov.lean` | `Concrete/GaussianOUCanonicalResidual.lean`, `GaussianOUCanonicalInterpolation.lean` | Differentiate the full time-dependent Mehler path, justify differentiation under the integral with an affine Gaussian dominator, identify the Bobkov residual, and prove it nonnegative. | **Checked** |
| Functional Bobkov closure | `GaussianBobkov.lean` | `Concrete/GaussianBobkovFunctional.lean` | Pass from local interpolation monotonicity to the closed functional inequality via long-time dominated convergence, closed-profile continuity, and endpoint truncation. | **Checked** |
| Smooth distance ramps and enlargement input | `GaussianBobkov.lean` | `Concrete/GaussianRampMollification.lean`, `GaussianRampThirdDerivative.lean`, `GaussianRampCanonicalInterpolation.lean` | Convolve expanded distance ramps with a normalized smooth bump; prove value, support, Lipschitz, derivative, and convergence bounds; specialize the canonical interpolation. | **Checked** |

The main certificate declarations are:

```lean
Concrete.gaussianBobkovSmoothInterpolation_of_boundedThirdJet
Concrete.gaussianRampMollified_bobkov
```

## Weak limits and target Bakry--Ledoux

| Mathematical content | Public entry | Implementation | Strategy and output | Status |
|---|---|---|---|---|
| Enlargement stability | `WeakLimitStability.lean` | `Concrete/WeakLimitEnlargement.lean`, `GaussianWeakLimit.lean` | Use compact inner approximation, an open input enlargement, a closed output neighborhood, and the two Portmanteau inequalities.  Handle Gaussian profile endpoints directly. | Checked |
| Finite Gaussian enlargement | `BakryLedoux.lean` | `Concrete/GaussianEnlargement.lean`, `GaussianRampCanonicalInterpolation.lean` | Derive perimeter and closed-set enlargement from the ramp inequality, prove intrinsic right-continuity and the Dini/quantile comparison, and extend to measurable sets by Radon approximation. | Checked |
| Arbitrary finite index types | `BakryLedoux.lean` | `Concrete/GaussianRampCanonicalInterpolation.lean` | Reindex Euclidean Gaussian space through a linear isometry and handle the empty-index case separately. | Checked |
| Finite Euler Gaussian images | `BakryLedoux.lean` | `Concrete/FiniteEulerGaussianImage.lean`, `FiniteEulerEnlargement.lean` | Prove deterministic innovation sensitivity and the endpoint Lipschitz coefficient `2/(2m-L^2 delta)`; transfer finite Gaussian enlargement through the endpoint map. | Checked |
| Direct target identification | `BakryLedoux.lean` | `Concrete/FiniteEulerTargetIdentification.lean` | Choose an explicit diagonal mesh/horizon schedule.  Combine Euler/RWM comparison, likelihood bounds, and contraction to prove endpoint laws converge directly to the normalized target. | Checked without SDEs |
| Target Bakry--Ledoux | `BakryLedoux.lean` | `Concrete/GaussianRampCanonicalInterpolation.lean` | Apply finite-index Gaussian enlargement to every diagonal endpoint and pass to the target using weak-limit stability and the coefficient limit `1/m`. | **Unconditional** |

The public endpoint is:

```lean
UniformRandomMALA.DiscreteTime.target_bakryLedoux
```

No diffusion existence, diffusion invariance, Fokker--Planck uniqueness, or
martingale-problem theorem is a dependency.

## Conductance and final spectral gap

| Mathematical content | Public entry | Implementation | Strategy and output | Status |
|---|---|---|---|---|
| Gaussian shift and separation | `SpectralGap.lean` | `Concrete/GaussianMills.lean`, `Quantile.lean`, `StandardGaussianShift.lean`, `SeparatedSets.lean` | Derive explicit Mills/quantile estimates and convert target Bakry--Ledoux into separated-set bounds. | Checked |
| Defective conductance | `SpectralGap.lean` | `Concrete/MALADefectiveConductance.lean`, `SafeComponent.lean` | Combine separation with MALA overlap to obtain safe and local dyadic boundary-flow estimates. | Checked |
| Component aggregation | `SpectralGap.lean` | `Concrete/CoareaCauchySchwarz.lean`, `ComponentAggregationFinal.lean` | Use median decomposition, bounded caps, monotone convergence, and finite Cauchy--Schwarz.  Avoid invalid extended-real cancellation. | Checked |
| Exceptional budget and ladder | `SpectralGap.lean` | `ExceptionalBudgetArithmetic.lean`, `Concrete/LadderComponents.lean` | Construct the finite cut assignment, control exceptional mass, and prove the finite harmonic bound with constant `6 * 2^30`. | Checked |
| Parameterized master bound | `SpectralGap.lean` | `Concrete/GlobalFromBakryLedoux.lean`, `GaussianRampCanonicalInterpolation.lean` | Assemble safe and ladder gap bounds and discharge target Bakry--Ledoux internally. | **Unconditional** |
| Universal master bound | `SpectralGap.lean` | `Concrete/UniversalConstants.lean`, `GaussianRampCanonicalInterpolation.lean` | Fix explicit `A0`, `b0`, and `c0`; prove all arithmetic side conditions; expose a theorem requiring only `FirstOrderPotential` and `H > 0`. | **Final checked result** |

The first-order assembly declaration is:

```lean
UniformRandomMALA.Concrete.FirstOrderPotential.
  universal_masterRHS_spectralGap_lower
```

The manuscript-facing endpoint additionally discharges the displayed
`C²` Hessian assumptions and uses the paper's `L²` Rayleigh definition:

```lean
UniformRandomMALA.Concrete.exists_universal_nonlazy_paperMasterRHS_lower
```

## Manuscript-facing calculus, gap, lazification, and aggregation

| Mathematical content | Implementation | Strategy and output | Status |
|---|---|---|---|
| Hessian-to-first-order bridge | `Concrete/HessianToFirstOrder.lean` | Record `ContDiff ℝ 2 U` and quadratic bounds on `iteratedFDeriv ℝ 2 U`; restrict to affine lines for the exact Taylor inequalities; derive cocoercivity and the Lipschitz Riesz gradient; build `FirstOrderPotential` with `gradU = ∇ U`. | **Checked** |
| Paper Rayleigh gap | `Concrete/RayleighSpectralGap.lean` | Define measurable `L²` tests and extended-valued quotients; prove equivalence between quotient infimum and the `L²` Poincaré-lower-bound supremum, treating zero variance, infinite energy, and an empty test family. | **Checked** |
| Non-lazy paper theorem | `Concrete/HessianMainTheorem.lean` | Compose the actual-Hessian bridge, the unconditional first-order lower-bound chain, and the Poincaré-to-Rayleigh implication; choose universal constants before the target parameters. | **Checked** |
| Concrete half-lazification | `Concrete/LazyKernel.lean` | Realize `(I+K)/2` as a fair Boolean parameter mixture; preserve Markovness and reversibility; compute exact half energy and half Rayleigh gap; specialize to randomized MALA. | **Checked** |
| Square-root-dimension corollary | `Concrete/SqrtDimensionCorollary.lean` | Substitute `H=c/(L sqrt d)` and prove `min{pStar(d+pStar)/d,d} ≤ 2 pStar` without a `pStar ≤ d` assumption. | **Checked** |
| Fractional aggregation | `Concrete/FractionalAggregation.lean` | Add weighted extended-valued Cauchy--Schwarz; use coarea, layer cake, median splitting, bounded `L²` truncations, and monotone convergence; allow zero `β_j`; specialize to hard assignment. | **Checked** |
| Full-parameter one-step flow | `Concrete/AllParameterMALAFlow.lean` | Generalize the already checked safe and ladder instances to every admissible real `p,θ,t`; retain the exact mass range, logarithmic condition, and small-step clause. | **Checked** |

The principal declarations are:

```lean
Concrete.HessianBoundedPotential.toFirstOrderPotential
Concrete.l2SpectralGap_eq_rayleighSpectralGap
Concrete.exists_universal_nonlazy_paperMasterRHS_lower
Concrete.exists_universal_lazy_paperMasterRHS_lower
Concrete.HessianBoundedPotential.sqrtDimensionCorollarySimplified_rayleighSpectralGap_lower
Concrete.fractionalAggregation_poincareLower
Concrete.FirstOrderPotential.allParameterMALAFlowBounds
```

## Fixed-step minimax obstruction

| Stage | Implementation | Strategy and output | Status |
|---|---|---|---|
| Generic upper-bound API | `Concrete/SpectralGapUpperBounds.lean` | Every admissible Rayleigh test bounds the gap from above; indicator energy equals outgoing stationary flow and indicator variance equals `π(S)(1-π(S))`. | **Checked** |
| Smooth hard potential | `Concrete/FixedStepHardPotential.lean` | Define the separable quadratic/cosine potential literally; prove `C∞`; compute its actual gradient and diagonal second Fréchet derivative; prove the `[mI,LI]` bounds. | **Checked** |
| Local branch | `Concrete/HardPotentialLocalObstruction.lean` | Identify the first target marginal as `N(0,m⁻¹)`, dominate accepted energy by proposal energy, and test with the first coordinate to obtain `mh+(mh)²/2`. | **Checked** |
| Log-ratio and concentration | `Concrete/HardPotentialLogRatio.lean`, `GaussianTrigonometricConcentration.lean`, `HardPotentialShiftedConcentration.lean` | Derive the coordinate Hastings-ratio identity; prove the two exact Gaussian trigonometric moments; choose a fixed positive MGF parameter by differentiability at zero; tensorize over independent coordinates and retain the required negative threshold. | **Checked** |
| Sticky cut | `Concrete/StickyRegionCut.lean`, `HardPotentialStickyObstruction.lean` | Prove continuity of proposal-averaged acceptance by dominated convergence; extract a positive target-mass ball of mass at most one half; control its outgoing flow by acceptance; apply the indicator cut bound. | **Checked** |
| Generic obstruction | `Concrete/FixedStepHardPotentialObstruction.lean` | Combine local and sticky branches and compress the two exceptional exponentials into `C exp(-c(d-1) min{(L-m)h,1})`. | **Checked** |
| Scalar optimization | `Concrete/FixedStepObstructionOptimization.lean` | Reparametrize by `t=Lh` and `κ=L/m`, split at an explicit balance threshold, absorb the reciprocal-square remainder, and control the supremum over every step. | **Checked** |
| Exact minimax proposition | `Concrete/FixedStepMinimax.lean` | Define the exact `C∞` actual-Hessian potential class, its `sInf` fixed-step worst gap, and the `iSup` over positive steps; insert the hard witness and absorb constants so `c` is universal and `C` depends only on `κ₀`. | **Checked** |

The final fixed-step declaration is:

```lean
UniformRandomMALA.Concrete.exists_universal_fixedStepMinimaxGap_paper_upper
```

## Verification ledger

| Check | Command | Expected result |
|---|---|---|
| Public API | `lake env lean UniformRandomMALA/AllResults.lean` | exit code 0 |
| Full kernel build | `lake build` | all jobs complete successfully |
| Axiom report | `lake env lean UniformRandomMALA/DependencyAudit.lean` | audited results list only standard Lean/mathlib logical axioms |
| Placeholder/import audit | `python3 scripts/static_audit.py` | no placeholders and all local imports resolve |
| Numerical transcription audit | `python3 scripts/numeric_sanity.py` | 2,000 deterministic trials pass |
| Complete Unix check | `./scripts/check.sh` | exit code 0 |
| Complete Windows check | `powershell -ExecutionPolicy Bypass -File scripts/check.ps1` | exit code 0 |

## Modular and archival APIs

Theorems ending in `_of_bakryLedoux` isolate a useful implication: assuming
an enlargement inequality for some measure, they derive separated-set,
conductance, or spectral-gap estimates. Future developments can reuse those
theorems with another isoperimetric input. For the target in this paper,
`DiscreteTime.target_bakryLedoux` proves the input and the final theorem
supplies it internally.

`PaperAnalyticInterfaces` is a legacy record from an earlier development
stage that bundled several analytic inputs as fields. It is kept for source
compatibility and modular experiments, but it is not on the dependency path
from `AllResults.lean` to the concrete final theorem. The extended file
`LEAN_FRIENDLY_PROOF_LEDGER.md` is an archival development record; this file
is the concise account of the completed proof.
