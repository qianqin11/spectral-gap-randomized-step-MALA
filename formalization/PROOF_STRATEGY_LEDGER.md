# Lean proof-strategy ledger

This ledger traces the gap, mixing, CLT, variance, and finite-sample MSE
proofs, the fixed-step obstruction, and the general aggregation results.
It also records the full nonconvex stationary-rejection argument.
Each table identifies the mathematical input, the implementation modules,
and the argument that connects them. Start with the
[reader guide](PAPER_READER_GUIDE.md) for a shorter route, or use
[THEOREM_MAP.md](THEOREM_MAP.md) to find a particular paper statement.
[BUILD_STATUS.md](BUILD_STATUS.md) records verification evidence.

The main lower-bound route starts from `C1Potential`, whose drift is the
actual gradient of the potential. The calculus adapter proves the descent
inequality and supplies `FirstOrderPotential`; the later assembly supplies
the required isoperimetry and rejection estimates. The aggregation and
lazy-kernel convergence results also have general statements independent
of this target model.

## Result dependency graph

```text
C1 actual-gradient input -> proved descent lemma -> FirstOrderPotential
                                                     |             |
                                                     |             +-> concrete MALA kernels
                                                     |
finite Gaussian likelihood + Euler/RWM coupling -----+
  -> stationary rejection moments -> p >= 1 interpolation
  -> MALA local overlap

Gaussian normal profile -> OU interpolation -> Bobkov functional inequality
  -> smooth distance ramps -> finite Gaussian Bakry--Ledoux
                                      |
FirstOrderPotential -> finite Euler Gaussian images --+
  -> discrete target identification + weak-limit stability
  -> target Bakry--Ledoux

target Bakry--Ledoux + MALA local overlap
  -> separated sets -> defective conductance -> component aggregation
  -> universal spectral-gap lower bound -> paper Rayleigh and lazy endpoints
  -> tuned H = c/(L sqrt(d pStar)) -> tuned spectral-gap lower bound

reversible kernel + half-lazification + Rayleigh lower bound
  -> positive quadratic form -> full L2 kernel contraction
  -> actual RN density evolution -> density and total-variation decay
  -> logarithmic ceiling estimate + tuned gap -> mixing-time corollary

centered kernel + positive gap -> Poisson resolvent
  -> actual path covariances -> stationary variance limit and bounds
  -> actual martingale increments -> Lindeberg + conditional variance LLN
  -> Gaussian CLT -> density approximation + acceptance -> every initial law

L2 decay + truncation/layer-cake interpolation -> L4 decay
  -> initial-density pairing + actual pair laws -> finite-sample MSE

small fixed-step Rayleigh energy -> extended asymptotic-variance lower bound
  -> actual observable witness -> randomized/fixed-step variance separation
```

## Foundations and target model

| Mathematical content | Public entry | Implementation | Strategy and output | Status |
|---|---|---|---|---|
| First-order strongly convex target | `Concrete/C1MainTheorem.lean` | `Concrete/C1ToFirstOrder.lean`, `EuclideanTarget.lean` | Record `C¹`, the strong-convexity supporting inequality, and Lipschitzness of the actual gradient; prove the descent lemma; build `FirstOrderPotential`; normalize `exp (-U)`. | Checked |
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
| Stationary rejection moments | `Concrete/C1MainTheorem.lean` | `Concrete/MALAFullPathAssembly.lean`, `MALAOverlapBounds.lean`, `DiscreteTime/MomentInterpolation.lean`, `Concrete/RejectionMomentsOne.lean` | Assemble the finite likelihood and coupling bounds; interpolate the second-moment estimate to cover every real `p ≥ 1`. | Checked |
| MALA local-overlap bounds | `Concrete/C1MainTheorem.lean` | `Concrete/MALALocalOverlap.lean`, `MALAOverlapBounds.lean`, `RejectionMomentsOne.lean` | Combine rejection good sets with equal-covariance Gaussian proposal TV and accept/reject discrepancy. Public declaration: `C1Potential.mala_overlap_bounds`. | **Certificate-free under the standing assumptions** |

The public overlap theorem uses

```text
cr = 1/(32e),       Cr = 12288 e^3,
```

and proves both a high-probability local statement and a global sufficiently
small-step statement for `p ≥ 1`. The sharper constants `1/(16e)` and
`6144 e^3` remain available in the checked `p ≥ 2` core.

## Full nonconvex stationary rejection

[Nonconvex/StationaryRejection.lean](UniformRandomMALA/Nonconvex/StationaryRejection.lean)
proves Proposition B.1 under its actual `C¹`, Lipschitz-gradient, and
normalizable Boltzmann assumptions. The proof reuses the potential-free
parts of the finite-chain route above and supplies the following weaker-input
specializations:

| Stage | Files | Proof difference |
|---|---|---|
| Potential and target | `Concrete/NonconvexPotential.lean`, `NonconvexMALA.lean` | Construct the actual Gaussian Metropolis kernel and reversible Boltzmann law without strong convexity. |
| Gradient moments | `Concrete/NonconvexGradientMoments.lean`, `NonconvexGradientMGF.lean` | Use Gaussian convolution and normalization to derive gradient moments; no target position moments are assumed. |
| Finite likelihood bounds | `Nonconvex/FiniteGaussianLikelihood.lean`, `FiniteEulerEnergyMGF.lean`, `FiniteEulerRealMoments.lean` | Supply the gradient moment bound to the finite-product likelihood argument. |
| Drift and coupling | `Concrete/NonconvexTaylor.lean`, `NonconvexEulerStability.lean`, `Nonconvex/EulerRWM*.lean` | Bound the absolute Taylor remainder and finite-horizon Lipschitz growth, then prove the actual pair-chain discrepancy vanishes. |
| Endpoint and rejection assembly | `Nonconvex/FiniteEulerEndpointContraction.lean`, `MALAWeakLimitAssembly.lean`, `MALAFullPathAssembly.lean`, `StationaryRejection.lean` | Identify the endpoint density and Metropolis meet, pass to the weak limit, and interpolate to every real `p ≥ 1`. |

This proves the full endpoint while bypassing the explicitly excluded
continuous-time Lemmas B.2–B.5. It does not use those statements as axioms
or hypotheses.

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
| Target Bakry--Ledoux | `BakryLedoux.lean` | `Concrete/GaussianRampCanonicalInterpolation.lean` | Apply finite-index Gaussian enlargement to every diagonal endpoint and pass to the target using weak-limit stability and the coefficient limit `1/m`. | **Certificate-free under `FirstOrderPotential`** |

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
| Parameterized master bound | `SpectralGap.lean` | `Concrete/GlobalFromBakryLedoux.lean`, `GaussianRampCanonicalInterpolation.lean` | Assemble safe and ladder gap bounds and discharge target Bakry--Ledoux internally. | **Certificate-free under `FirstOrderPotential`** |
| Universal master bound | `SpectralGap.lean` | `Concrete/UniversalConstants.lean`, `GaussianRampCanonicalInterpolation.lean` | Fix explicit `A0`, `b0`, and `c0`; prove all arithmetic side conditions; expose a theorem requiring only `FirstOrderPotential` and `H > 0`. | **Final checked result** |

The first-order assembly declaration is:

```lean
UniformRandomMALA.Concrete.FirstOrderPotential.
  universal_masterRHS_spectralGap_lower
```

The manuscript-facing endpoint starts from the `C¹` first-order
assumptions and uses the paper's `L²` Rayleigh definition:

```lean
UniformRandomMALA.Concrete.C1Potential.exists_universal_normalizedMasterRHS_bounds
```

## Manuscript-facing calculus, gap, lazification, and aggregation

| Mathematical content | Implementation | Strategy and output | Status |
|---|---|---|---|
| First-order bridge | `Concrete/C1ToFirstOrder.lean` | Record `ContDiff ℝ 1 U`, the lower supporting inequality, and Lipschitzness of `∇ U`; derive the descent inequality along affine lines; build `FirstOrderPotential` with `gradU = ∇ U`. | **Checked** |
| Optional smooth adapter | `Concrete/HessianToFirstOrder.lean` | Derive the first-order interface from actual Hessian quadratic bounds. This supplies a reusable smooth special case. | **Checked** |
| Paper Rayleigh gap | `Concrete/RayleighSpectralGap.lean` | Define measurable `L²` tests and extended-valued quotients; prove equivalence between quotient infimum and the `L²` Poincaré-lower-bound supremum, treating zero variance, infinite energy, and an empty test family. | **Checked** |
| Main paper theorem | `Concrete/C1MainTheorem.lean`, `PaperNormalizedGap.lean` | Compose the first-order bridge, proved lower-bound chain, Poincaré-to-Rayleigh implication, and concrete half-lazification; convert the internal constants to the current manuscript normalization with universal choices before target parameters. | **Checked** |
| Concrete half-lazification | `Concrete/LazyKernel.lean` | Realize `(I+K)/2` as a fair Boolean parameter mixture; preserve Markovness and reversibility; compute exact half energy and half Rayleigh gap; specialize to randomized MALA. | **Checked** |
| Square-root-dimension corollary | `Concrete/PaperNormalizedGap.lean`, with scalar bounds from `SqrtDimensionCorollary.lean` | Substitute `H=c/(L sqrt d)` and prove the first and simplified bounds with the normalized threshold, without a `pStar ≤ d` assumption. | **Checked** |
| Tuned third spectral-gap bound | `Concrete/PaperNormalizedGap.lean`, with scalar identities from `TunedSpectralGap.lean` | Substitute `c/sqrt pStar` into the normalized second bound and identify the actual kernel at `H=c/(L sqrt(d pStar))`. | **Checked** |
| Fractional aggregation | `Concrete/FractionalAggregation.lean` | Add weighted extended-valued Cauchy--Schwarz; use coarea, layer cake, median splitting, bounded `L²` truncations, and monotone convergence; allow zero `β_j`; specialize to hard assignment. | **Checked** |
| Full-parameter one-step flow | `Concrete/AllParameterMALAFlow.lean` | Generalize the already checked safe and ladder instances to every admissible real `p,θ,t`; retain the exact mass range, logarithmic condition, and small-step clause. | **Checked** |

The principal declarations are:

```lean
Concrete.C1Potential.upperTaylor
Concrete.C1Potential.toFirstOrderPotential
Concrete.l2SpectralGap_eq_rayleighSpectralGap
Concrete.C1Potential.exists_universal_normalizedMasterRHS_bounds
Concrete.C1Potential.normalizedSimplifiedCorollary_rayleighSpectralGap_lower
Concrete.C1Potential.normalizedTunedCorollary_rayleighSpectralGap_lower
Concrete.fractionalAggregation_poincareLower
Concrete.C1Potential.allParameterMALAFlowBounds
```

## From the spectral gap to actual mixing time

The gap and mixing corollaries share the tuned endpoint defined in
[PaperNormalizedGap.lean](UniformRandomMALA/Concrete/PaperNormalizedGap.lean).
[PaperNormalizedMixing.lean](UniformRandomMALA/Concrete/PaperNormalizedMixing.lean)
uses the proved gap in both ceiling bounds, with its prefactor depending
only on the positive tuning parameter.

| Stage | Implementation | What to inspect |
|---|---|---|
| Actual kernel action | `KernelLpBasic.lean`, `KernelLpOperator.lean` | The operator is Bochner integration against the transition kernel; Jensen and invariance prove `Lp` contraction. |
| Energy, symmetry, and positivity | `KernelLpL2.lean`, `KernelLpContraction.lean` | Reversibility yields the symmetric pairing; Dirichlet energy gives the quadratic gap bound; positivity yields exact `L²` norm decay. Half-lazy positivity is proved. |
| Actual density evolution | `L2DensityEvolution.lean` | Identify the Radon–Nikodym density of the iterated law and prove both inequalities in `eq:TVbound`, including the exact TV factor. |
| Finite gap and mixing time | `TargetGapRange.lean`, `TargetGapOne.lean`, `MixingTimeArithmetic.lean`, `MixingTime.lean` | Control the target's gap, include time zero, and derive the logarithmic ceiling from geometric decay. |

The earlier bounded-observable proof remains available in `L2Mixing*.lean`.
The current full-`L²` route also supports the density inequality and the
sample-average results below. Neither route assumes a mixing certificate.

## Actual sample averages, variance, and finite-sample error

| Stage | Implementation | Strategy and output |
|---|---|---|
| Finite Markov laws | `NonstationaryMSEPath.lean`, `StationaryPath.lean`, `StationaryPathMoments.lean` | Construct the joint law and prove coordinate and pair marginals. Expectations and covariances refer to actual observations. |
| Poisson equation | `StationaryVarianceResolvent.lean`, `StationaryVarianceCentered.lean` | Work on centered `L²`; a lazy Neumann series inverts `I−P` while retaining the nonlazy variance constant. |
| Stationary limit | `StationaryVariancePoisson.lean`, `StationaryVarianceLimit.lean`, `StationaryVarianceGeneral.lean` | Express the finite sample variance through covariances and prove the scaled limit, identified with the Poisson quadratic form. |
| Variance comparison | `VarianceSeparationExtended.lean`, `VarianceSeparationCorollary.lean`, `VarianceSeparationFixedStep.lean` | Prove the extended variance limit for reversible chains, including zero gap; turn a small-energy test into an actual large-variance observable. |
| `L⁴` decay | `KernelLpInterpolation.lean`, `KernelLpIterateContraction.lean` | Prove truncation and layer-cake interpolation from `L²` decay and the infinity bound, then apply it to actual kernel iterates. |
| Nonstationary MSE | `NonstationaryMSEMoments.lean`, `NonstationaryMSEPairBounds.lean`, `NonstationaryMSEExpansion.lean`, `NonstationaryMSESum.lean`, `NonstationaryMSE.lean` | Pair actual evolved densities with pair observables, expand the squared sample mean, and bound its finite covariance sum. |
| Paper specialization | `PaperAsymptoticVariance.lean`, `PaperNonstationaryMSE.lean` | Insert the actual randomized MALA gap and prove the paper's displayed bounds. |

## Central limit theorem from every initial distribution

| Stage | Implementation | Strategy and output |
|---|---|---|
| Infinite trajectory | `MarkovInfinitePath.lean`, `MarkovInfinitePrefix.lean`, `MarkovInfiniteInitial.lean` | Construct a trajectory kernel with Ionescu–Tulcea, prove finite-prefix correspondence and the exact shifted-law identity, and preserve initial-law domination. |
| Genuine martingale | `MarkovInfiniteMartingale.lean`, `MarkovInfiniteRow.lean` | Use the natural filtration, prove conditional means and squares of Poisson increments, and normalize the actual rows. |
| Conditional variance and Lindeberg | `MarkovErgodicL1Limit.lean`, `MarkovCLTVarianceLLN.lean`, `MarkovInfiniteCLTInputs.lean`, `MarkovBoundedCLTInputs.lean` | Derive the variance-clock `L¹` limit and tail estimates; transfer them to bounded initial densities. |
| Martingale Gaussian limit | `MartingaleCLT*.lean`, `MarkovCLTDistribution.lean` | Prove characteristic-function convergence using Taylor, truncation, stopping, and removal of the stop; apply the characteristic-function criterion for convergence in distribution. |
| Poisson boundary | `MarkovCLTBoundary.lean`, `MarkovGaussianCLT.lean` | Show the normalized boundary has vanishing second moment and identify the Gaussian variance with the actual stationary variance. |
| Arbitrary initial law | `MarkovInitialDensityApproximation.lean`, `MarkovCLTAbsolutelyContinuous.lean`, `MarkovAcceptanceApproximation.lean`, `MarkovCLTArbitraryStart.lean` | Approximate absolutely continuous starts by bounded densities, remove the singular rejection remainder, and discard a fixed finite prefix using the proved shifted law and normalization. |
| Paper endpoint | `PaperCentralLimit.lean` | Supply the actual MALA gap and acceptance facts for nonlazy and half-lazy kernels, with no restriction on the initial probability law. |

The public CLT takes a measurable `L²(π)` observable. Its martingale,
Lindeberg, conditional-variance, and acceptance inputs are all discharged
internally. Its limiting variance is the same quantity as in the stationary
variance corollary.

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
| Full kernel build | `lake build` | exit code 0 |
| Axiom report | `lake env lean UniformRandomMALA/DependencyAudit.lean` | only `propext`, `Classical.choice`, `Quot.sound` |
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
compatibility and modular experiments, but it is not a premise of the
concrete C1 final theorem. The extended file
`LEAN_FRIENDLY_PROOF_LEDGER.md` is an archival development record; this file
is the concise account of the completed proof.
