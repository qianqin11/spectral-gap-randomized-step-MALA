# Reading the paper alongside the Lean source

Use this guide to check the formalization against the [paper](paper/main.pdf)
and its [LaTeX source](paper/main.tex), then trace the proofs back to their
inputs. [THEOREM_MAP.md](THEOREM_MAP.md) is the complete index by theorem
number and TeX label. [BUILD_STATUS.md](BUILD_STATUS.md) records verification
evidence; the [README](README.md) gives commands to reproduce it.

## 1. Compare the assumptions and theorem statements

Start with [C1ToFirstOrder.lean](UniformRandomMALA/Concrete/C1ToFirstOrder.lean).
`UniformRandomMALA.Concrete.C1Potential` records the assumptions in Section 2
(`eq:first-order-assumptions`): a potential on Euclidean space, continuous
differentiability, the strong-convexity supporting inequality, and a
Lipschitz bound on mathlib's actual Riesz gradient `∇ U`.
`C1Potential.upperTaylor` derives the descent inequality, and
`C1Potential.toFirstOrderPotential` supplies the internal record with
`gradU := ∇ U`. Reading this adapter verifies that subsequent kernels use
the gradient of the same potential that defines the target.

Next open [C1MainTheorem.lean](UniformRandomMALA/Concrete/C1MainTheorem.lean).
Start with `C1Potential.exists_universal_paperMasterRHS_bounds`, the single
statement of both clauses of Theorem 2.1 (`thm:main`). Check the quantifiers:
the constants are chosen before the dimension, potential, and endpoint
`H`; both the ordinary and half-lazy bounds use those same constants.
`paperMomentThreshold` and `paperMasterRHS`, immediately above the theorem,
write out the paper's threshold and lower-bound expression. The theorem's
proof connects those expressions to the internal parameterized bound.

The corollary endpoints in that file are
`C1Potential.sqrtDimensionCorollary_rayleighSpectralGap_lower` and
`C1Potential.sqrtDimensionCorollarySimplified_rayleighSpectralGap_lower`.
Their right-hand sides are defined as `Parameters.sqrtDimensionCorollaryRHS`
and `Parameters.sqrtDimensionCorollarySimplifiedRHS` in
[SqrtDimensionCorollary.lean](UniformRandomMALA/Concrete/SqrtDimensionCorollary.lean).
Compare both displays in Corollary 2.2 (`cor:sqrt-d-endpoint`), with
`H = c/(L√d)`; the simplified bound has no extra restriction on `p⋆`.

For Proposition 2.3 (`prop:minimax-fixed-step-ceiling`), open
[FixedStepMinimax.lean](UniformRandomMALA/Concrete/FixedStepMinimax.lean).
`exists_universal_fixedStepMinimaxGap_paper_upper` chooses a universal
exponential rate, then a prefactor depending only on `κ₀`, before quantifying
over the dimension and curvature parameters. Read the three definitions
at the top of the file to check the optimization itself:

| Declaration (in `UniformRandomMALA.Concrete`) | Paper meaning |
|---|---|
| `smoothHessianPotentialGapValues` | Gap values for smooth potentials with the prescribed actual Hessian bounds |
| `fixedStepWorstPotentialGap` | Infimum over those potentials at a fixed step `h` |
| `fixedStepMinimaxGap` | Supremum of that infimum over all positive steps |

The smooth class is specified by `HessianBoundedPotential` in
[HessianToFirstOrder.lean](UniformRandomMALA/Concrete/HessianToFirstOrder.lean),
with `ContDiff ℝ ⊤` additionally required in the gap-value set. These
smoothness assumptions belong to the obstruction result; the randomized
lower bound takes `C1Potential`.

### Aggregation: Lemma 3.5 and Theorem 3.6

Both general aggregation results are proved in
[FractionalAggregation.lean](UniformRandomMALA/Concrete/FractionalAggregation.lean).
They apply to a probability measure and a finite family of Markov kernels
on a measurable space, independently of the MALA application. Their inputs
are the paper's reversibility, energy-domination, and one-step flow
conditions, with no assumptions on a potential.

| Paper result | Declarations in `UniformRandomMALA.Concrete` | Bound to compare |
|---|---|---|
| Lemma 3.5 (`lem:fractional`) | `fractionalAggregation_poincareLower`; `fractionalAggregation_le_spectralGap` | Reciprocal of `2 ∑ j, β_j²/γ_j` |
| Theorem 3.6 (`thm:aggregation`) | `hardAssignmentAggregation_poincareLower`; `hardAssignmentAggregation_le_spectralGap` | Reciprocal of `2 ∑ j, 1/(γ_j φ_j²)` |

In each statement, `hdom` requires energy domination for every measurable
`L²` function, as in the paper. The fractional lemma's `hflow` bounds the
mass of each measurable set of positive mass at most one half by the
weighted sum of component boundary flows; its coefficients `β_j` may be zero. The
theorem's `hflow` instead requires a suitable component for each such set.
Its proof invokes the fractional lemma with `β_j = 1/φ_j`.
`fractionalCost` in the same file and `harmonicCost` in
[ComponentAggregation.lean](UniformRandomMALA/Concrete/ComponentAggregation.lean)
define the two sums, and `fractionalCost_inv_eq_harmonicCost` proves the
substitution identity.

The conclusions first give the stronger internal Poincaré gap. Compose
either `_le_spectralGap` result with `spectralGap_le_rayleighSpectralGap` in
[RayleighSpectralGap.lean](UniformRandomMALA/Concrete/RayleighSpectralGap.lean)
to obtain exactly the paper's Rayleigh-gap lower bound. Lean requires
reversibility of the component kernels; the bound holds for a Markov
kernel `P` without separately requiring its reversibility, so it covers
the paper's reversible `P` as well.

To follow the proof, read `fractionalAggregation_evariance_le` and its
supporting truncation, coarea, and weighted Cauchy–Schwarz lemmas earlier in
the file. The four declarations above are exported by
[AllResults.lean](UniformRandomMALA/AllResults.lean) and explicitly selected
in [DependencyAudit.lean](UniformRandomMALA/DependencyAudit.lean).

## 2. Compare the algorithm and quantity definitions

For a public input `V : C1Potential d`, write
`W := V.toFirstOrderPotential`. Most algorithm definitions below are in the
namespace `UniformRandomMALA.Concrete.FirstOrderPotential` and are applied
to `W`. This is the same `W` appearing in the public theorem statements.
Other abbreviated namespaces are relative to `UniformRandomMALA`.

### Target and transition kernels

| Paper object | Definitions and identities to inspect | Source |
|---|---|---|
| State space `ℝᵈ` and normalized target `π(dx) ∝ exp(-U(x)) dx` | `Concrete.State`; `boltzmannWeight`, `boltzmannMeasure`, `target`, `targetDensity`; `target_apply` and `target_toMeasure_eq_withDensity` identify the normalized measure and density | [EuclideanTarget.lean](UniformRandomMALA/Concrete/EuclideanTarget.lean) |
| Proposal `Y = x - h∇U(x) + √(2h) Z` and its density `q_h` | `proposalMean`, `proposalMap`, `gaussianProposal`, `proposalDensityReal`, `gaussianDensityProposal` | [GaussianProposal.lean](UniformRandomMALA/Concrete/GaussianProposal.lean) |
| Acceptance `α_h(x,y) = min(1, π(y)q_h(y,x)/(π(x)q_h(x,y)))` | `malaAcceptance` specializes `MetropolisHastings.acceptance`; `edgeDensity` fixes the orientation of the ratio | [MALA.lean](UniformRandomMALA/Concrete/MALA.lean), [MetropolisHastings.lean](UniformRandomMALA/Concrete/MetropolisHastings.lean) |
| Fixed-step kernel `P_h`, including the rejection atom at `x` | `malaKernel` specializes `MetropolisHastings.kernel`; inspect `accepted`, `acceptanceMass`, and `rejected` | [MALA.lean](UniformRandomMALA/Concrete/MALA.lean), [MetropolisHastings.lean](UniformRandomMALA/Concrete/MetropolisHastings.lean) |
| Randomized kernel `P̄_H = H⁻¹ ∫₀ᴴ P_h dh` | `malaKernelFamily`, `sectR_malaKernelFamily`, `uniformStepMeasure`, `uniformStepMeasure_lintegral_of_pos`, and `uniformMALA` | [MALAFamily.lean](UniformRandomMALA/Concrete/MALAFamily.lean) |
| Dyadic component `K_t = (2/t) ∫_(t/2)^t P_h dh` | `intervalStepMeasure`, `dyadicStepMeasure`, and `dyadicMALA` | [MALAFamily.lean](UniformRandomMALA/Concrete/MALAFamily.lean) |
| Integration of a family of transitions | `UniformRandomMALA.Kernel.parameterMixture` and `parameterMixture_apply` identify the transition probability on each measurable set | [KernelMixture.lean](UniformRandomMALA/KernelMixture.lean) |
| Half-lazy kernel `(I + P̄_H)/2` | `Concrete.halfLazyKernel`, `halfLazyKernel_apply`, and `FirstOrderPotential.lazyUniformMALA`; `rayleighSpectralGap_halfLazyKernel` proves exact gap scaling | [LazyKernel.lean](UniformRandomMALA/Concrete/LazyKernel.lean) |

The proposal has both a Gaussian-image construction and a density
construction. Their equality is proved by
`DiscreteTime.gaussianProposal_eq_gaussianDensityProposal` in
[GaussianLawBridge.lean](UniformRandomMALA/DiscreteTime/GaussianLawBridge.lean).
This connects the explicit sampling formula to the proposal used by the
Metropolis kernel.

The step measures use `(0,H]` and `(t/2,t]`; their endpoints have zero
Lebesgue mass, so they give the paper's uniform laws. The joint family uses
`effectiveStep` to define a kernel for every real parameter, and
`effectiveStep_of_pos` proves it equals the supplied step on the positive
intervals used here. `uniformMALA` averages the already corrected `P_h`
kernels: it represents drawing a fresh step and then doing one MALA
transition. `malaKernel_isReversible` and `uniformMALA_isReversible` prove
detailed balance for these concrete definitions.

### Energy, gap, and proof quantities

| Paper quantity | Definition to inspect | Source |
|---|---|---|
| Dirichlet form `E_K(f,f) = ½ ∫ π(dx) K(x,dy) (f(x)-f(y))²` | `UniformRandomMALA.Dirichlet.energy`, including its factor `1/2` | [KernelMixture.lean](UniformRandomMALA/KernelMixture.lean) |
| Right spectral gap `inf E_K(f,f)/Var_π(f)` over nonconstant `L²(π)` functions | `Concrete.L2RayleighTest`, `rayleighQuotient`, and `rayleighSpectralGap`; the test record requires measurability, `MemLp f 2 π`, and nonzero variance | [RayleighSpectralGap.lean](UniformRandomMALA/Concrete/RayleighSpectralGap.lean) |
| Total variation `sup_A abs(μ(A)-ν(A))` | `UniformRandomMALA.setwiseTV`, with the supremum over measurable sets | [SetwiseTV.lean](UniformRandomMALA/Concrete/SetwiseTV.lean) |
| Stationary flow `J_K(A,B)` and outgoing flow `J_K(A,Aᶜ)` | `Concrete.flow` and `Concrete.boundaryFlow` | [Conductance.lean](UniformRandomMALA/Concrete/Conductance.lean) |
| Rejection probability conditional on the current state, and its dyadic average | `malaRejectionMassReal`, `malaRejectionMassReal_eq_fixed`, and `dyadicAverageRejection` | [MALARejectionGoodSet.lean](UniformRandomMALA/Concrete/MALARejectionGoodSet.lean) |
| Stationary rejection moment in Proposition B.1 | `StationaryMALARejectionMomentBoundOne` integrates the `p`th power of that conditional rejection probability against the target | [RejectionMomentsOne.lean](UniformRandomMALA/Concrete/RejectionMomentsOne.lean) |
| Threshold `p⋆` and right-hand side of Theorem 2.1 | `C1Potential.paperMomentThreshold` and `C1Potential.paperMasterRHS` | [C1MainTheorem.lean](UniformRandomMALA/Concrete/C1MainTheorem.lean) |

Energy, variance, and the gap use nonnegative extended reals (`ℝ≥0∞`);
`ENNReal.ofReal` embeds the real-valued lower bound in this type. The
variance in the quotient is mathlib's `evariance`, which agrees with
ordinary variance for `L²` tests (`MemLp.ofReal_variance_eq`, also used in
[Variance.lean](UniformRandomMALA/Concrete/Variance.lean)).

Some intermediate theorems use `Concrete.spectralGap`, defined through a
Poincaré inequality for all measurable functions. The public endpoints use
`rayleighSpectralGap`. In
[RayleighSpectralGap.lean](UniformRandomMALA/Concrete/RayleighSpectralGap.lean),
`spectralGap_le_rayleighSpectralGap` transfers the internal lower bound,
while `l2SpectralGap_eq_rayleighSpectralGap` proves equivalence with the
Poincaré formulation restricted to `L²`. These bridges make the change of
formulation explicit.

## 3. Trace the proof to its inputs

Read the type and proof of the public endpoint first, then follow the
declarations it invokes. A theorem that takes an isoperimetric or rejection
bound as a hypothesis checks an implication; the full route must also
provide a proof of that hypothesis. The following files show where this
happens for the concrete target and kernels.

| Stage | Files and connections to follow |
|---|---|
| Paper assumptions to the internal potential | [C1ToFirstOrder.lean](UniformRandomMALA/Concrete/C1ToFirstOrder.lean): `upperTaylor` and `toFirstOrderPotential` derive the internal fields from `C1Potential` |
| Stationary rejection to local overlap | [MALAFullPathAssembly.lean](UniformRandomMALA/Concrete/MALAFullPathAssembly.lean): `stationaryMALARejectionMomentBound_paperScale` assembles finite Gaussian likelihood estimates and Euler/RWM weak-limit comparison; [MALAOverlapBounds.lean](UniformRandomMALA/Concrete/MALAOverlapBounds.lean) supplies the rejection input to the overlap argument; [RejectionMomentsOne.lean](UniformRandomMALA/Concrete/RejectionMomentsOne.lean) extends the public range to every real `p ≥ 1` |
| Gaussian isoperimetry to target isoperimetry | [GaussianRampCanonicalInterpolation.lean](UniformRandomMALA/Concrete/GaussianRampCanonicalInterpolation.lean): `DiscreteTime.target_bakryLedoux` closes the Gaussian OU/Bobkov, finite-Euler enlargement, and target weak-limit construction |
| Overlap and separation to component flow | [MALADefectiveConductance.lean](UniformRandomMALA/Concrete/MALADefectiveConductance.lean), [SafeComponent.lean](UniformRandomMALA/Concrete/SafeComponent.lean), and [AllParameterMALAFlow.lean](UniformRandomMALA/Concrete/AllParameterMALAFlow.lean) combine overlap with separated-set bounds |
| Component estimates to the global gap | [Ladder.lean](UniformRandomMALA/Concrete/Ladder.lean) and [LadderComponents.lean](UniformRandomMALA/Concrete/LadderComponents.lean) construct the mixture components and their weights; [ComponentAggregationFinal.lean](UniformRandomMALA/Concrete/ComponentAggregationFinal.lean) and [GlobalFromBakryLedoux.lean](UniformRandomMALA/Concrete/GlobalFromBakryLedoux.lean) assemble the gap bound |
| Discharge isoperimetry and choose universal constants | [UniversalConstants.lean](UniformRandomMALA/Concrete/UniversalConstants.lean) fixes the parameters; `FirstOrderPotential.universal_masterRHS_spectralGap_lower` in [GaussianRampCanonicalInterpolation.lean](UniformRandomMALA/Concrete/GaussianRampCanonicalInterpolation.lean) passes the proved `target_bakryLedoux` into the conditional bound |
| Return to the paper's statement | [C1MainTheorem.lean](UniformRandomMALA/Concrete/C1MainTheorem.lean) applies the preceding theorem to `V.toFirstOrderPotential`, transfers to the Rayleigh gap, and obtains the half-lazy clause and corollary |
| Fixed-step obstruction | [FixedStepHardPotential.lean](UniformRandomMALA/Concrete/FixedStepHardPotential.lean) constructs the smooth witness; [FixedStepHardPotentialObstruction.lean](UniformRandomMALA/Concrete/FixedStepHardPotentialObstruction.lean) proves its gap bound; [FixedStepMinimax.lean](UniformRandomMALA/Concrete/FixedStepMinimax.lean) inserts it into the stated potential class and optimizes over steps |

[PROOF_STRATEGY_LEDGER.md](PROOF_STRATEGY_LEDGER.md) expands these stages.
The [aggregation comparison above](#aggregation-lemma-35-and-theorem-36)
identifies the general statements and their proof, beyond the component
estimates used in the MALA application.
The abstract records in `AnalyticInterfaces.lean` and theorems with names
ending in `_of_bakryLedoux` are useful conditional interfaces. Their
presence is not a gap in the public theorem: inspect the concrete endpoint
above to see the analytic inputs supplied by proved results.

## 4. Check compilation, dependencies, and scope

Run the complete verification commands in [README.md](README.md). The gate
checks all library sources and the public import
[AllResults.lean](UniformRandomMALA/AllResults.lean).
[DependencyAudit.lean](UniformRandomMALA/DependencyAudit.lean) selects the
declarations for `#print axioms`, including the main theorem, both corollary
endpoints, the fixed-step minimax theorem, and both the Poincaré and
spectral-gap forms of the aggregation lemma and theorem.
[check_axioms.py](scripts/check_axioms.py) checks the output against the
allow-list described in [TRUST_BOUNDARY.md](TRUST_BOUNDARY.md).

To inspect the main types and their transitive axiom dependencies separately,
save the following as `Review.lean` in the package directory and run
`lake env lean Review.lean` after building:

```lean
import UniformRandomMALA.AllResults

#print UniformRandomMALA.Concrete.C1Potential
#print UniformRandomMALA.Concrete.C1Potential.paperMasterRHS
#check UniformRandomMALA.Concrete.C1Potential.exists_universal_paperMasterRHS_bounds
#check UniformRandomMALA.Concrete.exists_universal_fixedStepMinimaxGap_paper_upper
#check UniformRandomMALA.Concrete.fractionalAggregation_le_spectralGap
#check UniformRandomMALA.Concrete.hardAssignmentAggregation_le_spectralGap
#print axioms UniformRandomMALA.Concrete.C1Potential.exists_universal_paperMasterRHS_bounds
#print axioms UniformRandomMALA.Concrete.exists_universal_fixedStepMinimaxGap_paper_upper
#print axioms UniformRandomMALA.Concrete.fractionalAggregation_le_spectralGap
#print axioms UniformRandomMALA.Concrete.hardAssignmentAggregation_le_spectralGap
```

Read theorem hypotheses as well as axiom output: an axiom audit does not
show that an assumed analytic bound has been proved, nor that a definition
matches the paper. The statement and definition comparisons above address
those separate questions.

The end-to-end claim concerns the mapped endpoints under their stated
assumptions. For isoperimetry, Lean proves the needed enlargement through
Gaussian OU/Bobkov interpolation and finite-Euler weak limits, whereas the
paper invokes a contraction theorem from the literature. For rejection,
Lean uses finite discrete chains and weak limits. The continuous-time
lemmas B.2–B.5 and Appendix B's additional nonconvex generalization are
outside the formalization. The strongly convex rejection estimate needed
for the main theorem is proved internally. These proof differences and
scope limits are detailed in [THEOREM_MAP.md](THEOREM_MAP.md).
