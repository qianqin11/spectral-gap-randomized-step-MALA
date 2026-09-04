# Trust boundary

Status date: **2026-08-30**

This document states what must be trusted when checking the Lean formalization
of the main lower-bound theorem in Qian Qin and Guanyang Wang's **A Global
Spectral Gap for MALA with a Uniformly Randomized Step Size**. Mathematical assumptions on the target are described
separately in `PAPER_READER_GUIDE.md`.

## Project trust boundary

The project adds no project-specific axioms and contains no `sorry` or
`admit`.  `UniformRandomMALA/DependencyAudit.lean` runs `#print axioms` on
the main declarations.  Their implementation uses only standard
Lean/mathlib logical principles such as `propext`, `Classical.choice`, and
`Quot.sound`.

## Moment-indexed MALA local overlap

```lean
UniformRandomMALA.Concrete.FirstOrderPotential.mala_overlap_bounds
```

is the content-named entry point for `prop:overlap` (Proposition 3.2 in the
current paper draft). It is unconditional and kernel-checked. It takes
neither a stationary
rejection hypothesis nor a continuous-time convergence theorem.  The proof
is a finite discrete-time construction followed by an ordinary Prokhorov
subsequence argument.  Euler--Maruyama and Ethier--Kurtz do not occur.

## Exact paper-form endpoints

The non-lazy Theorem 2.1 endpoint is

```lean
UniformRandomMALA.Concrete.exists_universal_nonlazy_paperMasterRHS_lower
```

It quantifies the universal constants before the dimension and target,
starts from `HessianBoundedPotential`, and concludes the displayed bound for
the manuscript's `L²` Rayleigh spectral gap. The concrete lazy endpoint is
`exists_universal_lazy_paperMasterRHS_lower`. The exact Corollary 2.2
endpoints are
`HessianBoundedPotential.sqrtDimensionCorollary_rayleighSpectralGap_lower`
and
`HessianBoundedPotential.sqrtDimensionCorollarySimplified_rayleighSpectralGap_lower`.

`HessianBoundedPotential.toFirstOrderPotential` constructs the internal
first-order interface from the paper's displayed `C²` bounds on the actual
second Fréchet derivative. It proves the Taylor inequalities, continuity,
and gradient Lipschitz bound, and records mathlib's Riesz gradient of `U`.
The bridge is therefore inside the kernel-checked chain.

`l2PoincareLower_iff_le_rayleighSpectralGap` and
`l2SpectralGap_eq_rayleighSpectralGap` connect the Poincaré and Rayleigh
definitions, including zero variance and infinite energy.
`fractionalAggregation_le_spectralGap` proves Lemma 3.5 using the paper's
`L²` energy-domination scope; its bounded truncations and limiting argument
are checked rather than hidden in a stronger premise.

Everything after Bakry--Ledoux is checked internally:

- standard Gaussian Mills inequalities, quantile estimates, and the shift
  bound;
- separated-set geometry;
- defective conductance for dyadic MALA, including the full-parameter
  Proposition 3.4 wrapper `allParameterMALAFlowBounds`;
- coarea, median truncation, fractional aggregation, and its hard-assignment
  corollary;
- safe-component conductance and spectral gap;
- the geometric ladder, exceptional budget, and exhaustive cut assignment;
- the real and ENNReal harmonic-sum estimates;
- the safe/ladder max-scale assembly;
- explicit admissible choices of `b₀`, `A₀`, and `c₀`.

The lazification proof is concrete: `halfLazyKernel` is the actual
identity/kernel mixture, `Dirichlet.energy_halfLazyKernel` proves exact
half-energy scaling, and `rayleighSpectralGap_halfLazyKernel` proves exact
half-gap scaling.

Accordingly, the exact final theorem has no extra mathematical theorem
argument. `GaussianOUCanonicalInterpolation.lean` proves the differentiated
residual identity and sign, and `GaussianRampCanonicalInterpolation.lean`
connects it to the target and final gap theorem.

No external smooth-ramp or enlargement-continuity premise remains (the
development stage formerly called G5).
`Concrete/GaussianRampMollification.lean` constructs
the smooth distance-ramp approximation by normalized bump convolution.
`Concrete/GaussianEnlargement.lean` proves the transition-strip estimate,
Gaussian perimeter step, intrinsic right-continuity of closed enlargement
masses, Dini/quantile comparison, sharp closed-set inequality, and Radon
inner approximation.

No weak-limit profile premise remains either.
`Concrete/GaussianWeakLimit.lean` proves stability directly for the Gaussian
shift using interior masses and the open/closed Portmanteau sandwich.
`Concrete/FiniteEulerEnlargement.lean` combines this with the finite Gaussian
image estimate.  `FiniteEulerTargetIdentification.lean` proves the explicit
diagonal endpoint laws converge to the normalized `exp(-U)` target, entirely
in discrete time.

The continuous-time Langevin/Davies/Girsanov derivation in Appendix B is not
formalized line by line. The package replaces it with the finite
discrete-time argument above and proves the same public stationary-rejection
and overlap conclusions. No SDE theorem is included in the trust claim.

## Fixed-step minimax theorem

The exact Proposition 2.3 endpoint is

```lean
UniformRandomMALA.Concrete.
  exists_universal_fixedStepMinimaxGap_paper_upper
```

`fixedStepMinimaxGap` is literally an `iSup` over positive steps of an
`sInf` over gap values from `C∞` potentials satisfying the actual Hessian
bounds. The explicit witness belongs to this class by
`fixedStepHardPotential_mem_smoothHessianPotentialGapValues`.

The checked route includes generic Rayleigh upper bounds, the exact
indicator-flow identity, the Gaussian first-coordinate branch, the hard
potential's Hessian and Hastings-ratio calculations, Gaussian trigonometric
expectations and product concentration, acceptance-profile continuity, the
small-ball sticky cut, and the scalar balance theorem
`fixedStepTwoBranchEnvelope_le_log_max_exp`. No certificate parameter or
problem-specific axiom is used.

## Reusable conditional implications

Theorems ending in `_of_bakryLedoux` state conditional mathematical
implications: if a measure has Bakry--Ledoux enlargement, then certain
separated-set, conductance, or spectral-gap estimates follow. They are useful
when applying the downstream machinery to another measure. For this paper's
target, `DiscreteTime.target_bakryLedoux` proves the hypothesis, and the final
theorem supplies it internally. These theorem parameters are not axioms.

## Legacy abstract assembly

`PaperAnalyticInterfaces` and
`paper_interfaces_imply_expanded_main_theorem` remain available. The former
is a record whose fields stand for the analytic inputs of an early modular
version of the paper proof; the latter assembles those fields. They remain
for source compatibility and alternate-input experiments. A reader checking
the completed theorem through `UniformRandomMALA.AllResults` does not need to
construct the record, and its fields are not assumptions of
`exists_universal_nonlazy_paperMasterRHS_lower` or its lazy counterpart.
