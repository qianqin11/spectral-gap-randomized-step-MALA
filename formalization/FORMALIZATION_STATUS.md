# Formalization status

This document records mathematical coverage. [BUILD_STATUS.md](BUILD_STATUS.md)
records the current package build and validation evidence. Use the
[reader guide](PAPER_READER_GUIDE.md) to compare definitions and follow proofs,
and [THEOREM_MAP.md](THEOREM_MAP.md) for exact declarations and manuscript labels.

## Coverage

Every result in the requested scope has a formalized endpoint. The explicit
exclusions are Lemmas B.2–B.5. This coverage statement is separate from the
full package verification gate recorded in `BUILD_STATUS.md`.

| Manuscript result | Coverage and entry point |
|---|---|
| Theorem 2.1 and Corollary 2.2 | Both nonlazy and half-lazy gap statements and all three corollary bounds: [PaperNormalizedGap.lean](UniformRandomMALA/Concrete/PaperNormalizedGap.lean). |
| Proposition 2.3 and Proposition A.1 | Smooth hard potential, fixed-step obstruction, and minimax optimization: [FixedStepMinimax.lean](UniformRandomMALA/Concrete/FixedStepMinimax.lean). |
| Corollary 2.5 and `eq:TVbound` | Actual density and total-variation decay, followed by both mixing-time ceilings: [PaperDensityConvergence.lean](UniformRandomMALA/Concrete/PaperDensityConvergence.lean) and [PaperNormalizedMixing.lean](UniformRandomMALA/Concrete/PaperNormalizedMixing.lean). |
| Corollary 2.6 | Nonlazy and half-lazy CLTs from every initial distribution in [PaperCentralLimit.lean](UniformRandomMALA/Concrete/PaperCentralLimit.lean), with the actual stationary variance limits and both bounds in [PaperAsymptoticVariance.lean](UniformRandomMALA/Concrete/PaperAsymptoticVariance.lean). |
| Corollary 2.7 | Both variance-comparison assertions, including zero-gap and infinite-variance cases: [VarianceSeparationCorollary.lean](UniformRandomMALA/Concrete/VarianceSeparationCorollary.lean) and [VarianceSeparationFixedStep.lean](UniformRandomMALA/Concrete/VarianceSeparationFixedStep.lean). |
| Corollary 2.8 | Both finite-sample mean-square error bounds for the actual nonstationary path law: [PaperNonstationaryMSE.lean](UniformRandomMALA/Concrete/PaperNonstationaryMSE.lean). |
| Section 3 | Mixture energy, overlap, separated sets, flow, fractional aggregation, and component aggregation. In particular, Lemma 3.5 and Theorem 3.6 are general proved theorems in [FractionalAggregation.lean](UniformRandomMALA/Concrete/FractionalAggregation.lean). |
| Proposition B.1 | Full nonconvex `C¹`, Lipschitz-gradient, normalizable Boltzmann scope, for every real `p ≥ 1`: [Nonconvex/StationaryRejection.lean](UniformRandomMALA/Nonconvex/StationaryRejection.lean). |
| Appendices C–F | Gaussian tail and shift estimates, defective conductance, exceptional budgets, aggregation, and ladder bounds; see the [appendix map](THEOREM_MAP.md#appendix-results-and-proof-correspondence). |
| Proposition G.1 and Remark 2.4 | Small-step fixed-MALA gap and its dimension endpoint: [SmallFixedStepGap.lean](UniformRandomMALA/Concrete/SmallFixedStepGap.lean). |
| Lemmas B.2–B.5 | Explicitly excluded. Their continuous-time statements are bypassed by the proved finite-chain rejection argument. |

## What makes the endpoints end-to-end

The main lower-bound input is `C1Potential`: the actual potential is `C¹`,
strongly convex in the first-order sense, and has a Lipschitz gradient.
The adapter proves the descent inequality and uses that actual gradient as
the MALA drift. Target normalization, measurable proposals, acceptance and
rejection, reversibility, isoperimetry, overlap, flow, and aggregation are
constructed or proved before the final spectral-gap theorem is applied.
The universal constants are chosen before the dimension, potential, and step.

The mixing corollary starts from the actual iterated kernel and the initial
Radon–Nikodym density. Full `L²` contraction and density evolution prove both
inequalities in `eq:TVbound`. The initial law has the manuscript's absolute
continuity and square-integrable density assumptions; the mixing prefactor
depends only on the positive tuning parameter.

The sample-average results use `finiteMarkovPathLaw`, its proved coordinate
and pair laws, and the integral defining the actual sample error. The
stationary variance theorem proves existence of the scaled-variance limit
and identifies it through the Poisson equation. The variance-separation
theorem constructs a smooth target and an actual unit-variance observable;
the extended variance theorem covers infinite limits. The nonstationary
MSE proof derives its `L⁴` decay, density pairing, and covariance sum internally.
No external MSE bound is supplied as a hypothesis.

The CLT uses the actual infinite Markov path law, with finite-prefix and
conditional-expectation identities proved from its construction. The
Poisson equation gives genuine adapted martingale increments. Their
Lindeberg tails and conditional variance convergence are proved before the
martingale limit theorem is applied. Bounded-density approximation,
acceptance, and a negligible finite prefix extend the result to every
initial probability measure. The final theorem requires a measurable
`L²(π)` observable and imposes no initial-density or initial-moment condition.

The aggregation lemma and theorem retain their stated energy-domination
and flow hypotheses. These are reusable general theorems. For MALA, the
concrete assembly proves the hypotheses before applying them. Both the
Poincaré and spectral-gap forms are exported and selected for dependency
inspection; the Rayleigh transfer is proved explicitly.

## Analytic route and exclusions

The isoperimetry proof uses Gaussian OU/Bobkov interpolation, finite-Euler
transport, and weak limits. The rejection proof uses finite Gaussian
likelihoods, Euler energy bounds, Euler/RWM comparison, endpoint density
identification, Metropolis meets, and moment interpolation.

For Proposition B.1, `NonconvexPotential` records only the appendix's
regularity, Lipschitz-gradient, and normalizability assumptions. Gradient
moments are proved without assuming target position moments, and the Euler
comparison allows Lipschitz growth instead of relying on convex contraction.
The `Nonconvex/` modules specialize this finite-chain route and reuse its
potential-independent probability lemmas. Lemmas B.2–B.5 are neither
formalized nor assumed by that proof.

Conditional interfaces remain useful intermediate APIs. A theorem taking a
convergence or analytic premise is not, by itself, the paper endpoint; the
reader guide shows where the concrete proof discharges each such premise.

## Verification and correspondence

[README.md](README.md#reproduce-the-verification) gives the check commands.
The Lean build checks proof terms; the selected axiom audit allows only
`propext`, `Classical.choice`, and `Quot.sound`. See
[TRUST_BOUNDARY.md](TRUST_BOUNDARY.md) for the scope of those checks.

The supplied manuscript's Lean-verification narrative predates this
expansion: it still describes Proposition B.1 as restricted to strong
convexity and records older audit counts. The current theorem matches the
full nonconvex mathematical statement. The supplied paper assets are
preserved; use `BUILD_STATUS.md` for current verification evidence.

Manuscript labels, citations, figure dependencies, typesetting, and file
checksums are separate validation evidence. They help locate the right
statement but do not replace comparing mathematical assumptions and
definitions. Historical records describe earlier snapshots, not the current
verification result.
