# Formalization status

This document describes the mathematical scope of the accompanying Lean
source. [BUILD_STATUS.md](BUILD_STATUS.md) records the latest kernel check
and manuscript validation. The paper, TeX source, bibliography, and figure
PDFs are bundled in `paper/`. Use the [reader guide](PAPER_READER_GUIDE.md)
for a reading route and [the theorem map](THEOREM_MAP.md) to locate individual
statements and their definitions.

## Main result

The package gives an end-to-end proof of Theorem 2.1 (`thm:main`) under the
paper's first-order assumptions (`eq:first-order-assumptions`): `U` is `C¹`,
satisfies the `m`-strong-convexity supporting inequality, and has an
`L`-Lipschitz actual gradient. The public theorem uses the paper's `L²`
Rayleigh spectral gap and covers both the concrete non-lazy uniform MALA
kernel and its half-lazy version.

```text
C1Potential
  -> derived upper Taylor inequality
  -> FirstOrderPotential with gradU = ∇U
  -> target isoperimetry, rejection/overlap, and multiscale aggregation
  -> concrete uniform MALA gap
  -> Rayleigh-gap and half-lazy statements
```

The public statement chooses its universal constants before the dimension,
potential, and step endpoint, and uses the same constants for both clauses.

## General aggregation results

The fractional aggregation lemma (Lemma 3.5, `lem:fractional`) and the
component-aggregation theorem (Theorem 3.6, `thm:aggregation`) are also
formalized as reusable results for finite families of Markov kernels,
independently of MALA or the assumptions on its potential.
[FractionalAggregation.lean](UniformRandomMALA/Concrete/FractionalAggregation.lean)
proves `fractionalAggregation_poincareLower` and
`fractionalAggregation_le_spectralGap`, then derives
`hardAssignmentAggregation_poincareLower` and
`hardAssignmentAggregation_le_spectralGap` by the paper's reciprocal-flow
coefficient substitution. The energy-domination premise has exactly the
paper's `L²` scope. The internal gap bounds transfer to the paper's Rayleigh
gap through `spectralGap_le_rayleighSpectralGap`.

All four declarations are exported by
[AllResults.lean](UniformRandomMALA/AllResults.lean) and included in
[DependencyAudit.lean](UniformRandomMALA/DependencyAudit.lean). The
[reader guide](PAPER_READER_GUIDE.md#aggregation-lemma-35-and-theorem-36)
locates their statements and explains how they connect to the paper.

## Coverage of paper results

In this table, “formalized” describes the result's presence in the Lean
source; verification evidence is maintained separately in `BUILD_STATUS.md`.
Declaration names have prefix `UniformRandomMALA.`.

| Paper item and TeX label | Scope | Principal Lean declaration |
|---|---|---|
| First-order assumptions (`eq:first-order-assumptions`) | Formalized | `Concrete.C1Potential` |
| Upper Taylor consequence and actual-gradient adapter | Formalized | `Concrete.C1Potential.upperTaylor`; `Concrete.C1Potential.toFirstOrderPotential` |
| Poincaré/Rayleigh relationship | Formalized | `Concrete.l2PoincareLower_iff_le_rayleighSpectralGap`; `Concrete.l2SpectralGap_eq_rayleighSpectralGap` |
| Theorem 2.1 (`thm:main`), non-lazy | Formalized | `Concrete.C1Potential.universal_masterRHS_rayleighSpectralGap_lower` |
| Theorem 2.1, half-lazy | Formalized | `Concrete.C1Potential.universal_half_masterRHS_lazy_rayleighSpectralGap_lower` |
| Theorem 2.1, both clauses with shared constants | Formalized | `Concrete.C1Potential.exists_universal_paperMasterRHS_bounds` |
| Corollary 2.2 (`cor:sqrt-d-endpoint`), first bound | Formalized | `Concrete.C1Potential.sqrtDimensionCorollary_rayleighSpectralGap_lower` |
| Corollary 2.2, simplified bound | Formalized | `Concrete.C1Potential.sqrtDimensionCorollarySimplified_rayleighSpectralGap_lower` |
| Corollary 2.2, tuned third bound | Formalized | `Concrete.C1Potential.tunedSqrtDimensionCorollary_rayleighSpectralGap_lower` |
| TV decay `eq:TVbound`, half-lazy reversible kernels | Formalized | `Concrete.setwiseTV_iterate_halfLazy_le` |
| Corollary 2.4 (`cor:mixing`), both ceiling inequalities | Formalized | `Concrete.C1Potential.mixingTimeCorollary` |
| Corollary 2.4, optional fixed-tuning specialization | Formalized | `Concrete.C1Potential.exists_universal_mixingTimeCorollary` |
| Lemma 3.1 (`lem:Kt`), mixture-energy comparison | Formalized | `Dirichlet.sum_energy_parameterMixture_restrict_le`; `Concrete.FirstOrderPotential.energy_restricted_uniformStep_eq_weight_dyadic` |
| Proposition 3.2 (`prop:overlap`), `p ≥ 1` | Formalized | `Concrete.C1Potential.mala_overlap_bounds` |
| Proposition 3.3 (`prop:separated`) | Formalized | `Concrete.C1Potential.separatedSets` |
| Proposition 3.4 (`prop:flow`), both flow bounds | Formalized | `Concrete.C1Potential.allParameterMALAFlowBounds` |
| Lemma 3.5 (`lem:fractional`) | Formalized | `Concrete.fractionalAggregation_poincareLower`; `fractionalAggregation_le_spectralGap` |
| Theorem 3.6 (`thm:aggregation`) | Formalized | `Concrete.hardAssignmentAggregation_poincareLower`; `Concrete.hardAssignmentAggregation_le_spectralGap` |
| Proposition A.1 (`prop:generic-fixed-step-obstruction`) | Formalized, smooth hard witness | `Concrete.exists_universal_fixedStepHardPotential_obstruction_allDimensions` and the smoothness/Hessian declarations in `Concrete/FixedStepHardPotential.lean` |
| Proposition 2.3 (`prop:minimax-fixed-step-ceiling`) | Formalized | `Concrete.exists_universal_fixedStepMinimaxGap_paper_upper` |
| Proposition B.1 (`prop:stationary-rejection`) | Formalized under standing strong convexity | `Concrete.C1Potential.stationary_rejection_moments` |
| Appendix B's additional nonconvex `C¹` scope | Not formalized | See below |

[THEOREM_MAP.md](THEOREM_MAP.md) supplies the more detailed component map.

## Mixing-time corollary

The mixing-time proof starts from the actual half-lazy uniform MALA kernel
and its proved Rayleigh gap. It establishes exact `L²` contraction of
bounded centered observables, pairs their iterates with the initial
Radon–Nikodym density, and obtains total-variation decay with the paper's
factor `1/2`. The initial law is absolutely continuous with square-integrable
density, as in the manuscript. The proof covers zero mixing time and the
maximal lazy-gap case.

The mixing prefactor depends only on the positive tuning constant `c`,
matching the manuscript. An optional specialization fixes a universal
tuning and obtains a universal prefactor. See the
[reader guide](PAPER_READER_GUIDE.md#main-results) for the declarations and
[the theorem map](THEOREM_MAP.md#main-results) for the explicit constant.

## Analytic route and scope qualifications

`C1Potential` uses mathlib's `gradient U`, the Riesz representative of the
Fréchet derivative. The proof derives the upper Taylor inequality by
restricting the potential to an affine line and applying the gradient
Lipschitz bound. The internal MALA drift is definitionally this gradient.
The optional `HessianBoundedPotential.toFirstOrderPotential` adapter is a
smooth special case used by the hard example, not a hypothesis of the
lower-bound endpoint.

Target Gaussian enlargement is proved through Gaussian OU/Bobkov
interpolation, smooth ramps, finite-Euler transport, weak-limit stability,
and identification of the target. Rejection moments use finite Gaussian
likelihoods, finite-Euler energy estimates, Euler/RWM comparison, and
weak-limit closure. The public `p ≥ 1` range follows by moment interpolation
from the retained `p ≥ 2` core; the rejection wrapper supplies the required
integrability from boundedness of the rejection mass.

The concrete half-lazy kernel is Markov and reversible, with Dirichlet
energy and Rayleigh gap equal to one half of those of the non-lazy kernel.
The simplification in Corollary 2.2 does not assume `pStar ≤ d`.
The aggregation proofs allow extended-valued energies and zero fractional
flow coefficients, using bounded truncations and monotone convergence.

The package does not prove the independent Appendix B extension to arbitrary
possibly nonconvex `C¹` potentials with Lipschitz gradient and integrable
`exp(-U)`. It also does not transcribe the continuous-time proofs of
`lem:linear-increment`, `lem:integrated-increments`,
`lem:frozen-endpoint-law`, or `lem:path-likelihood`. The discrete proof
supplies the strongly convex rejection input needed for Theorem 2.1.

## Validation and manuscript correspondence

[README.md](README.md) gives reproducible check commands.
[TRUST_BOUNDARY.md](TRUST_BOUNDARY.md) explains the logical assumptions and
the finite selection used by the axiom audit. Manuscript source checks
compare active TeX labels, references, citations, and figure dependencies,
and validate Lean's paper references. The supplied PDF's identity is
recorded in [validation/manuscript-pdf.sha256](validation/manuscript-pdf.sha256).
These checks are separate from kernel verification and LaTeX typesetting;
`BUILD_STATUS.md` reports the results of each. Older records under
`validation/historical/` preserve provenance and are not current results.
