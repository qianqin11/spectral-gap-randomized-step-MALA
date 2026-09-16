# Formalization status

Current as of **2026-09-15**. All entries marked complete were checked by the
pinned Lean 4.33.0 kernel against mathlib 4.33.0.

## Reader summary

The package is end-to-end for Theorem 2.1 under the revised manuscript's
standing assumptions: `U` is `C¹`, satisfies the first-order `m`-strong
convexity inequality, and has an `L`-Lipschitz actual gradient. No Hessian or
analytic certificate appears in the public theorem. The public endpoint uses
the paper's `L²` Rayleigh spectral gap and includes the concrete half-lazy
kernel.

The complete chain is:

```text
C1Potential
  -> proved descent/upper-Taylor inequality
  -> FirstOrderPotential with gradU = ∇U
  -> target isoperimetry + rejection/overlap + multiscale aggregation
  -> concrete non-lazy uniform MALA gap
  -> exact Rayleigh-gap and half-lazy statements
```

## Paper results

| Paper item | Status | Principal Lean declaration |
|---|---|---|
| Revised first-order assumptions | Complete | `Concrete.C1Potential` |
| Upper Taylor/descent consequence | Complete | `Concrete.C1Potential.upperTaylor` |
| First-order adapter with actual gradient | Complete | `Concrete.C1Potential.toFirstOrderPotential` |
| Poincaré/Rayleigh relationship | Complete | `Concrete.l2PoincareLower_iff_le_rayleighSpectralGap`; `Concrete.l2SpectralGap_eq_rayleighSpectralGap` |
| Theorem 2.1, non-lazy | Complete | `Concrete.C1Potential.universal_masterRHS_rayleighSpectralGap_lower` |
| Theorem 2.1, concrete lazy | Complete | `Concrete.C1Potential.universal_half_masterRHS_lazy_rayleighSpectralGap_lower` |
| Theorem 2.1, shared existential constants | Complete | `Concrete.C1Potential.exists_universal_paperMasterRHS_bounds` |
| Corollary 2.2, first display | Complete | `Concrete.C1Potential.sqrtDimensionCorollary_rayleighSpectralGap_lower` |
| Corollary 2.2, simplified display | Complete | `Concrete.C1Potential.sqrtDimensionCorollarySimplified_rayleighSpectralGap_lower` |
| Lemma 3.1, mixture-energy comparison | Complete | `Dirichlet.sum_energy_parameterMixture_restrict_le`; `Concrete.FirstOrderPotential.energy_restricted_uniformStep_eq_weight_dyadic` |
| Proposition 3.2, overlap for `p ≥ 1` | Complete | `Concrete.C1Potential.mala_overlap_bounds` |
| Proposition 3.3, separated sets | Complete | `Concrete.C1Potential.separatedSets` |
| Proposition 3.4, full parameters | Complete | `Concrete.C1Potential.allParameterMALAFlowBounds` |
| Lemma 3.5, fractional aggregation | Complete | `Concrete.fractionalAggregation_poincareLower`; `fractionalAggregation_le_spectralGap` |
| Theorem 3.6, hard-assignment aggregation | Complete | `Concrete.hardAssignmentAggregation_poincareLower`; `Concrete.hardAssignmentAggregation_le_spectralGap` |
| Proposition A.1, smooth hard-witness obstruction | Complete | `Concrete.exists_universal_fixedStepHardPotential_obstruction_allDimensions` and the smoothness/Hessian declarations in `Concrete/FixedStepHardPotential.lean` |
| Proposition 2.3, fixed-step minimax obstruction | Complete | `Concrete.exists_universal_fixedStepMinimaxGap_paper_upper` |
| Proposition B.1 in the standing strongly convex setup | Complete | `Concrete.C1Potential.stationary_rejection_moments` |
| Appendix B's extra nonconvex `C¹` generalization | Not formalized | See limitation below |

## Revised universal-constant range

Theorem 2.1 and Proposition 3.4 in the revised PDF allow a universal
`A₀ ≥ 1`. The public main-theorem existential statement and the smooth
compatibility statements now use this exact range. Their common witness
remains `concreteA0 ≥ 2`, so the internal `Parameters.hA0` assumption and
all downstream moment estimates remain valid. This is an existential choice;
the theorem does not claim the bound for every `A₀ ≥ 1` or for `A₀ = 1`.

## First-order bridge

`C1Potential` uses mathlib's `gradient U`, the Riesz representative of the
Fréchet derivative. Its `ContDiff ℝ 1 U` field supplies differentiability and
continuity. The lower Taylor inequality is assumed exactly as in the revised
standing setup. The upper inequality is proved by differentiating a scalar
residual along `x + s • (y-x)` and applying gradient Lipschitzness and
Cauchy--Schwarz. Thus the internal MALA drift is not an unrelated recorded
field and the proof does not pass through the old Hessian adapter.

`HessianBoundedPotential.toFirstOrderPotential` remains a checked reusable
smooth special case. It is needed for smooth examples and the hard witness in
Proposition 2.3, not for the revised lower-bound theorem.

## Analytic core

The certificate-free core proves target Gaussian enlargement by a discrete
route: Gaussian OU/Bobkov interpolation and smooth ramps, finite-Euler
transport estimates, weak-limit stability, and identification of the target.
The rejection estimate is likewise discrete, using finite Gaussian
likelihoods, finite-Euler energy control, Euler/RWM comparison, and weak-limit
closure. The `p ≥ 1` public range follows from a checked moment-interpolation
lemma and the sharper `p ≥ 2` core. The reusable interpolation lemma assumes
integrability of both powers appearing in its statement; the rejection
wrapper discharges those hypotheses from boundedness of the rejection mass.

The concrete identity kernel and half-lazy mixture are Markov and reversible;
their Dirichlet energy and Rayleigh gap scale by exactly `1/2`. Corollary 2.2's
scalar simplification does not assume `pStar ≤ d`.

The fractional aggregation result has the paper's full `L²` scope, including
bounded truncations, weighted Cauchy--Schwarz, zero weights, extended-valued
energies, and the limit passage. The hard-assignment theorem is a corollary.

The fixed-step obstruction contains the smooth hard potential, Hessian bounds,
Gaussian trigonometric identities and concentration, local test-function and
sticky-cut bounds, and the final minimax scalar optimization.

## Verification evidence

The fail-closed PowerShell gate completed successfully:

```text
STATIC AUDIT PASSED
FIRST-ORDER SOURCE AUDIT PASSED
MANUSCRIPT PDF AUDIT PASSED
PDF AUDIT REGRESSION TESTS: 7 passed
NUMERIC SANITY PASSED
Build completed successfully (3439 jobs).
AXIOM AUDIT PASSED: 266 declarations; only
  ['Classical.choice', 'Quot.sound', 'propext']
FULL SOURCE BUILD AND AXIOM AUDIT PASSED
```

The static audit covered 155 Lean files and counted 2,069 top-level
`def`/`lemma`/`theorem`/`structure` declarations with its source regex; this is
not a count of every declaration in the elaborated Lean environment. It found
no `sorry`, `admit`, project axiom, unsafe declaration, `native_decide`,
`implemented_by`, or `sorryAx`. The public `AllResults.lean` import was checked
separately. Mathlib is the only direct external Lean library.

## Remaining limitation

The package does not prove the independent Appendix B extension to arbitrary
possibly nonconvex `C¹` potentials with Lipschitz gradient and integrable
`exp(-U)`, nor does it formalize the manuscript's continuous-time SDE proof
line by line. This is a mathematical-scope omission, not an unfilled premise in
Theorem 2.1: the verified discrete proof supplies its rejection input under
the theorem's standing strong-convexity assumptions.

The current manuscript distribution is PDF-only: `paper/` contains
`main.pdf` and no other files. Its SHA-256 is
`eb3ec374502cbc7b01a2552164f8d64693f64fef333f9948173f575d09a6c4f9`.
The PDF identity and inventory are checked by `scripts/manuscript_audit.py`.
No current TeX build, source-label/reference/citation audit, or separate
figure-source verification is claimed. Superseded manuscript build evidence
is preserved under `validation/historical/2026-09-12/`.
