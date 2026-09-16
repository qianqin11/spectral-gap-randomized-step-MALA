# Completion report — first-order revision audit

Date: **2026-09-15**  
Toolchain: **Lean 4.33.0 / mathlib 4.33.0**  
Result: **full build, public-import check, and axiom gate passed**

## Executive result

The package is end-to-end for the revised form of Theorem 2.1. Its public
input is a continuously differentiable potential satisfying the displayed
first-order strong-convexity inequality and global Lipschitz continuity of the
actual Riesz gradient. The proof derives the upper Taylor inequality and then
uses the established certificate-free, discrete analytic core. Neither the
main theorem nor its lazy and square-root-dimension corollaries assume a
Hessian, an independently supplied drift, or a paper-specific analytic axiom.

The original first-order revision candidate did not initially compile. All discovered
source errors and the broken public import were corrected without changing
the mathematical statements or adding proof bypasses. A final fail-closed
PowerShell run built the complete package and checked actual axiom output.

## Paper-to-Lean endpoints

All names below begin with `UniformRandomMALA.Concrete.` unless a different
prefix is shown.

| Revised paper content | Exact Lean declaration | Status |
|---|---|---|
| Standing `C¹` first-order assumptions | `C1Potential` | Checked |
| Derived upper Taylor/descent inequality | `C1Potential.upperTaylor` | Checked |
| Actual-gradient internal adapter | `C1Potential.toFirstOrderPotential` | Checked |
| `L²` Poincaré/Rayleigh equivalence | `l2PoincareLower_iff_le_rayleighSpectralGap`; `l2SpectralGap_eq_rayleighSpectralGap` | Checked |
| Theorem 2.1, non-lazy | `C1Potential.universal_masterRHS_rayleighSpectralGap_lower` | Checked |
| Theorem 2.1, concrete half-lazy | `C1Potential.universal_half_masterRHS_lazy_rayleighSpectralGap_lower` | Checked |
| Theorem 2.1, both clauses and shared constants | `C1Potential.exists_universal_paperMasterRHS_bounds` | Checked |
| Corollary 2.2, first display | `C1Potential.sqrtDimensionCorollary_rayleighSpectralGap_lower` | Checked |
| Corollary 2.2, simplified display | `C1Potential.sqrtDimensionCorollarySimplified_rayleighSpectralGap_lower` | Checked |
| Lemma 3.1, mixture-energy comparison | `Dirichlet.sum_energy_parameterMixture_restrict_le`; `FirstOrderPotential.energy_restricted_uniformStep_eq_weight_dyadic` | Checked |
| Proposition 3.2 (`p ≥ 1`) | `C1Potential.mala_overlap_bounds` | Checked |
| Proposition 3.3 | `C1Potential.separatedSets` | Checked |
| Proposition 3.4, full range | `C1Potential.allParameterMALAFlowBounds` | Checked |
| Proposition B.1 under the standing strong-convexity setup | `C1Potential.stationary_rejection_moments` | Checked |
| Lemma 3.5, fractional form | `fractionalAggregation_poincareLower`; `fractionalAggregation_le_spectralGap` | Checked |
| Theorem 3.6, hard-assignment aggregation | `hardAssignmentAggregation_poincareLower`; `hardAssignmentAggregation_le_spectralGap` | Checked |
| Proposition A.1, smooth hard-witness obstruction | `exists_universal_fixedStepHardPotential_obstruction_allDimensions` plus the smoothness and Hessian-bound declarations | Checked |
| Proposition 2.3, fixed-step minimax | `exists_universal_fixedStepMinimaxGap_paper_upper` | Checked |

`THEOREM_MAP.md` gives the finer-grained component map.

## What the first-order bridge proves

`C1Potential` stores `ContDiff ℝ 1 U`, the lower first-order strong-convexity
inequality expressed with mathlib's `∇ U`, and `LipschitzWith` for that same
gradient. The proof of `upperTaylor` restricts `U` to an affine line, computes
the derivative of the residual, applies Cauchy--Schwarz and the Lipschitz
bound, and obtains monotonicity. In `toFirstOrderPotential`, the field
`gradU` is definitionally `∇ U`.

This avoids the circularity that would arise from recording an arbitrary
vector field and calling it a gradient. The previous
`HessianBoundedPotential.toFirstOrderPotential` theorem remains checked as an
optional smooth special case; it is not used as a premise by the revised
paper-facing endpoint.

## Other reusable results retained or added

- exact equivalence between the `L²` Poincaré and Rayleigh-infimum spectral
  gaps, including zero variance and infinite-energy cases;
- exact Markov, reversibility, energy, and Rayleigh-gap identities for the
  half-lazy kernel;
- a real-exponent moment inequality for `1 ≤ p ≤ 2`, assuming
  integrability of the `p`-th and second powers as stated in the API; the
  rejection application proves those hypotheses from boundedness;
- fractional finite-component aggregation with weighted Cauchy--Schwarz,
  bounded `L²` truncations, extended values, and hard assignment as a
  corollary;
- Gaussian OU/Bobkov interpolation, smooth-ramp approximation, finite-Euler
  transport, and weak-limit stability for target enlargement;
- generic Rayleigh test-function and indicator-cut upper bounds;
- the smooth hard potential, Gaussian trigonometric identities and product
  concentration used in the sticky-region obstruction.

See `REUSABLE_RESULTS.md` for theorem names and imports.

## Candidate defects corrected

### Lean source

- `Concrete/C1ToFirstOrder.lean`: made the nonnegative-real Lipschitz constant
  coercion explicit and gave the C1 adapter's private Euclidean instances
  distinct names, preventing a collision when the legacy Hessian adapter is
  imported in the same environment.
- `DiscreteTime/MomentInterpolation.lean`: removed unreachable `ring` tactics
  rejected by the pinned elaborator.
- `Concrete/RejectionMomentsOne.lean`: explicitly included the section
  potential where needed, replaced several failed automation calls by direct
  nonnegativity proofs, and removed an unused binder warning.
- `Concrete/C1MainTheorem.lean`: added a direct C1 wrapper for the full
  Proposition 3.4 conclusion.
- `AllResults.lean`: moved the revision import out of the module comment. The
  original candidate's apparent imports were inert, so its advertised public
  facade did not expose the new theorem.
- `DependencyAudit.lean`: added the C1 Proposition 3.4 endpoint to the actual
  axiom audit.
- `HessianMainTheorem.lean`, `LazyKernel.lean`, and
  `SqrtDimensionCorollary.lean`: relabeled Hessian endpoints as legacy smooth
  special cases so readers do not mistake them for the revised assumptions.

### Audit infrastructure

- `scripts/static_audit.py`: strips comments and strings before checking root
  imports, so commented imports cannot satisfy the coverage gate.
- `scripts/first_order_audit.py`: verifies reachability of every new public
  module from `AllResults`.
- `scripts/check.ps1`: detects either `python` or the Windows `py -3` launcher.
- Current reader documentation and curated validation records were rewritten
  to describe the checked first-order release rather than the pre-build
  candidate.

## Files changed by this audit

Lean and audit source:

- `UniformRandomMALA/AllResults.lean`
- `UniformRandomMALA/AnalyticInterfaces.lean`
- `UniformRandomMALA/MALAOverlap.lean`
- `UniformRandomMALA/SpectralGap.lean`
- `UniformRandomMALA/Concrete/C1ToFirstOrder.lean`
- `UniformRandomMALA/Concrete/C1MainTheorem.lean`
- `UniformRandomMALA/Concrete/GlobalFromBakryLedoux.lean`
- `UniformRandomMALA/Concrete/HessianMainTheorem.lean`
- `UniformRandomMALA/Concrete/LazyKernel.lean`
- `UniformRandomMALA/Concrete/MALADefectiveConductance.lean`
- `UniformRandomMALA/Concrete/MALAOverlapBounds.lean`
- `UniformRandomMALA/Concrete/RejectionMomentsOne.lean`
- `UniformRandomMALA/Concrete/SqrtDimensionCorollary.lean`
- `UniformRandomMALA/DependencyAudit.lean`
- `UniformRandomMALA/DiscreteTime/MomentInterpolation.lean`
- `UniformRandomMALA/DiscreteTime/StationaryRejection.lean`
- `scripts/check.ps1`
- `scripts/check_axioms.py`
- `scripts/first_order_audit.py`
- `scripts/manuscript_audit.py`
- `scripts/static_audit.py`

Documentation/validation:

- repository-level `../README.md`, `../simulation/README.md`, and
  `../simulation/Makefile`
- `README.md`, `BUILD_STATUS.md`, `CHECK_STATUS.txt`, `CHECK_OUTPUT.txt`
- `BAKRY_LEDOUX_DISCRETE_LANGEVIN_PROOF.md` and
  `LEAN_FRIENDLY_PROOF_LEDGER.md`
- `COMPLETION_REPORT.md`, `FIRST_ORDER_REVISION.md`
- `FORMALIZATION_REPORT.md`, `FORMALIZATION_STATUS.md`
- `PACKAGE_MANIFEST.md`, `PAPER_READER_GUIDE.md`
- `PROOF_STRATEGY_LEDGER.md`, `REUSABLE_RESULTS.md`, `THEOREM_MAP.md`
- `TRUST_BOUNDARY.md`, `WORKLOG.md`
- `paper/`: the revised `main.pdf` only
- current files under `validation/` and the regenerated checksum manifest

## Reproducible validation

From `formalization/` on Windows:

```powershell
lake exe cache get
powershell -ExecutionPolicy Bypass -File .\scripts\check.ps1
```

The final run produced:

```text
Lake version 5.0.0-src+d8b1897 (Lean version 4.33.0)
STATIC AUDIT PASSED
  155 Lean files; 2069 declarations; 5808 `by` blocks
FIRST-ORDER SOURCE AUDIT PASSED
MANUSCRIPT PDF AUDIT PASSED
PDF AUDIT REGRESSION TESTS: 7 passed
NUMERIC SANITY PASSED
Build completed successfully (3439 jobs).
AXIOM AUDIT PASSED: 266 declarations; only
  ['Classical.choice', 'Quot.sound', 'propext']
FULL SOURCE BUILD AND AXIOM AUDIT PASSED
```

The static auditor's `2069 declarations` line is a source-regex count of
top-level `def`, `lemma`, `theorem`, and `structure` declarations. It is not a
count of every declaration in the elaborated Lean environment.

The command `lake env lean UniformRandomMALA/AllResults.lean` was also run by
the wrapper and succeeded. `validation/local/axioms.log` contains the full
machine-generated output in the working build; local logs and `.lake/` are
excluded from the release ZIP because they are large and reproducible.

Principal C1 endpoints each printed exactly:

```text
[propext, Classical.choice, Quot.sound]
```

This includes `upperTaylor`, `toFirstOrderPotential`, target enlargement,
rejection/overlap, full-parameter flow, both main clauses, shared-constant
packaging, and both Corollary 2.2 endpoints.

## Manuscript/package synchronization

`paper/` contains only the revised 47-page `main.pdf`, with SHA-256
`eb3ec374502cbc7b01a2552164f8d64693f64fef333f9948173f575d09a6c4f9`.
Its Section 2 first-order assumptions match `C1Potential`. The public
existential statements now expose `A₀ ≥ 1`, matching Theorem 2.1, while
retaining the internal witness `concreteA0 ≥ 2`.

The PDF audit checks the recorded checksum, basic PDF header/end marker,
and the single-file inventory. It is not a source or mathematical-content
audit. TeX, bibliography, and separate figure files are not bundled, so no
current LaTeX build or source-reference/citation audit is claimed.
The previous manuscript build and source-audit logs are retained under
`validation/historical/2026-09-12/` for provenance.

## Remaining omissions

One mathematical-scope item remains: Appendix B's independent extension of
the rejection lemmas to possibly nonconvex `C¹` potentials with Lipschitz
gradient and integrable `exp(-U)` is not formalized. The Lean rejection theorem
retains the paper's standing strong-convexity input and supplies everything
needed by Theorem 2.1. Classify this as **additional mathematical/library
formalization work**, not an end-to-end gap in the checked main theorem.

No kernel, dependency, public-import, packaging, or engineering blocker
remains for checking the delivered source. The manuscript's continuous-time
SDE derivation is not claimed; the checked proof uses the discrete alternative.
