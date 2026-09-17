# Historical note: the first-order interface

This note describes the transition to the first-order manuscript interface
recorded in the 2026-09-12 validation. Current manuscript inventory,
mathematical coverage, and verification results are documented in
[PACKAGE_MANIFEST.md](PACKAGE_MANIFEST.md),
[FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md), and
[BUILD_STATUS.md](BUILD_STATUS.md).

## Change in the mathematical interface

The public interface moved from a Hessian-bounded smooth potential to a
continuously differentiable potential satisfying, for all `x,y`,

```text
U(y) ≥ U(x) + ⟪∇U(x), y-x⟫ + (m/2)‖y-x‖²,
‖∇U(y)-∇U(x)‖ ≤ L‖y-x‖,
```

with `0 < m ≤ L`. These are the assumptions now labeled
`eq:first-order-assumptions` in the manuscript source.

`Concrete/C1ToFirstOrder.lean` introduced `C1Potential`, using
`ContDiff ℝ 1 U` and mathlib's actual Riesz gradient `∇ U`.
`C1Potential.upperTaylor` derives the upper Taylor inequality by restricting
the potential to an affine line. `C1Potential.toFirstOrderPotential` supplies
the internal record with `gradU := ∇ U` definitionally. This connects the
first-order assumptions to the existing analytic core without adding an
upper-Taylor or result-specific analytic certificate.

Three further modules expose this route:

- `DiscreteTime/MomentInterpolation.lean` supplies the interpolation used for
  `1 ≤ p ≤ 2`;
- `Concrete/RejectionMomentsOne.lean` extends the public rejection and overlap
  range to `p ≥ 1`;
- `Concrete/C1MainTheorem.lean` exports the main theorem (`thm:main`),
  corollary (`cor:sqrt-d-endpoint`), and ingredient bounds directly from
  `C1Potential`.

The retained `p ≥ 2` core gives sharper constants than the public `p ≥ 1`
wrappers and continues to support the multiscale argument.

## Relation to the proof in the paper

The isoperimetric argument in Lean uses Gaussian OU/Bobkov interpolation,
smooth ramps, finite-Euler transport, and a weak limit. The rejection
argument uses finite Gaussian likelihoods, Euler energy estimates,
Euler/RWM comparison, and weak-limit closure. These constructions use the
first-order interface; they do not require a Hessian bound on the potential.

The scope qualification introduced with this interface remains relevant:
Appendix B's additional nonconvex `C¹` generalization and continuous-time
proof are not formalized. The Lean rejection theorem retains strong
convexity and supplies the input required by the main theorem. The older
`HessianBoundedPotential` adapter remains available for smooth special
cases and the fixed-step hard witness.

## Historical evidence and current distribution

Earlier Hessian-facing records are retained under
`validation/historical/pre-first-order/`. Manuscript build and source-audit
records from the first-order transition are retained under
`validation/historical/2026-09-12/`. Their dates, counts, and manuscript
checksums describe those historical versions.

The current `paper/` directory includes `main.tex`, `main.pdf`,
`uniform_random_mala.bib`, and the three figure PDFs. The current public
existential theorem states the paper's `A₀ ≥ 1` range, with an internal
witness satisfying `A₀ ≥ 2`. The authoritative current PDF digest is
[validation/manuscript-pdf.sha256](validation/manuscript-pdf.sha256).
Use the current check scripts and `BUILD_STATUS.md` to reproduce and
interpret validation of the present source.
