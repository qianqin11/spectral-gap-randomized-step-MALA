# First-order manuscript and Lean revision

Original first-order revision and kernel-validation date: **2026-09-12**.
The subsequent PDF-only and `A₀ ≥ 1` reconciliation is recorded in
`FORMALIZATION_STATUS.md` and `BUILD_STATUS.md`.

## Outcome

The revised package is kernel-checked with Lean/mathlib 4.33.0. A complete
`lake build` succeeded, `UniformRandomMALA/AllResults.lean` elaborated as the
public entry point, and the actual dependency audit passed for 266 requested
declarations with only `propext`, `Classical.choice`, and `Quot.sound`.

The original revision candidate was not buildable as supplied. The audit
repaired elaboration errors in the descent and moment proofs, a private-name
collision, and public imports that had been placed inside a comment. The
source gates were strengthened so that a commented-out public import cannot
again pass unnoticed. No mathematical claim was weakened and no axiom,
`sorry`, or certificate parameter was introduced.

The current manuscript is the revised 47-page `paper/main.pdf`.
Only that PDF is distributed in `paper/`; TeX, bibliography, and separate
figure files are not bundled. Its identity is recorded in
`validation/manuscript-pdf.sha256`. The old LaTeX build and source-audit
records are historical evidence under `validation/historical/2026-09-12/`.
Historical verification documents for the earlier Hessian-facing package are
retained under `validation/historical/pre-first-order/`.

## Revised standing assumptions

The manuscript now assumes that `U` is continuously differentiable, `m > 0`,
`m ≤ L`, and, for all `x,y`,

```text
U(y) ≥ U(x) + ⟪∇U(x), y-x⟫ + (m/2)‖y-x‖²,
‖∇U(y)-∇U(x)‖ ≤ L‖y-x‖.
```

The upper Taylor bound is a consequence (the descent lemma), not an input.
The `C∞` class in the fixed-step minimax obstruction remains deliberate: the
hard example is smooth, so that obstruction holds even on the smooth subclass.

## Lean realization

`Concrete/C1ToFirstOrder.lean` defines `C1Potential`. Its fields are:

- `ContDiff ℝ 1 U`;
- the strong-convexity supporting inequality;
- `LipschitzWith` for mathlib's actual Riesz gradient `∇ U`;
- the scalar and dimension side conditions.

It does not store a Hessian, an independent vector field, an upper-Taylor
certificate, or a result-specific analytic certificate.
`C1Potential.upperTaylor` differentiates the potential along the affine line
from `x` to `y` and proves the descent inequality by a one-dimensional
monotonicity argument. `C1Potential.toFirstOrderPotential` then supplies the
existing internal record with `gradU := ∇ U` definitionally.

Three additional revision modules complete the public route:

- `DiscreteTime/MomentInterpolation.lean` proves the `L²`-to-`Lᵖ`
  interpolation used when `1 ≤ p ≤ 2`;
- `Concrete/RejectionMomentsOne.lean` extends stationary rejection and overlap
  to the paper's range `p ≥ 1`;
- `Concrete/C1MainTheorem.lean` exports the main lazy/non-lazy theorem,
  Corollary 2.2, isoperimetry, separated sets, rejection/overlap, and
  Proposition 3.4 directly from `C1Potential`.

The public `p ≥ 1` overlap constants are `1/(32e)` and `12288 e³`. The sharper
historical `p ≥ 2` bounds at `1/(16e)` and `6144 e³` remain internal inputs to
the multiscale proof, so the main theorem's explicit universal witnesses are
unchanged.

## Why the analytic core remains first order

The manuscript cites Caffarelli's contraction theorem in the nonsmooth form
justified by Kim and Milman. The Lean proof does not assume that external
theorem. Its established core proves Gaussian enlargement via Gaussian
OU/Bobkov interpolation and smooth ramps, transports the estimate to finite
Euler endpoint laws, and identifies a weak limit with the target. Those
constructions use the first-order potential interface.

Similarly, the manuscript's rejection proof uses stationary time reversal,
Girsanov, and martingale estimates. Lean instead uses finite Gaussian
likelihoods, finite-Euler energy bounds, Euler/RWM comparison, and weak-limit
closure. This discrete route is an alternative proof of the strongly convex
input needed by Theorem 2.1, not a formalization of the continuous-time SDE
argument.

Relevant literature retained by the manuscript includes:

- Caffarelli, *Comm. Math. Phys.* 214 (2000), 547--563;
- Kim and Milman, *Math. Ann.* 354 (2012), 827--862;
- Durmus and Moulines, *Ann. Appl. Probab.* 27 (2017), 1551--1587;
- Nesterov, *Introductory Lectures on Convex Optimization* (2004),
  Theorem 2.1.5 for the descent lemma.

## Exact scope qualification

Appendix B says that its rejection lemmas extend to possibly nonconvex `C¹`
potentials with Lipschitz gradient and integrable `exp(-U)`. That broader
nonconvex statement is not a Lean theorem in this package. The formalized
rejection endpoint retains the paper's standing strong-convexity input. This
does not leave a gap in the formalized proof of Theorem 2.1, but it is a genuine
omission if one wants every independent generalization stated in Appendix B.

The old `HessianBoundedPotential` adapter remains available for smooth users
and for the fixed-step hard target. It is a special case and is not used as an
assumption by the revised main endpoint.

## Reproducing the audit

From `formalization/`:

```powershell
lake exe cache get
powershell -ExecutionPolicy Bypass -File .\scripts\check.ps1
```

The 2026-09-12 run reported:

```text
STATIC AUDIT PASSED
FIRST-ORDER SOURCE AUDIT PASSED
NUMERIC SANITY PASSED
Build completed successfully (3439 jobs).
AXIOM AUDIT PASSED: 266 declarations; only
  ['Classical.choice', 'Quot.sound', 'propext']
FULL SOURCE BUILD AND AXIOM AUDIT PASSED
```

The sole direct Lean dependency is pinned mathlib 4.33.0. The static audit
found 155 Lean files, 2,069 declarations, 5,805 explicit `by` proof blocks,
resolved local imports, and no proof placeholders or trust shortcuts.
