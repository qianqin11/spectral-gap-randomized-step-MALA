# Reader guide for the revised manuscript and Lean source

The current paper-facing interface is first order: a continuously
differentiable, strongly convex potential with a Lipschitz actual gradient.
The full package was kernel-checked with Lean/mathlib 4.33.0 on 2026-09-15.

## 1. Start with the assumptions

Read `Concrete/C1ToFirstOrder.lean`. `C1Potential` records `ContDiff ℝ 1 U`,
the strong-convexity supporting inequality, and `LipschitzWith` for mathlib's
Riesz gradient `∇ U`. It contains no Hessian, independent drift, upper-Taylor
certificate, isoperimetric certificate, or rejection certificate.

`C1Potential.upperTaylor` proves the descent inequality by restricting to the
affine line from `x` to `y`. `C1Potential.toFirstOrderPotential` then reuses the
established analytic core with `gradU := ∇ U` definitionally.

## 2. Read the paper-facing endpoints

`Concrete/C1MainTheorem.lean` contains the best entry points:

- `exists_universal_paperMasterRHS_bounds` packages both clauses of Theorem
  2.1 with the same universal constants;
- `universal_masterRHS_rayleighSpectralGap_lower` is the non-lazy clause;
- `universal_half_masterRHS_lazy_rayleighSpectralGap_lower` is the exact
  half-lazy clause;
- the two `sqrtDimensionCorollary...` declarations are the two displays of
  Corollary 2.2;
- `mala_overlap_bounds`, `separatedSets`, and
  `allParameterMALAFlowBounds` expose Propositions 3.2--3.4 directly from a
  `C1Potential`.

Use `THEOREM_MAP.md` for exact names and `COMPLETION_REPORT.md` for the audit.

## 3. Understand the analytic route

The manuscript cites the nonsmooth Caffarelli/Kim--Milman contraction result.
Lean does not assume it. The formal proof builds Gaussian OU/Bobkov
interpolation, obtains Gaussian enlargement through smooth ramps, transports
it to finite-Euler endpoints, and takes a weak limit identified with the
target. This downstream construction already needs only first-order potential
data.

Likewise, the manuscript's stationary-rejection proof uses continuous-time
tools, while Lean uses finite Gaussian likelihoods, finite-Euler estimates,
Euler/RWM comparison, and weak-limit closure. `MomentInterpolation.lean` adds
the paper's full `p ≥ 1` range to the sharper retained `p ≥ 2` core. The public
constants are `1/(32e)` and `12288 e³`.

The broader Appendix B statement for nonconvex `C¹` potentials is not a Lean
theorem. The discrete proof establishes exactly the strongly convex rejection
input needed for the end-to-end proof of Theorem 2.1.

## 4. Distinguish compatibility material

`HessianToFirstOrder.lean` is an optional smooth adapter inherited from the
previous package. It is not a hypothesis of the revised main theorem. The
fixed-step minimax upper-bound obstruction deliberately remains in a `C∞`,
Hessian-bounded subclass because that is the paper's hard witness.

For a machine check, import `UniformRandomMALA.AllResults` and run
`scripts/check.ps1` or `scripts/check.sh` as described in `README.md`.
