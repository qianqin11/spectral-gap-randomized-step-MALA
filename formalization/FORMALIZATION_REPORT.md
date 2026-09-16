# Formalization report: uniform-random MALA

Validation date: **2026-09-15**.

This package kernel-checks the principal randomized-step lower bound and the
fixed-step minimax upper bound in Qian Qin's *A global spectral gap for
Metropolis-adjusted Langevin algorithm with a uniformly randomized step size*.
The revised main theorem no longer assumes a twice differentiable potential.

The paper-facing record `Concrete.C1Potential` uses only continuous
differentiability, a first-order strong-convexity inequality, and global
Lipschitz continuity of the actual Riesz gradient. `C1Potential.upperTaylor`
derives the missing descent inequality; `toFirstOrderPotential` then connects
these assumptions to the established discrete analytic core without a
certificate parameter.

The principal endpoint is:

```lean
UniformRandomMALA.Concrete.C1Potential.exists_universal_paperMasterRHS_bounds
```

It packages the non-lazy and concrete half-lazy clauses with shared universal
constants satisfying `A₀ ≥ 1` and the paper's `L²` Rayleigh spectral gap. The package also includes
both displays of Corollary 2.2, the `p ≥ 1` MALA overlap theorem, separated-set
and full-parameter flow bounds, the exact fractional aggregation lemma, and
the smooth fixed-step minimax obstruction. See `THEOREM_MAP.md`.

The full PowerShell gate passed under Lean/mathlib 4.33.0:

- source audit: 155 files, 2,069 declarations, no proof bypasses;
- PDF identity/inventory audit and seven audit regression tests: passed;
- `lake build`: 3,439 jobs completed successfully;
- public `AllResults` elaboration: passed;
- actual `#print axioms`: 266 declarations, with only `propext`,
  `Classical.choice`, and `Quot.sound`.

The paper's continuous-time Appendix B derivation is not translated
line-by-line, and its extra nonconvex scope is not claimed. Lean proves the
strongly convex rejection result needed by Theorem 2.1 through a documented
finite-Gaussian/Euler/RWM route. The older Hessian adapter remains a reusable
smooth special case, not a premise of the revised endpoint.

For detailed declarations, proof architecture, reusable results, commands, and
limitations, read `COMPLETION_REPORT.md`, `PROOF_STRATEGY_LEDGER.md`,
`REUSABLE_RESULTS.md`, `README.md`, and `TRUST_BOUNDARY.md`.
