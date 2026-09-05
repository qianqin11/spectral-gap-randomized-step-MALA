# Formalization report: uniform-random MALA

Last recorded Lean validation: **2026-08-30**

Documentation/PDF synchronization: **2026-09-05**; no new Lean build.

This package kernel-checks the main randomized-step lower bound and the
fixed-step minimax upper bound in Qian Qin's *A global spectral gap for Metropolis-adjusted Langevin algorithm
with a uniformly randomized step size*.
The verification statements below refer to the recorded 2026-08-30 checks;
this synchronization preserves every Lean source and build input. See
`DOCUMENTATION_UPDATE_2026-09-05.md` for the new static/package checks.

The main manuscript-facing declarations are:

```lean
UniformRandomMALA.Concrete.exists_universal_nonlazy_paperMasterRHS_lower
UniformRandomMALA.Concrete.exists_universal_lazy_paperMasterRHS_lower
UniformRandomMALA.Concrete.HessianBoundedPotential.
  sqrtDimensionCorollarySimplified_rayleighSpectralGap_lower
UniformRandomMALA.Concrete.fractionalAggregation_poincareLower
UniformRandomMALA.Concrete.FirstOrderPotential.allParameterMALAFlowBounds
UniformRandomMALA.Concrete.exists_universal_fixedStepMinimaxGap_paper_upper
```

The lower-bound endpoint begins with the manuscript's actual `C²` Hessian
bounds. `HessianBoundedPotential.toFirstOrderPotential` derives the Taylor
inequalities and Lipschitz Riesz gradient rather than recording an unrelated
vector field. The conclusion is stated with the manuscript's `L²` Rayleigh
spectral gap, whose equivalence with the corresponding Poincaré formulation
is proved in `Concrete/RayleighSpectralGap.lean`.

The fixed-step endpoint takes the infimum over the exact class of `C∞`
potentials with their actual second Fréchet derivative in `[mI,LI]`, followed
by the supremum over every positive step size. It proves the manuscript's
logarithmic/exponential ceiling with a universal exponential rate and a
prefactor depending only on the lower condition-number cutoff.

The complete formalization also includes the concrete half-lazy kernel,
Corollary 2.2 without a `pStar ≤ d` assumption, the exact `L²` fractional
aggregation lemma, and the full-parameter form of Proposition 3.4.

For theorem-by-theorem declarations, proof strategy, reusable results, and
verification commands, see:

- `COMPLETION_REPORT.md`;
- `THEOREM_MAP.md`;
- `PROOF_STRATEGY_LEDGER.md`;
- `REUSABLE_RESULTS.md`;
- `FORMALIZATION_STATUS.md`.

The paper's continuous-time Appendix B derivation is not translated
line-by-line. Its required stationary-rejection and local-overlap conclusions
are proved by the documented finite Gaussian/Euler/RWM alternative. No final
endpoint assumes an SDE theorem or a replacement certificate.

The full `scripts/check.ps1` audit passed on 2026-08-30: static and numerical
checks passed, `lake build` completed successfully with 3,435 jobs, the public
aggregate import elaborated, and the dependency audit reported only
`propext`, `Classical.choice`, and `Quot.sound`. There is no `sorry`, `admit`,
or project-specific axiom.
