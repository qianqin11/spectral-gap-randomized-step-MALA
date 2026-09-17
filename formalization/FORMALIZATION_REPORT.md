# Formalization report: uniform-random MALA

This Lean development covers the principal randomized-step spectral-gap
lower bound and the smooth fixed-step minimax upper bound in Qian Qin's
*A global spectral gap for Metropolis-adjusted Langevin algorithm with a
uniformly randomized step size*. The paper, its TeX source, bibliography,
and figure PDFs are included in `paper/`.

The public record `Concrete.C1Potential` expresses continuous
differentiability, first-order strong convexity, and global Lipschitz
continuity of the actual Riesz gradient (`eq:first-order-assumptions`).
`C1Potential.upperTaylor` derives the descent inequality, and
`toFirstOrderPotential` connects these hypotheses to the discrete analytic
core without requiring an additional analytic certificate.

The principal endpoint is:

```lean
UniformRandomMALA.Concrete.C1Potential.exists_universal_paperMasterRHS_bounds
```

It packages the non-lazy and concrete half-lazy clauses of Theorem 2.1
(`thm:main`) using the paper's `L²` Rayleigh spectral gap and common
universal constants with `A₀ ≥ 1`. The development also covers both bounds
of Corollary 2.2 (`cor:sqrt-d-endpoint`), the mixture, overlap, separation,
flow, and aggregation ingredients, and Proposition 2.3
(`prop:minimax-fixed-step-ceiling`).

The manuscript's continuous-time Appendix B proof is not transcribed.
The formal rejection estimate retains the standing strong-convexity
assumption and follows a finite-Gaussian/Euler/RWM argument. Appendix B's
additional nonconvex generalization remains outside the formalization.
The optional Hessian adapter supplies smooth special cases, including
the fixed-step hard witness.

Mathematical coverage and exact declarations are documented in
[FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) and
[THEOREM_MAP.md](THEOREM_MAP.md). The latest validation and its evidence are
recorded in [BUILD_STATUS.md](BUILD_STATUS.md). The reproducibility gate
builds the full source with the pinned toolchain, checks the public import,
and audits selected declarations' actual axiom dependencies. Manuscript
source checks and numerical trials provide separate supporting checks;
they are not substitutes for the Lean kernel check.

For an introduction, see [PAPER_READER_GUIDE.md](PAPER_READER_GUIDE.md).
[PROOF_STRATEGY_LEDGER.md](PROOF_STRATEGY_LEDGER.md),
[REUSABLE_RESULTS.md](REUSABLE_RESULTS.md), and
[TRUST_BOUNDARY.md](TRUST_BOUNDARY.md) describe the proof architecture,
reusable mathematics, and logical assumptions.
