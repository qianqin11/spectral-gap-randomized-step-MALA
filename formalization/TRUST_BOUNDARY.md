# Trust boundary

This document explains the inputs, proof dependencies, and scope of the
public MALA, aggregation, and sample-average results. The latest validation evidence is
in [BUILD_STATUS.md](BUILD_STATUS.md); reproducible commands are in
[README.md](README.md). The reader guide links the
[algorithm and quantity definitions](PAPER_READER_GUIDE.md#3-compare-definitions-with-the-paper)
and the [concrete proof route](PAPER_READER_GUIDE.md#4-follow-the-complete-proofs)
to the source files needed to check these claims.

## Input assumptions

`Concrete.C1Potential d` contains a potential `U`, constants `m` and `L`, a
positive dimension, `0 < m ≤ L`, `ContDiff ℝ 1 U`, the first-order
strong-convexity inequality, and a Lipschitz bound on mathlib's actual
gradient. These correspond to `eq:first-order-assumptions` in the bundled
[paper/main.tex](paper/main.tex).

`C1Potential.upperTaylor` proves the descent inequality, and
`C1Potential.toFirstOrderPotential` sets the internal drift to `∇ U`.
`C1Potential.exists_universal_normalizedMasterRHS_bounds` states both clauses of
Theorem 2.1 (`thm:main`) with constants chosen before all dimensions,
potentials, and time horizons. The record and theorem require no Hessian,
independent drift, upper-Taylor assumption, stationary-rejection certificate,
isoperimetric certificate, or spectral-gap certificate.

## Analytic arguments proved internally

Target isoperimetry follows from Gaussian OU/Bobkov interpolation, smooth
ramps, finite-Euler image estimates, and a weak limit. The contraction theorem
cited in the manuscript is not a Lean axiom or package dependency.

The rejection result uses finite Gaussian likelihoods, Euler energy bounds,
Euler/RWM comparison, weak-limit density closure, and moment interpolation.
The interpolation lemma assumes integrability of the powers in its
statement; the rejection application establishes this from the bounded
rejection mass. The nonconvex endpoint uses `NonconvexPotential`: an actual
C¹ potential with Lipschitz gradient and integrable Boltzmann weight. Its
gradient moments are proved without a position-moment assumption, and its
Euler comparison allows Lipschitz growth in place of convex contraction.
`Nonconvex/StationaryRejection.lean` supplies the full Proposition B.1
(`prop:stationary-rejection`). Lemmas B.2–B.5 are excluded from the requested
scope and are not assumed by this proof.

The Hessian adapter and smooth hard-target/minimax endpoints are optional
special cases. Importing them does not add differentiability hypotheses to
a theorem whose argument is a `C1Potential`. Conditional assembly interfaces
also remain available as reusable lemmas; the public endpoint supplies their
analytic inputs through proved results.

The mixing-time corollary additionally takes the paper's initial-law
assumptions: a probability measure absolutely continuous with respect to the
target and a square-integrable Radon–Nikodym density. Its TV-decay bound is
proved through actual kernel integration in `KernelLpBasic.lean`, the
`L²` energy and positivity arguments in `KernelLpL2.lean` and
`KernelLpContraction.lean`, and Radon–Nikodym density evolution in
`L2DensityEvolution.lean`. `L2DensityTV.lean` supplies the exact TV factor.
The earlier bounded-observable route remains available in `L2Mixing*.lean`. No external mixing theorem or convergence
certificate is assumed. The prefactor is a universal multiple of
`max c (1/c)`; [THEOREM_MAP.md](THEOREM_MAP.md) locates its definition.

The variance clauses of Corollary 2.6 and both bounds in Corollary 2.8
are connected to the actual MALA kernels and finite sample averages.
Their operator, density, interpolation, and covariance estimates are
proved internally. Corollary 2.7 uses the extended stationary variance:
`VarianceSeparationExtended.lean` proves its actual limit, including at zero
gap, and `VarianceSeparationFixedStep.lean` constructs the required observable.
The CLT clauses of Corollary 2.6 are proved in `PaperCentralLimit.lean`
for measurable `L²(π)` observables and every initial probability measure.
The proof constructs the infinite trajectory law, identifies its finite
prefixes, and establishes the actual Poisson martingale's conditional
expectations. It derives the Lindeberg and conditional-variance limits,
proves Gaussian convergence, and removes restrictions on the initial law
through density approximation and acceptance. No CLT, Harris-recurrence,
Lindeberg, or initial-density certificate is an input to the paper wrappers.
[FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) summarizes the scope.

## External dependencies and logical axioms

The sole direct external Lean library is mathlib, pinned with the Lean
toolchain by `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain`.
Lean core and mathlib's ordinary transitive packages form the surrounding
proof environment.

The static audit rejects `sorry`, `admit`, project axiom declarations,
`native_decide`, `implemented_by`, `sorryAx`, and unsafe declarations.
The dependency audit executes `#print axioms` for the declarations selected
in `UniformRandomMALA/DependencyAudit.lean` and allows only:

- `propext`;
- `Classical.choice`;
- `Quot.sound`.

`scripts/check_axioms.py` fails when a requested declaration is absent from
the output, Lean reports an error, or another axiom occurs. The selection is
broad but finite. The complete source audit covers the Lean files separately;
its declaration total is a source-regex count, not a count of every
declaration in the elaborated Lean environment. Full compilation checks the
proof terms accepted by Lean. The selected axiom audit provides additional
information about their logical dependencies.

## Manuscript and auxiliary checks

The manuscript is exposition and a specification for correspondence, not
part of the Lean trust base. `paper/` contains the TeX source, bibliography,
three figure PDFs, and the typeset paper. The checksum is recorded in
[validation/manuscript-pdf.sha256](validation/manuscript-pdf.sha256).

The manuscript audit checks the supplied files, active labels, references,
citation keys, figure dependencies, and paper references in Lean. A valid
label or matching checksum does not by itself prove that a Lean theorem and
a paper statement have identical mathematical content. The correspondence
and scope qualifications are documented in
[THEOREM_MAP.md](THEOREM_MAP.md) and
[FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md). LaTeX builds and numerical
sanity checks provide separate evidence; `BUILD_STATUS.md` identifies which
checks were performed. Earlier records in `validation/historical/` remain
historical evidence.
