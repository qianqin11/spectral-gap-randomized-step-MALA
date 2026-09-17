# Trust boundary

The mathematical input, proof dependencies, and scope limits described here
apply to the public first-order interface. The latest validation evidence is
in [BUILD_STATUS.md](BUILD_STATUS.md); reproducible commands are in
[README.md](README.md).

## Input assumptions

`Concrete.C1Potential d` contains a potential `U`, constants `m` and `L`, a
positive dimension, `0 < m ≤ L`, `ContDiff ℝ 1 U`, the first-order
strong-convexity inequality, and a Lipschitz bound on mathlib's actual
gradient. These correspond to `eq:first-order-assumptions` in the bundled
[paper/main.tex](paper/main.tex).

`C1Potential.upperTaylor` proves the descent inequality, and
`C1Potential.toFirstOrderPotential` sets the internal drift to `∇ U`.
`C1Potential.exists_universal_paperMasterRHS_bounds` states both clauses of
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
rejection mass. The rejection theorem retains strong convexity. Appendix B's
additional nonconvex generalization and continuous-time proof are outside
the formalized scope. The required strongly convex conclusion of
Proposition B.1 (`prop:stationary-rejection`) is supplied internally.

The Hessian adapter and smooth hard-target/minimax endpoints are optional
special cases. Importing them does not add differentiability hypotheses to
a theorem whose argument is a `C1Potential`. Conditional assembly interfaces
also remain available as reusable lemmas; the public endpoint supplies their
analytic inputs through proved results.

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
