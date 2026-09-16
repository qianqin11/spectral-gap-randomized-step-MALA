# Trust boundary for the first-order verification

**Verified 2026-09-15:** the full package builds under pinned Lean/mathlib
4.33.0, the public import elaborates, and actual axiom output for 266 selected
principal and intermediate declarations passes the allow-list gate.

## Input assumptions

`Concrete.C1Potential d` contains a potential `U`, constants `m` and `L`, a
positive dimension, `0 < m ≤ L`, `ContDiff ℝ 1 U`, the first-order
strong-convexity inequality, and a Lipschitz bound on mathlib's actual gradient.
It contains no independent gradient field, Hessian, upper-Taylor hypothesis,
stationary-rejection certificate, isoperimetric certificate, or spectral-gap
conclusion.

`C1Potential.upperTaylor` proves the descent inequality, and
`C1Potential.toFirstOrderPotential` sets the internal drift to `∇ U`.
`C1Potential.exists_universal_paperMasterRHS_bounds` states the lazy and
non-lazy paper bounds with constants chosen before all dimensions, potentials,
and time horizons. It accepts no analytic certificate parameter.

## Analytic arguments supplied internally

Target isoperimetry is proved through Gaussian OU/Bobkov interpolation, smooth
ramps, finite-Euler image estimates, and a weak limit. The contraction theorem
cited in the manuscript is therefore not a Lean axiom or package dependency.

The rejection result uses finite Gaussian likelihoods, Euler energy bounds,
Euler/RWM comparison, weak-limit density closure, and moment interpolation.
The generic real-exponent interpolation lemma assumes integrability of the
`p`-th and second powers; the rejection proof establishes these hypotheses
from the bounded rejection mass. The result retains strong convexity. The
paper's broader nonconvex continuous-time Appendix B statement is not
formalized and is not needed by Theorem 2.1.

The Hessian adapter and smooth hard-target/minimax endpoints are optional
special cases. Their being imported does not add differentiability hypotheses
to a theorem whose argument is a `C1Potential`.

## External dependencies and axioms

Mathlib 4.33.0 is the sole direct external Lean dependency; its ordinary
transitive packages and Lean core are part of the trusted environment. The
static audit rejects `sorry`, `admit`, project axioms, `native_decide`,
`implemented_by`, `sorryAx`, and unsafe declarations. The actual dependency
audit allows only:

- `propext`;
- `Classical.choice`;
- `Quot.sound`.

`scripts/check_axioms.py` fails if any requested declaration is absent from the
log, if Lean reports an error, or if another axiom occurs. The gate passed for
all 266 requests. `#print axioms` selection is broad but finite; the complete
source audit separately covers all 155 Lean files and counts 2,069 top-level
`def`/`lemma`/`theorem`/`structure` declarations by a source regex. That number
is not a count of every declaration in Lean's elaborated environment.

Older conditional assembly interfaces remain valid reusable lemmas, but they
are not the proof route for the current public endpoint.

The manuscript is evidence and exposition, not part of the Lean trust base.
The current manuscript package contains only `paper/main.pdf`. The recorded
SHA-256 and single-file inventory are audited independently of Lean. TeX,
bibliography, and separate figures are not bundled; no current LaTeX build
or source-label/reference/citation audit is claimed. Earlier manuscript build
records are historical evidence under `validation/historical/2026-09-12/`.
