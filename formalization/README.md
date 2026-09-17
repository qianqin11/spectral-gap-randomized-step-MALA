# Uniform-random MALA: Lean verification

This package accompanies Qian Qin's *A global spectral gap for
Metropolis-adjusted Langevin algorithm with a uniformly randomized step size*.
It formalizes the randomized-step spectral-gap bound (Theorem 2.1), its
square-root-dimension corollary (Corollary 2.2), and the smooth fixed-step
minimax obstruction (Proposition 2.3), together with their proof ingredients.
The [paper PDF](paper/main.pdf) and [LaTeX source](paper/main.tex) are bundled.

## Where to start

Two checks matter: that Lean proves the conclusions from the stated
assumptions, and that the formal statements and definitions express the
mathematics in the paper. The [reader guide](PAPER_READER_GUIDE.md) gives a
route through both checks; the [theorem map](THEOREM_MAP.md) indexes results
by paper number and TeX label.

| What to verify | Files to read |
|---|---|
| The paper's assumptions on the potential and its actual gradient | [C1ToFirstOrder.lean](UniformRandomMALA/Concrete/C1ToFirstOrder.lean): `C1Potential` and its adapter to the internal interface |
| Theorem 2.1 and Corollary 2.2, including the quantities in their bounds | [C1MainTheorem.lean](UniformRandomMALA/Concrete/C1MainTheorem.lean): start with `exists_universal_paperMasterRHS_bounds`, `paperMomentThreshold`, and `paperMasterRHS` |
| The target distribution and the MALA algorithm | [EuclideanTarget.lean](UniformRandomMALA/Concrete/EuclideanTarget.lean), [GaussianProposal.lean](UniformRandomMALA/Concrete/GaussianProposal.lean), [MALA.lean](UniformRandomMALA/Concrete/MALA.lean), and [MALAFamily.lean](UniformRandomMALA/Concrete/MALAFamily.lean); the [definition-by-definition guide](PAPER_READER_GUIDE.md#2-compare-the-algorithm-and-quantity-definitions) also covers acceptance, mixtures, and lazification |
| The paper's Dirichlet form and spectral-gap convention | [KernelMixture.lean](UniformRandomMALA/KernelMixture.lean): `Dirichlet.energy`; [RayleighSpectralGap.lean](UniformRandomMALA/Concrete/RayleighSpectralGap.lean): `L2RayleighTest`, `rayleighQuotient`, and `rayleighSpectralGap` |
| Proposition 2.3 and its order of optimization over steps and potentials | [FixedStepMinimax.lean](UniformRandomMALA/Concrete/FixedStepMinimax.lean): `fixedStepMinimaxGap` and `exists_universal_fixedStepMinimaxGap_paper_upper` |
| How the proofs reach the concrete endpoints without assumed analytic results | The [proof route](PAPER_READER_GUIDE.md#3-trace-the-proof-to-its-inputs), [trust boundary](TRUST_BOUNDARY.md), and [DependencyAudit.lean](UniformRandomMALA/DependencyAudit.lean) |

The public import is `UniformRandomMALA.AllResults`. The main theorem starts
from a continuously differentiable, strongly convex potential with a
Lipschitz gradient. The target, kernels, rejection estimates, isoperimetry,
and final gap bound are constructed or proved within the development; no
rejection, isoperimetry, or spectral-gap certificate is an input to that
endpoint. The reader guide shows where these dependencies are discharged.

The formalization uses different proofs for two analytic inputs: Gaussian
OU/Bobkov interpolation and finite-Euler weak limits for isoperimetry, and a
discrete-time argument for rejection. Appendix B's continuous-time lemmas
and additional nonconvex scope are not formalized. See the
[theorem map](THEOREM_MAP.md) for result-by-result coverage and
[FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) for scope details.

## Reproduce the verification

Install Git, Python 3, and `elan`. The Lean and mathlib versions are pinned
by `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`. Run from the
`formalization/` directory. On Windows:

```powershell
lake exe cache get
if ($LASTEXITCODE -ne 0) { throw 'Cache retrieval failed.' }
powershell -ExecutionPolicy Bypass -File .\scripts\check.ps1
```

On Linux or macOS:

```bash
lake exe cache get
bash scripts/check.sh
```

The gate builds the library, checks the public import, and runs
`#print axioms` for the declarations selected in
[DependencyAudit.lean](UniformRandomMALA/DependencyAudit.lean), including the
main endpoints. It also runs the source, first-order-interface, manuscript,
and numerical audits and the manuscript-audit regression tests. The only
allowed logical axioms are `propext`, `Classical.choice`, and `Quot.sound`.
The final success marker is:

```text
FULL SOURCE BUILD AND AXIOM AUDIT PASSED
```

[BUILD_STATUS.md](BUILD_STATUS.md) records the latest validation and its
evidence. A successful build checks the formal proofs; comparing their
definitions and statements with the paper remains a separate reading task.
The manuscript-label audit and numerical checks support that comparison
but do not establish mathematical equivalence.

## Further documentation

The [proof-strategy ledger](PROOF_STRATEGY_LEDGER.md) gives a more detailed
dependency route, and [REUSABLE_RESULTS.md](REUSABLE_RESULTS.md) describes
general lemmas. The [package manifest](PACKAGE_MANIFEST.md) lists the
distributed files; [REPOSITORY_UPDATE.md](REPOSITORY_UPDATE.md) gives
maintainer instructions. Generated caches and logs live in `.lake/` and
`validation/local/`; records in `validation/historical/` describe earlier
snapshots.

To typeset the bundled manuscript, run
`latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex` from `paper/`
with a LaTeX distribution installed. The bibliography and figure PDFs are
supplied. Typesetting evidence and the manuscript checksum are linked from
[BUILD_STATUS.md](BUILD_STATUS.md).
