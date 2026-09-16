# Uniform-random MALA: Lean verification

This package accompanies Qian Qin's *A global spectral gap for
Metropolis-adjusted Langevin algorithm with a uniformly randomized step size*.
The revised 47-page manuscript is `paper/main.pdf`. The `paper/` directory
contains only this PDF; TeX source, bibliography files, and separate figures
are not included. Its SHA-256 is
`eb3ec374502cbc7b01a2552164f8d64693f64fef333f9948173f575d09a6c4f9`.
`scripts/manuscript_audit.py` checks the PDF identity and this inventory;
it does not rebuild LaTeX or audit source labels, references, or citations.

**Verified status (2026-09-15):** the complete source builds with pinned Lean
4.33.0 and mathlib 4.33.0. The public `AllResults` import elaborates, and the
fail-closed dependency audit checked 266 declarations. Their only logical
axioms are Lean/mathlib's standard `propext`, `Classical.choice`, and
`Quot.sound`. The source contains no `sorry`, `admit`, project axiom, unsafe
declaration, or native-code proof shortcut.

## Mathematical scope

The paper-facing input is `Concrete.C1Potential`. It says that
`U : EuclideanSpace ℝ (Fin d) → ℝ` is continuously differentiable,
`m`-strongly convex through the first-order supporting inequality, and has an
`L`-Lipschitz actual Riesz gradient, with `0 < m ≤ L`. It does not contain a
Hessian or a separately recorded drift. `C1Potential.upperTaylor` proves the
upper Taylor/descent inequality, and `toFirstOrderPotential` installs
`gradU := ∇ U` definitionally.

The package then constructs the normalized target, concrete MALA and lazy
MALA kernels, the uniform-step mixture, and the paper's `L²` Rayleigh spectral
gap. It proves both clauses of Theorem 2.1 with common universal constants,
both displays of Corollary 2.2, Propositions 3.2--3.4 in the ranges used by the
revised paper, the exact fractional aggregation lemma, and the smooth
fixed-step minimax obstruction.

The Appendix B claim that the rejection lemmas also hold for general
nonconvex `C¹` potentials is not formalized. Lean proves the rejection input
needed by Theorem 2.1 under the paper's standing strong-convexity assumptions,
using a finite-Euler/discrete-time argument instead of a line-by-line SDE
formalization. The older Hessian adapter remains as an optional smooth special
case and is still used by the deliberately smooth hard example.


## Reader entry points

```lean
import UniformRandomMALA.AllResults

#check UniformRandomMALA.Concrete.C1Potential
#check UniformRandomMALA.Concrete.C1Potential.upperTaylor
#check UniformRandomMALA.Concrete.C1Potential.toFirstOrderPotential
#check UniformRandomMALA.Concrete.C1Potential.exists_universal_paperMasterRHS_bounds
#check UniformRandomMALA.Concrete.C1Potential.sqrtDimensionCorollary_rayleighSpectralGap_lower
#check UniformRandomMALA.Concrete.C1Potential.sqrtDimensionCorollarySimplified_rayleighSpectralGap_lower
#check UniformRandomMALA.Concrete.C1Potential.mala_overlap_bounds
#check UniformRandomMALA.Concrete.C1Potential.allParameterMALAFlowBounds
#check UniformRandomMALA.Concrete.exists_universal_fixedStepMinimaxGap_paper_upper
```

See `THEOREM_MAP.md` for the paper-to-Lean correspondence,
`PROOF_STRATEGY_LEDGER.md` for the proof architecture,
`REUSABLE_RESULTS.md` for general lemmas, and `TRUST_BOUNDARY.md` for the exact
assumption and dependency boundary.

## Kernel check

Install Git, Python 3, and `elan`, then run these commands in this
`formalization` directory. On Windows, either `python` or the standard `py -3`
launcher may be available; the PowerShell script detects both.

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

The check performs Lean-source, first-order-interface, PDF identity/inventory,
and numerical audits, tests the PDF audit failure cases, runs a full
`lake build`, and directly elaborates
`UniformRandomMALA/AllResults.lean`. It then executes the `#print axioms`
requests and checks their output against the allowed axioms. A successful
final line is:

```text
FULL SOURCE BUILD AND AXIOM AUDIT PASSED
```

The build creates `.lake/`, often hundreds of megabytes or more because it
contains compiled project files and dependency caches. It is reproducible and
safe to delete when Lean/VS Code is closed. The release archive deliberately
excludes `.lake/`, compiled objects, and `validation/local/` logs.

The active combined-repository workflow is `../.github/workflows/lean.yml`.
Historical documentation for the earlier Hessian-facing release is preserved
under `validation/historical/pre-first-order/`. The superseded TeX build and
source-audit evidence is under `validation/historical/2026-09-12/`.
See `REPOSITORY_UPDATE.md` for copying this checked package into the GitHub
repository and committing the update.
