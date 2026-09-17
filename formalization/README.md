# Uniform-random MALA: Lean verification

This package accompanies Qian Qin's *A global spectral gap for
Metropolis-adjusted Langevin algorithm with a uniformly randomized step size*.
It formalizes the principal randomized-step spectral-gap lower bound and the
smooth fixed-step minimax obstruction in Lean 4.

The manuscript is available as [paper/main.pdf](paper/main.pdf). The same
directory includes [main.tex](paper/main.tex), the bibliography
`uniform_random_mala.bib`, and the three PDF figures used by the source.
[PACKAGE_MANIFEST.md](PACKAGE_MANIFEST.md) describes the distribution;
the manuscript checksum is recorded in
[validation/manuscript-pdf.sha256](validation/manuscript-pdf.sha256).

## Mathematical scope

The input record `Concrete.C1Potential` expresses the paper's first-order
assumptions (`eq:first-order-assumptions`): a continuously differentiable
potential `U : EuclideanSpace ℝ (Fin d) → ℝ`, the `m`-strong-convexity
supporting inequality, and an `L`-Lipschitz actual Riesz gradient, with
`0 < m ≤ L`. The upper Taylor inequality is derived from these assumptions.

The development constructs the normalized target, concrete MALA and
half-lazy kernels, the uniform-step mixture, and the paper's `L²` Rayleigh
spectral gap. It proves both clauses of Theorem 2.1 (`thm:main`) with common
universal constants satisfying `A₀ ≥ 1`, both bounds in Corollary 2.2
(`cor:sqrt-d-endpoint`), the mixture, overlap, separation, flow, and aggregation
results used in their proof, and the fixed-step minimax obstruction in
Proposition 2.3 (`prop:minimax-fixed-step-ceiling`).

The additional nonconvex scope of Appendix B is not formalized. The rejection
estimate needed for Theorem 2.1 is proved under the standing strong-convexity
assumptions by a discrete-time argument. The manuscript's continuous-time
SDE proof is not transcribed into Lean. The optional Hessian adapter remains
available for smooth special cases and the smooth hard example.

## Reading the formalization

Start with [PAPER_READER_GUIDE.md](PAPER_READER_GUIDE.md) for a route through
the assumptions and endpoints. [THEOREM_MAP.md](THEOREM_MAP.md) pairs the
paper's theorem numbers and TeX labels with Lean declarations.
[FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) records mathematical
coverage, and [TRUST_BOUNDARY.md](TRUST_BOUNDARY.md) explains the assumptions
and dependencies. The proof architecture and reusable results are described
in [PROOF_STRATEGY_LEDGER.md](PROOF_STRATEGY_LEDGER.md) and
[REUSABLE_RESULTS.md](REUSABLE_RESULTS.md).

The public import is:

```lean
import UniformRandomMALA.AllResults

#check UniformRandomMALA.Concrete.C1Potential
#check UniformRandomMALA.Concrete.C1Potential.exists_universal_paperMasterRHS_bounds
#check UniformRandomMALA.Concrete.C1Potential.sqrtDimensionCorollary_rayleighSpectralGap_lower
#check UniformRandomMALA.Concrete.C1Potential.sqrtDimensionCorollarySimplified_rayleighSpectralGap_lower
#check UniformRandomMALA.Concrete.C1Potential.allParameterMALAFlowBounds
#check UniformRandomMALA.Concrete.exists_universal_fixedStepMinimaxGap_paper_upper
```

## Reproducing the checks

The toolchain is pinned by `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`. Install Git, Python 3, and `elan`, then run from the
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

The gate runs the source, first-order-interface, manuscript, and numerical
audits, the manuscript-audit regression tests, `lake build`, the public
`AllResults` import, and the selected declarations' `#print axioms` audit.
The axiom allow-list contains `propext`, `Classical.choice`, and `Quot.sound`.
The final success marker is:

```text
FULL SOURCE BUILD AND AXIOM AUDIT PASSED
```

[BUILD_STATUS.md](BUILD_STATUS.md) records the latest validation, its scope,
and evidence. Manuscript checks and numerical trials are distinct from Lean
kernel verification. The source-label audit checks correspondence with the
bundled TeX; it does not itself establish mathematical equivalence or replace
a LaTeX build.

To typeset the manuscript, run the following from `paper/` with a LaTeX
distribution installed:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The figure PDFs and bibliography are supplied. See `BUILD_STATUS.md` for
whether the current validation includes typesetting.

The local check creates dependency caches and compiled files under `.lake/`
and logs under `validation/local/`. These generated files are excluded from
the source distribution. Historical validation records are retained under
`validation/historical/`; they do not describe the current manuscript.
[REPOSITORY_UPDATE.md](REPOSITORY_UPDATE.md) provides maintainer guidance.
