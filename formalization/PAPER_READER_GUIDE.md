# Reading the paper alongside the Lean source

The public Lean interface follows the first-order assumptions in
[paper/main.tex](paper/main.tex), label `eq:first-order-assumptions`.
The typeset paper, TeX source, bibliography, and figure PDFs are bundled in
`paper/`. Use [THEOREM_MAP.md](THEOREM_MAP.md) to navigate by theorem number
or TeX label, and [BUILD_STATUS.md](BUILD_STATUS.md) for verification evidence.

## 1. Start with the assumptions

Read
[C1ToFirstOrder.lean](UniformRandomMALA/Concrete/C1ToFirstOrder.lean).
`Concrete.C1Potential` records `ContDiff ℝ 1 U`, the strong-convexity
supporting inequality, and `LipschitzWith` for mathlib's Riesz gradient
`∇ U`, together with the dimension and scalar side conditions.
It contains no Hessian, independent drift, upper-Taylor certificate,
isoperimetric certificate, or rejection certificate.

`C1Potential.upperTaylor` proves the descent inequality by restricting the
potential to an affine line. `C1Potential.toFirstOrderPotential` connects
these assumptions to the internal analytic interface with `gradU := ∇ U`
definitionally.

## 2. Read the main endpoints

[C1MainTheorem.lean](UniformRandomMALA/Concrete/C1MainTheorem.lean) contains
the principal reader-facing declarations. All names below have prefix
`UniformRandomMALA.Concrete.C1Potential.`.

| Paper result and TeX label | Lean declaration |
|---|---|
| Theorem 2.1 (`thm:main`), both clauses with shared constants | `exists_universal_paperMasterRHS_bounds` |
| Theorem 2.1, non-lazy clause | `universal_masterRHS_rayleighSpectralGap_lower` |
| Theorem 2.1, half-lazy clause | `universal_half_masterRHS_lazy_rayleighSpectralGap_lower` |
| Corollary 2.2 (`cor:sqrt-d-endpoint`), first bound | `sqrtDimensionCorollary_rayleighSpectralGap_lower` |
| Corollary 2.2, simplified bound | `sqrtDimensionCorollarySimplified_rayleighSpectralGap_lower` |
| Proposition 3.2 (`prop:overlap`) | `mala_overlap_bounds` |
| Proposition 3.3 (`prop:separated`) | `separatedSets` |
| Proposition 3.4 (`prop:flow`) | `allParameterMALAFlowBounds` |

The main existential statement chooses universal constants before the
dimension, potential, and time horizon. It states the paper's `A₀ ≥ 1`
range. The chosen internal witness satisfies `A₀ ≥ 2`; the theorem does not
assert that every choice of `A₀ ≥ 1` works.

The fixed-step minimax endpoint for Proposition 2.3
(`prop:minimax-fixed-step-ceiling`) is
`UniformRandomMALA.Concrete.exists_universal_fixedStepMinimaxGap_paper_upper`.
Its smooth hard witness corresponds to Proposition A.1
(`prop:generic-fixed-step-obstruction`).

## 3. Follow the proof ingredients

The randomized-step proof combines the disjoint mixture-energy comparison
(Lemma 3.1, `lem:Kt`), overlap and separation, the flow bounds, and the
fractional and hard-assignment aggregation results (Lemma 3.5,
`lem:fractional`; Theorem 3.6, `thm:aggregation`).
[PROOF_STRATEGY_LEDGER.md](PROOF_STRATEGY_LEDGER.md) explains this chain.

For isoperimetry, the manuscript cites a nonsmooth contraction theorem.
Lean obtains target enlargement from Gaussian OU/Bobkov interpolation,
smooth ramps, finite-Euler transport, and a weak limit identified with the
target. The contraction theorem is not assumed by the formal proof.

For stationary rejection (Proposition B.1, `prop:stationary-rejection`),
Lean uses finite Gaussian likelihoods, finite-Euler estimates, Euler/RWM
comparison, and weak-limit closure. Moment interpolation extends the
retained `p ≥ 2` core to the public `p ≥ 1` range. The public overlap
constants are `1/(32e)` and `12288 e³`.

## 4. Identify the scope boundary

The continuous-time proofs of `lem:linear-increment`,
`lem:integrated-increments`, `lem:frozen-endpoint-law`, and
`lem:path-likelihood` are not transcribed. Appendix B's additional
nonconvex `C¹` generalization is also outside the formalization. The
discrete proof establishes the strongly convex rejection input used by
Theorem 2.1.

`HessianToFirstOrder.lean` supplies an optional smooth adapter. The
fixed-step obstruction deliberately uses a smooth, Hessian-bounded hard
witness. These smooth interfaces do not add assumptions to the `C1Potential`
lower-bound theorem. [TRUST_BOUNDARY.md](TRUST_BOUNDARY.md) gives the precise
logical boundary, and [README.md](README.md) provides commands for checking
the complete development.
