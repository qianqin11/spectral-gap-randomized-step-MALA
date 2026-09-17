# Build status

Paper-synchronization date: **2026-09-05**

Last recorded full Lean build: **2026-08-30**

This is the recorded validation status for the Lean package accompanying
Qian Qin's **A global spectral gap for Metropolis-adjusted Langevin algorithm
with a uniformly randomized step size**. It is a build report; mathematical notation and the paper-to-Lean map
are explained in `PAPER_READER_GUIDE.md`.

The full-build and axiom-audit results below are historical records from
2026-08-30, not new checks of this distribution. The 2026-09-05 update changes
only documentation and the supplied manuscript PDF. All Lean sources and
existing build/check inputs are byte-for-byte unchanged. Static and numerical
checks were rerun for the update; their results and limitations are recorded
in `DOCUMENTATION_UPDATE_2026-09-05.md`. No Lean executable is available in
the update environment, so no new `lake build` or axiom audit was run.

- Target toolchain: `leanprover/lean4:v4.33.0`.
- Target mathlib tag: `v4.33.0`.
- Static project audit: **passed on 2026-08-30**; no `sorry`, `admit`, or
  project-level axiom.
- Deterministic numerical sanity audit: **passed on 2026-08-30**; 2,000
  trials, including the current assumption-free Corollary 2.2
  simplification.
- Full Lean kernel build: **passed on 2026-08-30** (`lake build`, 3,435
  jobs).
- Content-named public API: **passed** through
  `UniformRandomMALA.AllResults`.
- Unconditional MALA local-overlap build: **passed** through
  `UniformRandomMALA.MALAOverlap` and
  `UniformRandomMALA.Concrete.MALAOverlapBounds`.
- Reader-facing MALA local-overlap theorem:
  `Concrete.FirstOrderPotential.mala_overlap_bounds`.
- Exact non-lazy paper-form theorem:
  `Concrete.exists_universal_nonlazy_paperMasterRHS_lower`.
- Exact concrete lazy theorem:
  `Concrete.exists_universal_lazy_paperMasterRHS_lower`.
- Exact fixed-step minimax theorem:
  `Concrete.exists_universal_fixedStepMinimaxGap_paper_upper`.
- Explicit constants: `cr = 1/(16e)` and `Cr = 6144 e^3`.
- Finite Euler likelihood audit: **passed**; energy MGF, real moments,
  tilted/frozen endpoint identity, and endpoint contraction are unconditional.
- Euler/RWM coupling audit: **passed**; pair kernel, stationary second
  marginal, unequal-start recurrence, finite iteration, fixed-horizon
  vanishing energy, retained-initial edge coupling, and common structured
  weak limit are unconditional.
- Moving-reference/MALA-meet audit: **passed**; RN closure, accepted-flow meet,
  rejection marginal, and paper-scale stationary rejection are unconditional.
- Local/global overlap audit: **passed**; both clauses of the paper's
  moment-indexed local-overlap proposition (`prop:overlap`, Proposition 3.2
  in the current draft) are unconditional.
- Gaussian shift/separation audit: **passed**; Mills, quantile, shift, and
  separated sets are checked from Bakry--Ledoux.
- Bakry--Ledoux finite Gaussian-image layer: **passed**; strong monotonicity,
  finite Euler innovation sensitivity, Euclidean block norm packaging,
  endpoint `LipschitzWith`, the finite geometric coefficient, and its sharp
  mesh limit `1/m` are kernel-checked.
- Bakry--Ledoux weak-limit stability is checked twice: at the abstract profile
  level and, in `Concrete/GaussianWeakLimit.lean`, directly for the
  endpoint-corrected Gaussian shift.  The Gaussian theorem needs only the
  usual interior-mass finite inequalities and avoids an extra ENNReal
  endpoint-profile hypothesis.
- The Gaussian normal-profile calculus and Mehler OU module are checked:
  profile symmetry/strict concavity, `I I'' = -1`, quantile/profile endpoint
  limits, a continuous closed profile, Gaussian
  invariance, the semigroup law, invariant integration, long-time convergence,
  and Fréchet-derivative commutation for bounded `C¹` data.
- The local Gaussian OU residual argument and its functional closure
  (historical development stages G3 and G4) are checked through the explicit
  canonical field.
  `Concrete/GaussianOUCanonicalFields.lean` fixes
  `Q_s = sqrt(I(P_(t-s)f)^2 + (1-exp(-2s))|grad P_(t-s)f|^2)`, proves its
  endpoints, joint continuity, a uniform compact-time bound, and continuity
  of `s ↦ P_s Q_s`.  `Concrete/GaussianOUGenerator.lean` proves Gaussian
  integration by parts, direct fixed/time-dependent Mehler differentiation,
  the coordinate generator identity, the residual algebra/sign, and the
  monotonicity closure.  `GaussianOUCanonicalResidual.lean` and
  `GaussianOUCanonicalInterpolation.lean` complete the higher derivatives,
  time derivative, integrable path domination, and bounded residual package.
- The functional long-time limit, continuous closed-profile passage, and
  endpoint truncation are checked. The smooth-ramp-to-enlargement stage
  (historically G5) is also checked without external approximation
  or enlargement-continuity premises: `Concrete/GaussianRampMollification.lean`
  constructs normalized smooth bump convolutions of expanded distance ramps,
  and `Concrete/GaussianEnlargement.lean` proves the strip/perimeter, intrinsic
  right-continuity, Dini comparison, closed-set, and Radon steps.
- `Concrete/FiniteEulerEnlargement.lean` proves the Lipschitz-image transfer,
  packages finite Euler endpoint laws, and combines the mesh coefficient
  limit with Gaussian weak-limit stability.  Thus any weak limit of the
  finite endpoint laws satisfies sharp curvature-`m` Bakry--Ledoux.
  `GaussianRampCanonicalInterpolation.lean` supplies the Gaussian theorem in
  every finite innovation dimension and the diagonal endpoint convergence
  identifies the limit with the normalized target.
- Defective-conductance audit: **passed** for the concrete dyadic MALA
  kernels, including both clauses of the full-parameter Proposition 3.4
  wrapper `FirstOrderPotential.allParameterMALAFlowBounds`.
- Fractional component-aggregation audit: **passed** with the paper's exact
  `L²` energy-domination scope; bounded `L²` caps justify the hypothesis and
  make ENNReal cancellation and monotone convergence valid.
- Exceptional-budget and ladder-assignment audit: **passed**.
- Harmonic-sum audit: **passed** with explicit constant `6·2^30`.
- Hessian-to-first-order calculus audit: **passed**; the actual second
  Fréchet derivative bounds yield the exact Taylor inequalities, Riesz
  gradient, continuity, and Lipschitz gradient used by the internal
  `FirstOrderPotential` chain.
- Spectral-gap definition audit: **passed**; the `L²` Poincaré and Rayleigh
  formulations are formally equivalent, including zero-variance and
  infinite-energy cases.
- Concrete master theorem: **passed from the manuscript's `C²` Hessian
  assumptions** through
  `HessianBoundedPotential.universal_masterRHS_rayleighSpectralGap_lower`
  and `exists_universal_nonlazy_paperMasterRHS_lower`.
- Concrete lazification audit: **passed**; Markovness, reversibility, exact
  half-energy, exact half-Rayleigh-gap, and the lazy paper endpoint are
  checked for the literal identity/kernel mixture.
- Corollary 2.2 audit: **passed** for both displays; the final simplification
  does not assume `pStar ≤ d`.
- Proposition 2.3 audit: **passed**; the explicit `C∞` hard potential,
  Hessian bounds, local test branch, sticky cut branch, scalar optimization,
  and literal supremum–infimum endpoint are kernel-checked.
- Dependency audit: **passed**; audited declarations use only the standard
  Lean/mathlib logical dependencies `propext`, `Classical.choice`, and
  `Quot.sound`.
- Reproducible full check: `./scripts/check.sh` or the included GitHub Actions
  workflow.

The static and numerical audits are useful bug-finding checks; neither is a
substitute for Lean elaboration and kernel checking.

The paper's continuous-time Appendix B SDE derivation is not formalized.
Its stationary-rejection and overlap outputs are established by the checked
finite discrete-time replacement described in `PAPER_READER_GUIDE.md`.

The legacy `MainTheorem` assembles caller-supplied fields from the old
`PaperAnalyticInterfaces` record. It remains for compatibility and modular
experiments. The concrete route proves the corresponding inputs internally
and does not depend on that record.
