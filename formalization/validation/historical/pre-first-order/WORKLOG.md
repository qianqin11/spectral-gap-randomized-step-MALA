# Formalization worklog

Canonical manuscript: `paper/main.pdf`, copied without alteration from the
author-supplied `main.pdf` on 2026-09-05. The paper directory is PDF-only.
Entries dated 2026-08-30 below describe earlier checkpoints, including
manuscript source and legacy materials no longer in this distribution.

Pinned toolchain: Lean `v4.33.0`, mathlib `v4.33.0`.

## 2026-08-30: canonical-package intake

Complete:

- Inspected the attached archive before extraction and checked its paths for
  traversal or absolute-path entries.
- Compared its 132 Lean source modules against the previous package. Ten Lean
  files differed only in manuscript-synchronization comments; no theorem
  declaration, proof body, or import differed.
- Copied the attached `paper/main.tex`, `paper/main.pdf`, and
  `paper/uniform_random_mala.bib` into the working project as the canonical
  manuscript set.
- Merged the attached reader documentation and source comments.
- Restored the pinned toolchain through `ELAN_HOME=C:\Users\qianq\.elan`.
- Ran the pre-change baseline command:

  ```text
  lake build
  ```

  Result: success, `Build completed successfully (3405 jobs).`

In progress at this intake checkpoint (completed below):

- Audit existing Lean declarations and mathlib APIs for the Hessian bridge,
  spectral-gap equivalence, lazification, endpoint corollary, fractional
  aggregation, full defective-conductance range, and fixed-step obstruction.

Next task at this intake checkpoint (completed below):

- Implement the coordinate-free `C²` Hessian-to-`FirstOrderPotential` bridge,
  after confirming the narrowest available calculus and Riesz APIs in the
  pinned mathlib source.

## 2026-08-30: Milestone 1 calculus and gap semantics

Complete:

- Audited the canonical manuscript labels and statements. Added the missing
  content label `cor:sqrt-d-endpoint` to Corollary 2.2.
- Cleaned `paper/`: the current manuscript, bibliography, and PDF are the
  only current files. Confirmed superseded drafts were removed; the unique
  standalone Davies companion was preserved under `paper/legacy/` with a
  contextual README. A static audit found no duplicate or undefined active
  references.
- Added `Concrete/HessianToFirstOrder.lean`:
  `HessianBoundedPotential` records `ContDiff ℝ 2 U` and quadratic-form
  bounds on `iteratedFDeriv ℝ 2 U`; `lowerTaylor` and `upperTaylor` are proved
  on affine lines; `gradient_cocoercive` and `gradient_lipschitz` are derived;
  `toFirstOrderPotential` records exactly `gradient U`.
- Added `Concrete/RayleighSpectralGap.lean` with declarations
  `L2RayleighTest`, `rayleighQuotient`, `rayleighSpectralGap`,
  `L2PoincareLower`, `l2SpectralGap`,
  `l2PoincareLower_iff_le_rayleighSpectralGap`,
  `l2SpectralGap_eq_rayleighSpectralGap`, and
  `spectralGap_le_rayleighSpectralGap`.
- Added `Concrete/HessianMainTheorem.lean`, exporting
  `HessianBoundedPotential.universal_masterRHS_spectralGap_lower` and
  `HessianBoundedPotential.universal_masterRHS_rayleighSpectralGap_lower`.

Commands run:

```text
lake env lean UniformRandomMALA/Concrete/HessianToFirstOrder.lean
lake env lean UniformRandomMALA/Concrete/RayleighSpectralGap.lean
lake build UniformRandomMALA.Concrete.HessianMainTheorem
```

The first two module checks succeeded. At this checkpoint, the targeted Lake
build was still compiling the deep existing dependency chain; its successful
completion is recorded in the following milestone entry.

In progress at this checkpoint (completed below):

- Exact paper endpoint build and axiom audit.
- Concrete lazification and current Corollary 2.2.
- Fractional `L²` aggregation and full-parameter flow wrappers (independent
  modules delegated for parallel implementation).

Next task at this checkpoint (completed below):

- Finish the targeted endpoint build, add the new modules to the public
  import surface, and inspect `#print axioms` for the two principal endpoints.

## 2026-08-30: Milestones 1--4 integrated

Complete:

- Milestone 1: the Hessian bridge, Rayleigh spectral-gap semantics, and the
  paper-form non-lazy endpoint compile.  In addition to the record-level
  theorem, `exists_universal_nonlazy_paperMasterRHS_lower` states the exact
  displayed formula with `A₀,b₀,c₀` chosen before the dimension and potential.
- Milestone 2: `Concrete/LazyKernel.lean` constructs the concrete fair lazy
  kernel, proves Markovness, reversibility, setwise and energy identities,
  exact Rayleigh-gap halving, and the existential paper-form lazy endpoint.
  `Concrete/SqrtDimensionCorollary.lean` proves both displays of Corollary 2.2,
  including `min_sqrtDimensionDenominator_le_two_pStar` with no assumption
  `pStar ≤ d`.
- Milestone 3: integrated `Concrete/FractionalAggregation.lean`.  Its exact
  `L²` endpoint is `fractionalAggregation_poincareLower`; energy domination
  is invoked only on bounded `MemLp` truncations.  Zero `β` coefficients and
  extended-valued cases are covered.  The hard-assignment corollary is
  `hardAssignmentAggregation_poincareLower`.
- Milestone 4: `Concrete/AllParameterMALAFlow.lean` proves arbitrary
  admissible `p,θ,t`, both exact flow clauses, and the unsaturated inequality
  `m t log(1/π(S)) ≤ 1`.  The bundled endpoint is
  `FirstOrderPotential.allParameterMALAFlowBounds`.
- Added all four milestones to the public import surface and dependency audit.

Verification performed in the active package:

```text
lake build UniformRandomMALA.Concrete.HessianMainTheorem
lake env lean UniformRandomMALA/Concrete/LazyKernel.lean
lake env lean UniformRandomMALA/Concrete/FractionalAggregation.lean
lake env lean UniformRandomMALA/Concrete/AllParameterMALAFlow.lean
```

All commands succeeded. Independent full builds for Milestones 2--4 also
succeeded before integration. At this checkpoint, an active-package full
build remained to be run after Milestone 5; the completed build is recorded
in the final entry below.

In progress at this checkpoint (completed in the final entry below):

- Milestone 5.  `Concrete/SpectralGapUpperBounds.lean` now supplies generic
  Rayleigh test-function and exact indicator-cut upper bounds.
- `Concrete/FixedStepHardPotential.lean` defines the manuscript's explicit
  cosine-perturbed potential, proves it `C^∞`, computes its actual second
  Fréchet derivative, proves the `[m,L]` Hessian bounds, and packages it via
  `HessianBoundedPotential` so its MALA drift is the genuine Riesz gradient.
- The first-coordinate local branch and Gaussian trigonometric/Chernoff
  branch are being developed independently.

Next task at this checkpoint (completed below):

- Complete and combine the local and sticky-region branches, then formalize
  the scalar minimax optimization and run the full active-package audit.

## 2026-08-30: reader documentation synchronized through Milestone 4

Complete:

- Rewrote `README.md` for readers of the paper. It now begins from the
  manuscript's `C²` Hessian assumptions and identifies the paper-form
  non-lazy and lazy theorem declarations, instead of describing the older
  `FirstOrderPotential` endpoint as the final trust boundary.
- Rewrote `FORMALIZATION_STATUS.md` to distinguish kernel-checked Milestones
  1--4 from the current Milestone 5 working modules. Removed obsolete claims
  that the Hessian bridge, Rayleigh-gap connection, concrete lazy kernel,
  fractional aggregation lemma, or full-parameter flow theorem were missing.
- Expanded `REUSABLE_RESULTS.md` with theorem-level accounts of:
  the affine-line Hessian calculus bridge; the exact `L²`
  Poincaré--Rayleigh equivalence and its extended-valued cases; generic fair
  lazification; fractional finite-component aggregation with `L²`-scoped
  domination; Rayleigh test/cut upper bounds; full-parameter MALA flow;
  finite Gaussian Bakry--Ledoux enlargement; and weak-limit transfer.
- Documented the current fixed-step modules without claiming Proposition 2.3:
  the `C^∞` hard potential and actual Hessian, the local first-coordinate
  bound, origin log-ratio algebra, exact Gaussian trigonometric moments, MGF
  contraction, and finite-product Chernoff estimate.
- Preserved the explicit statement that the package uses a finite
  discrete-time replacement for the paper's continuous-time Appendix B
  route and does not claim an SDE formalization.

Documentation verification:

```text
rg --files UniformRandomMALA/Concrete
rg -n "^(theorem|def|structure|lemma) " <new milestone modules>
```

The declaration names and module boundaries in the three reader documents
were checked directly against the current Lean sources. No Lean source,
manuscript source, bibliography, import surface, or completion report was
changed in this documentation pass.

In progress at this checkpoint (completed in the final entry below):

- Milestone 5 integration. The generic upper-bound, hard-potential,
  local-obstruction, log-ratio, and Gaussian concentration source modules were
  present; their final aggregate build and axiom audit were pending at this
  checkpoint.

Next task at this checkpoint (completed below):

- Prove acceptance continuity and the positive-mass sticky neighborhood,
  derive the exponential cut-flow upper bound, combine it with the local
  branch, complete the scalar minimax theorem, and then run the full package
  and manuscript audits.

## 2026-08-30: Milestone 5 completed and fully integrated

Complete:

- Added the generic sticky-cut infrastructure in
  `Concrete/StickyRegionCut.lean`. The endpoint
  `FirstOrderPotential.continuous_malaAcceptanceProfile` proves continuity of
  the proposal-averaged acceptance by dominated convergence.
  `FirstOrderPotential.exists_target_ball_rayleighSpectralGap_le_two_mul`
  constructs a centered ball with positive target mass below one half and
  converts a strict origin acceptance bound into both an outgoing-flow bound
  and the Rayleigh upper bound `Gap ≤ 2b`.
- Added `Concrete/HardPotentialShiftedConcentration.lean`. It shifts the
  Gaussian trigonometric increment by half the magnitude of its negative
  mean, chooses a fixed positive Chernoff parameter, and proves a universal
  product contraction at the required negative linear threshold. The
  finite-product endpoint is
  `exists_universal_contraction_factor_for_pi_scaledGaussian_tail`.
- Added `Concrete/HardPotentialStickyObstruction.lean`. It combines the exact
  origin log-ratio, negative-threshold concentration, acceptance-profile
  continuity, and the centered sticky ball. Its universal endpoint is
  `exists_universal_fixedStepHard_sticky_rayleighSpectralGap_upper`.
- Combined the local and sticky branches in
  `Concrete/FixedStepHardPotentialObstruction.lean`. The dimension-indexed
  endpoint
  `exists_universal_fixedStepHardPotential_obstruction_allDimensions`
  proves, for the explicit `C∞` witness,

  ```text
  Gap(P_h) ≤ 8 min(
    mh + (mh)^2/2,
    exp(-c(d-1) min((L-m)h,1))).
  ```

- Added the scalar compression and balance-point proof in
  `Concrete/FixedStepObstructionOptimization.lean`, including
  `iSup_fixedStepTwoBranchEnvelope_le_log_max_exp`.
- Added the literal minimax definitions in `Concrete/FixedStepMinimax.lean`:
  `smoothHessianPotentialGapValues` is the exact class of `C∞` potentials
  with actual Hessian in `[mI,LI]`; `fixedStepWorstPotentialGap` is its
  `sInf`; `fixedStepMinimaxGap` is the `iSup` over every positive step size.
  The explicit hard potential is proved to belong to this class.
- Completed Proposition 2.3 at
  `exists_universal_fixedStepMinimaxGap_paper_upper`. It chooses one universal
  exponential rate `c>0`; for every `κ₀>1` it chooses `C>0` depending only on
  `κ₀` and proves

  ```text
  fixedStepMinimaxGap d m L ≤
    C max(log((L/m)d)/((L/m)d), exp(-c d))
  ```

  whenever `d≥2`, `0<m<L`, and `κ₀≤L/m`.
- Added the completed fixed-step modules and principal endpoints to
  `AllResults.lean`, the root import surface, and `DependencyAudit.lean`.
- Updated `README.md`, `FORMALIZATION_STATUS.md`, and
  `REUSABLE_RESULTS.md` so Proposition 2.3 is described as checked rather
  than provisional, with the exact complete-lattice quantifiers and constant
  dependence made explicit.

Verification:

```text
lake build
```

Result: success, `Build completed successfully (3435 jobs).`

The dependency audit contains `#print axioms` commands for the generic
sticky-cut endpoints, hard-potential local and sticky branches, combined
obstruction, smooth-class witness membership, scalar optimization, and
`exists_universal_fixedStepMinimaxGap_paper_upper`.

Remaining package tasks:

- Synchronize the manuscript's Lean-verification section with the completed
  package, compile the manuscript and bibliography, run the final source and
  reference audits, and assemble the requested archive and completion report.

## 2026-08-30: final manuscript, kernel, and packaging audit

Complete:

- Rewrote the manuscript's `Lean verification` section to describe the
  actual-Hessian bridge, paper Rayleigh gap, concrete lazification,
  Corollary 2.2, exact `L²` fractional aggregation, full-parameter flow, and
  completed fixed-step minimax theorem without overstating the SDE proof
  route.
- Audited 96 active LaTeX labels: no duplicate active label, undefined
  `\ref`/`\eqref`/`\cref`, or unreferenced equation label remains.
- Ran `latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex` in
  `paper/`. BibTeX and the final PDF build succeeded; the PDF has 43 pages and
  the final log contained no undefined citation/reference or duplicate-label
  warning.
- Added the four final fixed-step endpoints to `DependencyAudit.lean` and ran
  the audit. Each reports only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Ran the complete Windows audit with the bundled Python runtime on `PATH`:

  ```text
  powershell -ExecutionPolicy Bypass -File scripts/check.ps1
  ```

  Static audit: passed (151 Lean files, 2,036 declarations, no placeholder or
  project axiom). Numerical audit: passed (2,000 deterministic trials). Full
  kernel build: passed (3,435 jobs). Public aggregate import and dependency
  audit: passed.
- Added `COMPLETION_REPORT.md` and synchronized all reader-facing status,
  theorem-map, trust-boundary, build, manifest, and audit-summary files.

Next task at that checkpoint: create and verify the clean distribution
archive and copy the then-requested standalone manuscript source and
bibliography to `outputs/`. This is a historical task, superseded by the
PDF-only synchronization below.


## 2026-09-05: time-reversal documentation and PDF-only synchronization

- Updated the paper/Lean comparison to describe the stationary time-reversal
  argument and credit Lyons--Zheng (1988, Section 1, equation (1.7)).
- Updated the increment references to Lemmas B.2--B.3 and the path-moment
  reference to Lemma B.5 in the current PDF. Kept subsection B.4 references
  unchanged; they identify the overlap-proof subsection.
- Preserved the finite Gaussian likelihood, Euler/RWM, and weak-limit Lean
  proof and every existing Lean/build/check source byte-for-byte.
- Replaced all contents of `paper/` with the author-supplied `main(3).pdf`,
  named `paper/main.pdf`. Removed the legacy companion directory rather than
  moving it elsewhere in the package. The PDF was not edited or recompiled.
- Synchronized current author/title metadata to the supplied PDF. Marked
  prior kernel-build, axiom, LaTeX, and bibliography audit results as
  historical rather than treating them as new validation.
- Added a documentation-only patch and a guarded PowerShell updater for
  existing repositories, plus `GITHUB_UPDATE_GUIDE.md`. The updater neither
  commits nor pushes and does not replace Lean or simulation sources.
- Reran the existing static and deterministic numerical checks. Compared
  source/configuration hashes and the PDF hash; see
  `DOCUMENTATION_UPDATE_2026-09-05.md` for the checks and their scope.
- No new Lean kernel build was run: Lean/Lake is not installed in the update
  environment. No live repository contents were fetched or modified.
