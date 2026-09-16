# Formalization worklog

> **2026-09-15 current verification:** the public `C1Potential` route and the
> `p >= 1` rejection/overlap extension are kernel-checked with Lean/mathlib
> 4.33.0. The full 3,439-job build and 266-declaration axiom gate passed.
> Earlier Hessian endpoints remain compatibility special cases.

Current manuscript inventory: `paper/main.pdf` only. TeX, bibliography,
and separate figure files are not bundled. The public existential statements
use `A₀ ≥ 1`, with the established `A₀ ≥ 2` witness. Historical entries below
retain the inventories and checks from their original dates; they do not
assert that old manuscript source files are present in the current package.

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

## 2026-09-12 — first-order manuscript and interface revision

Prepared a candidate replacing the standing C2/Hessian formulation by C1 plus
strong convexity and Lipschitz actual gradient. The revised manuscript added a
broader nonconvex Appendix B scope; the Lean claim explicitly excluded that
independent generalization. Added the C1 adapter and matching
main/corollary/rejection/overlap scripts; extended p >= 1 by interpolation.
Added a repository-root CI workflow and strict post-build axiom gate. At this
candidate-preparation checkpoint only the static and numerical checks had run;
the next entry records the later kernel audit.

## 2026-09-12 — kernel audit and corrected release

Complete:

- restored and used pinned Lean/mathlib 4.33.0;
- repaired elaboration failures in `C1ToFirstOrder.lean`,
  `MomentInterpolation.lean`, and `RejectionMomentsOne.lean`;
- renamed colliding private Euclidean instances in the C1 adapter;
- repaired `AllResults.lean`, whose intended revision imports were inside a
  block comment and therefore inert;
- strengthened the static and first-order audits to strip comments and verify
  public reachability;
- added `C1Potential.allParameterMALAFlowBounds`, a direct first-order wrapper
  for the full Proposition 3.4 conclusion;
- updated the actual axiom audit and reader documentation;
- relabeled Hessian theorem comments as optional smooth compatibility results.

Verification commands:

```text
lake build
lake env lean UniformRandomMALA/AllResults.lean
lake env lean UniformRandomMALA/DependencyAudit.lean
python scripts/check_axioms.py validation/local/axioms.log
powershell -ExecutionPolicy Bypass -File scripts/check.ps1
```

Results:

```text
155 Lean files; 2069 declarations; no proof placeholders
FIRST-ORDER SOURCE AUDIT PASSED
NUMERIC SANITY PASSED (2000 trials)
Build completed successfully (3439 jobs).
AXIOM AUDIT PASSED: 266 declarations; only
  [propext, Classical.choice, Quot.sound]
FULL SOURCE BUILD AND AXIOM AUDIT PASSED
```

Remaining mathematical scope: Appendix B's optional extension of the
rejection lemmas to general nonconvex C1 potentials is not formalized. The
checked strongly convex discrete route is end-to-end for Theorem 2.1.

Release handoff at that checkpoint: checksum regeneration and clean-archive
validation remained release-engineering work. The final reconciliation entry
below supersedes this former "next task" marker; it is not an outstanding Lean
proof task.

## 2026-09-12 — final API and reader-documentation reconciliation

Complete:

- checked every theorem name used in the reader documentation against the
  public `UniformRandomMALA.AllResults` import;
- clarified that the 2,069 figure is the static source regex's count of
  top-level `def`/`lemma`/`theorem`/`structure` declarations, not a census of
  Lean's elaborated environment;
- recorded the explicit `SFinite` reference-measure hypotheses on generic
  lazy-kernel reversibility, energy, quotient, and gap scaling;
- distinguished the fractional aggregation theorem's direct
  all-measurable `spectralGap` conclusion from its transfer to the paper's
  `L²` Rayleigh gap;
- documented the literal quantifier order of the generic Gaussian
  contraction theorem, the finite-Euler module import, and the namespace
  setup needed for standalone examples;
- clarified that the real-exponent moment inequality takes integrability as
  an API hypothesis and that the rejection application proves it from
  boundedness; and
- recorded the manuscript status then available at that checkpoint. The
  subsequent source-recovery and rebuild entry below supersedes that interim
  PDF-only inventory.

No Lean declaration or proof was changed in this documentation pass. The
kernel, import, and axiom results recorded immediately above remain the final
mathematical verification state; checksum and ZIP validation are packaging
gates rather than missing formalization work.

## 2026-09-12 — canonical manuscript source and final release reconciliation

Complete:

- recovered the editable revised manuscript source, bibliography, and all
  three included figure PDFs and installed them as the canonical `paper/`
  source set;
- changed only the obsolete Lean-status paragraph, the typo `temrs`, an
  unnumbered ESJD display that had produced a duplicate PDF destination, and
  one unused equation label;
- rebuilt `paper/main.pdf` from `paper/main.tex` with
  `latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex` (47 pages);
- audited 106 unique labels, 240 reference uses over 103 labels, 94 active
  citation commands containing 120 bibliography-key uses over 48 keys, 72
  referenced equation labels, and three present figure inputs; no item was
  unresolved or duplicated;
- checked all 225 PDF named destinations and all 543 PDF actions; every target
  resolves, and the rebuilt PDF has no undefined reference/citation, duplicate
  destination, or overfull-box warning;
- visually inspected the edited status page and its neighboring pages at high
  resolution and confirmed that the text remains searchable;
- reran the complete PowerShell checker after the Lean-comment and audit-script
  reconciliation: the 3,439-job build, public import, and 266-declaration axiom
  gate all passed; and
- staged a clean distribution, regenerated `validation/SHA256SUMS.txt`,
  re-extracted the ZIP, verified exact file-set equality and every SHA-256
  checksum, reran all four source/numerical audits in the extraction, and
  confirmed that no build cache, Git data, local axiom log, Python bytecode, or
  compiled Lean artifact is present.

The delivered package is therefore synchronized at all three reader-visible
layers: the revised paper statement, the public Lean declarations, and the
validation/documentation record. The only explicitly unformalized extension
is Appendix B's broader nonconvex `C¹` rejection result; it is independent of
the end-to-end strongly convex proof of Theorem 2.1.

## 2026-09-15 — revised A₀ range and PDF-only manuscript

- Changed the three public existential main-theorem statements to `A₀ ≥ 1`.
  The concrete witness and all internal `A₀ ≥ 2` assumptions remain intact.
- Recorded the revised PDF SHA-256 `eb3ec374502cbc7b01a2552164f8d64693f64fef333f9948173f575d09a6c4f9`. The `paper/` directory
  contains only `main.pdf`; corrected the active inventory documentation.
- Replaced the mandatory TeX-source gate by an explicit PDF identity and
  inventory audit, with seven passing failure-case regression tests.
  Archived the old TeX build and source-audit evidence under
  `validation/historical/2026-09-12/`.
- Reran the full PowerShell gate: static and first-order audits, PDF audit,
  2,000 numerical trials, all 3,439 build jobs, direct `AllResults` elaboration,
  and actual axiom checks for 266 declarations passed. Only `propext`,
  `Classical.choice`, and `Quot.sound` were reported.
- Added `REPOSITORY_UPDATE.md`; no GitHub commit, push, or PR was performed.
- Regenerated the checksum manifest for the distributed `formalization/`
  files, excluding build caches, scratch files, and local logs.
