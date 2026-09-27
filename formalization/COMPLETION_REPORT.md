# Coverage and verification report

The package contains the paper-facing gap and mixing theorems, stationary
variance limits and bounds, both variance-separation assertions, the
nonstationary MSE corollary, the full nonconvex rejection theorem, and the
general aggregation lemma and theorem. The nonlazy and half-lazy CLTs are
also proved from every initial distribution. Every requested result has a
formalized endpoint; Lemmas B.2–B.5 are the explicit scope exclusion.

For the current statement-by-statement status, use
[FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md). For the latest full
build and audit result, use [BUILD_STATUS.md](BUILD_STATUS.md). This report
explains how to review coverage without conflating it with build evidence.

## Review the mathematical endpoints

1. Find the paper number and TeX label in [THEOREM_MAP.md](THEOREM_MAP.md).
2. Read the linked declaration's assumptions and conclusion. The public
   main theorem takes `C1Potential`, whose drift is the actual gradient;
   Proposition B.1 instead takes the weaker `NonconvexPotential` interface.
3. Compare the target, proposal, acceptance rule, kernel mixture, gap,
   density norm, and sample-law definitions using the
   [definition map](PAPER_READER_GUIDE.md#3-compare-definitions-with-the-paper).
4. Follow the [proof paths](PAPER_READER_GUIDE.md#4-follow-the-complete-proofs)
   to the results supplying each analytic input.

`PaperNormalizedGap.lean` contains the current main theorem and all three
gap-corollary bounds. `PaperNormalizedMixing.lean` contains both mixing-time
ceilings with the stated tuning dependence. `PaperAsymptoticVariance.lean`,
`VarianceSeparationCorollary.lean`, `VarianceSeparationFixedStep.lean`, and
`PaperNonstationaryMSE.lean` connect the sample-average claims to actual
Markov path laws, including the extended variance needed at zero gap.
`PaperCentralLimit.lean` proves Gaussian convergence for the actual infinite
trajectory from every initial probability measure, with the same stationary
variance as the variance-limit theorem.

`FractionalAggregation.lean` proves Lemma 3.5 and Theorem 3.6 for general
finite kernel families, independently of MALA. The MALA application supplies
their flow and energy hypotheses internally. `Nonconvex/StationaryRejection.lean`
proves Proposition B.1 under its full appendix assumptions.

## Review proof dependencies

The public import is `UniformRandomMALA.AllResults`. The full gate builds
the source, checks that import, and executes the selected `#print axioms`
requests in `DependencyAudit.lean`. It permits only `propext`,
`Classical.choice`, and `Quot.sound`; missing declarations, Lean errors, and
additional axioms fail the check. Source and numerical audits are separate
checks and do not replace kernel verification.

The alternative finite-chain rejection proof proves the endpoint without
the continuous-time Lemmas B.2–B.5. The isoperimetry proof likewise derives
the needed enlargement inequality internally. The optional Hessian adapter
provides smooth special cases and the fixed-step hard witness, without
changing the first-order assumptions of the lower-bound theorem.

Run the commands in [README.md](README.md#reproduce-the-verification).
[TRUST_BOUNDARY.md](TRUST_BOUNDARY.md) explains the checks and their limits.
Manuscript typesetting and source/PDF correspondence evidence are reported
separately in `BUILD_STATUS.md`. Records under `validation/historical/`
remain historical evidence.
