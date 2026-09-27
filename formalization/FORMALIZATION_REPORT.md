# Formalization report: uniform-random MALA

This package develops the mathematics of Qian Qin's *A spectral gap for
Metropolis-adjusted Langevin algorithm with a uniformly randomized step size*
in Lean using mathlib. The manuscript, source, bibliography, and figures are
bundled in `paper/`. Begin with [PAPER_READER_GUIDE.md](PAPER_READER_GUIDE.md)
to locate statements, compare definitions, and follow complete proofs.

## Mathematical architecture

| Layer | Role and principal sources |
|---|---|
| Assumptions and algorithms | `C1ToFirstOrder.lean` uses the actual gradient and derives its Taylor bound. `EuclideanTarget.lean`, `MALA.lean`, `MALAFamily.lean`, and `LazyKernel.lean` construct the normalized target and the fixed, randomized, and half-lazy algorithms. |
| Rejection and isoperimetry | Finite Gaussian likelihoods and Euler/RWM weak limits establish rejection. Gaussian OU/Bobkov interpolation and finite-Euler transport establish target enlargement. `Nonconvex/StationaryRejection.lean` also proves full Proposition B.1 under its weaker assumptions. |
| Gap and mixing | General energy and flow aggregation lead to `PaperNormalizedGap.lean`. Actual `L²` kernel contraction and density evolution lead to `PaperNormalizedMixing.lean`. |
| Sample averages | Actual finite path laws, a centered kernel operator, the Poisson equation, and covariance identities give stationary variance limits. `L⁴` interpolation and density pairing give the nonstationary MSE theorem. Extended variance and Rayleigh witnesses prove the fixed-step comparison. |
| Reusable probability | `KernelLp*.lean`, `StationaryPath*.lean`, `MarkovInfinite*.lean`, and `MartingaleCLT*.lean` supply kernel integration, path laws, conditional expectations, and martingale limit arguments. `PaperCentralLimit.lean` proves both CLTs from every initial distribution with the actual stationary limiting variance. |

The general fractional aggregation lemma and component-aggregation theorem
are fully formalized in `FractionalAggregation.lean`. Their energy and flow
hypotheses match the general paper statements; the MALA proof establishes
those hypotheses before using the theorems.

The explicit excluded statements are Lemmas B.2–B.5. The finite-chain proof
of Proposition B.1 bypasses their continuous-time stochastic-calculus route.
This exclusion does not impose an unproved rejection premise on the public
MALA theorems. [THEOREM_MAP.md](THEOREM_MAP.md) gives precise coverage and
declarations; [FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) records
the completed scope and explicit exclusions.

## Verification

The pinned toolchain builds the proofs and the public `AllResults` import.
The dependency audit inspects actual logical dependencies of selected
declarations; [BUILD_STATUS.md](BUILD_STATUS.md) records its result and the
full package gate. Source, manuscript, numerical, and typesetting checks
provide separate evidence. Comparing the Lean definitions and theorem types
with the paper remains part of the review.

For more detail, use [PROOF_STRATEGY_LEDGER.md](PROOF_STRATEGY_LEDGER.md),
[REUSABLE_RESULTS.md](REUSABLE_RESULTS.md), and
[TRUST_BOUNDARY.md](TRUST_BOUNDARY.md).
