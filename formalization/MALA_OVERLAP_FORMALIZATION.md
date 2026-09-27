# Rejection and local overlap

Proposition 3.2 is formalized by
`UniformRandomMALA.Concrete.C1Potential.mala_overlap_bounds` in
[C1MainTheorem.lean](UniformRandomMALA/Concrete/C1MainTheorem.lean).
It proves the moment-indexed local dyadic-MALA overlap and the globally safe
overlap for every real `p ≥ 1`. The full nonconvex Proposition B.1 is
formalized separately by `NonconvexPotential.exists_universal_stationary_rejection_moments`
in [Nonconvex/StationaryRejection.lean](UniformRandomMALA/Nonconvex/StationaryRejection.lean).

## Check the statements and definitions

For local overlap, compare `C1Potential` with the standing first-order
assumptions, then inspect `MALARejectionGoodSet.lean`, `MALALocalOverlap.lean`,
and `MALAOverlapBounds.lean`. The good set is measurable, its exceptional
mass has the paper's moment scale, and both overlap conclusions use the
paper's total-variation threshold. `RejectionMomentsOne.lean` supplies the
full exponent range by second-moment interpolation.

For Proposition B.1, inspect `NonconvexPotential.lean` and `NonconvexMALA.lean`.
They use a `C¹` potential, its actual Lipschitz gradient, and an integrable
Boltzmann weight. The theorem bounds the literal `Lᵖ(π)` norm of the actual
Gaussian Metropolis rejection probability. It does not assume strong
convexity or target position moments.

## Follow the finite-chain proof

| Stage | Main source families | What is proved |
|---|---|---|
| Likelihood moments | `FiniteGaussianLikelihood`, `FiniteEulerEnergyMGF`, `FiniteEulerRealMoments`, `FiniteEulerLikelihoodBounds` | Actual finite Gaussian change of measure and centered real-exponent likelihood bounds. |
| Endpoint law | `FiniteGaussianEndpointLaw`, `FiniteEulerEndpointContraction`, `FiniteEulerEdgeBridge` | Frozen-drift proposal identity and contraction of density moments to the endpoint. |
| Euler/RWM comparison | `EulerRWMPairChain`, `EulerRWMRecurrence`, `EulerRWMFiniteRecurrence`, `EulerRWMVanishingStep` | An actual common-noise pair chain and a fixed-horizon discrepancy tending to zero. |
| Retained-initial edge law | `EulerRWMEdgeCoupling`, `EulerRWMEdgeVanishing` | A common weak limit with target marginals and symmetry. |
| Acceptance and rejection | `MALAMetropolisMeet`, `MALAWeakLimitAssembly`, `MALAFullPathAssembly` | The accepted-flow meet and the rejection moment bound. |
| Full exponent range | `MomentInterpolation`, `RejectionMomentsOne`, `StationaryRejection` | Every real `p ≥ 1`, followed by the local-overlap application. |

The original strongly convex implementation lives in `Concrete/` and
`DiscreteTime/`. Its nonconvex specializations live in `Nonconvex/` and
reuse the same potential-independent Gaussian, measure, and weak-limit
lemmas. `NonconvexGradientMoments.lean` and `NonconvexGradientMGF.lean` prove
the needed gradient moments. `NonconvexEulerStability.lean` and the
nonconvex recurrence control finite-horizon Lipschitz growth in place of
convex contraction.

The continuous-time increment and likelihood statements of Lemmas B.2–B.5 are
explicitly excluded. The finite-chain argument above proves Proposition B.1
without using them as assumptions. The proof uses mathlib's probability
measure topology for weak limits and does not require a diffusion or an
SDE approximation theorem.

## Public and intermediate interfaces

The `FirstOrderPotential.mala_overlap_bounds` theorem retains the sharper
internal `p ≥ 2` form. New paper-facing code should start with
`C1Potential.mala_overlap_bounds`. Conditional assembly records, including
the older `PaperAnalyticInterfaces`, remain reusable interfaces; they are
not hypotheses of either public endpoint described here.

The main gap proof continues from overlap through separated sets,
conductance, and aggregation, with target isoperimetry supplied internally.
Use [PAPER_READER_GUIDE.md](PAPER_READER_GUIDE.md) for that route and
[BUILD_STATUS.md](BUILD_STATUS.md) for current package verification evidence.
