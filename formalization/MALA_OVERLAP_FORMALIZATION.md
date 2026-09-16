# MALA local-overlap formalization note

> **2026-09-12 first-order revision:** the public `C1Potential` route and the
> `p >= 1` rejection/overlap extension are kernel-checked with Lean/mathlib
> 4.33.0. The broader nonconvex Appendix B extension remains outside the Lean
> claim. Earlier Hessian endpoints are compatibility special cases.

## First-order entry route

`C1Potential` -> proved descent lemma -> `FirstOrderPotential` -> existing
concrete proof. No target Hessian is required. The p >= 1 rejection/overlap
exports use second-moment interpolation; the old p >= 2 estimates and Gaussian
OU/Euler–RWM core are unchanged. See `FIRST_ORDER_REVISION.md` for the exact
names, mathematical scope, and Appendix B qualification.

Current Lean validation: **2026-09-15**. The complete 3,439-job build and the
266-declaration axiom gate passed with Lean/mathlib 4.33.0.

This note concerns the moment-indexed local-overlap result labeled
`prop:overlap` and numbered Proposition 3.2 in `paper/main.pdf`,
**A global spectral gap for Metropolis-adjusted Langevin algorithm
with a uniformly randomized step size**.
It is the input that converts stationary rejection-moment control into local
total-variation overlap for dyadic mixtures of MALA step sizes.

## Certificate-free Lean entry point under the standing assumptions

The revised reader-facing theorem, proved without an analytic interface
parameter, is

```lean
UniformRandomMALA.Concrete.C1Potential.mala_overlap_bounds
```

in `Concrete/C1MainTheorem.lean`. It applies for every real `p >= 1`, and its
explicit universal constants are

```lean
proposition32CrSmallOne = 1 / (32 * Real.exp 1)
proposition32CrLargeOne = 12288 * (Real.exp 1) ^ 3
```

The theorem gives both assertions in the paper: the moment-indexed local
dyadic-MALA overlap with a measurable good set and the globally safe overlap.
The local exceptional mass is

```text
(proposition32CrLargeOne * L * t * sqrt (p * (d + p))) ^ p,
```

and both overlap conclusions use the paper threshold `3/4`.

The adapter first constructs `V.toFirstOrderPotential`, then invokes the
`p >= 1` theorem in `Concrete/RejectionMomentsOne.lean`. The sharper internal
core remains

```lean
UniformRandomMALA.Concrete.FirstOrderPotential.mala_overlap_bounds
```

in `UniformRandomMALA/MALAOverlap.lean`. It assumes `p >= 2` and uses the
constants `1/(16e)` and `6144e^3`. The content-equivalent numbered declaration
`FirstOrderPotential.proposition32_discreteTime` is retained for compatibility
with older source. New paper-facing code should prefer
`C1Potential.mala_overlap_bounds`.

The still older declaration

```lean
PaperAnalyticInterfaces.elementary_proof_implies_proposition32
```

belongs to `PaperAnalyticInterfaces`, a legacy record that represented several
analytic inputs as fields. It is available for modular experiments and old
imports, but it is not used by the concrete theorem above.

## Relation to the revised manuscript

The manuscript now obtains its linear-increment estimate (Lemma B.2) by
stationary time reversal, an elementary specialization of the Lyons--Zheng
forward--backward decomposition (1988, Section 1, equation (1.7)). The
integrated-increment proof (Lemma B.3) retains Gaussian randomization and
Jensen's inequality. The finite discrete-time proof documented below is
unchanged and does not formalize those continuous-time identities.

## Compiled elementary dependency graph

```text
finite Euler recursion and Gaussian maximal estimate
  -> finite Euler energy MGF
  -> real moments of the chronological Gaussian likelihood
  -> full-path centered L^p bound with constant 1024 e^3

finite likelihood tilt and endpoint data processing
  -> frozen-drift proposal edge law
  -> Euler endpoint Radon--Nikodym moment bound

shared Gaussian--uniform Euler/RWM update
  -> one-step bias and second-moment estimates
  -> stationary finite pair-chain recurrence
  -> fixed-horizon L^2 discrepancy tends to zero
  -> retained-initial edge coupling with vanishing ENNReal cost
  -> common Prokhorov subsequence and symmetric target self-coupling

moving-reference L^p closure
  + concrete MALA accepted-flow RN meet
  -> stationary MALA rejection moment bound for p >= 2
  -> factor six: 1024 e^3 becomes 6144 e^3

second-moment specialization + L^2-to-L^p interpolation for 1 <= p <= 2
  -> stationary rejection bound for every p >= 1
  -> rescaled constants 1/(32e) and 12288 e^3
  -> revised moment-indexed local overlap

safe acceptance + Gaussian proposal TV + accept/reject comparison
  -> global overlap (the intermediate setwise bound is 17/32)
```

No Euler--Maruyama approximation, diffusion construction, or Ethier--Kurtz
theorem occurs in this dependency graph.

## Principal certificate-free modules

- `Concrete/FiniteEulerEnergyMGF.lean` proves the finite Euler energy
  exponential estimate.
- `Concrete/FiniteEulerLikelihoodBounds.lean` and
  `Concrete/FiniteEulerRealMoments.lean` derive the centered likelihood
  moments, including
  `finiteGaussianDRec_centered_rpow_root_le_paper_scale` with constant
  `1024 * e^3`.
- `Concrete/FiniteEulerEndpointContraction.lean` proves the tilted/frozen
  endpoint identity and endpoint moment contraction.
- `DiscreteTime/EulerRWMPairChain.lean`, `EulerRWMRecurrence.lean`, and
  `EulerRWMFiniteRecurrence.lean` build and iterate the shared finite pair
  chain.
- `DiscreteTime/EulerRWMVanishingStep.lean` proves the fixed-horizon energy
  limit. Its explicit scale is

  ```lean
  stationaryEulerRWMRecurrenceScaleConstant V =
    2 * sqrt 2 * stationaryEulerRWMCouplingConstant V +
      (2 * targetGradNormMoment V 2 +
        8 * stationaryRWMRejectionBiasSqConstant V)
  ```

- `DiscreteTime/EulerRWMEdgeCoupling.lean` and
  `EulerRWMEdgeVanishing.lean` retain the initial endpoint, convert the real
  pair energy to the `ENNReal` coupling cost, choose the elementary offset
  schedule `delta_n = h/(n+N)`, and extract a common structured weak limit.
- `DiscreteTime/FiniteEulerEdgeBridge.lean` identifies the Euler edge law
  used by the pair chain with the likelihood endpoint law.
- `Concrete/MALAAcceptedMeet.lean`, `MALAMetropolisMeet.lean`, and
  `MALAWeakLimitAssembly.lean` identify the limiting MALA meet and its
  rejection marginal.
- `Concrete/MALAFullPathAssembly.lean` proves
  `stationaryMALARejectionMomentBound_paperScale`.
- `DiscreteTime/MomentInterpolation.lean` and
  `Concrete/RejectionMomentsOne.lean` extend the moment and overlap range from
  `p >= 2` to every `p >= 1`.
- `Concrete/MALARejectionGoodSet.lean`, `MALALocalOverlap.lean`,
  `MALASetwiseTV.lean`, and `MALAOverlapBounds.lean` finish the local and
  global clauses of the sharper `p >= 2` core.

All these declarations are ordinary theorem proofs with no project-specific
axioms and no proof placeholders.

## Formalization assessment

Proposition 3.2 in its revised `p >= 1` range is fully formalized and
kernel-checked through `C1Potential.mala_overlap_bounds`. The route
is finite-dimensional until the single Prokhorov subsequence step, and that
step is expressed entirely in Mathlib's topology of probability measures.
The previously difficult infrastructure---finite Gaussian product
likelihoods, endpoint RN contraction, pair-kernel iteration, stationary
marginals, retained-initial couplings, and moving-reference closure---has now
been built and instantiated.

The subsequent paper-level route has also advanced: Mills/quantile bounds,
Gaussian shift, separated sets, defective conductance, concrete component
aggregation, exceptional-set assignment, and the harmonic ladder are now
checked.  The concrete master theorem in
`Concrete/UniversalConstants.lean` depends only on Bakry--Ledoux.  The older
legacy `PaperAnalyticInterfaces` theorem is retained as a modular
specification, while the public end-to-end route proves its inputs directly.
