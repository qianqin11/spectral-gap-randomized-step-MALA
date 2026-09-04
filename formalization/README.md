# Uniform-random MALA in Lean 4

This package accompanies Qian Qin and Guanyang Wang's paper **A Global
Spectral Gap for MALA with a Uniformly Randomized Step Size**. The current
manuscript is `paper/main.pdf`; its source is `paper/main.tex`, with references
in `paper/uniform_random_mala.bib`.

The development formalizes the paper's lower bound for uniformly randomized
MALA from the displayed `C²` Hessian assumptions. It also proves the concrete
half-lazy statement, the square-root-dimension corollary, the fractional
finite-component aggregation lemma, the full-parameter one-step flow bound,
and the fixed-step minimax obstruction over the manuscript's exact class of
infinitely differentiable Hessian-bounded potentials.

All completed results are checked by Lean's kernel. The source contains no
`sorry`, `admit`, or problem-specific axiom declarations.

The recommended aggregate import is:

```lean
import UniformRandomMALA.AllResults
```

## The main theorem

Let

```text
π(dx) = Z⁻¹ exp(-U(x)) dx,     x ∈ ℝᵈ,
```

where `U : ℝᵈ → ℝ` is twice continuously differentiable and its actual
Fréchet Hessian satisfies

```text
m ‖v‖² ≤ D²U(x)[v,v] ≤ L ‖v‖²
```

for all `x,v`, with `d > 0` and `0 < m ≤ L`. At each transition,
uniform-random MALA samples a step size uniformly from `(0,H)` and performs
the corresponding MALA update.

The structure

```lean
UniformRandomMALA.Concrete.HessianBoundedPotential d
```

records these assumptions using `ContDiff ℝ 2 U` and
`iteratedFDeriv ℝ 2 U`. Its gradient is mathlib's Riesz gradient `∇ U`; no
independent vector field is postulated. The construction

```lean
HessianBoundedPotential.toFirstOrderPotential
```

proves the two Taylor inequalities and the `L`-Lipschitz gradient estimate
needed by the existing MALA argument.

The paper-form endpoint is

```lean
UniformRandomMALA.Concrete.
  exists_universal_nonlazy_paperMasterRHS_lower
```

It chooses universal constants `A₀,b₀,c₀`, with
`2 ≤ A₀`, `0 < b₀ ≤ 1/2`, and `0 < c₀`, before the dimension and potential.
For

```text
p⋆ = A₀ (1 + log(d+1) + log(L/m)),
```

it proves, for every `H > 0`,

```text
Gap(P̄_H) ≥
  c₀ (m/H)
    min(H, (b₀/L) max(1/sqrt(p⋆(d+p⋆)), 1/d))².
```

Here `Gap` is the manuscript's extended-valued `L²` Rayleigh gap. The
definition `rayleighSpectralGap` takes the infimum of energy divided by
variance over measurable `L²` functions with nonzero variance. The module
`Concrete/RayleighSpectralGap.lean` proves its exact equivalence with the
`L²` Poincaré-lower-bound formulation, including zero-variance, infinite
energy, and empty-test-family cases. It also proves that the package's older,
stronger Poincaré formulation supplies the same Rayleigh lower bounds.

## Lazy kernel and Corollary 2.2

`Concrete/LazyKernel.lean` defines the identity/random-move mixture

```text
P_lazy = (I + P̄_H)/2
```

as a fair Boolean parameter mixture. For an arbitrary Markov kernel it proves
Markovness, preservation of reversibility, exact halving of every Dirichlet
energy, and

```text
Gap(P_lazy) = Gap(P̄_H)/2.
```

The concrete randomized-MALA declarations are

```lean
Concrete.FirstOrderPotential.lazyUniformMALA
Concrete.FirstOrderPotential.energy_lazyUniformMALA
Concrete.FirstOrderPotential.rayleighSpectralGap_lazyUniformMALA
Concrete.exists_universal_lazy_paperMasterRHS_lower
```

`Concrete/SqrtDimensionCorollary.lean` formalizes both inequalities in
Corollary 2.2 for `H = c/(L sqrt d)`. The key scalar estimate

```lean
Parameters.min_sqrtDimensionDenominator_le_two_pStar
```

is proved over the full parameter range and does not assume `p⋆ ≤ d`.

## Aggregation and one-step flow

`Concrete/FractionalAggregation.lean` contains the paper's fractional
finite-component aggregation lemma. Given reversible component kernels
`K j`, positive energy weights `γ j`, nonnegative fractional cut weights
`β j`, the `L²` energy domination

```text
∑ j, γ_j E_{K_j}(f,f) ≤ E_P(f,f),
```

and the cut-flow bound

```text
π(S) ≤ ∑ j, β_j J_{K_j}(S,Sᶜ),
```

it proves the Poincaré constant

```text
(2 ∑ j, β_j²/γ_j)⁻¹.
```

The energy-domination premise has exactly measurable-`L²` scope. The proof
applies it to bounded truncations, handles vanishing `β j` and extended-real
edge cases, and removes truncation by monotone convergence. The main endpoints
are `fractionalAggregation_poincareLower` and
`fractionalAggregation_le_spectralGap`; the hard-assignment theorem follows
by taking `β j = (φ j)⁻¹`.

`Concrete/AllParameterMALAFlow.lean` packages Proposition 3.4 for arbitrary
admissible real `p`, `θ`, and step size. Its endpoint

```lean
Concrete.FirstOrderPotential.allParameterMALAFlowBounds
```

contains both the local moment-indexed clause, including
`m t log(1/π(S)) ≤ 1`, and the safe small-step clause for
`0 < t ≤ 1/(2Ld)`.

## Fixed-step minimax obstruction

Proposition 2.3 is formalized in `Concrete/FixedStepMinimax.lean`. The final
endpoint is:

```lean
UniformRandomMALA.Concrete.
  exists_universal_fixedStepMinimaxGap_paper_upper
```

The potential class is literal. `smoothHessianPotentialGapValues d m L h`
contains the Rayleigh gaps of MALA kernels generated by potentials that are
`ContDiff ℝ ⊤`, whose actual second Fréchet derivatives lie between `mI` and
`LI`, and whose MALA drift is obtained from the proved Riesz-gradient bridge.
The definitions

```lean
Concrete.fixedStepWorstPotentialGap
Concrete.fixedStepMinimaxGap
```

use `sInf` for the infimum over that potential class at fixed `h` and `iSup`
over the subtype `{h : ℝ // 0 < h}` for the supremum over all positive step
sizes.

For every lower condition-number cutoff `κ₀ > 1`, the theorem supplies a
constant `C > 0` depending only on `κ₀`; it also supplies a universal rate
`c > 0`, independent of `κ₀`, `d`, `m`, and `L`. If `d ≥ 2`, `0 < m < L`,
and `κ₀ ≤ L/m`, then

```text
sup_{h>0} inf_U Gap(P_{U,h}) ≤
  C max(log((L/m)d)/((L/m)d), exp(-c d)).
```

The checked route has two independent branches for the explicit smooth hard
potential:

- The local branch identifies the first target marginal as `N(0,m⁻¹)` and
  uses `f(x)=x₀` to prove
  `Gap(P_h) ≤ mh + (mh)²/2`.
- The sticky branch computes the origin Hastings ratio, proves a direct
  negative-threshold Gaussian product concentration bound, establishes
  continuity of the proposal-averaged acceptance profile by dominated
  convergence, and extracts a positive-target-mass ball of mass below one
  half. The indicator-cut bound then gives exponential decay in
  `(d-1) min((L-m)h,1)`.

The most reusable supporting modules are:

- `Concrete/SpectralGapUpperBounds.lean`: Rayleigh-test and exact
  indicator-flow upper bounds;
- `Concrete/StickyRegionCut.lean`: continuous acceptance profiles and the
  generic small-ball cut theorem
  `FirstOrderPotential.exists_target_ball_rayleighSpectralGap_le_two_mul`;
- `Concrete/FixedStepHardPotential.lean`: the literal `C^∞` hard potential,
  genuine gradient, diagonal Hessian, and `[m,L]` bounds;
- `Concrete/HardPotentialLocalObstruction.lean`: the local Gaussian marginal
  and coordinate-test branch;
- `Concrete/HardPotentialShiftedConcentration.lean`: direct Chernoff
  concentration at the required negative linear threshold;
- `Concrete/HardPotentialStickyObstruction.lean`: conversion of the origin
  acceptance estimate into the sticky spectral-gap branch;
- `Concrete/FixedStepHardPotentialObstruction.lean`: the combined generic
  obstruction, ending at
  `exists_universal_fixedStepHardPotential_obstruction_allDimensions`;
- `Concrete/FixedStepObstructionOptimization.lean`: scalar exponential
  compression and uniform step-size optimization.

## Gaussian isoperimetry and the lower-bound proof route

The target Bakry--Ledoux enlargement inequality is proved rather than
assumed. The key standalone endpoint is

```lean
UniformRandomMALA.DiscreteTime.target_bakryLedoux
```

The proof route is:

```text
Gaussian normal profile + Ornstein--Uhlenbeck interpolation
  → smooth Gaussian Bobkov inequality
  → sharp finite-dimensional Gaussian enlargement
  → Lipschitz finite-Euler images + weak-limit stability
  → Bakry--Ledoux enlargement for π

finite Gaussian likelihood + Euler/RWM comparison
  → MALA local overlap

overlap + target enlargement
  → separated-set and defective-conductance bounds
  → finite component aggregation on a dyadic step ladder
  → global randomized-MALA spectral-gap lower bound.
```

The paper derives one stationary rejection estimate using continuous-time
Langevin diffusion. The Lean development instead uses a finite,
discrete-time Gaussian-product argument. It does not claim to formalize the
continuous-time SDE derivation.

## Main reader-facing files

| Result | Lean file | Principal declaration |
|---|---|---|
| Hessian calculus bridge | `Concrete/HessianToFirstOrder.lean` | `Concrete.HessianBoundedPotential.toFirstOrderPotential` |
| Rayleigh/Poincaré gap equivalence | `Concrete/RayleighSpectralGap.lean` | `Concrete.l2SpectralGap_eq_rayleighSpectralGap` |
| Paper-form non-lazy theorem | `Concrete/HessianMainTheorem.lean` | `Concrete.exists_universal_nonlazy_paperMasterRHS_lower` |
| Concrete half-lazification | `Concrete/LazyKernel.lean` | `Concrete.rayleighSpectralGap_halfLazyKernel` |
| Square-root-dimension corollary | `Concrete/SqrtDimensionCorollary.lean` | `Concrete.HessianBoundedPotential.sqrtDimensionCorollary_rayleighSpectralGap_lower` |
| Fractional aggregation | `Concrete/FractionalAggregation.lean` | `Concrete.fractionalAggregation_poincareLower` |
| Full-parameter one-step flow | `Concrete/AllParameterMALAFlow.lean` | `Concrete.FirstOrderPotential.allParameterMALAFlowBounds` |
| Fixed-step minimax upper bound | `Concrete/FixedStepMinimax.lean` | `Concrete.exists_universal_fixedStepMinimaxGap_paper_upper` |
| Target Bakry--Ledoux enlargement | `BakryLedoux.lean` | `DiscreteTime.target_bakryLedoux` |
| All completed public results | `AllResults.lean` | aggregate import |

All names in the table are relative to the namespace `UniformRandomMALA`.
The short top-level files are reader-facing import surfaces; most proofs live
in descriptively named modules under `UniformRandomMALA/Concrete/` and
`UniformRandomMALA/DiscreteTime/`.

## Building and auditing

The project is pinned to Lean `v4.33.0` and mathlib `v4.33.0`. Install
[Elan](https://github.com/leanprover/elan), extract the archive, and run from
the directory containing `lakefile.toml`:

```bash
lake exe cache get
lake build
lake env lean UniformRandomMALA/AllResults.lean
lake env lean UniformRandomMALA/DependencyAudit.lean
```

`lake build` is the authoritative package check. The current full build
reports `Build completed successfully (3435 jobs).` `DependencyAudit.lean`
runs `#print axioms` on the principal endpoints. The full scripted audit is:

```bash
./scripts/check.sh
```

or on Windows PowerShell:

```powershell
powershell -ExecutionPolicy Bypass -File scripts/check.ps1
```

For example:

```lean
import UniformRandomMALA.AllResults

#check UniformRandomMALA.Concrete.
  exists_universal_nonlazy_paperMasterRHS_lower
#check UniformRandomMALA.Concrete.
  exists_universal_lazy_paperMasterRHS_lower
#check UniformRandomMALA.Concrete.fractionalAggregation_poincareLower
#check UniformRandomMALA.Concrete.
  exists_universal_fixedStepMinimaxGap_paper_upper
#print axioms UniformRandomMALA.DiscreteTime.target_bakryLedoux
```

Save the snippet as a `.lean` file and compile it with
`lake env lean YourFile.lean`.

## Documentation map

- `PAPER_READER_GUIDE.md`: notation, translation between the manuscript and
  Lean, and suggested reading paths;
- `REUSABLE_RESULTS.md`: theorem-level descriptions of general results and
  their exact hypotheses;
- `THEOREM_MAP.md`: paper formulas mapped to Lean declarations;
- `FORMALIZATION_STATUS.md`: checked, in-progress, and omitted components;
- `PROOF_STRATEGY_LEDGER.md`: dependency ledger for the lower-bound proof;
- `WORKLOG.md`: chronological commands, milestones, and current next task;
- `TRUST_BOUNDARY.md`: foundations and deliberately out-of-scope material;
- `BUILD_STATUS.md`: recorded validation commands and results.

Compatibility modules and declarations ending in `_of_bakryLedoux` expose
useful intermediate implications—for example, converting an enlargement
inequality into a flow bound. They are not additional assumptions of the
paper-form endpoint: the concrete target theorem proves and supplies the
Bakry--Ledoux inequality internally.
