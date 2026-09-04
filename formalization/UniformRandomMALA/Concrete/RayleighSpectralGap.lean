import UniformRandomMALA.Concrete.SpectralGap

/-!
# The paper's `L²` Rayleigh spectral gap

The original concrete development defines `spectralGap` as the supremum of
constants satisfying a Poincaré inequality for every measurable real
function.  The paper instead takes the infimum of the Dirichlet-energy to
variance quotient over nonconstant measurable `L²` functions.

This file defines that Rayleigh gap and proves its exact equivalence with the
`L²` Poincaré formulation.  Zero variance is handled separately in the
reverse implication, while infinite energy is allowed by `ℝ≥0∞` arithmetic.
The admissible family may be empty (for example on a one-point probability
space); then both characterizations give `∞`.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

variable {α : Type*} [MeasurableSpace α] {π : Measure α}

/-- A measurable `L²` function with nonzero variance, i.e. an admissible
test in the paper's Rayleigh quotient. -/
structure L2RayleighTest (π : Measure α) where
  toFun : α → ℝ
  measurable_toFun : Measurable toFun
  memLp_toFun : MemLp toFun 2 π
  evariance_ne_zero : evariance toFun π ≠ 0

instance (π : Measure α) : CoeFun (L2RayleighTest π) (fun _ => α → ℝ) :=
  ⟨L2RayleighTest.toFun⟩

/-- The extended-valued Rayleigh quotient.  An infinite Dirichlet energy
gives quotient `∞`; the denominator is finite and nonzero for every test. -/
def rayleighQuotient (π : Measure α) (K : Kernel α α)
    (f : L2RayleighTest π) : ℝ≥0∞ :=
  Dirichlet.energy π K f / evariance f π

/-- The manuscript's spectral gap: the infimum of the Rayleigh quotient over
measurable, nonconstant `L²` functions. -/
def rayleighSpectralGap (π : Measure α) (K : Kernel α α) : ℝ≥0∞ :=
  ⨅ f : L2RayleighTest π, rayleighQuotient π K f

/-- Poincaré lower bound with exactly the manuscript's `L²` scope. -/
def L2PoincareLower (π : Measure α) (K : Kernel α α) (c : ℝ≥0∞) : Prop :=
  ∀ f : α → ℝ, Measurable f → MemLp f 2 π →
    c * evariance f π ≤ Dirichlet.energy π K f

/-- Supremum-of-Poincaré-constants presentation with `L²` scope. -/
def l2SpectralGap (π : Measure α) (K : Kernel α α) : ℝ≥0∞ :=
  sSup {c : ℝ≥0∞ | L2PoincareLower π K c}

lemma L2RayleighTest.evariance_ne_top [IsFiniteMeasure π]
    (f : L2RayleighTest π) : evariance f π ≠ ∞ :=
  f.memLp_toFun.evariance_ne_top

/-- Exact equivalence between the `L²` Poincaré and Rayleigh-infimum
formulations of the spectral gap. -/
theorem l2PoincareLower_iff_le_rayleighSpectralGap
    [IsFiniteMeasure π] (K : Kernel α α) (c : ℝ≥0∞) :
    L2PoincareLower π K c ↔ c ≤ rayleighSpectralGap π K := by
  constructor
  · intro hc
    rw [rayleighSpectralGap]
    refine le_iInf fun f => ?_
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl f.evariance_ne_zero)
      (Or.inl f.evariance_ne_top)).2
    exact hc f f.measurable_toFun f.memLp_toFun
  · intro hc f hf hL2
    by_cases hvar : evariance f π = 0
    · simp [hvar]
    · let test : L2RayleighTest π :=
        ⟨f, hf, hL2, hvar⟩
      have hquot : c ≤ rayleighQuotient π K test :=
        hc.trans (iInf_le (fun g : L2RayleighTest π =>
          rayleighQuotient π K g) test)
      exact (ENNReal.le_div_iff_mul_le
        (Or.inl hvar)
        (Or.inl hL2.evariance_ne_top)).1 hquot

/-- The supremum of `L²` Poincaré constants is exactly the infimum of the
Rayleigh quotients. -/
theorem l2SpectralGap_eq_rayleighSpectralGap
    [IsFiniteMeasure π] (K : Kernel α α) :
    l2SpectralGap π K = rayleighSpectralGap π K := by
  apply le_antisymm
  · apply sSup_le
    intro c hc
    exact (l2PoincareLower_iff_le_rayleighSpectralGap K c).1 hc
  · apply le_sSup
    exact (l2PoincareLower_iff_le_rayleighSpectralGap K
      (rayleighSpectralGap π K)).2 le_rfl

/-- The original all-measurable Poincaré premise implies its `L²`
counterpart. -/
theorem PoincareLower.toL2 {π : Measure α} {K : Kernel α α} {c : ℝ≥0∞}
    (h : PoincareLower π K c) : L2PoincareLower π K c := by
  intro f hf hL2
  exact h f hf

/-- The original package gap is bounded above by the paper's Rayleigh gap.
This is the direction needed to transfer every existing concrete lower bound
to the manuscript definition, without silently identifying the stronger
all-measurable formulation with its `L²` restriction. -/
theorem spectralGap_le_rayleighSpectralGap
    [IsFiniteMeasure π] (K : Kernel α α) :
    spectralGap π K ≤ rayleighSpectralGap π K := by
  apply sSup_le
  intro c hc
  exact (l2PoincareLower_iff_le_rayleighSpectralGap K c).1 hc.toL2

end

end UniformRandomMALA.Concrete
