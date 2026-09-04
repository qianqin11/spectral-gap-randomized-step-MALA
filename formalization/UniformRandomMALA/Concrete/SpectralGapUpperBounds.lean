import UniformRandomMALA.Concrete.RayleighSpectralGap
import UniformRandomMALA.Concrete.Conductance

/-!
# Reusable upper bounds for the Rayleigh spectral gap

The lower-bound development mainly uses Poincaré inequalities.  Fixed-step
obstructions require the dual variational API: every admissible `L²` test
function, and in particular every nontrivial measurable cut indicator, gives
an upper bound on the manuscript's spectral gap.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

variable {α : Type*} [MeasurableSpace α] {π : Measure α}

/-- A single admissible Rayleigh test bounds the spectral gap from above. -/
theorem rayleighSpectralGap_le_quotient
    (K : Kernel α α) (f : L2RayleighTest π) :
    rayleighSpectralGap π K ≤ rayleighQuotient π K f := by
  exact iInf_le (fun g : L2RayleighTest π => rayleighQuotient π K g) f

/-- Unbundled single-test upper bound. -/
theorem rayleighSpectralGap_le_energy_div_evariance
    (K : Kernel α α) (f : α → ℝ)
    (hf : Measurable f) (hL2 : MemLp f 2 π)
    (hvar : evariance f π ≠ 0) :
    rayleighSpectralGap π K ≤
      Dirichlet.energy π K f / evariance f π := by
  let test : L2RayleighTest π := ⟨f, hf, hL2, hvar⟩
  exact rayleighSpectralGap_le_quotient K test

/-- Equivalent multiplication form, convenient when division in `ℝ≥0∞`
would obscure a finite denominator. -/
theorem rayleighSpectralGap_mul_evariance_le_energy
    [IsFiniteMeasure π]
    (K : Kernel α α) (f : α → ℝ)
    (hf : Measurable f) (hL2 : MemLp f 2 π) :
    rayleighSpectralGap π K * evariance f π ≤
      Dirichlet.energy π K f := by
  exact (l2PoincareLower_iff_le_rayleighSpectralGap K
    (rayleighSpectralGap π K)).2 le_rfl f hf hL2

/-- A measurable cut indicator belongs to every finite `Lᵖ` space on a
finite measure space. -/
lemma memLp_indicatorReal [IsFiniteMeasure π]
    {A : Set α} (hA : MeasurableSet A) (p : ℝ≥0∞) :
    MemLp (indicatorReal A : α → ℝ) p π := by
  apply MemLp.of_bound (measurable_indicatorReal hA).aestronglyMeasurable 1
  filter_upwards with x
  classical
  by_cases hx : x ∈ A <;> simp [indicatorReal, hx]

lemma integral_indicatorReal [IsFiniteMeasure π]
    {A : Set α} (hA : MeasurableSet A) :
    ∫ x, indicatorReal A x ∂π = π.real A := by
  have hfun : (indicatorReal A : α → ℝ) = A.indicator (fun _ => (1 : ℝ)) := by
    funext x
    classical
    by_cases hx : x ∈ A <;> simp [indicatorReal, Set.indicator, hx]
  rw [hfun]
  simpa [smul_eq_mul] using
    (integral_indicator_const (μ := π) (1 : ℝ) hA)

/-- Exact variance of a measurable cut indicator under a probability
measure. -/
theorem variance_indicatorReal [IsProbabilityMeasure π]
    {A : Set α} (hA : MeasurableSet A) :
    variance (indicatorReal A) π = π.real A * (1 - π.real A) := by
  let q : ℝ := π.real A
  have hmeas := measurable_indicatorReal hA
  have hL2 : MemLp (indicatorReal A : α → ℝ) 2 π :=
    memLp_indicatorReal hA 2
  have hint : Integrable
      (fun x => (indicatorReal A x - q) ^ 2) π := by
    exact (hL2.sub (memLp_const q)).integrable_sq
  rw [variance_eq_integral hmeas.aemeasurable, integral_indicatorReal hA]
  change (∫ x, (indicatorReal A x - q) ^ 2 ∂π) = q * (1 - q)
  rw [← integral_add_compl hA hint]
  have h_on : (∫ x in A, (indicatorReal A x - q) ^ 2 ∂π) =
      π.real A * (1 - q) ^ 2 := by
    calc
      (∫ x in A, (indicatorReal A x - q) ^ 2 ∂π) =
          ∫ _x in A, (1 - q) ^ 2 ∂π := by
            apply setIntegral_congr_fun hA
            intro x hx
            simp [indicatorReal, hx]
      _ = π.real A * (1 - q) ^ 2 := by simp
  have h_off : (∫ x in Aᶜ, (indicatorReal A x - q) ^ 2 ∂π) =
      π.real Aᶜ * q ^ 2 := by
    calc
      (∫ x in Aᶜ, (indicatorReal A x - q) ^ 2 ∂π) =
          ∫ _x in Aᶜ, q ^ 2 ∂π := by
            apply setIntegral_congr_fun hA.compl
            intro x hx
            have hxA : x ∉ A := by simpa using hx
            simp [indicatorReal, hxA]
      _ = π.real Aᶜ * q ^ 2 := by simp
  rw [h_on, h_off, measureReal_compl hA, probReal_univ]
  dsimp [q]
  ring

theorem evariance_indicatorReal [IsProbabilityMeasure π]
    {A : Set α} (hA : MeasurableSet A) :
    evariance (indicatorReal A) π =
      ENNReal.ofReal (π.real A * (1 - π.real A)) := by
  rw [← (memLp_indicatorReal hA 2).ofReal_variance_eq,
    variance_indicatorReal hA]

/-- Indicator-cut upper bound before simplifying the variance.  Together
with `energy_indicatorReal`, this is the exact cut API needed for sticky-set
arguments, and it remains valid for extended-valued flow. -/
theorem rayleighSpectralGap_le_boundaryFlow_div_evariance_indicator
    [IsFiniteMeasure π]
    (K : Kernel α α) (hrev : Kernel.IsReversible K π)
    {A : Set α} (hA : MeasurableSet A)
    (hvar : evariance (indicatorReal A) π ≠ 0) :
    rayleighSpectralGap π K ≤
      boundaryFlow π K A / evariance (indicatorReal A) π := by
  rw [← energy_indicatorReal π K hrev hA]
  exact rayleighSpectralGap_le_energy_div_evariance K
    (indicatorReal A) (measurable_indicatorReal hA)
    (memLp_indicatorReal hA 2) hvar

/-- Standard conductance-style cut upper bound with the exact Bernoulli
variance denominator. -/
theorem rayleighSpectralGap_le_boundaryFlow_div_cutVariance
    [IsProbabilityMeasure π]
    (K : Kernel α α) (hrev : Kernel.IsReversible K π)
    {A : Set α} (hA : MeasurableSet A)
    (hvar : π.real A * (1 - π.real A) ≠ 0) :
    rayleighSpectralGap π K ≤
      boundaryFlow π K A /
        ENNReal.ofReal (π.real A * (1 - π.real A)) := by
  rw [← evariance_indicatorReal hA]
  apply rayleighSpectralGap_le_boundaryFlow_div_evariance_indicator K hrev hA
  rw [evariance_indicatorReal hA]
  apply ENNReal.ofReal_ne_zero_iff.mpr
  have hq0 : 0 ≤ π.real A := measureReal_nonneg
  have hq1 : π.real A ≤ 1 := by
    calc
      π.real A ≤ π.real Set.univ := measureReal_mono (μ := π) (Set.subset_univ A)
      _ = 1 := probReal_univ
  exact lt_of_le_of_ne (mul_nonneg hq0 (sub_nonneg.mpr hq1)) (Ne.symm hvar)

/-- Multiplication form of the exact indicator energy/flow identity. -/
theorem rayleighSpectralGap_mul_indicatorVariance_le_boundaryFlow
    [IsFiniteMeasure π]
    (K : Kernel α α) (hrev : Kernel.IsReversible K π)
    {A : Set α} (hA : MeasurableSet A) :
    rayleighSpectralGap π K * evariance (indicatorReal A) π ≤
      boundaryFlow π K A := by
  rw [← energy_indicatorReal π K hrev hA]
  exact rayleighSpectralGap_mul_evariance_le_energy K
    (indicatorReal A) (measurable_indicatorReal hA)
    (memLp_indicatorReal hA 2)

end

end UniformRandomMALA.Concrete
