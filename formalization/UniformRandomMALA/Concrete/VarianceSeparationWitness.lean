import UniformRandomMALA.Concrete.VarianceSeparationRayleigh

/-!
# Actual large-variance witnesses from spectral-gap upper bounds

The zero-gap branch uses genuine extended variance limits and low-energy
Rayleigh tests. The positive-gap branch uses the solved Poisson equation.
Neither branch assumes a worst-case variance identity.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory KernelLp
open scoped ENNReal ProbabilityTheory RealInnerProductSpace

noncomputable section
variable {α : Type*} [MeasurableSpace α]

theorem exists_unit_large_variance_of_gap_zero
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hrev : Kernel.IsReversible K π)
    (hgap : rayleighSpectralGap π K = 0) (N : ℕ) :
    ∃ f : α → ℝ, MemLp f 2 π ∧ variance f π = 1 ∧
      ENNReal.ofReal (2 * (N : ℝ) - 1) ≤ asymptoticVarianceExtended π K f := by
  have hdenom : 0 < 4 * (N : ℝ) + 1 := by positivity
  have hβ : 0 < 1 / (4 * (N : ℝ) + 1) := one_div_pos.mpr hdenom
  obtain ⟨f, hf, he⟩ := exists_centered_unit_energy_lt π K hrev.invariant hβ (by
    rw [hgap]
    exact ENNReal.ofReal_pos.mpr hβ)
  refine ⟨(f : Lp ℝ 2 π), Lp.memLp _, ?_, ?_⟩
  · rw [centeredL2_variance_eq_norm_sq, hf]
    norm_num
  · apply asymptoticVarianceExtended_centered_ge_nat_of_energy π K hrev f hf N
    have h := (lt_div_iff₀ hdenom).mp he
    linarith

/-- A finite ceiling for a spectral gap at most one forces an actual
unit-variance observable with reciprocal-order asymptotic variance. The
gap may be zero and the resulting variance may be infinite. -/
theorem exists_unit_variance_ge_of_gap_le
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hrev : Kernel.IsReversible K π)
    {B : ℝ} (hB : 0 < B)
    (hbound : rayleighSpectralGap π K ≤ ENNReal.ofReal B)
    (hone : rayleighSpectralGap π K ≤ 1) :
    ∃ f : α → ℝ, MemLp f 2 π ∧ variance f π = 1 ∧
      ENNReal.ofReal (1 / (2 * B)) ≤ asymptoticVarianceExtended π K f := by
  have htop : rayleighSpectralGap π K ≠ ∞ := ne_of_lt (hone.trans_lt (by norm_num))
  by_cases hg0 : rayleighSpectralGap π K = 0
  · obtain ⟨N, hN⟩ := exists_nat_gt (1 / (2 * B) + 1)
    obtain ⟨f, hf, hv, hσ⟩ := exists_unit_large_variance_of_gap_zero π K hrev hg0 N
    refine ⟨f, hf, hv, (ENNReal.ofReal_le_ofReal ?_).trans hσ⟩
    nlinarith [show (0 : ℝ) ≤ N by positivity]
  · let g := (rayleighSpectralGap π K).toReal
    have hg : 0 < g := ENNReal.toReal_pos hg0 htop
    have hg1 : g ≤ 1 := ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using hone)
    have hgB : g ≤ B := ENNReal.toReal_le_of_le_ofReal hB.le hbound
    let β := 4 * g / 3
    have hβ : 0 < β := by dsimp [β]; positivity
    have hlt : rayleighSpectralGap π K < ENNReal.ofReal β := by
      rw [← ENNReal.ofReal_toReal htop]
      exact (ENNReal.ofReal_lt_ofReal_iff hβ).2 (by dsimp [β]; linarith)
    obtain ⟨f, hf, he⟩ := exists_centered_unit_energy_lt π K hrev.invariant hβ hlt
    obtain ⟨hE, hσ⟩ := stationaryAsymptoticVariance_centered_lower π K hrev f hf hg
      (hg1.trans (by norm_num)) ENNReal.ofReal_toReal_le
    have hginv : 1 ≤ 1 / g := (le_div_iff₀ hg).2 (by simpa using hg1)
    have hbase : 1 / (2 * g) ≤ 2 / β - 1 := by
      have hid : 2 / β - 1 = 1 / (2 * g) + (1 / g - 1) := by
        dsimp [β]
        field_simp
        ring
      rw [hid]
      linarith
    have hrecip : 2 / β ≤ 2 / ⟪f, f - centeredOperator K π hrev.invariant f⟫ :=
      div_le_div_of_nonneg_left (by norm_num) hE he.le
    have hlow : 1 / (2 * B) ≤ stationaryAsymptoticVariance π K (f : Lp ℝ 2 π) := by
      have hBg : 1 / (2 * B) ≤ 1 / (2 * g) :=
        div_le_div_of_nonneg_left (by norm_num) (mul_pos (by norm_num) hg)
          (mul_le_mul_of_nonneg_left hgB (by norm_num))
      linarith
    refine ⟨(f : Lp ℝ 2 π), Lp.memLp _, ?_, ?_⟩
    · rw [centeredL2_variance_eq_norm_sq, hf]
      norm_num
    · rw [asymptoticVarianceExtended_eq_of_gap π K hrev.invariant (Lp.memLp _) hg
        (hg1.trans (by norm_num)) ENNReal.ofReal_toReal_le]
      exact ENNReal.ofReal_le_ofReal hlow

end
end UniformRandomMALA.Concrete
