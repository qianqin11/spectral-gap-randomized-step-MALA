import UniformRandomMALA.Concrete.StationaryVarianceGeneral
import UniformRandomMALA.Concrete.PaperNormalizedMixing
import UniformRandomMALA.Concrete.TargetGapOne

/-!
# The asymptotic-variance bounds for randomized MALA

The variance clauses of Corollary 2.6 (`cor:asymptotic-variance`) refer to
the limit of the actual stationary path variances, for every L² observable.
This module proves existence of that limit and both gap and dimensional
bounds for the nonlazy and half-lazy kernels. `PaperCentralLimit` proves
the Gaussian CLTs from arbitrary initial probability laws with these
same stationary asymptotic variances.
-/

namespace UniformRandomMALA.Concrete.C1Potential

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory Topology

noncomputable section
variable {d : ℕ}

theorem stationaryAsymptoticVariance_nonlazy_bounds
    (V : C1Potential d) (c : ℝ) (hc : 0 < c)
    {f : State d → ℝ} (hf : MemLp f 2 (V.toFirstOrderPotential.target : Measure (State d))) :
    let W := V.toFirstOrderPotential
    let π := (W.target : Measure (State d))
    let K := W.uniformMALA (V.normalizedTunedStep c) (V.normalizedTunedStep_pos c hc)
    let gap := (rayleighSpectralGap π K).toReal
    let σ2 := stationaryAsymptoticVariance π K f
    0 ≤ σ2 ∧ σ2 ≤ (2 / gap - 1) * variance f π ∧
      σ2 ≤ normalizedMixingConstant c * V.normalizedMixingScale * variance f π ∧
      Tendsto (scaledMarkovSampleVariance π K f) atTop (𝓝 σ2) := by
  let W := V.toFirstOrderPotential
  let π := (W.target : Measure (State d))
  let K := W.uniformMALA (V.normalizedTunedStep c) (V.normalizedTunedStep_pos c hc)
  let : IsMarkovKernel K := W.uniformMALA_isMarkovKernel _ _
  have hrev : Kernel.IsReversible K π := W.uniformMALA_isReversible _ _
  let G := (rayleighSpectralGap π K).toReal
  have hbound : V.normalizedTunedGapRHS c ≤ G :=
    (ENNReal.ofReal_le_iff_le_toReal (W.rayleighSpectralGap_ne_top K hrev)).mp
      (V.normalizedTunedCorollary_rayleighSpectralGap_lower c hc)
  have hG : 0 < G := (V.normalizedTunedGapRHS_pos c hc).trans_le hbound
  have hG2 : G ≤ 2 := by
    have h := ENNReal.toReal_mono (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      (W.rayleighSpectralGap_le_two K hrev)
    simpa only [ENNReal.toReal_ofNat] using h
  have hspec := stationaryAsymptoticVariance_spec π K hrev.invariant hf hG hG2
    ENNReal.ofReal_toReal_le
  refine ⟨hspec.1, hspec.2.1, ?_, hspec.2.2⟩
  have hrate : 2 / G ≤ normalizedMixingConstant c * V.normalizedMixingScale := by
    rw [← V.two_div_normalizedTunedGapRHS c]
    exact div_le_div_of_nonneg_left (by norm_num) (V.normalizedTunedGapRHS_pos c hc) hbound
  calc
    _ ≤ (2 / G - 1) * variance f π := hspec.2.1
    _ ≤ (2 / G) * variance f π :=
      mul_le_mul_of_nonneg_right (by linarith) (variance_nonneg _ _)
    _ ≤ _ := mul_le_mul_of_nonneg_right hrate (variance_nonneg _ _)

theorem stationaryAsymptoticVariance_lazy_bounds
    (V : C1Potential d) (c : ℝ) (hc : 0 < c)
    {f : State d → ℝ} (hf : MemLp f 2 (V.toFirstOrderPotential.target : Measure (State d))) :
    let W := V.toFirstOrderPotential
    let π := (W.target : Measure (State d))
    let H := V.normalizedTunedStep c
    let hH := V.normalizedTunedStep_pos c hc
    let K := W.uniformMALA H hH
    let P := W.lazyUniformMALA H hH
    let gap := (rayleighSpectralGap π K).toReal
    let σ2 := stationaryAsymptoticVariance π P f
    0 ≤ σ2 ∧ σ2 ≤ (4 / gap - 1) * variance f π ∧
      σ2 ≤ 2 * normalizedMixingConstant c * V.normalizedMixingScale * variance f π ∧
      Tendsto (scaledMarkovSampleVariance π P f) atTop (𝓝 σ2) := by
  let W := V.toFirstOrderPotential
  let π := (W.target : Measure (State d))
  let H := V.normalizedTunedStep c
  let hH := V.normalizedTunedStep_pos c hc
  let K := W.uniformMALA H hH
  let P := W.lazyUniformMALA H hH
  let : IsMarkovKernel K := W.uniformMALA_isMarkovKernel _ _
  let : IsMarkovKernel P := W.lazyUniformMALA_isMarkovKernel _ _
  have hrev : Kernel.IsReversible K π := W.uniformMALA_isReversible _ _
  have hPrev : Kernel.IsReversible P π := W.lazyUniformMALA_isReversible _ _
  let G := (rayleighSpectralGap π K).toReal
  have hbound : V.normalizedTunedGapRHS c ≤ G :=
    (ENNReal.ofReal_le_iff_le_toReal (W.rayleighSpectralGap_ne_top K hrev)).mp
      (V.normalizedTunedCorollary_rayleighSpectralGap_lower c hc)
  have hG : 0 < G := (V.normalizedTunedGapRHS_pos c hc).trans_le hbound
  have hG2 : G ≤ 2 := by
    have h := ENNReal.toReal_mono (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      (W.rayleighSpectralGap_le_two K hrev)
    simpa only [ENNReal.toReal_ofNat] using h
  have hPg : ENNReal.ofReal (G / 2) ≤ rayleighSpectralGap π P := by
    rw [W.rayleighSpectralGap_lazyUniformMALA H hH,
      ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    simpa only [ENNReal.ofReal_ofNat, div_eq_mul_inv, mul_comm] using
      (mul_le_mul_of_nonneg_left (ENNReal.ofReal_toReal_le
        (a := rayleighSpectralGap π K)) (by positivity : 0 ≤ (2 : ℝ≥0∞)⁻¹))
  have hspec := stationaryAsymptoticVariance_spec π P hPrev.invariant hf
    (div_pos hG (by norm_num)) (by linarith : G / 2 ≤ 2) hPg
  have hformula : 2 / (G / 2) = 4 / G := by ring
  rw [hformula] at hspec
  refine ⟨hspec.1, hspec.2.1, ?_, hspec.2.2⟩
  have hrate : 4 / G ≤ 2 * normalizedMixingConstant c * V.normalizedMixingScale := by
    have htwo : 2 / G ≤ normalizedMixingConstant c * V.normalizedMixingScale := by
      rw [← V.two_div_normalizedTunedGapRHS c]
      exact div_le_div_of_nonneg_left (by norm_num) (V.normalizedTunedGapRHS_pos c hc) hbound
    calc
      4 / G = 2 * (2 / G) := by ring
      _ ≤ 2 * (normalizedMixingConstant c * V.normalizedMixingScale) :=
        mul_le_mul_of_nonneg_left htwo (by norm_num)
      _ = _ := by ring
  calc
    _ ≤ (4 / G - 1) * variance f π := hspec.2.1
    _ ≤ (4 / G) * variance f π :=
      mul_le_mul_of_nonneg_right (by linarith) (variance_nonneg _ _)
    _ ≤ _ := mul_le_mul_of_nonneg_right hrate (variance_nonneg _ _)

end
end UniformRandomMALA.Concrete.C1Potential
