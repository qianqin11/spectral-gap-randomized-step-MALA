import UniformRandomMALA.Concrete.NonstationaryMSE
import UniformRandomMALA.Concrete.PaperNormalizedMixing
import UniformRandomMALA.Concrete.TargetGapOne

/-!
# Nonstationary sample averages for randomized MALA

Corollary 2.8 (`cor:nonstationary-variance`) uses the actual half-lazy
uniform-step kernel and the finite path law started from `μ`. The average
contains `X₀,...,Xₙ₋₁`. Both the actual-gap bound and the normalized
dimensional bound are derived from the proved gap and covariance estimates.
-/

namespace UniformRandomMALA.Concrete.C1Potential

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
noncomputable section
variable {d : ℕ}

/-- The first inequality of Corollary 2.8 (`cor:nonstationary-variance`). -/
theorem nonstationaryMSE_actualGap_bound
    (V : C1Potential d) (c : ℝ) (hc : 0 < c)
    (μ : Measure (State d)) [IsProbabilityMeasure μ]
    (hμ : μ ≪ (V.toFirstOrderPotential.target : Measure (State d)))
    (hDensity : MemLp
      (fun x => (μ.rnDeriv (V.toFirstOrderPotential.target : Measure (State d)) x).toReal)
      2 (V.toFirstOrderPotential.target : Measure (State d)))
    {f : State d → ℝ} (hf : MemLp f 4 (V.toFirstOrderPotential.target : Measure (State d)))
    {n : ℕ} (hn : 0 < n) :
    let W := V.toFirstOrderPotential
    let π := (W.target : Measure (State d))
    let H := V.normalizedTunedStep c
    let hH := V.normalizedTunedStep_pos c hc
    let gap := (rayleighSpectralGap π (W.uniformMALA H hH)).toReal
    finiteMarkovMSE μ π (W.lazyUniformMALA H hH) f n ≤
      (4 / gap - 1) / n * variance f π +
        512 * centeredDensityL2Norm μ π * lpNorm (KernelLp.center π f) 4 π ^ 2 /
          ((n : ℝ) ^ 2 * gap ^ 2) := by
  let W := V.toFirstOrderPotential
  let π := (W.target : Measure (State d))
  let H := V.normalizedTunedStep c
  let hH := V.normalizedTunedStep_pos c hc
  let K := W.uniformMALA H hH
  let P := W.lazyUniformMALA H hH
  let : IsMarkovKernel K := W.uniformMALA_isMarkovKernel H hH
  have hrev : Kernel.IsReversible K π := W.uniformMALA_isReversible H hH
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
  have h := finiteMarkovMSE_halfLazy_le μ π hμ hDensity K hrev
    (div_pos hG (by norm_num)) (by linarith : G / 2 ≤ 1) hPg hf hn
  change finiteMarkovMSE μ π P f n ≤ _ at h ⊢
  convert h using 1
  ring

/-- The normalized right side displayed in Corollary 2.8 (`cor:nonstationary-variance`). The constant
`normalizedCorollaryConstant` is universal and proved strictly positive. -/
def normalizedMSERHS (V : C1Potential d) (c : ℝ)
    (μ : Measure (State d)) (f : State d → ℝ) (n : ℕ) : ℝ :=
  let π := (V.toFirstOrderPotential.target : Measure (State d))
  4 * max c (1 / c) * (V.L / V.m) *
      Real.sqrt ((d : ℝ) * V.normalizedMomentThreshold) /
      (normalizedCorollaryConstant * n) * variance f π +
    512 * max (c ^ 2) (1 / c ^ 2) * (V.L / V.m) ^ 2 *
      (d : ℝ) * V.normalizedMomentThreshold /
      (normalizedCorollaryConstant ^ 2 * (n : ℝ) ^ 2) *
      centeredDensityL2Norm μ π * lpNorm (KernelLp.center π f) 4 π ^ 2

/-- Both displayed inequalities of Corollary 2.8
(`cor:nonstationary-variance`), for the actual finite sample mean. -/
theorem nonstationaryMSE_corollary
    (V : C1Potential d) (c : ℝ) (hc : 0 < c)
    (μ : Measure (State d)) [IsProbabilityMeasure μ]
    (hμ : μ ≪ (V.toFirstOrderPotential.target : Measure (State d)))
    (hDensity : MemLp
      (fun x => (μ.rnDeriv (V.toFirstOrderPotential.target : Measure (State d)) x).toReal)
      2 (V.toFirstOrderPotential.target : Measure (State d)))
    {f : State d → ℝ} (hf : MemLp f 4 (V.toFirstOrderPotential.target : Measure (State d)))
    {n : ℕ} (hn : 0 < n) :
    let W := V.toFirstOrderPotential
    let π := (W.target : Measure (State d))
    let H := V.normalizedTunedStep c
    let hH := V.normalizedTunedStep_pos c hc
    let gap := (rayleighSpectralGap π (W.uniformMALA H hH)).toReal
    let bound := (4 / gap - 1) / n * variance f π +
      512 * centeredDensityL2Norm μ π * lpNorm (KernelLp.center π f) 4 π ^ 2 /
        ((n : ℝ) ^ 2 * gap ^ 2)
    finiteMarkovMSE μ π (W.lazyUniformMALA H hH) f n ≤ bound ∧
      bound ≤ V.normalizedMSERHS c μ f n := by
  refine ⟨V.nonstationaryMSE_actualGap_bound c hc μ hμ hDensity hf hn, ?_⟩
  let W := V.toFirstOrderPotential
  let π := (W.target : Measure (State d))
  let K := W.uniformMALA (V.normalizedTunedStep c) (V.normalizedTunedStep_pos c hc)
  let : IsMarkovKernel K := W.uniformMALA_isMarkovKernel _ _
  have hrev : Kernel.IsReversible K π := W.uniformMALA_isReversible _ _
  let G := (rayleighSpectralGap π K).toReal
  let R := max c (1 / c) * V.normalizedMixingScale / normalizedCorollaryConstant
  have hbound : V.normalizedTunedGapRHS c ≤ G :=
    (ENNReal.ofReal_le_iff_le_toReal (W.rayleighSpectralGap_ne_top K hrev)).mp
      (V.normalizedTunedCorollary_rayleighSpectralGap_lower c hc)
  have hG : 0 < G := (V.normalizedTunedGapRHS_pos c hc).trans_le hbound
  have hR : 1 / G ≤ R := by
    calc
      _ ≤ 1 / V.normalizedTunedGapRHS c :=
        div_le_div_of_nonneg_left zero_le_one (V.normalizedTunedGapRHS_pos c hc) hbound
      _ = R := by
        have h := V.two_div_normalizedTunedGapRHS c
        unfold normalizedMixingConstant normalizedMixingUniversalConstant at h
        dsimp [R]
        linear_combination h / 2
  have hR2 : 1 / G ^ 2 ≤ R ^ 2 := by
    have h := pow_le_pow_left₀ (one_div_nonneg.mpr hG.le) hR 2
    simpa only [div_pow, one_pow] using h
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hF : 0 ≤ centeredDensityL2Norm μ π * lpNorm (KernelLp.center π f) 4 π ^ 2 :=
    mul_nonneg (centeredDensityL2Norm_nonneg μ π) (sq_nonneg _)
  have hmax : (max c (1 / c)) ^ 2 = max (c ^ 2) (1 / c ^ 2) := by
    rcases le_total c (1 / c) with h | h
    · rw [max_eq_right h, max_eq_right (by
        simpa only [div_pow, one_pow] using pow_le_pow_left₀ hc.le h 2), div_pow, one_pow]
    · rw [max_eq_left h, max_eq_left (by
        simpa only [div_pow, one_pow] using pow_le_pow_left₀ (by positivity : 0 ≤ 1 / c) h 2)]
  have hscale : V.normalizedMixingScale ^ 2 =
      (V.L / V.m) ^ 2 * ((d : ℝ) * V.normalizedMomentThreshold) := by
    rw [normalizedMixingScale, mul_pow, Real.sq_sqrt]
    exact mul_nonneg (Nat.cast_nonneg _) V.normalizedMomentThreshold_pos.le
  change (4 / G - 1) / n * variance f π +
      512 * centeredDensityL2Norm μ π * lpNorm (KernelLp.center π f) 4 π ^ 2 /
        ((n : ℝ) ^ 2 * G ^ 2) ≤ _
  calc
    _ ≤ (4 * R) / n * variance f π +
        (512 / (n : ℝ) ^ 2) * R ^ 2 *
          (centeredDensityL2Norm μ π * lpNorm (KernelLp.center π f) 4 π ^ 2) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_right _ (variance_nonneg _ _)
        apply div_le_div_of_nonneg_right _ hn0
        calc
          _ ≤ 4 * (1 / G) := by ring_nf; linarith
          _ ≤ _ := mul_le_mul_of_nonneg_left hR (by norm_num)
      · calc
          _ = (512 / (n : ℝ) ^ 2) * (1 / G ^ 2) *
              (centeredDensityL2Norm μ π * lpNorm (KernelLp.center π f) 4 π ^ 2) := by
            simp only [div_eq_mul_inv, mul_inv_rev]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hR2 (by positivity)) hF
    _ = _ := by
      dsimp [R]
      rw [div_pow, mul_pow, hmax, hscale]
      unfold normalizedMSERHS normalizedMixingScale
      simp only [div_eq_mul_inv, mul_inv_rev, pow_two]
      ring

end
end UniformRandomMALA.Concrete.C1Potential
