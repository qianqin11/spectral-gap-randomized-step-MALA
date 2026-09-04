import UniformRandomMALA.Concrete.Quantile

/-!
# Measurable medians

This file constructs a median of an arbitrary measurable real-valued
function on a probability space.  The construction is the lower `1/2`
quantile of the pushforward law.

Both strict-tail estimates are retained explicitly.  This is the form needed
by the positive/negative median split: the supports of `(f-b)⁺` and
`(f-b)⁻` have mass at most `1/2`, even when the pushforward has an atom at
the median.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped ENNReal Topology

noncomputable section

namespace Concrete

variable {α : Type*} [MeasurableSpace α]

/-- `b` is a median of `f` if both strict tails have mass at most one half. -/
structure IsMedian (π : Measure α) (f : α → ℝ) (b : ℝ) : Prop where
  measure_lt : π {x | f x < b} ≤ (2 : ℝ≥0∞)⁻¹
  measure_gt : π {x | b < f x} ≤ (2 : ℝ≥0∞)⁻¹

private lemma ofReal_one_half :
    ENNReal.ofReal (1 / 2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

/-- The lower half-quantile leaves mass at most one half strictly below it. -/
theorem measure_Iio_lowerQuantile_half_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    μ (Iio (lowerQuantile μ (1 / 2))) ≤ (2 : ℝ≥0∞)⁻¹ := by
  let q : ℝ := lowerQuantile μ (1 / 2)
  have hbelow : ∀ y : ℝ, y < q → cdf μ y ≤ (1 / 2 : ℝ) := by
    intro y hy
    by_contra h
    push_neg at h
    have hqy : q ≤ y :=
      lowerQuantile_le_of_le_cdf μ (by norm_num) h.le
    exact (not_le_of_gt hy) hqy
  have hevent : ∀ᶠ y in 𝓝[<] q, cdf μ y ≤ (1 / 2 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hbelow y hy
  have hleft : leftLim (cdf μ) q ≤ (1 / 2 : ℝ) :=
    le_of_tendsto ((monotone_cdf μ).tendsto_leftLim q) hevent
  calc
    μ (Iio q) = (cdf μ).measure (Iio q) := by rw [measure_cdf μ]
    _ = ENNReal.ofReal (leftLim (cdf μ) q) := by
      simpa using (cdf μ).measure_Iio (tendsto_cdf_atBot μ) q
    _ ≤ ENNReal.ofReal (1 / 2 : ℝ) := ENNReal.ofReal_le_ofReal hleft
    _ = (2 : ℝ≥0∞)⁻¹ := ofReal_one_half

/-- The lower half-quantile leaves mass at most one half strictly above it. -/
theorem measure_Ioi_lowerQuantile_half_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    μ (Ioi (lowerQuantile μ (1 / 2))) ≤ (2 : ℝ≥0∞)⁻¹ := by
  let q : ℝ := lowerQuantile μ (1 / 2)
  have hcdf : (1 / 2 : ℝ) ≤ cdf μ q :=
    (lowerQuantile_le_iff μ (by norm_num) (by norm_num)).1 le_rfl
  have htail : 1 - cdf μ q ≤ (1 / 2 : ℝ) := by linarith
  calc
    μ (Ioi q) = (cdf μ).measure (Ioi q) := by rw [measure_cdf μ]
    _ = ENNReal.ofReal (1 - cdf μ q) :=
      (cdf μ).measure_Ioi (tendsto_cdf_atTop μ) q
    _ ≤ ENNReal.ofReal (1 / 2 : ℝ) := ENNReal.ofReal_le_ofReal htail
    _ = (2 : ℝ≥0∞)⁻¹ := ofReal_one_half

/-- Every measurable real function on a probability space has a median. -/
theorem exists_isMedian
    (π : Measure α) [IsProbabilityMeasure π]
    (f : α → ℝ) (hf : Measurable f) :
    ∃ b : ℝ, IsMedian π f b := by
  let μ : Measure ℝ := π.map f
  letI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hf.aemeasurable
  let b : ℝ := lowerQuantile μ (1 / 2)
  refine ⟨b, ?_⟩
  constructor
  · change π (f ⁻¹' Iio b) ≤ (2 : ℝ≥0∞)⁻¹
    rw [← Measure.map_apply hf measurableSet_Iio]
    exact measure_Iio_lowerQuantile_half_le μ
  · change π (f ⁻¹' Ioi b) ≤ (2 : ℝ≥0∞)⁻¹
    rw [← Measure.map_apply hf measurableSet_Ioi]
    exact measure_Ioi_lowerQuantile_half_le μ

end Concrete

end

end UniformRandomMALA
