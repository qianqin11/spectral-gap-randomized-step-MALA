import UniformRandomMALA.Concrete.StationaryVarianceGeneral

/-! # Actual stationary sample averages converge in mean square -/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ProbabilityTheory

noncomputable section
variable {α : Type*} [MeasurableSpace α]

theorem stationary_finiteMarkovSampleMean_integral
    (π : Measure α) (K : Kernel α α) [IsMarkovKernel K]
    (hπ : Kernel.Invariant K π) {f : α → ℝ} (hf : Integrable f π)
    {n : ℕ} (hn : n ≠ 0) :
    ∫ path, finiteMarkovSampleMean f n path ∂finiteMarkovPathLaw π K n = ∫ x, f x ∂π := by
  have hi (i : Fin n) : Integrable (fun path => f (path i)) (finiteMarkovPathLaw π K n) :=
    memLp_one_iff_integrable.1 ((memLp_one_iff_integrable.2 hf).comp_measurePreserving
      (stationaryPathLaw_measurePreserving_coordinate π K hπ n i))
  simp only [finiteMarkovSampleMean, integral_div]
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp only [stationaryPathLaw_integral_coordinate π K hπ hf.1,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn)

theorem stationary_sampleMean_variance_tendsto_zero
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {f : α → ℝ} (hf : MemLp f 2 π) {g : ℝ} (hg : 0 < g) (hg2 : g ≤ 2)
    (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π K) :
    Tendsto (fun n => variance (finiteMarkovSampleMean f n) (finiteMarkovPathLaw π K n))
      atTop (𝓝 0) := by
  have ht := (stationaryAsymptoticVariance_spec π K hπ hf hg hg2 hgap).2.2
  have hd := ht.div_atTop tendsto_natCast_atTop_atTop
  apply hd.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  change scaledMarkovSampleVariance π K f n / (n : ℝ) = _
  unfold scaledMarkovSampleVariance
  exact mul_div_cancel_left₀ _ (by exact_mod_cast hn.ne')

/-- The law of large numbers in actual mean square, with the empirical
mean built from the recursively constructed finite Markov trajectory. -/
theorem stationary_finiteMarkovMSE_tendsto_zero
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {f : α → ℝ} (hf : MemLp f 2 π) {g : ℝ} (hg : 0 < g) (hg2 : g ≤ 2)
    (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π K) :
    Tendsto (finiteMarkovMSE π π K f) atTop (𝓝 0) := by
  apply (stationary_sampleMean_variance_tendsto_zero π K hπ hf hg hg2 hgap).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  rw [variance_eq_integral (finiteMarkovSampleMean_memLp π K hπ hf n).1.aemeasurable,
    stationary_finiteMarkovSampleMean_integral π K hπ (hf.integrable (by norm_num)) hn.ne']
  rfl

end
end UniformRandomMALA.Concrete
