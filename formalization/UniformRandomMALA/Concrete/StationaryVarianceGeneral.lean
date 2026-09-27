import UniformRandomMALA.Concrete.StationaryVarianceLimit

/-! # Stationary asymptotic variance for every `L²` observable -/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory Filter KernelLp
open scoped ENNReal ProbabilityTheory RealInnerProductSpace Topology

noncomputable section
variable {α : Type*} [MeasurableSpace α]

theorem finiteMarkovSampleMean_memLp (π : Measure α) (K : Kernel α α)
    [IsMarkovKernel K] (hπ : Kernel.Invariant K π) {f : α → ℝ}
    (hf : MemLp f 2 π) (n : ℕ) :
    MemLp (finiteMarkovSampleMean f n) 2 (finiteMarkovPathLaw π K n) := by
  have hs : MemLp (fun path => ∑ i : Fin n, f (path i)) 2 (finiteMarkovPathLaw π K n) :=
    memLp_finsetSum Finset.univ fun i _ =>
      stationaryPathLaw_memLp_coordinate π K hπ hf n i
  change MemLp (fun path : Fin n → α => (∑ i : Fin n, f (path i)) / (n : ℝ)) 2 _
  simpa only [div_eq_mul_inv] using hs.mul_const (n : ℝ)⁻¹

theorem finiteMarkovSampleMean_congr_ae (π : Measure α) (K : Kernel α α)
    [IsMarkovKernel K] (hπ : Kernel.Invariant K π) {f g : α → ℝ}
    (hfg : f =ᵐ[π] g) (n : ℕ) :
    finiteMarkovSampleMean f n =ᵐ[finiteMarkovPathLaw π K n] finiteMarkovSampleMean g n := by
  have hi (i : Fin n) : (fun path => f (path i)) =ᵐ[finiteMarkovPathLaw π K n]
      (fun path => g (path i)) :=
    (stationaryPathLaw_measurePreserving_coordinate π K hπ n i).quasiMeasurePreserving.ae_eq_comp hfg
  filter_upwards [ae_all_iff.2 hi] with path hpath
  simp only [finiteMarkovSampleMean, hpath]

theorem scaledMarkovSampleVariance_congr (π : Measure α) (K : Kernel α α)
    [IsMarkovKernel K] (hπ : Kernel.Invariant K π) {f g : α → ℝ}
    (hfg : f =ᵐ[π] g) (n : ℕ) :
    scaledMarkovSampleVariance π K f n = scaledMarkovSampleVariance π K g n := by
  unfold scaledMarkovSampleVariance
  rw [variance_congr (finiteMarkovSampleMean_congr_ae π K hπ hfg n)]

omit [MeasurableSpace α] in
theorem finiteMarkovSampleMean_sub_const (f : α → ℝ) (c : ℝ) {n : ℕ} (hn : n ≠ 0) :
    finiteMarkovSampleMean (fun x => f x - c) n =
      fun path => finiteMarkovSampleMean f n path - c := by
  funext path
  simp only [finiteMarkovSampleMean, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sub_div]
  rw [mul_div_cancel_left₀ c (Nat.cast_ne_zero.mpr hn)]

theorem scaledMarkovSampleVariance_sub_const (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {f : α → ℝ} (hf : MemLp f 2 π) (c : ℝ) (n : ℕ) :
    scaledMarkovSampleVariance π K (fun x => f x - c) n =
      scaledMarkovSampleVariance π K f n := by
  by_cases hn : n = 0
  · simp [scaledMarkovSampleVariance, hn]
  · unfold scaledMarkovSampleVariance
    rw [finiteMarkovSampleMean_sub_const f c hn,
      variance_sub_const (finiteMarkovSampleMean_memLp π K hπ hf n).1]

def centeredObservableL2 (π : Measure α) [IsProbabilityMeasure π]
    (f : α → ℝ) (hf : MemLp f 2 π) : centeredL2 π :=
  ⟨(hf.sub (memLp_const (∫ x, f x ∂π))).toLp (fun x => f x - ∫ x, f x ∂π), by
    rw [mem_centeredL2_iff, integral_congr_ae (MemLp.coeFn_toLp _),
      integral_sub (hf.integrable (by norm_num)) (integrable_const _)]
    simp⟩

theorem centeredObservableL2_coeFn (π : Measure α) [IsProbabilityMeasure π]
    (f : α → ℝ) (hf : MemLp f 2 π) :
    (centeredObservableL2 π f hf : Lp ℝ 2 π) =ᵐ[π] fun x => f x - ∫ y, f y ∂π :=
  MemLp.coeFn_toLp (hf.sub (memLp_const (∫ x, f x ∂π)))

theorem centeredObservableL2_norm_sq (π : Measure α) [IsProbabilityMeasure π]
    (f : α → ℝ) (hf : MemLp f 2 π) :
    ‖centeredObservableL2 π f hf‖ ^ 2 = variance f π := by
  change ‖(centeredObservableL2 π f hf : Lp ℝ 2 π)‖ ^ 2 = _
  rw [← integral_sq_eq_norm_sq, variance_eq_integral hf.1.aemeasurable]
  apply integral_congr_ae
  filter_upwards [centeredObservableL2_coeFn π f hf] with x hx
  rw [hx]

/-- The real asymptotic variance is the limit of the actual scaled
finite-path variances. The next theorem proves that limit exists under a
positive spectral gap. -/
def stationaryAsymptoticVariance (π : Measure α) (K : Kernel α α) (f : α → ℝ) : ℝ :=
  limUnder atTop (scaledMarkovSampleVariance π K f)

theorem stationaryAsymptoticVariance_centered_eq
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    (f : centeredL2 π) {g : ℝ} (hg : 0 < g) (hg2 : g ≤ 2)
    (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π K) :
    stationaryAsymptoticVariance π K (f : Lp ℝ 2 π) =
      2 * ⟪f, poissonResolvent (centeredOperator K π hπ) f⟫ - ‖f‖ ^ 2 :=
  (scaledMarkovSampleVariance_tendsto_centered π K hπ f hg hg2 hgap).limUnder_eq

theorem stationaryAsymptoticVariance_spec
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {f : α → ℝ} (hf : MemLp f 2 π) {g : ℝ} (hg : 0 < g) (hg2 : g ≤ 2)
    (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π K) :
    0 ≤ stationaryAsymptoticVariance π K f ∧
      stationaryAsymptoticVariance π K f ≤ (2 / g - 1) * variance f π ∧
      Tendsto (scaledMarkovSampleVariance π K f) atTop
        (𝓝 (stationaryAsymptoticVariance π K f)) := by
  obtain ⟨σ2, hσ0, hσb, hσt⟩ := exists_scaledMarkovSampleVariance_limit_centered π K hπ
    (centeredObservableL2 π f hf) hg hg2 hgap
  rw [centeredObservableL2_norm_sq] at hσb
  have heq (n : ℕ) : scaledMarkovSampleVariance π K
      (centeredObservableL2 π f hf : Lp ℝ 2 π) n = scaledMarkovSampleVariance π K f n := by
    rw [scaledMarkovSampleVariance_congr π K hπ (centeredObservableL2_coeFn π f hf),
      scaledMarkovSampleVariance_sub_const π K hπ hf]
  have ht : Tendsto (scaledMarkovSampleVariance π K f) atTop (𝓝 σ2) :=
    hσt.congr' (Filter.Eventually.of_forall heq)
  have hv : stationaryAsymptoticVariance π K f = σ2 := ht.limUnder_eq
  rw [hv]
  exact ⟨hσ0, hσb, ht⟩

end
end UniformRandomMALA.Concrete
