import UniformRandomMALA.Concrete.MarkovErgodicL1

/-! # Truncation extends the stationary ergodic estimate from `L²` to `L¹` -/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ProbabilityTheory ENNReal

noncomputable section
variable {α : Type*} [MeasurableSpace α]

def truncatedObservable (f : α → ℝ) (R : ℕ) : α → ℝ :=
  {x | |f x| ≤ (R : ℝ)}.indicator f

theorem truncatedObservable_measurable {f : α → ℝ} (hf : Measurable f) (R : ℕ) :
    Measurable (truncatedObservable f R) :=
  hf.indicator (measurableSet_le hf.abs measurable_const)

theorem truncatedObservable_memLp (π : Measure α) [IsFiniteMeasure π]
    {f : α → ℝ} (hf : Measurable f) (R : ℕ) : MemLp (truncatedObservable f R) 2 π := by
  apply MemLp.of_bound (truncatedObservable_measurable hf R).aestronglyMeasurable (R : ℝ)
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : |f x| ≤ (R : ℝ)
  · simp [truncatedObservable, hx, Real.norm_eq_abs]
  · simp [truncatedObservable, hx]

omit [MeasurableSpace α] in
theorem abs_sub_truncatedObservable_le (f : α → ℝ) (R : ℕ) (x : α) :
    |f x - truncatedObservable f R x| ≤ |f x| := by
  by_cases hx : |f x| ≤ (R : ℝ)
  · simp [truncatedObservable, hx]
  · simp [truncatedObservable, hx]

theorem integral_abs_sub_truncatedObservable_tendsto_zero
    (π : Measure α) {f : α → ℝ} (hm : Measurable f) (hf : Integrable f π) :
    Tendsto (fun R => ∫ x, |f x - truncatedObservable f R x| ∂π) atTop (𝓝 0) := by
  have ht := tendsto_integral_of_dominated_convergence
    (F := fun R x => |f x - truncatedObservable f R x|) (f := fun _ => (0 : ℝ))
    (fun x => |f x|)
    (fun R => (hm.sub (truncatedObservable_measurable hm R)).abs.aestronglyMeasurable)
    hf.abs (fun R => Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, abs_abs, Pi.sub_apply] using abs_sub_truncatedObservable_le f R x)
    (Filter.Eventually.of_forall fun x => ?_)
  · simpa only [integral_zero] using ht
  · obtain ⟨N, hN⟩ := exists_nat_ge |f x|
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with R hR
    have hx : |f x| ≤ (R : ℝ) := hN.trans (by exact_mod_cast hR)
    simp [truncatedObservable, hx]

/-- Conditional variances need only be integrable: truncation of the
observable and the proved stationary `L²` estimate give mean-absolute
ergodic convergence on the actual finite trajectory laws. -/
theorem stationaryMeanAbsoluteError_tendsto_zero_L1
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {f : α → ℝ} (hm : Measurable f) (hf : Integrable f π)
    {g : ℝ} (hg : 0 < g) (hg2 : g ≤ 2)
    (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π K) :
    Tendsto (stationaryMeanAbsoluteError π K f) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨R, hR⟩ := ((integral_abs_sub_truncatedObservable_tendsto_zero π hm hf).eventually_lt_const
    (show (0 : ℝ) < ε / 4 by positivity)).exists
  have hb := truncatedObservable_memLp π hm R
  have ht := stationaryMeanAbsoluteError_tendsto_zero_L2 π K hπ hb hg hg2 hgap
  obtain ⟨N, hN⟩ := (eventually_atTop.1 (ht.eventually_lt_const
    (show (0 : ℝ) < ε / 2 by positivity)))
  refine ⟨max 1 N, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  have hbnd := stationaryMeanAbsoluteError_approximation π K hπ hf
    (hb.integrable (by norm_num)) hn0
  have hsmall := hN n (le_trans (le_max_right _ _) hn)
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (stationaryMeanAbsoluteError_nonneg π K f n)]
  linarith

end
end UniformRandomMALA.Concrete
