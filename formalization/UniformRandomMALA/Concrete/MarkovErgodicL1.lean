import UniformRandomMALA.Concrete.MarkovErgodicAverages
import UniformRandomMALA.Concrete.L2DensityTV
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Mean-absolute convergence of stationary averages of integrable functions -/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ProbabilityTheory ENNReal

noncomputable section
variable {α : Type*} [MeasurableSpace α]

theorem finiteMarkovSampleMean_integrable (π : Measure α) (K : Kernel α α)
    [IsMarkovKernel K] (hπ : Kernel.Invariant K π) {f : α → ℝ}
    (hf : Integrable f π) (n : ℕ) :
    Integrable (finiteMarkovSampleMean f n) (finiteMarkovPathLaw π K n) := by
  have hi (i : Fin n) : Integrable (fun path => f (path i)) (finiteMarkovPathLaw π K n) :=
    memLp_one_iff_integrable.1 ((memLp_one_iff_integrable.2 hf).comp_measurePreserving
      (stationaryPathLaw_measurePreserving_coordinate π K hπ n i))
  have hs := integrable_finsetSum Finset.univ (fun i _ => hi i)
  exact hs.div_const (n : ℝ)

omit [MeasurableSpace α] in
theorem abs_finiteMarkovSampleMean_le (f : α → ℝ) (n : ℕ) (path : Fin n → α) :
    |finiteMarkovSampleMean f n path| ≤ finiteMarkovSampleMean (fun x => |f x|) n path := by
  simp only [finiteMarkovSampleMean, abs_div, abs_of_nonneg (show 0 ≤ (n : ℝ) by positivity)]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (show 0 ≤ (n : ℝ) by positivity)

theorem integral_abs_finiteMarkovSampleMean_le
    (π : Measure α) (K : Kernel α α) [IsMarkovKernel K]
    (hπ : Kernel.Invariant K π) {f : α → ℝ} (hf : Integrable f π)
    {n : ℕ} (hn : n ≠ 0) :
    (∫ path, |finiteMarkovSampleMean f n path| ∂finiteMarkovPathLaw π K n) ≤
      ∫ x, |f x| ∂π := by
  calc
    _ ≤ ∫ path, finiteMarkovSampleMean (fun x => |f x|) n path ∂finiteMarkovPathLaw π K n :=
      integral_mono (finiteMarkovSampleMean_integrable π K hπ hf n).abs
        (finiteMarkovSampleMean_integrable π K hπ hf.abs n)
        (abs_finiteMarkovSampleMean_le f n)
    _ = _ := stationary_finiteMarkovSampleMean_integral π K hπ hf.abs hn

def stationaryMeanAbsoluteError (π : Measure α) (K : Kernel α α) (f : α → ℝ) (n : ℕ) : ℝ :=
  ∫ path, |finiteMarkovSampleMean f n path - ∫ x, f x ∂π| ∂finiteMarkovPathLaw π K n

theorem stationaryMeanAbsoluteError_nonneg (π : Measure α) (K : Kernel α α)
    (f : α → ℝ) (n : ℕ) : 0 ≤ stationaryMeanAbsoluteError π K f n :=
  integral_nonneg fun _ => abs_nonneg _

theorem stationaryMeanAbsoluteError_le_sqrt_MSE
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {f : α → ℝ} (hf : MemLp f 2 π) (n : ℕ) :
    stationaryMeanAbsoluteError π K f n ≤ Real.sqrt (finiteMarkovMSE π π K f n) := by
  have hF : MemLp (fun path : Fin n → α =>
      |finiteMarkovSampleMean f n path - ∫ x, f x ∂π|) 2 (finiteMarkovPathLaw π K n) :=
    ((finiteMarkovSampleMean_memLp π K hπ hf n).sub (memLp_const (∫ x, f x ∂π))).abs
  have h := abs_integral_mul_le_sqrt_integral_sq hF (memLp_const (1 : ℝ))
  simp only [mul_one, sq_abs, integral_const, probReal_univ,
    smul_eq_mul, one_pow, Real.sqrt_one,
    abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)] at h
  exact h

theorem stationaryMeanAbsoluteError_tendsto_zero_L2
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {f : α → ℝ} (hf : MemLp f 2 π) {g : ℝ} (hg : 0 < g) (hg2 : g ≤ 2)
    (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π K) :
    Tendsto (stationaryMeanAbsoluteError π K f) atTop (𝓝 0) := by
  apply squeeze_zero (stationaryMeanAbsoluteError_nonneg π K f)
    (stationaryMeanAbsoluteError_le_sqrt_MSE π K hπ hf)
  simpa only [Function.comp_def, Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp
    (stationary_finiteMarkovMSE_tendsto_zero π K hπ hf hg hg2 hgap)

omit [MeasurableSpace α] in
theorem finiteMarkovSampleMean_sub (f g : α → ℝ) (n : ℕ) (path : Fin n → α) :
    finiteMarkovSampleMean (fun x => f x - g x) n path =
      finiteMarkovSampleMean f n path - finiteMarkovSampleMean g n path := by
  simp only [finiteMarkovSampleMean, Finset.sum_sub_distrib, sub_div]

theorem stationaryMeanAbsoluteError_approximation
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {f b : α → ℝ} (hf : Integrable f π) (hb : Integrable b π)
    {n : ℕ} (hn : n ≠ 0) :
    stationaryMeanAbsoluteError π K f n ≤ stationaryMeanAbsoluteError π K b n +
      2 * ∫ x, |f x - b x| ∂π := by
  have hfi := finiteMarkovSampleMean_integrable π K hπ hf n
  have hbi := finiteMarkovSampleMean_integrable π K hπ hb n
  have hdi := finiteMarkovSampleMean_integrable π K hπ (hf.sub hb) n
  have hpoint (path : Fin n → α) :
      |finiteMarkovSampleMean f n path - ∫ x, f x ∂π| ≤
        |finiteMarkovSampleMean b n path - ∫ x, b x ∂π| +
          |finiteMarkovSampleMean (fun x => f x - b x) n path| +
            |∫ x, (f x - b x) ∂π| := by
    rw [finiteMarkovSampleMean_sub, integral_sub hf hb]
    calc
      _ = |(finiteMarkovSampleMean b n path - ∫ x, b x ∂π) +
          (finiteMarkovSampleMean f n path - finiteMarkovSampleMean b n path) -
          ((∫ x, f x ∂π) - ∫ x, b x ∂π)| := by congr 1; ring
      _ ≤ |(finiteMarkovSampleMean b n path - ∫ x, b x ∂π) +
          (finiteMarkovSampleMean f n path - finiteMarkovSampleMean b n path)| +
          |(∫ x, f x ∂π) - ∫ x, b x ∂π| := abs_sub _ _
      _ ≤ _ := add_le_add (abs_add_le _ _) le_rfl
  have hferr : Integrable (fun path : Fin n → α =>
      |finiteMarkovSampleMean f n path - ∫ x, f x ∂π|) (finiteMarkovPathLaw π K n) :=
    (hfi.sub (integrable_const _)).abs
  have hberr : Integrable (fun path : Fin n → α =>
      |finiteMarkovSampleMean b n path - ∫ x, b x ∂π|) (finiteMarkovPathLaw π K n) :=
    (hbi.sub (integrable_const _)).abs
  have hdabs : Integrable (fun path : Fin n → α =>
      |finiteMarkovSampleMean (fun x => f x - b x) n path|) (finiteMarkovPathLaw π K n) := hdi.abs
  have hsum : Integrable (fun path : Fin n → α =>
      |finiteMarkovSampleMean b n path - ∫ x, b x ∂π| +
      |finiteMarkovSampleMean (fun x => f x - b x) n path|) (finiteMarkovPathLaw π K n) :=
    hberr.add hdabs
  have htotal : Integrable (fun path : Fin n → α =>
      (|finiteMarkovSampleMean b n path - ∫ x, b x ∂π| +
      |finiteMarkovSampleMean (fun x => f x - b x) n path|) + |∫ x, (f x - b x) ∂π|)
      (finiteMarkovPathLaw π K n) := hsum.add (integrable_const _)
  have hbound := integral_mono hferr htotal hpoint
  have hexp : (∫ path, (|finiteMarkovSampleMean b n path - ∫ x, b x ∂π| +
      |finiteMarkovSampleMean (fun x => f x - b x) n path|) + |∫ x, (f x - b x) ∂π|
      ∂finiteMarkovPathLaw π K n) = stationaryMeanAbsoluteError π K b n +
        (∫ path, |finiteMarkovSampleMean (fun x => f x - b x) n path|
          ∂finiteMarkovPathLaw π K n) + |∫ x, (f x - b x) ∂π| := by
    rw [integral_add hsum (integrable_const _), integral_add hberr hdabs, integral_const]
    simp [stationaryMeanAbsoluteError]
  rw [hexp] at hbound
  have hmean := integral_abs_finiteMarkovSampleMean_le π K hπ (hf.sub hb) hn
  change (∫ path, |finiteMarkovSampleMean (fun x => f x - b x) n path|
    ∂finiteMarkovPathLaw π K n) ≤ ∫ x, |f x - b x| ∂π at hmean
  have hconst : |∫ x, (f x - b x) ∂π| ≤ ∫ x, |f x - b x| ∂π := abs_integral_le_integral_abs
  change stationaryMeanAbsoluteError π K f n ≤ _ at hbound
  linarith

end
end UniformRandomMALA.Concrete
