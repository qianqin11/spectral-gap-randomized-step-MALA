import UniformRandomMALA.Concrete.VarianceSeparationCovariance
import UniformRandomMALA.Concrete.VarianceSeparationSequence
import UniformRandomMALA.Concrete.VarianceSeparationPositiveGap

/-!
# Genuine extended asymptotic variance for reversible kernels

The extended quantity is defined from the actual finite stationary path
variances. Its convergence theorem includes zero spectral gaps and infinite
limits; existence is proved by pairing consecutive covariances.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory Filter KernelLp
open scoped ENNReal ProbabilityTheory RealInnerProductSpace Topology

noncomputable section
variable {α : Type*} [MeasurableSpace α]

/-- Extended asymptotic variance of the actual stationary sample means.
The subsequent convergence theorem proves this limsup is a genuine limit. -/
def asymptoticVarianceExtended (π : Measure α) (K : Kernel α α) (f : α → ℝ) : ℝ≥0∞ :=
  limsup (fun n => ENNReal.ofReal (scaledMarkovSampleVariance π K f n)) atTop

theorem scaledMarkovSampleVariance_centered_eq_covarianceCesaro
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    (f : centeredL2 π) (n : ℕ) :
    scaledMarkovSampleVariance π K (f : Lp ℝ 2 π) n =
      covarianceCesaroVariance (operatorCovariance (centeredOperator K π hπ) f) n := by
  calc
    scaledMarkovSampleVariance π K (f : Lp ℝ 2 π) n =
        scaledSampleVariance (finiteMarkovPathLaw π K n)
          (finitePathObservable (f : Lp ℝ 2 π) n) n := by
      simp only [scaledMarkovSampleVariance, scaledSampleVariance, sampleMean_finitePathObservable]
    _ = _ := by
      rw [scaledSampleVariance_eq, variance_sampleSum_eq_sum_covarianceIncrement_of_lt
        (fun k => finitePathObservable_memLp π K hπ (Lp.memLp (f : Lp ℝ 2 π)) n k) n
        (finitePathObservable_covariance π K hπ f n)]
      rfl

theorem asymptoticVarianceExtended_tendsto_centered
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hrev : Kernel.IsReversible K π)
    (f : centeredL2 π) :
    Tendsto (fun n => ENNReal.ofReal (scaledMarkovSampleVariance π K (f : Lp ℝ 2 π) n))
      atTop (𝓝 (asymptoticVarianceExtended π K (f : Lp ℝ 2 π))) := by
  let P := centeredOperator K π hrev.invariant
  have hP := norm_centeredOperator_le K π hrev.invariant
  have hs := centeredOperator_isSymmetric π K hrev
  obtain ⟨σ, ht⟩ := exists_covarianceCesaroVariance_extended_limit
    (fun n => operatorCovariancePair_nonneg P hP hs f n)
    (fun n => by rw [operatorCovariance_even P hs]; positivity)
    (operatorCovariance_even_antitone P hP hs f)
  have heq : (fun n => ENNReal.ofReal (scaledMarkovSampleVariance π K (f : Lp ℝ 2 π) n)) =
      (fun n => ENNReal.ofReal (covarianceCesaroVariance (operatorCovariance P f) n)) := by
    funext n
    rw [scaledMarkovSampleVariance_centered_eq_covarianceCesaro]
  unfold asymptoticVarianceExtended
  rw [heq, ht.limsup_eq]
  exact ht

theorem asymptoticVarianceExtended_centered_ge_pairSum
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hrev : Kernel.IsReversible K π)
    (f : centeredL2 π) (N : ℕ) :
    ENNReal.ofReal (2 * covariancePairSum
      (operatorCovariance (centeredOperator K π hrev.invariant) f) N - ‖f‖ ^ 2) ≤
        asymptoticVarianceExtended π K (f : Lp ℝ 2 π) := by
  let P := centeredOperator K π hrev.invariant
  have hP := norm_centeredOperator_le K π hrev.invariant
  have hs := centeredOperator_isSymmetric π K hrev
  have h := covarianceCesaroVariance_limsup_ge_pairSum
    (fun n => operatorCovariancePair_nonneg P hP hs f n)
    (fun n => by rw [operatorCovariance_even P hs]; positivity)
    (operatorCovariance_even_antitone P hP hs f) N
  unfold asymptoticVarianceExtended
  simp only [scaledMarkovSampleVariance_centered_eq_covarianceCesaro π K hrev.invariant,
    operatorCovariance, pow_zero, one_apply_eq_self, real_inner_self_eq_norm_sq] at h ⊢
  exact h

/-- Stationary asymptotic variance exists in `[0,∞]` for every reversible
Markov kernel and every `L²` observable, including zero-gap kernels. -/
theorem asymptoticVarianceExtended_tendsto
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hrev : Kernel.IsReversible K π)
    {f : α → ℝ} (hf : MemLp f 2 π) :
    Tendsto (fun n => ENNReal.ofReal (scaledMarkovSampleVariance π K f n)) atTop
      (𝓝 (asymptoticVarianceExtended π K f)) := by
  let F := centeredObservableL2 π f hf
  have heq (n : ℕ) : scaledMarkovSampleVariance π K (F : Lp ℝ 2 π) n =
      scaledMarkovSampleVariance π K f n := by
    rw [scaledMarkovSampleVariance_congr π K hrev.invariant (centeredObservableL2_coeFn π f hf),
      scaledMarkovSampleVariance_sub_const π K hrev.invariant hf]
  have heq' : (fun n => ENNReal.ofReal (scaledMarkovSampleVariance π K (F : Lp ℝ 2 π) n)) =
      (fun n => ENNReal.ofReal (scaledMarkovSampleVariance π K f n)) := by
    funext n
    rw [heq n]
  have ht := asymptoticVarianceExtended_tendsto_centered π K hrev F
  unfold asymptoticVarianceExtended at ht ⊢
  rwa [heq'] at ht

/-- With a positive gap, the extended variance agrees exactly with the
previously constructed finite real stationary variance. -/
theorem asymptoticVarianceExtended_eq_of_gap
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {f : α → ℝ} (hf : MemLp f 2 π) {g : ℝ} (hg : 0 < g) (hg2 : g ≤ 2)
    (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π K) :
    asymptoticVarianceExtended π K f = ENNReal.ofReal (stationaryAsymptoticVariance π K f) :=
  (ENNReal.tendsto_ofReal (stationaryAsymptoticVariance_spec π K hπ hf hg hg2 hgap).2.2).limsup_eq

/-- Small Dirichlet energy forces large actual asymptotic variance. This
bound remains valid when the spectral gap is zero and when the variance is
infinite. -/
theorem asymptoticVarianceExtended_centered_ge_nat_of_energy
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hrev : Kernel.IsReversible K π)
    (f : centeredL2 π) (hf : ‖f‖ = 1) (N : ℕ)
    (henergy : (4 * (N : ℝ) + 1) * ⟪f, f - centeredOperator K π hrev.invariant f⟫ ≤ 1) :
    ENNReal.ofReal (2 * (N : ℝ) - 1) ≤ asymptoticVarianceExtended π K (f : Lp ℝ 2 π) := by
  let P := centeredOperator K π hrev.invariant
  have hP := norm_centeredOperator_le K π hrev.invariant
  have hs := centeredOperator_isSymmetric π K hrev
  have hE := inner_sub_operator_nonneg P hP f
  have hsum : (N : ℝ) ≤ covariancePairSum (operatorCovariance P f) N := by
    calc
      (N : ℝ) = ∑ k ∈ Finset.range N, (1 : ℝ) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k hk
        have hkn : (k : ℝ) ≤ N := by exact_mod_cast (Finset.mem_range.mp hk).le
        have hq := operatorCovariancePair_lower P hP hs f k
        rw [hf] at hq
        change 1 ≤ operatorCovariancePair P f k
        change (4 * (N : ℝ) + 1) * ⟪f, f - P f⟫ ≤ 1 at henergy
        nlinarith
  have h := asymptoticVarianceExtended_centered_ge_pairSum π K hrev f N
  rw [hf] at h
  apply le_trans (ENNReal.ofReal_le_ofReal (show 2 * (N : ℝ) - 1 ≤
    2 * covariancePairSum (operatorCovariance P f) N - 1 ^ 2 by nlinarith)) h

end
end UniformRandomMALA.Concrete
