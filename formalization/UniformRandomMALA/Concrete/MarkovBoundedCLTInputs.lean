import UniformRandomMALA.Concrete.MarkovBoundedInitial
import UniformRandomMALA.Concrete.MarkovInfiniteCLTInputs
import UniformRandomMALA.Concrete.MarkovCLTBoundary

/-! # CLT hypotheses and boundary control for bounded initial densities -/

namespace UniformRandomMALA.Concrete
open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal ProbabilityTheory Topology
noncomputable section

theorem integral_nonneg_le_toReal_mul_of_measure_le_smul
    {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω} {B : ℝ≥0∞}
    (hB : B ≠ ∞) (hdom : μ ≤ B • ν) {f : Ω → ℝ}
    (hf : Integrable f ν) (hf0 : ∀ x, 0 ≤ f x) :
    (∫ x, f x ∂μ) ≤ B.toReal * ∫ x, f x ∂ν := by
  have h := integral_mono_measure hdom (Eventually.of_forall hf0) (hf.smul_measure hB)
  simpa only [integral_smul_measure, smul_eq_mul] using h

variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]

theorem boundedNormalizedPoissonRow_expectedTailSum_le
    (π μ : Measure α) [IsProbabilityMeasure π] [IsProbabilityMeasure μ]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hdom : μ ≤ B • π) (u : Lp ℝ 2 π) (δ : ℝ) (n : ℕ) :
    (boundedNormalizedPoissonRow π μ K hπ hB hdom u n).expectedTailSum δ n ≤
      B.toReal * (normalizedPoissonRow π K hπ u n).expectedTailSum δ n := by
  unfold MartingaleDifferenceRow.expectedTailSum
  rw [mul_sum]
  apply sum_le_sum
  intro k _
  have heq : (boundedNormalizedPoissonRow π μ K hπ hB hdom u n).tailTerm δ k =
      (normalizedPoissonRow π K hπ u n).tailTerm δ k := by
    funext path
    simp only [MartingaleDifferenceRow.tailTerm, boundedNormalizedPoissonRow_increment,
      normalizedPoissonRow_increment]
    rfl
  rw [heq]
  exact integral_nonneg_le_toReal_mul_of_measure_le_smul hB
    (infiniteMarkovPathLaw_le_smul B hdom K)
    ((normalizedPoissonRow π K hπ u n).tailTerm_integrable δ k)
    ((normalizedPoissonRow π K hπ u n).tailTerm_nonneg δ k)

theorem boundedNormalizedPoissonRow_varianceError_le
    (π μ : Measure α) [IsProbabilityMeasure π] [IsProbabilityMeasure μ]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hdom : μ ≤ B • π) (u : Lp ℝ 2 π) (v : ℝ) (n : ℕ) :
    (boundedNormalizedPoissonRow π μ K hπ hB hdom u n).varianceError v n ≤
      B.toReal * (normalizedPoissonRow π K hπ u n).varianceError v n := by
  have hpath := infiniteMarkovPathLaw_le_smul B hdom K
  have hac := Measure.absolutelyContinuous_of_le_smul hpath
  have heq : (boundedNormalizedPoissonRow π μ K hπ hB hdom u n).totalVariance n
      =ᵐ[infiniteMarkovPathLaw μ K] (normalizedPoissonRow π K hπ u n).totalVariance n := by
    filter_upwards [ae_all_iff.2 (fun k => boundedNormalizedPoissonRow_conditionalVariance
      π μ K hπ hB hdom u n k),
      hac.ae_le (ae_all_iff.2 (fun k => normalizedPoissonRow_conditionalVariance π K hπ u n k))]
      with path hμ hπ
    unfold MartingaleDifferenceRow.totalVariance varianceClock
    simp only [hμ, hπ]
  have heqabs : (fun path => |(boundedNormalizedPoissonRow π μ K hπ hB hdom u n).totalVariance n path - v|)
      =ᵐ[infiniteMarkovPathLaw μ K]
      (fun path => |(normalizedPoissonRow π K hπ u n).totalVariance n path - v|) := by
    filter_upwards [heq] with path hp
    rw [hp]
  unfold MartingaleDifferenceRow.varianceError
  rw [integral_congr_ae heqabs]
  exact integral_nonneg_le_toReal_mul_of_measure_le_smul hB hpath
    (((normalizedPoissonRow π K hπ u n).totalVariance_integrable n).sub (integrable_const v)).abs
    (fun path => abs_nonneg _)

theorem boundedNormalizedPoissonRow_expectedTailSum_tendsto_zero
    (π μ : Measure α) [IsProbabilityMeasure π] [IsProbabilityMeasure μ]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hdom : μ ≤ B • π) (u : Lp ℝ 2 π) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => (boundedNormalizedPoissonRow π μ K hπ hB hdom u n).expectedTailSum δ n)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun n => (boundedNormalizedPoissonRow π μ K hπ hB hdom u n).expectedTailSum_nonneg δ n)
    (boundedNormalizedPoissonRow_expectedTailSum_le π μ K hπ hB hdom u δ)
  simpa only [mul_zero] using
    (normalizedPoissonRow_expectedTailSum_tendsto_zero π K hπ u hδ).const_mul B.toReal

theorem boundedNormalizedPoissonRow_varianceError_tendsto_zero
    (π μ : Measure α) [IsProbabilityMeasure π] [IsProbabilityMeasure μ]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hdom : μ ≤ B • π) (u : Lp ℝ 2 π)
    {g : ℝ} (hg : 0 < g) (hg2 : g ≤ 2) (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π K) :
    Tendsto (fun n => (boundedNormalizedPoissonRow π μ K hπ hB hdom u n).varianceError
      (∫ z : α × α, poissonIncrement K u z.1 z.2 ^ 2 ∂(π ⊗ₘ K)) n) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => integral_nonneg (fun _ => abs_nonneg _))
    (boundedNormalizedPoissonRow_varianceError_le π μ K hπ hB hdom u _)
  simpa only [mul_zero] using
    (normalizedPoissonRow_varianceError_tendsto_zero π K hπ u hg hg2 hgap).const_mul B.toReal

omit [StandardBorelSpace α] [Nonempty α] in
theorem boundedInitial_normalizedMarkovSum_sub_poisson_secondMoment_tendsto_zero
    (π μ : Measure α) [IsProbabilityMeasure π] [IsProbabilityMeasure μ]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hdom : μ ≤ B • π) {u f : α → ℝ} (hu : MemLp u 2 π)
    (hPoisson : (fun x => u x - KernelLp.average K u x) =ᵐ[π] f) :
    Tendsto (fun n => ∫ path, (normalizedMarkovSum f n path - normalizedPoissonSum K u n path) ^ 2
      ∂infiniteMarkovPathLaw μ K) atTop (𝓝 0) := by
  have hbound (n : ℕ) :
      (∫ path, (normalizedMarkovSum f n path - normalizedPoissonSum K u n path) ^ 2 ∂infiniteMarkovPathLaw μ K) ≤
      B.toReal * ∫ path, (normalizedMarkovSum f n path - normalizedPoissonSum K u n path) ^ 2
        ∂infiniteMarkovPathLaw π K := by
    have heq := infinitePoisson_decomposition_ae π K hπ hPoisson n
    have h0 := hu.comp_measurePreserving (stationaryInfinitePathLaw_measurePreserving_coordinate π K hπ 0)
    have hn := hu.comp_measurePreserving (stationaryInfinitePathLaw_measurePreserving_coordinate π K hπ n)
    have hmem : MemLp (fun path => normalizedMarkovSum f n path - normalizedPoissonSum K u n path) 2
        (infiniteMarkovPathLaw π K) := (memLp_congr_ae heq).2
          ((h0.sub hn).const_mul (Real.sqrt (n : ℝ))⁻¹)
    exact integral_nonneg_le_toReal_mul_of_measure_le_smul hB
      (infiniteMarkovPathLaw_le_smul B hdom K) hmem.integrable_sq (fun _ => sq_nonneg _)
  apply squeeze_zero (fun n => integral_nonneg (fun _ => sq_nonneg _)) hbound
  simpa only [mul_zero] using
    (normalizedMarkovSum_sub_poisson_secondMoment_tendsto_zero π K hπ hu hPoisson).const_mul B.toReal

end
end UniformRandomMALA.Concrete
