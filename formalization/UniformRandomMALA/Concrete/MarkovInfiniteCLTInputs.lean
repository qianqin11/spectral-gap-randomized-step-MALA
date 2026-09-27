import UniformRandomMALA.Concrete.MarkovInfiniteRow
import UniformRandomMALA.Concrete.MarkovInfinitePrefix
import UniformRandomMALA.Concrete.MarkovCLTVarianceLLN
import UniformRandomMALA.Concrete.MartingaleCLTUnstop

/-! # Conditional-variance convergence for the actual normalized Markov rows -/

namespace UniformRandomMALA.Concrete
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory Topology
noncomputable section
variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]

theorem normalizedPoissonRow_varianceClock_ae
    (π : Measure α) [IsProbabilityMeasure π] (K : Kernel α α) [IsMarkovKernel K]
    (hπ : Kernel.Invariant K π) (u : Lp ℝ 2 π) (n : ℕ) :
    (fun path => varianceClock (fun k => (normalizedPoissonRow π K hπ u n).conditionalVariance k path) n)
      =ᵐ[infiniteMarkovPathLaw π K]
    (fun path => finiteMarkovSampleMean (poissonConditionalVariance K u) n (markovPathPrefix n path)) := by
  filter_upwards [ae_all_iff.2 (fun k => normalizedPoissonRow_conditionalVariance π K hπ u n k)]
    with path hpath
  simp only [varianceClock, hpath, finiteMarkovSampleMean, markovPathPrefix]
  rw [Fin.sum_univ_eq_sum_range (fun k => poissonConditionalVariance K u (path k)) n]
  simp [div_eq_mul_inv, Finset.mul_sum, mul_comm]

theorem normalizedPoissonRow_varianceError_eq
    (π : Measure α) [IsProbabilityMeasure π] (K : Kernel α α) [IsMarkovKernel K]
    (hπ : Kernel.Invariant K π) (u : Lp ℝ 2 π) (n : ℕ) :
    (normalizedPoissonRow π K hπ u n).varianceError (∫ x, poissonConditionalVariance K u x ∂π) n =
      stationaryMeanAbsoluteError π K (poissonConditionalVariance K u) n := by
  unfold MartingaleDifferenceRow.varianceError MartingaleDifferenceRow.totalVariance
  trans ∫ path, |finiteMarkovSampleMean (poissonConditionalVariance K u) n
    (markovPathPrefix n path) - ∫ y, poissonConditionalVariance K u y ∂π|
      ∂infiniteMarkovPathLaw π K
  · apply integral_congr_ae
    filter_upwards [normalizedPoissonRow_varianceClock_ae π K hπ u n] with path hp
    rw [hp]
  have hq := poissonConditionalVariance_measurable K (Lp.stronglyMeasurable u)
  have hsum : Measurable (finiteMarkovSampleMean (poissonConditionalVariance K u) n) := by
    exact (Finset.measurable_sum _ fun i _ => hq.comp (measurable_pi_apply i)).div_const (n : ℝ)
  have hm := integral_map (μ := infiniteMarkovPathLaw π K) (φ := markovPathPrefix n)
    (measurable_markovPathPrefix n).aemeasurable
    (f := fun path : Fin n → α =>
      |finiteMarkovSampleMean (poissonConditionalVariance K u) n path -
        ∫ y, poissonConditionalVariance K u y ∂π|)
    (hsum.sub_const _).abs.aestronglyMeasurable
  rw [infiniteMarkovPathLaw_map_prefix] at hm
  exact hm.symm

/-- The conditional variance hypothesis of the triangular martingale CLT
is discharged by the proved `L¹` ergodic theorem and exact finite-prefix law. -/
theorem normalizedPoissonRow_varianceError_tendsto_zero
    (π : Measure α) [IsProbabilityMeasure π] (K : Kernel α α) [IsMarkovKernel K]
    (hπ : Kernel.Invariant K π) (u : Lp ℝ 2 π) {g : ℝ} (hg : 0 < g) (hg2 : g ≤ 2)
    (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π K) :
    Tendsto (fun n => (normalizedPoissonRow π K hπ u n).varianceError
      (∫ z : α × α, poissonIncrement K u z.1 z.2 ^ 2 ∂(π ⊗ₘ K)) n) atTop (𝓝 0) := by
  simp_rw [← integral_poissonConditionalVariance π K hπ (Lp.memLp u),
    normalizedPoissonRow_varianceError_eq]
  exact poissonConditionalVariance_meanAbsoluteError_tendsto_zero π K hπ u hg hg2 hgap

end
end UniformRandomMALA.Concrete
