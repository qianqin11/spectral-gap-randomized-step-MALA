import UniformRandomMALA.Concrete.MarkovBoundedCLTInputs
import UniformRandomMALA.Concrete.MarkovCLTDistribution

/-! # The Gaussian CLT for the actual Markov averages

The variance here is the limit of the actual scaled sample variances,
already proved to exist. The proof constructs the Poisson solution,
checks the true martingale-array hypotheses, and removes its negligible
boundary. An initial probability with bounded density is allowed.
-/

namespace UniformRandomMALA.Concrete
open MeasureTheory ProbabilityTheory Filter Finset KernelLp Complex
open scoped ENNReal ProbabilityTheory Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]

omit [StandardBorelSpace α] [Nonempty α] in
theorem measurable_normalizedMarkovSum {f : α → ℝ} (hf : Measurable f) (n : ℕ) :
    Measurable (normalizedMarkovSum f n) :=
  (Finset.measurable_sum (range n) fun k _ => hf.comp (measurable_pi_apply k)).const_mul _

omit [StandardBorelSpace α] [Nonempty α] in
theorem measurable_normalizedPoissonSum (K : Kernel α α) [IsMarkovKernel K]
    {u : α → ℝ} (hu : Measurable u) (n : ℕ) : Measurable (normalizedPoissonSum K u n) := by
  have hs : Measurable (fun path : ℕ → α => ∑ k ∈ range n, infinitePoissonIncrement K u k path) := by
    apply Finset.measurable_sum
    intro k _
    exact ((infinitePoissonIncrement_measurable K hu k).mono
      (markovPathFiltration.le (k + 1))).measurable
  exact hs.const_mul _

theorem boundedInitial_normalizedPoissonSum_characteristic_tendsto
    (π μ : Measure α) [IsProbabilityMeasure π] [IsProbabilityMeasure μ]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hdom : μ ≤ B • π) (u : Lp ℝ 2 π)
    {g : ℝ} (hg : 0 < g) (hg2 : g ≤ 2) (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π K)
    (t : ℝ) :
    Tendsto (fun n => ∫ path, Complex.exp (Complex.I * (t * normalizedPoissonSum K u n path))
      ∂infiniteMarkovPathLaw μ K) atTop
      (𝓝 (Real.exp (-(t ^ 2 * (∫ z : α × α, poissonIncrement K u z.1 z.2 ^ 2 ∂(π ⊗ₘ K)) / 2)) : ℂ)) := by
  have h := martingale_characteristicFunction_tendsto
    (fun n => boundedNormalizedPoissonRow π μ K hπ hB hdom u n)
    (integral_nonneg fun _ => sq_nonneg _)
    (fun δ hδ => boundedNormalizedPoissonRow_expectedTailSum_tendsto_zero π μ K hπ hB hdom u hδ)
    (boundedNormalizedPoissonRow_varianceError_tendsto_zero π μ K hπ hB hdom u hg hg2 hgap) t
  have heq (n : ℕ) : (boundedNormalizedPoissonRow π μ K hπ hB hdom u n).incrementSum n =
      normalizedPoissonSum K u n := by
    funext path
    simp only [MartingaleDifferenceRow.incrementSum, boundedNormalizedPoissonRow_increment,
      normalizedPoissonSum, infinitePoissonIncrement, mul_sum]
  simpa only [boundedNormalizedPoissonRow_length,
    heq] using h

theorem boundedInitial_poissonSolution_characteristic_tendsto
    (π μ : Measure α) [IsProbabilityMeasure π] [IsProbabilityMeasure μ]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hdom : μ ≤ B • π) (u : Lp ℝ 2 π)
    {f : α → ℝ} (hm : Measurable f)
    (hPoisson : (fun x => u x - KernelLp.average K u x) =ᵐ[π] f)
    {g : ℝ} (hg : 0 < g) (hg2 : g ≤ 2) (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π K) :
    ∀ t : ℝ, Tendsto (fun n => ∫ path, Complex.exp (Complex.I * (t * normalizedMarkovSum f n path))
      ∂infiniteMarkovPathLaw μ K) atTop
      (𝓝 (Real.exp (-(t ^ 2 * (∫ z : α × α, poissonIncrement K u z.1 z.2 ^ 2 ∂(π ⊗ₘ K)) / 2)) : ℂ)) := by
  have hdiff (n : ℕ) : MemLp (fun path => normalizedMarkovSum f n path - normalizedPoissonSum K u n path)
      2 (infiniteMarkovPathLaw μ K) := by
    have h0 := (Lp.memLp u).comp_measurePreserving (stationaryInfinitePathLaw_measurePreserving_coordinate π K hπ 0)
    have hn := (Lp.memLp u).comp_measurePreserving (stationaryInfinitePathLaw_measurePreserving_coordinate π K hπ n)
    have hmem : MemLp (fun path => normalizedMarkovSum f n path - normalizedPoissonSum K u n path) 2
        (infiniteMarkovPathLaw π K) :=
      (memLp_congr_ae (infinitePoisson_decomposition_ae π K hπ hPoisson n)).2
        ((h0.sub hn).const_mul (Real.sqrt (n : ℝ))⁻¹)
    exact hmem.of_measure_le_smul hB (infiniteMarkovPathLaw_le_smul B hdom K)
  exact characteristic_limit_of_sq_error (fun _ => infiniteMarkovPathLaw μ K)
    (normalizedPoissonSum K u) (normalizedMarkovSum f)
    (fun n => (measurable_normalizedPoissonSum K (Lp.stronglyMeasurable u).measurable n).aemeasurable)
    (fun n => (measurable_normalizedMarkovSum hm n).aemeasurable) hdiff
    (boundedInitial_normalizedMarkovSum_sub_poisson_secondMoment_tendsto_zero π μ K hπ hB hdom (Lp.memLp u) hPoisson)
    (boundedInitial_normalizedPoissonSum_characteristic_tendsto π μ K hπ hB hdom u hg hg2 hgap)

omit [StandardBorelSpace α] [Nonempty α] in
theorem stationaryAsymptoticVariance_centeredObservable
    (π : Measure α) [IsProbabilityMeasure π] (K : Kernel α α) [IsMarkovKernel K]
    (hπ : Kernel.Invariant K π) {f : α → ℝ} (hf : MemLp f 2 π) :
    stationaryAsymptoticVariance π K (centeredObservableL2 π f hf : Lp ℝ 2 π) =
      stationaryAsymptoticVariance π K f := by
  unfold stationaryAsymptoticVariance
  congr 1
  funext n
  rw [scaledMarkovSampleVariance_congr π K hπ (centeredObservableL2_coeFn π f hf),
    scaledMarkovSampleVariance_sub_const π K hπ hf]

/-- The complete characteristic-function endpoint for a bounded initial
density, with the actual sample-variance limit as the Gaussian variance. -/
theorem boundedInitial_normalizedMarkovSum_characteristic_tendsto
    (π μ : Measure α) [IsProbabilityMeasure π] [IsProbabilityMeasure μ]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hdom : μ ≤ B • π)
    {f : α → ℝ} (hm : Measurable f) (hf : MemLp f 2 π)
    {g : ℝ} (hg : 0 < g) (hg2 : g ≤ 2) (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π K) :
    ∀ t : ℝ, Tendsto (fun n => ∫ path, Complex.exp (Complex.I *
      (t * normalizedMarkovSum (fun x => f x - ∫ y, f y ∂π) n path)) ∂infiniteMarkovPathLaw μ K)
      atTop (𝓝 (Real.exp (-(t ^ 2 * stationaryAsymptoticVariance π K f / 2)) : ℂ)) := by
  let f0 := centeredObservableL2 π f hf
  let u0 := poissonResolvent (centeredOperator K π hπ) f0
  let u : Lp ℝ 2 π := u0
  have hPoisson : (fun x => u x - KernelLp.average K u x) =ᵐ[π]
      fun x => f x - ∫ y, f y ∂π :=
    (resolvent_poissonEquation_ae π K hπ f0 hg hg2 hgap).trans (centeredObservableL2_coeFn π f hf)
  have hv : (∫ z : α × α, poissonIncrement K u z.1 z.2 ^ 2 ∂(π ⊗ₘ K)) =
      stationaryAsymptoticVariance π K f :=
    (resolvent_increment_variance_eq_asymptoticVariance π K hπ f0 hg hg2 hgap).trans
      (stationaryAsymptoticVariance_centeredObservable π K hπ hf)
  simpa only [hv] using boundedInitial_poissonSolution_characteristic_tendsto
    π μ K hπ hB hdom u (hm.sub_const _) hPoisson hg hg2 hgap

/-- The genuine Gaussian CLT, including the degenerate zero-variance
case, on the actual infinite Markov trajectory law. -/
theorem boundedInitial_markovCLT
    (π μ : Measure α) [IsProbabilityMeasure π] [IsProbabilityMeasure μ]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hdom : μ ≤ B • π)
    {f : α → ℝ} (hm : Measurable f) (hf : MemLp f 2 π)
    {g : ℝ} (hg : 0 < g) (hg2 : g ≤ 2) (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π K) :
    TendstoInDistribution (normalizedMarkovSum (fun x => f x - ∫ y, f y ∂π)) atTop
      (id : ℝ → ℝ) (fun _ => infiniteMarkovPathLaw μ K)
      (gaussianReal 0 ⟨stationaryAsymptoticVariance π K f,
        (stationaryAsymptoticVariance_spec π K hπ hf hg hg2 hgap).1⟩) :=
  tendstoInDistribution_gaussian_of_characteristic (fun _ => infiniteMarkovPathLaw μ K)
    (normalizedMarkovSum (fun x => f x - ∫ y, f y ∂π))
    (fun n => (measurable_normalizedMarkovSum (hm.sub_const _) n).aemeasurable)
    (stationaryAsymptoticVariance_spec π K hπ hf hg hg2 hgap).1
    (boundedInitial_normalizedMarkovSum_characteristic_tendsto π μ K hπ hB hdom hm hf hg hg2 hgap)

end
end UniformRandomMALA.Concrete
