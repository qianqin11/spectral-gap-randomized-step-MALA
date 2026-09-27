import UniformRandomMALA.Concrete.StationaryVarianceKernel

/-!
# The actual stationary Markov sample-variance limit

Finite-path covariance identities and the centered Hilbert resolvent give
the limit of `n Var(n⁻¹ ∑ f(Xᵢ))` and its sharp spectral-gap upper bound.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory Filter DiscreteTime KernelLp
open scoped ENNReal ProbabilityTheory RealInnerProductSpace Topology

noncomputable section
variable {α : Type*} [MeasurableSpace α]

/-- The finite stationary quantity whose limit is the asymptotic variance. -/
def scaledMarkovSampleVariance (π : Measure α) (K : Kernel α α) (f : α → ℝ)
    (n : ℕ) : ℝ :=
  (n : ℝ) * variance (finiteMarkovSampleMean f n) (finiteMarkovPathLaw π K n)

/-- Coordinates extended by zero outside the finite trajectory. -/
def finitePathObservable (f : α → ℝ) (n k : ℕ) (path : Fin n → α) : ℝ :=
  if hk : k < n then f (path ⟨k, hk⟩) else 0

omit [MeasurableSpace α] in
theorem finitePathObservable_of_lt (f : α → ℝ) {n k : ℕ} (hk : k < n) :
    finitePathObservable f n k = fun path => f (path ⟨k, hk⟩) := by
  funext path
  exact dif_pos hk

theorem finitePathObservable_memLp (π : Measure α) (K : Kernel α α)
    [IsMarkovKernel K] (hπ : Kernel.Invariant K π) {f : α → ℝ}
    (hf : MemLp f 2 π) (n k : ℕ) :
    MemLp (finitePathObservable f n k) 2 (finiteMarkovPathLaw π K n) := by
  by_cases hk : k < n
  · rw [finitePathObservable_of_lt f hk]
    exact stationaryPathLaw_memLp_coordinate π K hπ hf n ⟨k, hk⟩
  · have heq : finitePathObservable f n k = 0 := by
      funext path
      exact dif_neg hk
    rw [heq]
    exact MemLp.zero

omit [MeasurableSpace α] in
theorem sampleMean_finitePathObservable (f : α → ℝ) (n : ℕ) :
    sampleMean (finitePathObservable f n) n = finiteMarkovSampleMean f n := by
  funext path
  unfold sampleMean sampleSum finiteMarkovSampleMean
  rw [Finset.sum_range]
  simp only [finitePathObservable, dif_pos (Fin.isLt _)]
  rw [div_eq_mul_inv, mul_comm]

theorem finitePathObservable_covariance (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    (f : centeredL2 π) (n i j : ℕ) (hij : i + j < n) :
    covariance (finitePathObservable (f : Lp ℝ 2 π) n i)
      (finitePathObservable (f : Lp ℝ 2 π) n (i + j))
      (finiteMarkovPathLaw π K n) = ⟪f, ((centeredOperator K π hπ) ^ j) f⟫ := by
  have hi : i < n := by omega
  rw [finitePathObservable_of_lt _ hi, finitePathObservable_of_lt _ hij]
  rw [stationaryPathLaw_covariance π K hπ (Lp.memLp (f : Lp ℝ 2 π))
    (centeredL2_integral π f) n ⟨i, hi⟩ ⟨i + j, hij⟩ (by simp),
    Nat.add_sub_cancel_left, inner_centeredOperator_pow]

/-- The limiting value is calculated from the actual Markov resolvent. -/
theorem scaledMarkovSampleVariance_tendsto_centered
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    (f : centeredL2 π) {g : ℝ} (hg : 0 < g) (hg2 : g ≤ 2)
    (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π K) :
    Tendsto (scaledMarkovSampleVariance π K (f : Lp ℝ 2 π)) atTop
      (𝓝 (2 * ⟪f, poissonResolvent (centeredOperator K π hπ) f⟫ - ‖f‖ ^ 2)) := by
  have ht := scaledSampleVariance_family_tendsto_of_rightGap
    (fun n k => finitePathObservable_memLp π K hπ (Lp.memLp (f : Lp ℝ 2 π)) n k)
    (centeredOperator K π hπ) (norm_centeredOperator_le K π hπ) f hg hg2
    (centeredOperator_rightGap K π hπ hg.le hgap)
    (finitePathObservable_covariance π K hπ f)
  change Tendsto (fun n : ℕ => (n : ℝ) * variance (finiteMarkovSampleMean (f : Lp ℝ 2 π) n)
    (finiteMarkovPathLaw π K n)) atTop _
  simpa only [scaledSampleVariance, sampleMean_finitePathObservable] using ht

/-- A genuine stationary variance limit exists and obeys the precise
`2 / gap - 1` bound. No convergence or variance certificate is an input. -/
theorem exists_scaledMarkovSampleVariance_limit_centered
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    (f : centeredL2 π) {g : ℝ} (hg : 0 < g) (hg2 : g ≤ 2)
    (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π K) :
    ∃ σ2 : ℝ, 0 ≤ σ2 ∧ σ2 ≤ (2 / g - 1) * ‖f‖ ^ 2 ∧
      Tendsto (scaledMarkovSampleVariance π K (f : Lp ℝ 2 π)) atTop (𝓝 σ2) := by
  let σ2 := 2 * ⟪f, poissonResolvent (centeredOperator K π hπ) f⟫ - ‖f‖ ^ 2
  have ht := scaledMarkovSampleVariance_tendsto_centered π K hπ f hg hg2 hgap
  refine ⟨σ2, ?_, ?_, ht⟩
  · apply ge_of_tendsto ht
    exact Filter.Eventually.of_forall fun n =>
      mul_nonneg (Nat.cast_nonneg n) (variance_nonneg _ _)
  · exact poissonResolvent_variance_le (centeredOperator K π hπ)
      (norm_centeredOperator_le K π hπ) f hg hg2
      (centeredOperator_rightGap K π hπ hg.le hgap)

end
end UniformRandomMALA.Concrete
