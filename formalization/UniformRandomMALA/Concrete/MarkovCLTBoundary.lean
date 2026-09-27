import UniformRandomMALA.Concrete.MarkovInfiniteMartingale

/-! # The Poisson boundary is negligible on the actual infinite chain -/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ProbabilityTheory ENNReal

noncomputable section
variable {α : Type*} [MeasurableSpace α]

def normalizedMarkovSum (f : α → ℝ) (n : ℕ) (path : ℕ → α) : ℝ :=
  (Real.sqrt (n : ℝ))⁻¹ * ∑ k ∈ range n, f (path k)

def normalizedPoissonSum (K : Kernel α α) (u : α → ℝ) (n : ℕ) (path : ℕ → α) : ℝ :=
  (Real.sqrt (n : ℝ))⁻¹ * ∑ k ∈ range n, infinitePoissonIncrement K u k path

theorem infinitePoisson_decomposition_ae
    (π : Measure α) [IsProbabilityMeasure π] (K : Kernel α α) [IsMarkovKernel K]
    (hπ : Kernel.Invariant K π) {u f : α → ℝ}
    (hPoisson : (fun x => u x - KernelLp.average K u x) =ᵐ[π] f) (n : ℕ) :
    (fun path => normalizedMarkovSum f n path - normalizedPoissonSum K u n path)
      =ᵐ[infiniteMarkovPathLaw π K]
        fun path => (Real.sqrt (n : ℝ))⁻¹ * (u (path 0) - u (path n)) := by
  have hi (k : ℕ) := (stationaryInfinitePathLaw_measurePreserving_coordinate π K hπ k).quasiMeasurePreserving.ae_eq_comp hPoisson
  filter_upwards [ae_all_iff.2 hi] with path hp
  simp only [Function.comp_apply] at hp
  have hs : (∑ k ∈ range n, f (path k)) -
      ∑ k ∈ range n, infinitePoissonIncrement K u k path = u (path 0) - u (path n) := by
    rw [← sum_sub_distrib]
    calc
      _ = ∑ k ∈ range n, (u (path k) - u (path (k + 1))) := by
        apply sum_congr rfl
        intro k _
        rw [← hp k]
        simp only [infinitePoissonIncrement, poissonIncrement]
        ring
      _ = _ := sum_range_sub' (fun k => u (path k)) n
  simpa only [normalizedMarkovSum, normalizedPoissonSum, ← mul_sub] using congrArg
    (fun a => (Real.sqrt (n : ℝ))⁻¹ * a) hs

theorem stationaryInfinitePath_integral_coordinate
    (π : Measure α) [IsProbabilityMeasure π] (K : Kernel α α) [IsMarkovKernel K]
    (hπ : Kernel.Invariant K π) {f : α → ℝ} (hf : AEStronglyMeasurable f π) (k : ℕ) :
    ∫ path, f (path k) ∂infiniteMarkovPathLaw π K = ∫ x, f x ∂π := by
  have hm : AEStronglyMeasurable f ((infiniteMarkovPathLaw π K).map (fun path => path k)) := by
    rw [stationaryInfinitePathLaw_map_coordinate π K hπ]
    exact hf
  rw [← integral_map (measurable_pi_apply k).aemeasurable hm,
    stationaryInfinitePathLaw_map_coordinate π K hπ]

theorem infinitePoissonBoundary_secondMoment_le
    (π : Measure α) [IsProbabilityMeasure π] (K : Kernel α α) [IsMarkovKernel K]
    (hπ : Kernel.Invariant K π) {u : α → ℝ} (hu : MemLp u 2 π) (n : ℕ) :
    (∫ path, ((Real.sqrt (n : ℝ))⁻¹ * (u (path 0) - u (path n))) ^ 2
      ∂infiniteMarkovPathLaw π K) ≤ (4 * ∫ x, u x ^ 2 ∂π) / n := by
  have h0 : MemLp (fun path : ℕ → α => u (path 0)) 2 (infiniteMarkovPathLaw π K) :=
    hu.comp_measurePreserving (stationaryInfinitePathLaw_measurePreserving_coordinate π K hπ 0)
  have hn : MemLp (fun path : ℕ → α => u (path n)) 2 (infiniteMarkovPathLaw π K) :=
    hu.comp_measurePreserving (stationaryInfinitePathLaw_measurePreserving_coordinate π K hπ n)
  have hI : Integrable (fun path : ℕ → α => (u (path 0) - u (path n)) ^ 2)
      (infiniteMarkovPathLaw π K) := (h0.sub hn).integrable_sq
  have hJ : Integrable (fun path : ℕ → α => 2 * u (path 0) ^ 2 + 2 * u (path n) ^ 2)
      (infiniteMarkovPathLaw π K) := (h0.integrable_sq.const_mul 2).add (hn.integrable_sq.const_mul 2)
  have hb : (∫ path, (u (path 0) - u (path n)) ^ 2 ∂infiniteMarkovPathLaw π K) ≤
      4 * ∫ x, u x ^ 2 ∂π := by
    have h := integral_mono hI hJ (fun path => by nlinarith [sq_nonneg (u (path 0) + u (path n))])
    rw [integral_add (h0.integrable_sq.const_mul 2) (hn.integrable_sq.const_mul 2),
      integral_const_mul, integral_const_mul,
      stationaryInfinitePath_integral_coordinate π K hπ hu.integrable_sq.1,
      stationaryInfinitePath_integral_coordinate π K hπ hu.integrable_sq.1] at h
    linarith
  simp only [mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [integral_const_mul, div_eq_mul_inv]
  exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (Nat.cast_nonneg n))).trans_eq (mul_comm _ _)

theorem normalizedMarkovSum_sub_poisson_secondMoment_tendsto_zero
    (π : Measure α) [IsProbabilityMeasure π] (K : Kernel α α) [IsMarkovKernel K]
    (hπ : Kernel.Invariant K π) {u f : α → ℝ} (hu : MemLp u 2 π)
    (hPoisson : (fun x => u x - KernelLp.average K u x) =ᵐ[π] f) :
    Tendsto (fun n => ∫ path, (normalizedMarkovSum f n path - normalizedPoissonSum K u n path) ^ 2
      ∂infiniteMarkovPathLaw π K) atTop (𝓝 0) := by
  have hbound (n : ℕ) : (∫ path, (normalizedMarkovSum f n path - normalizedPoissonSum K u n path) ^ 2
      ∂infiniteMarkovPathLaw π K) ≤ (4 * ∫ x, u x ^ 2 ∂π) / n := by
    have heq := infinitePoisson_decomposition_ae π K hπ hPoisson n
    have hs : (fun path => (normalizedMarkovSum f n path - normalizedPoissonSum K u n path) ^ 2)
        =ᵐ[infiniteMarkovPathLaw π K]
      (fun path => ((Real.sqrt (n : ℝ))⁻¹ * (u (path 0) - u (path n))) ^ 2) := by
      filter_upwards [heq] with path hp
      rw [hp]
    rw [integral_congr_ae hs]
    exact infinitePoissonBoundary_secondMoment_le π K hπ hu n
  exact squeeze_zero (fun n => integral_nonneg (fun _ => sq_nonneg _))
    hbound (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)

end
end UniformRandomMALA.Concrete
