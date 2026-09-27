import UniformRandomMALA.Concrete.MarkovCLTBoundary
import UniformRandomMALA.Concrete.MarkovInfiniteInitial
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-! # Fixed burn-in and the normalization of actual trajectory sums -/

namespace UniformRandomMALA.Concrete
open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology
noncomputable section
variable {α : Type*} [MeasurableSpace α]

/-- The `n` retained observations use the normalization of the full `n + k`
observations, including the fixed discarded prefix. -/
def delayedNormalizedMarkovSum (f : α → ℝ) (k n : ℕ) (path : ℕ → α) : ℝ :=
  (Real.sqrt ((n + k : ℕ) : ℝ))⁻¹ * ∑ j ∈ range n, f (path j)

theorem measurable_delayedNormalizedMarkovSum {f : α → ℝ} (hf : Measurable f)
    (k n : ℕ) : Measurable (delayedNormalizedMarkovSum f k n) := by
  exact (Finset.measurable_sum _ fun j _ => hf.comp (measurable_pi_apply j)).const_mul _

theorem sqrt_normalization_ratio_tendsto_one (k : ℕ) :
    Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) / Real.sqrt ((n + k : ℕ) : ℝ))
      atTop (𝓝 1) := by
  have hden : Tendsto (fun n : ℕ => ((n + k : ℕ) : ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat k)
  have hquot : Tendsto (fun n : ℕ => (n : ℝ) / ((n + k : ℕ) : ℝ)) atTop (𝓝 1) := by
    have h : Tendsto (fun n : ℕ => 1 - (k : ℝ) / ((n + k : ℕ) : ℝ))
        atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub
      (tendsto_const_nhds.div_atTop hden :
        Tendsto (fun n : ℕ => (k : ℝ) / ((n + k : ℕ) : ℝ)) atTop (𝓝 0))
    apply (show Tendsto (fun n : ℕ => 1 - (k : ℝ) / ((n + k : ℕ) : ℝ))
      atTop (𝓝 1) by simpa using h).congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnk : ((n + k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : n + k ≠ 0)
    rw [Nat.cast_add] at hnk ⊢
    field_simp
    ring
  simpa only [Real.sqrt_div (Nat.cast_nonneg _), Real.sqrt_one] using hquot.sqrt

omit [MeasurableSpace α] in
theorem delayedNormalizedMarkovSum_eq_ratio (f : α → ℝ) (k n : ℕ) (path : ℕ → α) :
    delayedNormalizedMarkovSum f k n path =
      (Real.sqrt (n : ℝ) / Real.sqrt ((n + k : ℕ) : ℝ)) * normalizedMarkovSum f n path := by
  by_cases hn : n = 0
  · simp [hn, delayedNormalizedMarkovSum, normalizedMarkovSum]
  have hs : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast Nat.pos_of_ne_zero hn)
  unfold delayedNormalizedMarkovSum normalizedMarkovSum
  rw [div_eq_mul_inv]
  calc
    _ = (Real.sqrt (n : ℝ) * (Real.sqrt (n : ℝ))⁻¹) *
        ((Real.sqrt ((n + k : ℕ) : ℝ))⁻¹ * ∑ j ∈ range n, f (path j)) := by
      rw [mul_inv_cancel₀ hs, one_mul]
    _ = _ := by ring

/-- Slutsky's theorem removes the harmless fixed change in sample-size
normalization for any probability law on trajectories. -/
theorem tendstoInDistribution_delayedNormalizedMarkovSum
    (μ : Measure (ℕ → α)) [IsProbabilityMeasure μ]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (f : α → ℝ) (k : ℕ)
    (h : TendstoInDistribution (normalizedMarkovSum f) atTop id (fun _ => μ) ν) :
    TendstoInDistribution (delayedNormalizedMarkovSum f k) atTop id (fun _ => μ) ν := by
  have hratio : TendstoInMeasure μ
      (fun (n : ℕ) (_ : ℕ → α) => Real.sqrt (n : ℝ) / Real.sqrt ((n + k : ℕ) : ℝ))
      atTop (fun _ => (1 : ℝ)) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (Filter.Eventually.of_forall fun _ => sqrt_normalization_ratio_tendsto_one k)
  have hmul := h.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun z : ℝ × ℝ => z.2 * z.1) (by fun_prop) hratio
    (fun _ => aemeasurable_const)
  exact hmul.congr (fun n => Filter.Eventually.of_forall fun path =>
    (delayedNormalizedMarkovSum_eq_ratio f k n path).symm)
    (Filter.Eventually.of_forall fun _ => one_mul _)

omit [MeasurableSpace α] in
/-- Discarding a fixed initial block leaves exactly its normalized finite sum. -/
theorem normalizedMarkovSum_sub_delayed_shift (f : α → ℝ) (k n : ℕ) (path : ℕ → α) :
    normalizedMarkovSum f (n + k) path -
      delayedNormalizedMarkovSum f k n (markovPathShift k path) =
        (Real.sqrt ((n + k : ℕ) : ℝ))⁻¹ * ∑ j ∈ range k, f (path j) := by
  unfold normalizedMarkovSum delayedNormalizedMarkovSum markovPathShift
  rw [show n + k = k + n by omega, sum_range_add]
  ring

omit [MeasurableSpace α] in
theorem normalizedMarkovSum_sub_delayed_tendsto_zero
    (f : α → ℝ) (k : ℕ) (path : ℕ → α) :
    Tendsto (fun n => normalizedMarkovSum f (n + k) path -
      delayedNormalizedMarkovSum f k n (markovPathShift k path)) atTop (𝓝 0) := by
  simp_rw [normalizedMarkovSum_sub_delayed_shift]
  have hden : Tendsto (fun n : ℕ => ((n + k : ℕ) : ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat k)
  simpa using (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hden)).mul_const
    (∑ j ∈ range k, f (path j))

end
end UniformRandomMALA.Concrete
