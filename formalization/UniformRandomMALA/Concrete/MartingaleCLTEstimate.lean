import UniformRandomMALA.Concrete.MartingaleCLTProcess

/-! # A finite-row characteristic-function estimate -/

namespace UniformRandomMALA.Concrete.MartingaleDifferenceRow

open MeasureTheory ProbabilityTheory Filter Finset Complex
open scoped Topology ProbabilityTheory

noncomputable section
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

def expectedTailSum (D : MartingaleDifferenceRow μ) (δ : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range n, ∫ x, D.tailTerm δ k x ∂μ

omit [IsProbabilityMeasure μ] in
theorem expectedTailSum_nonneg (D : MartingaleDifferenceRow μ) (δ : ℝ) (n : ℕ) :
    0 ≤ D.expectedTailSum δ n :=
  sum_nonneg fun k _ => integral_nonneg (D.tailTerm_nonneg δ k)

theorem integral_sq_stoppedIncrement (D : MartingaleDifferenceRow μ) (C : ℝ) (k : ℕ) :
    (∫ x, D.stoppedIncrement C k x ^ 2 ∂μ) =
      ∫ x, stoppedVariance (fun j => D.conditionalVariance j x) C k ∂μ := by
  calc
    _ = ∫ x, μ[fun y => D.stoppedIncrement C k y ^ 2 | D.filtration k] x ∂μ :=
      (integral_condExp (D.filtration.le k)).symm
    _ = _ := integral_congr_ae (D.stoppedIncrement_conditionalVariance C k)

theorem sum_integral_sq_stoppedIncrement_le (D : MartingaleDifferenceRow μ)
    {C : ℝ} (hC : 0 ≤ C) (n : ℕ) :
    (∑ k ∈ range n, ∫ x, D.stoppedIncrement C k x ^ 2 ∂μ) ≤ C := by
  simp_rw [D.integral_sq_stoppedIncrement]
  rw [← integral_finsetSum (range n) (fun k _ =>
    (D.stoppedVariance_memLp hC k 1).integrable (by norm_num))]
  have hsum : Integrable (D.stoppedClock C n) μ := integrable_finsetSum (range n)
    fun k _ => (D.stoppedVariance_memLp hC k 1).integrable (by norm_num)
  change (∫ x, D.stoppedClock C n x ∂μ) ≤ C
  simpa using integral_mono hsum (integrable_const C) (D.stoppedClock_le_cap hC n)

omit [IsProbabilityMeasure μ] in
theorem stopped_square_small_or_tail (D : MartingaleDifferenceRow μ)
    (C : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (t : ℝ) (k : ℕ) (x : Ω) :
    D.stoppedIncrement C k x ^ 2 * min 1 |t * D.stoppedIncrement C k x| ≤
      |t| * δ * D.stoppedIncrement C k x ^ 2 + D.tailTerm δ k x := by
  by_cases hx : x ∈ D.beforeVarianceCap C k
  · simpa only [stoppedIncrement, Set.indicator_of_mem hx, tailTerm] using
      square_small_or_tail hδ t (D.increment k x)
  · simp only [stoppedIncrement, Set.indicator_of_notMem hx, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero, zero_mul, zero_add]
    exact D.tailTerm_nonneg δ k x

theorem sum_integral_square_min_stopped_le (D : MartingaleDifferenceRow μ)
    {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ) (t : ℝ) (n : ℕ) :
    (∑ k ∈ range n, ∫ x, D.stoppedIncrement C k x ^ 2 *
      min 1 |t * D.stoppedIncrement C k x| ∂μ) ≤
      |t| * δ * C + D.expectedTailSum δ n := by
  have hp (k : ℕ) : (∫ x, D.stoppedIncrement C k x ^ 2 *
      min 1 |t * D.stoppedIncrement C k x| ∂μ) ≤
      |t| * δ * (∫ x, D.stoppedIncrement C k x ^ 2 ∂μ) + ∫ x, D.tailTerm δ k x ∂μ := by
    have hs := (D.stoppedIncrement_memLp C k).integrable_sq
    have ht := D.tailTerm_integrable δ k
    have h := integral_mono (integrable_square_min _ (D.stoppedIncrement_memLp C k) t)
      ((hs.const_mul (|t| * δ)).add ht) (D.stopped_square_small_or_tail C hδ t k)
    simp only [Pi.add_apply] at h
    rw [integral_add (hs.const_mul _) ht, integral_const_mul] at h
    exact h
  calc
    _ ≤ ∑ k ∈ range n, (|t| * δ * (∫ x, D.stoppedIncrement C k x ^ 2 ∂μ) +
        ∫ x, D.tailTerm δ k x ∂μ) := sum_le_sum fun k _ => hp k
    _ = |t| * δ * (∑ k ∈ range n, ∫ x, D.stoppedIncrement C k x ^ 2 ∂μ) +
        D.expectedTailSum δ n := by rw [sum_add_distrib, mul_sum]; rfl
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (D.sum_integral_sq_stoppedIncrement_le hC n)
      (mul_nonneg (abs_nonneg t) hδ)) le_rfl

/-- The key finite-row bound: after variance stopping, the error of the
exponentially compensated characteristic function is controlled only by
the Lindeberg tail and an arbitrarily small deterministic threshold. -/
theorem norm_integral_compensatedProcess_sub_one_le
    (D : MartingaleDifferenceRow μ) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (t : ℝ) (n : ℕ) :
    ‖(∫ x, D.compensatedProcess C t n x ∂μ) - 1‖ ≤
      Real.exp (t ^ 2 * C / 2) * Real.exp (t ^ 2 * C / 2) *
        (4 * t ^ 2 * (|t| * δ * C + D.expectedTailSum δ n) +
          (t ^ 2 / 2) ^ 2 * (δ ^ 2 * C + C * D.expectedTailSum δ n)) := by
  have hsum : ‖(∫ x, D.compensatedProcess C t n x ∂μ) - 1‖ ≤
      ∑ k ∈ range n, ‖(∫ x, D.compensatedProcess C t (k + 1) x ∂μ) -
        ∫ x, D.compensatedProcess C t k x ∂μ‖ := by
    have ht := norm_sum_le (range n) (fun k => (∫ x, D.compensatedProcess C t (k + 1) x ∂μ) -
      ∫ x, D.compensatedProcess C t k x ∂μ)
    rw [sum_range_sub (fun k => ∫ x, D.compensatedProcess C t k x ∂μ) n] at ht
    simpa only [D.compensatedProcess_zero, integral_const, probReal_univ,
      one_smul] using ht
  have hsq : (∑ k ∈ range n, ∫ x,
      stoppedVariance (fun j => D.conditionalVariance j x) C k ^ 2 ∂μ) ≤
      δ ^ 2 * C + C * D.expectedTailSum δ n := by
    rw [← integral_finsetSum (range n) (fun k _ => (D.stoppedVariance_memLp hC k 2).integrable_sq)]
    exact D.integral_sum_sq_stoppedVariance_le hC hδ n
  calc
    _ ≤ ∑ k ∈ range n, (Real.exp (t ^ 2 * C / 2) * Real.exp (t ^ 2 * C / 2) *
        (4 * t ^ 2 * (∫ x, D.stoppedIncrement C k x ^ 2 *
          min 1 |t * D.stoppedIncrement C k x| ∂μ) +
          (t ^ 2 / 2) ^ 2 * ∫ x, stoppedVariance
            (fun j => D.conditionalVariance j x) C k ^ 2 ∂μ)) :=
      hsum.trans (sum_le_sum fun k _ => D.norm_integral_compensatedProcess_step_le hC t k)
    _ = Real.exp (t ^ 2 * C / 2) * Real.exp (t ^ 2 * C / 2) *
        (4 * t ^ 2 * (∑ k ∈ range n, ∫ x, D.stoppedIncrement C k x ^ 2 *
          min 1 |t * D.stoppedIncrement C k x| ∂μ) +
          (t ^ 2 / 2) ^ 2 * ∑ k ∈ range n, ∫ x, stoppedVariance
            (fun j => D.conditionalVariance j x) C k ^ 2 ∂μ) := by
      simp only [mul_add, sum_add_distrib, mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_left (D.sum_integral_square_min_stopped_le hC hδ t n) (by positivity))
      (mul_le_mul_of_nonneg_left hsq (sq_nonneg _))) (by positivity)

end
end UniformRandomMALA.Concrete.MartingaleDifferenceRow
