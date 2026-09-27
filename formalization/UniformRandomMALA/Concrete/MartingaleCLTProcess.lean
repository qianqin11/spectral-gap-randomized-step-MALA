import UniformRandomMALA.Concrete.MartingaleCLTStep
import UniformRandomMALA.Concrete.MartingaleCLTLindeberg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # The stopped exponential process for a martingale row -/

namespace UniformRandomMALA.Concrete.MartingaleDifferenceRow

open MeasureTheory ProbabilityTheory Filter Finset Complex
open scoped Topology ProbabilityTheory

noncomputable section
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

def stoppedSum (D : MartingaleDifferenceRow μ) (C : ℝ) (n : ℕ) (x : Ω) : ℝ :=
  ∑ k ∈ range n, D.stoppedIncrement C k x

def stoppedClock (D : MartingaleDifferenceRow μ) (C : ℝ) (n : ℕ) (x : Ω) : ℝ :=
  ∑ k ∈ range n, stoppedVariance (fun j => D.conditionalVariance j x) C k

def compensatedProcess (D : MartingaleDifferenceRow μ) (C t : ℝ) (n : ℕ) (x : Ω) : ℂ :=
  (Real.exp (t ^ 2 * D.stoppedClock C n x / 2) : ℂ) *
    Complex.exp (Complex.I * (t * D.stoppedSum C n x))

omit [IsProbabilityMeasure μ] in
theorem stoppedIncrement_measurable (D : MartingaleDifferenceRow μ) (C : ℝ) (k : ℕ) :
    StronglyMeasurable[D.filtration (k + 1)] (D.stoppedIncrement C k) :=
  (D.measurable k).indicator
    ((D.filtration.mono (Nat.le_succ k)) _ (D.beforeVarianceCap_measurable C k))

omit [IsProbabilityMeasure μ] in
theorem stoppedSum_measurable (D : MartingaleDifferenceRow μ) (C : ℝ) (n : ℕ) :
    StronglyMeasurable[D.filtration n] (D.stoppedSum C n) := by
  apply Measurable.stronglyMeasurable
  apply Finset.measurable_sum
  intro k hk
  exact ((D.stoppedIncrement_measurable C k).mono
    (D.filtration.mono (Finset.mem_range.mp hk))).measurable

omit [IsProbabilityMeasure μ] in
theorem stoppedClock_measurable (D : MartingaleDifferenceRow μ) (C : ℝ) (n : ℕ) :
    StronglyMeasurable[D.filtration n] (D.stoppedClock C n) := by
  apply Measurable.stronglyMeasurable
  apply Finset.measurable_sum
  intro k hk
  exact ((D.stoppedVariance_measurable C k).mono
    (D.filtration.mono (Nat.le_of_lt (Finset.mem_range.mp hk)))).measurable

omit [IsProbabilityMeasure μ] in
theorem stoppedClock_nonneg (D : MartingaleDifferenceRow μ) (C : ℝ) (n : ℕ) (x : Ω) :
    0 ≤ D.stoppedClock C n x :=
  sum_nonneg fun k _ => stoppedVariance_nonneg (fun j => D.conditionalVariance_nonneg j x) C k

omit [IsProbabilityMeasure μ] in
theorem stoppedClock_le_cap (D : MartingaleDifferenceRow μ) {C : ℝ} (hC : 0 ≤ C)
    (n : ℕ) (x : Ω) : D.stoppedClock C n x ≤ C :=
  sum_stoppedVariance_le_cap (fun j => D.conditionalVariance_nonneg j x) hC n

omit [IsProbabilityMeasure μ] in
theorem compensatedProcess_measurable (D : MartingaleDifferenceRow μ) (C t : ℝ) (n : ℕ) :
    StronglyMeasurable[D.filtration n] (D.compensatedProcess C t n) := by
  have hs := D.stoppedSum_measurable C n
  have hv := D.stoppedClock_measurable C n
  unfold compensatedProcess
  fun_prop

omit [IsProbabilityMeasure μ] in
theorem norm_compensatedProcess (D : MartingaleDifferenceRow μ) (C t : ℝ)
    (n : ℕ) (x : Ω) :
    ‖D.compensatedProcess C t n x‖ = Real.exp (t ^ 2 * D.stoppedClock C n x / 2) := by
  rw [compensatedProcess, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have hn : ‖Complex.exp (Complex.I * (t * D.stoppedSum C n x))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hn, mul_one]

omit [IsProbabilityMeasure μ] in
theorem norm_compensatedProcess_le (D : MartingaleDifferenceRow μ) {C : ℝ} (hC : 0 ≤ C)
    (t : ℝ) (n : ℕ) (x : Ω) :
    ‖D.compensatedProcess C t n x‖ ≤ Real.exp (t ^ 2 * C / 2) := by
  rw [D.norm_compensatedProcess]
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (D.stoppedClock_le_cap hC n x) (sq_nonneg t)) (by norm_num)

theorem compensatedProcess_integrable (D : MartingaleDifferenceRow μ) {C : ℝ} (hC : 0 ≤ C)
    (t : ℝ) (n : ℕ) : Integrable (D.compensatedProcess C t n) μ := by
  exact (MemLp.of_bound ((D.compensatedProcess_measurable C t n).mono
    (D.filtration.le n)).aestronglyMeasurable (p := 1) (Real.exp (t ^ 2 * C / 2))
      (Eventually.of_forall (D.norm_compensatedProcess_le hC t n))).integrable (by norm_num)

omit [IsProbabilityMeasure μ] in
@[simp] theorem compensatedProcess_zero (D : MartingaleDifferenceRow μ) (C t : ℝ) (x : Ω) :
    D.compensatedProcess C t 0 x = 1 := by
  simp [compensatedProcess, stoppedClock, stoppedSum]

omit [IsProbabilityMeasure μ] in
theorem compensatedProcess_succ (D : MartingaleDifferenceRow μ) (C t : ℝ)
    (n : ℕ) (x : Ω) :
    D.compensatedProcess C t (n + 1) x = D.compensatedProcess C t n x *
      (Real.exp (t ^ 2 * stoppedVariance (fun j => D.conditionalVariance j x) C n / 2) : ℂ) *
      Complex.exp (Complex.I * (t * D.stoppedIncrement C n x)) := by
  unfold compensatedProcess stoppedClock stoppedSum
  rw [sum_range_succ, sum_range_succ]
  simp only [mul_add, add_div, Real.exp_add, Complex.ofReal_mul, Complex.ofReal_add, Complex.exp_add]
  ring

theorem norm_integral_compensatedProcess_step_le
    (D : MartingaleDifferenceRow μ) {C : ℝ} (hC : 0 ≤ C) (t : ℝ) (k : ℕ) :
    ‖(∫ x, D.compensatedProcess C t (k + 1) x ∂μ) -
        ∫ x, D.compensatedProcess C t k x ∂μ‖ ≤
      Real.exp (t ^ 2 * C / 2) * Real.exp (t ^ 2 * C / 2) *
        (4 * t ^ 2 * (∫ x, D.stoppedIncrement C k x ^ 2 *
          min 1 |t * D.stoppedIncrement C k x| ∂μ) +
          (t ^ 2 / 2) ^ 2 * ∫ x, stoppedVariance
            (fun j => D.conditionalVariance j x) C k ^ 2 ∂μ) := by
  rw [← integral_sub (D.compensatedProcess_integrable hC t (k + 1))
    (D.compensatedProcess_integrable hC t k)]
  simp_rw [D.compensatedProcess_succ C t k]
  exact @norm_integral_compensated_step_le Ω mΩ μ _ (D.filtration k) (D.filtration.le k)
    (D.stoppedIncrement C k) (fun x => stoppedVariance (fun j => D.conditionalVariance j x) C k)
    (D.compensatedProcess C t k) C (Real.exp (t ^ 2 * C / 2)) (Real.exp_pos _).le
    (D.stoppedIncrement_memLp C k) (D.stoppedIncrement_mean_zero C k)
    (D.stoppedIncrement_conditionalVariance C k) (D.stoppedVariance_measurable C k)
    (fun x => stoppedVariance_nonneg (fun j => D.conditionalVariance_nonneg j x) C k)
    (fun x => stoppedVariance_le_cap (fun j => D.conditionalVariance_nonneg j x) hC k)
    (D.compensatedProcess_measurable C t k) (D.norm_compensatedProcess_le hC t k) t

end
end UniformRandomMALA.Concrete.MartingaleDifferenceRow
