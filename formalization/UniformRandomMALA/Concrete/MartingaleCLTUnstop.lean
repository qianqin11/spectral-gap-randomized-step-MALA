import UniformRandomMALA.Concrete.MartingaleCLTEstimate

/-! # Removing the predictable variance stop -/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory Filter Finset Complex
open scoped Topology ProbabilityTheory

noncomputable section

theorem abs_exp_sub_one_le_mul_exp_abs (y : ℝ) :
    |Real.exp y - 1| ≤ |y| * Real.exp |y| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (y : ℂ) 1
  simp only [sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    Complex.norm_real, Real.norm_eq_abs, pow_one] at h
  rw [← Complex.ofReal_exp, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at h
  exact h

namespace MartingaleDifferenceRow
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

def incrementSum (D : MartingaleDifferenceRow μ) (n : ℕ) (x : Ω) : ℝ :=
  ∑ k ∈ range n, D.increment k x

def totalVariance (D : MartingaleDifferenceRow μ) (n : ℕ) (x : Ω) : ℝ :=
  varianceClock (fun k => D.conditionalVariance k x) n

def varianceError (D : MartingaleDifferenceRow μ) (v : ℝ) (n : ℕ) : ℝ :=
  ∫ x, |D.totalVariance n x - v| ∂μ

omit [IsProbabilityMeasure μ] in
theorem totalVariance_integrable (D : MartingaleDifferenceRow μ) (n : ℕ) :
    Integrable (D.totalVariance n) μ :=
  integrable_finsetSum (range n) fun k _ => D.conditionalVariance_integrable k

omit [IsProbabilityMeasure μ] in
theorem stoppedSum_eq_of_total_le (D : MartingaleDifferenceRow μ) (C : ℝ)
    (n : ℕ) (x : Ω) (hx : D.totalVariance n x ≤ C) :
    D.stoppedSum C n x = D.incrementSum n x := by
  apply sum_congr rfl
  intro k hk
  have hle : x ∈ D.beforeVarianceCap C k :=
    (varianceClock_mono (fun j => D.conditionalVariance_nonneg j x)
      (Nat.succ_le_iff.mpr (mem_range.mp hk))).trans hx
  exact Set.indicator_of_mem hle _

omit [IsProbabilityMeasure μ] in
theorem stoppedClock_eq_of_total_le (D : MartingaleDifferenceRow μ) (C : ℝ)
    (n : ℕ) (x : Ω) (hx : D.totalVariance n x ≤ C) :
    D.stoppedClock C n x = D.totalVariance n x := by
  apply sum_congr rfl
  intro k hk
  exact stoppedVariance_eq_of_total_le (fun j => D.conditionalVariance_nonneg j x)
    hx (mem_range.mp hk)

omit [IsProbabilityMeasure μ] in
theorem norm_characteristicIncrementSum (D : MartingaleDifferenceRow μ) (t : ℝ)
    (n : ℕ) (x : Ω) :
    ‖Complex.exp (Complex.I * (t * D.incrementSum n x))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem characteristicIncrementSum_integrable (D : MartingaleDifferenceRow μ) (t : ℝ)
    (n : ℕ) : Integrable (fun x => Complex.exp (Complex.I * (t * D.incrementSum n x))) μ := by
  have hm : Measurable (D.incrementSum n) := by
    apply Finset.measurable_sum
    intro k _
    exact ((D.measurable k).mono (D.filtration.le (k + 1))).measurable
  have hc : StronglyMeasurable (fun x => Complex.exp (Complex.I * (t * D.incrementSum n x))) := by
    fun_prop
  exact (MemLp.of_bound hc.aestronglyMeasurable (p := 1) 1
    (Eventually.of_forall fun x => (D.norm_characteristicIncrementSum t n x).le)).integrable (by norm_num)

def unstopConstant (v t : ℝ) : ℝ :=
  1 + Real.exp (t ^ 2 * (v + 1) / 2) + (t ^ 2 / 2) * Real.exp (t ^ 2 / 2)

omit [IsProbabilityMeasure μ] in
theorem norm_characteristic_sub_compensated_le (D : MartingaleDifferenceRow μ)
    {v : ℝ} (hv : 0 ≤ v) (t : ℝ) (n : ℕ) (x : Ω) :
    ‖Complex.exp (Complex.I * (t * D.incrementSum n x)) -
      (Real.exp (-(t ^ 2 * v / 2)) : ℂ) * D.compensatedProcess (v + 1) t n x‖ ≤
      unstopConstant v t * |D.totalVariance n x - v| := by
  let a : ℝ := t ^ 2 / 2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hC : 0 ≤ v + 1 := by linarith
  have hexp : Real.exp (-(t ^ 2 * v / 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [mul_nonneg (sq_nonneg t) hv]
  by_cases hx : |D.totalVariance n x - v| ≤ 1
  · have hclock : D.totalVariance n x ≤ v + 1 := by
      have hh := le_abs_self (D.totalVariance n x - v)
      linarith
    rw [compensatedProcess, D.stoppedSum_eq_of_total_le _ n x hclock,
      D.stoppedClock_eq_of_total_le _ n x hclock]
    have heq : (Real.exp (-(t ^ 2 * v / 2)) : ℂ) *
        ((Real.exp (t ^ 2 * D.totalVariance n x / 2) : ℂ) *
          Complex.exp (Complex.I * (t * D.incrementSum n x))) =
        (Real.exp (a * (D.totalVariance n x - v)) : ℂ) *
          Complex.exp (Complex.I * (t * D.incrementSum n x)) := by
      rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
      congr 2
      dsimp [a]
      ring_nf
    rw [heq, ← one_sub_mul, norm_mul, D.norm_characteristicIncrementSum, mul_one]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    have habs : |a * (D.totalVariance n x - v)| = a * |D.totalVariance n x - v| := by
      rw [abs_mul, abs_of_nonneg ha]
    have hsmall : a * |D.totalVariance n x - v| ≤ a := by nlinarith
    have hb := abs_exp_sub_one_le_mul_exp_abs (a * (D.totalVariance n x - v))
    rw [habs] at hb
    calc
      _ ≤ a * |D.totalVariance n x - v| * Real.exp (a * |D.totalVariance n x - v|) := hb
      _ ≤ a * |D.totalVariance n x - v| * Real.exp a :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsmall) (by positivity)
      _ ≤ _ := by
        dsimp [unstopConstant, a]
        nlinarith [abs_nonneg (D.totalVariance n x - v), Real.exp_pos (t ^ 2 * (v + 1) / 2)]
  · have hbig : 1 ≤ |D.totalVariance n x - v| := (lt_of_not_ge hx).le
    calc
      _ ≤ ‖Complex.exp (Complex.I * (t * D.incrementSum n x))‖ +
          ‖(Real.exp (-(t ^ 2 * v / 2)) : ℂ) * D.compensatedProcess (v + 1) t n x‖ := norm_sub_le _ _
      _ ≤ 1 + Real.exp (t ^ 2 * (v + 1) / 2) := by
        rw [D.norm_characteristicIncrementSum, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
        exact add_le_add le_rfl (by
          simpa only [one_mul] using mul_le_mul hexp (D.norm_compensatedProcess_le hC t n x)
            (norm_nonneg _) (by norm_num))
      _ ≤ _ := by
        have hpos : 0 ≤ (t ^ 2 / 2) * Real.exp (t ^ 2 / 2) := by positivity
        dsimp [unstopConstant]
        nlinarith [Real.exp_pos (t ^ 2 * (v + 1) / 2)]

/-- Removing the stop costs only the mean-absolute error of the actual
conditional variance. The limiting Gaussian variance can be zero. -/
theorem norm_characteristic_expectation_sub_gaussian_le
    (D : MartingaleDifferenceRow μ) {v : ℝ} (hv : 0 ≤ v) (t : ℝ) (n : ℕ) :
    ‖(∫ x, Complex.exp (Complex.I * (t * D.incrementSum n x)) ∂μ) -
      (Real.exp (-(t ^ 2 * v / 2)) : ℂ)‖ ≤
      unstopConstant v t * D.varianceError v n +
        ‖(∫ x, D.compensatedProcess (v + 1) t n x ∂μ) - 1‖ := by
  let z : ℂ := ∫ x, D.compensatedProcess (v + 1) t n x ∂μ
  let c : ℂ := (Real.exp (-(t ^ 2 * v / 2)) : ℂ)
  let A : ℂ := ∫ x, Complex.exp (Complex.I * (t * D.incrementSum n x)) ∂μ
  have hC : 0 ≤ v + 1 := by linarith
  have hc : ‖c‖ ≤ 1 := by
    simp only [c, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    nlinarith [mul_nonneg (sq_nonneg t) hv]
  have hdiff : ‖A - c * z‖ ≤ unstopConstant v t * D.varianceError v n := by
    have hbound : Integrable (fun x => unstopConstant v t * |D.totalVariance n x - v|) μ :=
      ((D.totalVariance_integrable n).sub (integrable_const v)).abs.const_mul _
    have h := norm_integral_le_of_norm_le hbound
      (Eventually.of_forall (D.norm_characteristic_sub_compensated_le hv t n))
    have hi := D.characteristicIncrementSum_integrable t n
    have hj : Integrable (fun x => c * D.compensatedProcess (v + 1) t n x) μ :=
      (D.compensatedProcess_integrable hC t n).const_mul c
    change ‖∫ x, Complex.exp (Complex.I * (t * D.incrementSum n x)) -
      c * D.compensatedProcess (v + 1) t n x ∂μ‖ ≤ _ at h
    rw [integral_sub hi hj, integral_const_mul, integral_const_mul] at h
    exact h
  change ‖A - c‖ ≤ _
  calc
    _ = ‖(A - c * z) + c * (z - 1)‖ := by congr 1; ring
    _ ≤ ‖A - c * z‖ + ‖c * (z - 1)‖ := norm_add_le _ _
    _ ≤ unstopConstant v t * D.varianceError v n + ‖z - 1‖ := by
      apply add_le_add hdiff
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hc

end MartingaleDifferenceRow
end
end UniformRandomMALA.Concrete
