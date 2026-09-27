import UniformRandomMALA.Concrete.MartingaleCLTUnstop
import UniformRandomMALA.Concrete.MartingaleCLTLimitAux

/-! # Characteristic-function CLT for genuine triangular martingale rows

The probability space and filtration may change with the row. The
hypotheses are the usual conditional variance and Lindeberg conditions,
in the mean-absolute/expected-tail form used for the stationary Markov
chain. The conclusion concerns the ordinary characteristic functions of
the actual increment sums.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology ProbabilityTheory

noncomputable section
variable {Ω : ℕ → Type*} [mΩ : ∀ n, MeasurableSpace (Ω n)]
  {μ : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]

theorem martingale_compensatedProcess_tendsto
    (D : (n : ℕ) → MartingaleDifferenceRow (μ n))
    (htail : ∀ δ > 0, Tendsto (fun n => (D n).expectedTailSum δ (D n).length) atTop (𝓝 0))
    {C : ℝ} (hC : 0 ≤ C) (t : ℝ) :
    Tendsto (fun n => ∫ x, (D n).compensatedProcess C t (D n).length x ∂μ n)
      atTop (𝓝 1) := by
  have hnorm : Tendsto (fun n => ‖(∫ x, (D n).compensatedProcess C t (D n).length x ∂μ n) - 1‖)
      atTop (𝓝 0) := by
    apply tendsto_zero_of_small_parameter_bound
      (b := fun δ n => Real.exp (t ^ 2 * C / 2) * Real.exp (t ^ 2 * C / 2) *
        (4 * t ^ 2 * (|t| * δ * C + (D n).expectedTailSum δ (D n).length) +
          (t ^ 2 / 2) ^ 2 * (δ ^ 2 * C + C * (D n).expectedTailSum δ (D n).length)))
      (c := fun δ => Real.exp (t ^ 2 * C / 2) * Real.exp (t ^ 2 * C / 2) *
        (4 * t ^ 2 * (|t| * δ * C) + (t ^ 2 / 2) ^ 2 * (δ ^ 2 * C)))
    · exact fun n => norm_nonneg _
    · exact fun δ hδ n => (D n).norm_integral_compensatedProcess_sub_one_le hC hδ.le t (D n).length
    · intro δ hδ
      have hc : Continuous (fun y : ℝ => Real.exp (t ^ 2 * C / 2) * Real.exp (t ^ 2 * C / 2) *
          (4 * t ^ 2 * (|t| * δ * C + y) + (t ^ 2 / 2) ^ 2 * (δ ^ 2 * C + C * y))) := by
        fun_prop
      simpa only [Function.comp_def, add_zero, mul_zero] using (hc.tendsto 0).comp (htail δ hδ)
    · fun_prop
    · simp
  exact tendsto_iff_norm_sub_tendsto_zero.2 hnorm

/-- The Gaussian characteristic limit follows from martingale
conditional moments, Lindeberg tails, and convergence of the actual
conditional-variance sum. No independence assumption is made. -/
theorem martingale_characteristicFunction_tendsto
    (D : (n : ℕ) → MartingaleDifferenceRow (μ n))
    {v : ℝ} (hv : 0 ≤ v)
    (htail : ∀ δ > 0, Tendsto (fun n => (D n).expectedTailSum δ (D n).length) atTop (𝓝 0))
    (hvariance : Tendsto (fun n => (D n).varianceError v (D n).length) atTop (𝓝 0))
    (t : ℝ) :
    Tendsto (fun n => ∫ x, Complex.exp (Complex.I * (t * (D n).incrementSum (D n).length x)) ∂μ n)
      atTop (𝓝 (Real.exp (-(t ^ 2 * v / 2)) : ℂ)) := by
  have hc := martingale_compensatedProcess_tendsto D htail (show 0 ≤ v + 1 by linarith) t
  have hn := tendsto_iff_norm_sub_tendsto_zero.1 hc
  have hupper := (hvariance.const_mul (MartingaleDifferenceRow.unstopConstant v t)).add hn
  have hnorm := squeeze_zero (fun n => norm_nonneg _)
    (fun n => (D n).norm_characteristic_expectation_sub_gaussian_le hv t (D n).length)
    (by simpa only [mul_zero, add_zero] using hupper)
  exact tendsto_iff_norm_sub_tendsto_zero.2 hnorm

end
end UniformRandomMALA.Concrete
