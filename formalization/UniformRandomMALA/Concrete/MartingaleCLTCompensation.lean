import UniformRandomMALA.Concrete.MartingaleCLTConditional
import UniformRandomMALA.Concrete.MarkovCLTTaylor

/-! # Algebra and quantitative remainder of exponential compensation -/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory Complex
open scoped Topology ProbabilityTheory

noncomputable section

def characteristicTaylorRemainder (t x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (t * x)) - 1 - Complex.I * (t * x) + ((t * x : ℝ) : ℂ) ^ 2 / 2

theorem norm_characteristicTaylorRemainder_le (t x : ℝ) :
    ‖characteristicTaylorRemainder t x‖ ≤ 4 * t ^ 2 * x ^ 2 * min 1 |t * x| := by
  simpa only [characteristicTaylorRemainder, Complex.ofReal_mul, mul_pow, mul_assoc] using
    norm_exp_I_mul_taylor_two_le (t * x)

theorem norm_characteristicTaylorRemainder_le_sq (t x : ℝ) :
    ‖characteristicTaylorRemainder t x‖ ≤ 4 * t ^ 2 * x ^ 2 :=
  (norm_characteristicTaylorRemainder_le t x).trans
    (by nlinarith [min_le_left (1 : ℝ) |t * x|, mul_nonneg (sq_nonneg t) (sq_nonneg x)])

/-- The deterministic remainder after the linear and quadratic
conditional-moment terms have been removed. -/
def compensatedStepRemainder (t x v : ℝ) (z : ℂ) : ℂ :=
  (z * (Real.exp (t ^ 2 * v / 2) : ℂ)) * characteristicTaylorRemainder t x +
    z * ((Real.exp (t ^ 2 * v / 2) * (1 - t ^ 2 * v / 2) - 1 : ℝ) : ℂ)

theorem compensatedStep_expansion (t x v : ℝ) (z : ℂ) :
    z * (Real.exp (t ^ 2 * v / 2) : ℂ) * Complex.exp (Complex.I * (t * x)) - z =
      compensatedStepRemainder t x v z +
        (Complex.I * (t : ℂ)) * (x • (z * (Real.exp (t ^ 2 * v / 2) : ℂ))) -
        ((t : ℂ) ^ 2 / 2) * ((x ^ 2 - v) • (z * (Real.exp (t ^ 2 * v / 2) : ℂ))) := by
  simp only [compensatedStepRemainder, characteristicTaylorRemainder,
    Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one]
  ring

theorem norm_compensatedStepRemainder_le {M C v : ℝ} (hM : 0 ≤ M)
    (hv : 0 ≤ v) (hvC : v ≤ C) (t x : ℝ) {z : ℂ} (hz : ‖z‖ ≤ M) :
    ‖compensatedStepRemainder t x v z‖ ≤
      M * Real.exp (t ^ 2 * C / 2) *
        (4 * t ^ 2 * x ^ 2 * min 1 |t * x| + (t ^ 2 / 2) ^ 2 * v ^ 2) := by
  have hb : 0 ≤ t ^ 2 * v / 2 := by positivity
  have hbC : t ^ 2 * v / 2 ≤ t ^ 2 * C / 2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hvC (sq_nonneg t)) (by norm_num)
  have he := abs_exp_mul_one_sub_sub_one_le hb hbC
  have hexp : Real.exp (t ^ 2 * v / 2) ≤ Real.exp (t ^ 2 * C / 2) :=
    Real.exp_le_exp.mpr hbC
  have hr0 : 0 ≤ 4 * t ^ 2 * x ^ 2 * min 1 |t * x| := by positivity
  calc
    _ ≤ ‖z * (Real.exp (t ^ 2 * v / 2) : ℂ) * characteristicTaylorRemainder t x‖ +
        ‖z * ((Real.exp (t ^ 2 * v / 2) * (1 - t ^ 2 * v / 2) - 1 : ℝ) : ℂ)‖ :=
      norm_add_le _ _
    _ = ‖z‖ * Real.exp (t ^ 2 * v / 2) * ‖characteristicTaylorRemainder t x‖ +
        ‖z‖ * |Real.exp (t ^ 2 * v / 2) * (1 - t ^ 2 * v / 2) - 1| := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
    _ ≤ M * Real.exp (t ^ 2 * C / 2) *
        (4 * t ^ 2 * x ^ 2 * min 1 |t * x|) +
        M * (Real.exp (t ^ 2 * C / 2) * (t ^ 2 * v / 2) ^ 2) := by
      apply add_le_add
      · exact mul_le_mul
          (mul_le_mul hz hexp (Real.exp_pos _).le hM)
          (norm_characteristicTaylorRemainder_le t x) (norm_nonneg _) (by positivity)
      · exact mul_le_mul hz he (abs_nonneg _) hM
    _ = _ := by ring

theorem square_small_or_tail {δ : ℝ} (hδ : 0 ≤ δ) (t x : ℝ) :
    x ^ 2 * min 1 |t * x| ≤ |t| * δ * x ^ 2 +
      (if δ < |x| then x ^ 2 else 0) := by
  by_cases hx : δ < |x|
  · rw [if_pos hx]
    have hm := mul_le_mul_of_nonneg_left (min_le_left (1 : ℝ) |t * x|) (sq_nonneg x)
    nlinarith [mul_nonneg (mul_nonneg (abs_nonneg t) hδ) (sq_nonneg x)]
  · rw [if_neg hx, add_zero]
    calc
      _ ≤ x ^ 2 * |t * x| := mul_le_mul_of_nonneg_left (min_le_right _ _) (sq_nonneg x)
      _ ≤ x ^ 2 * (|t| * δ) := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (le_of_not_gt hx) (abs_nonneg t)) (sq_nonneg x)
      _ = _ := by ring

end
end UniformRandomMALA.Concrete
