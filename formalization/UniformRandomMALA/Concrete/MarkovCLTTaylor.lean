import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# Taylor errors for the martingale characteristic-function argument

These scalar bounds supply the Lindeberg remainder and exponential
compensation error. They are analytic ingredients, not a CLT statement.
-/

namespace UniformRandomMALA.Concrete

open Complex

/-- Quadratic Taylor error with a vanishing small-increment factor. -/
theorem norm_exp_I_mul_taylor_two_le (y : ℝ) :
    ‖Complex.exp (Complex.I * y) - 1 - Complex.I * y + (y : ℂ) ^ 2 / 2‖ ≤
      4 * y ^ 2 * min 1 |y| := by
  have hn : ‖Complex.I * (y : ℂ)‖ = |y| := by simp
  have hy2 : |y| ^ 2 = y ^ 2 := sq_abs y
  by_cases hy : |y| ≤ 1
  · rw [min_eq_right hy]
    have h := Complex.exp_bound (x := Complex.I * y) (by simpa [hn] using hy)
      (n := 3) (by norm_num)
    have hpoly : (∑ m ∈ Finset.range 3, (Complex.I * (y : ℂ)) ^ m / m.factorial) =
        1 + Complex.I * y - (y : ℂ) ^ 2 / 2 := by
      norm_num [Finset.sum_range_succ, mul_pow, Complex.I_sq]
      ring
    rw [hpoly, hn] at h
    norm_num at h
    have heq : Complex.exp (Complex.I * y) - 1 - Complex.I * y + (y : ℂ) ^ 2 / 2 =
        Complex.exp (Complex.I * y) - (1 + Complex.I * y - (y : ℂ) ^ 2 / 2) := by ring
    rw [heq]
    calc
      _ ≤ |y| ^ 3 * (2 / 9) := h
      _ ≤ 4 * y ^ 2 * |y| := by
        rw [pow_succ, hy2]
        nlinarith [mul_nonneg (sq_nonneg y) (abs_nonneg y)]
  · have hy1 : 1 ≤ |y| := (lt_of_not_ge hy).le
    rw [min_eq_left hy1, mul_one]
    have hexp : ‖Complex.exp (Complex.I * (y : ℂ))‖ = 1 := by simp
    calc
      _ ≤ ‖Complex.exp (Complex.I * y) - 1 - Complex.I * y‖ + ‖(y : ℂ) ^ 2 / 2‖ := norm_add_le _ _
      _ ≤ (‖Complex.exp (Complex.I * y) - 1‖ + ‖Complex.I * (y : ℂ)‖) +
          ‖(y : ℂ) ^ 2 / 2‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ ((‖Complex.exp (Complex.I * y)‖ + ‖(1 : ℂ)‖) + ‖Complex.I * (y : ℂ)‖) +
          ‖(y : ℂ) ^ 2 / 2‖ := by gcongr; exact norm_sub_le _ _
      _ = 2 + |y| + y ^ 2 / 2 := by norm_num [hexp, norm_pow, hy2]
      _ ≤ 4 * y ^ 2 := by nlinarith [sq_nonneg (|y| - 1), hy2]

/-- Error made by compensating a second-order characteristic-function
factor with an exponential, on a bounded nonnegative variance interval. -/
theorem abs_exp_mul_one_sub_sub_one_le {v B : ℝ} (hv : 0 ≤ v) (hvB : v ≤ B) :
    |Real.exp v * (1 - v) - 1| ≤ Real.exp B * v ^ 2 := by
  have hsign : Real.exp v * (1 - v) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-v)) (Real.exp_pos v).le
    rw [← Real.exp_add] at h
    simpa only [add_neg_cancel, Real.exp_zero, sub_eq_add_neg, add_comm] using h
  have hbound : |Real.exp v * (1 - v) - 1| ≤ Real.exp v * v ^ 2 := by
    by_cases hv1 : v ≤ 1
    · have h := Real.abs_exp_sub_one_sub_id_le (x := -v) (by simpa [abs_of_nonneg hv])
      have heq : Real.exp v * (1 - v) - 1 =
          -Real.exp v * (Real.exp (-v) - 1 - (-v)) := by
        have hexp : Real.exp v * Real.exp (-v) = 1 := by rw [← Real.exp_add]; simp
        nlinarith
      rw [heq, abs_mul, abs_neg, abs_of_pos (Real.exp_pos v)]
      simpa only [neg_sq] using mul_le_mul_of_nonneg_left h (Real.exp_pos v).le
    · have h1 : 1 ≤ v := (lt_of_not_ge hv1).le
      rw [abs_of_nonpos (by linarith)]
      have he1 := Real.one_le_exp hv
      have hq : 0 ≤ Real.exp v * (v ^ 2 - v) :=
        mul_nonneg (Real.exp_pos v).le (by nlinarith)
      nlinarith
  exact hbound.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hvB) (sq_nonneg v))

end UniformRandomMALA.Concrete
