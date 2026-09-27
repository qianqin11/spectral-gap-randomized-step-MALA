import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Summing the nonstationary covariance error

Scalar geometric-series estimates for Corollary 2.8
(`cor:nonstationary-variance`). These lemmas only sum the error estimate;
the kernel and path-law arguments must establish that estimate separately.
-/

namespace UniformRandomMALA.Concrete

open Finset

lemma sum_range_nonneg_pow_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑ i ∈ range n, r ^ i ≤ 1 / (1 - r) := by
  simpa only [Nat.Ico_zero_eq_range, pow_zero] using
    (geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hr0 hr1)

lemma sum_range_sqrt_pow_succ_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (n : ℕ) :
    ∑ j ∈ range n, (Real.sqrt ρ) ^ (j + 1) ≤ 2 / (1 - ρ) := by
  have hr0 := Real.sqrt_nonneg ρ
  have hr1 : Real.sqrt ρ < 1 := by
    have hsq := Real.sq_sqrt hρ0
    nlinarith
  calc
    _ ≤ ∑ j ∈ range n, (Real.sqrt ρ) ^ j := by
      apply sum_le_sum
      intro j _
      rw [pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg hr0 j) hr1.le
    _ ≤ 1 / (1 - Real.sqrt ρ) := sum_range_nonneg_pow_le hr0 hr1 n
    _ ≤ 2 / (1 - ρ) := by
      rw [div_le_div_iff₀ (sub_pos.mpr hr1) (sub_pos.mpr hρ1)]
      nlinarith [Real.sq_sqrt hρ0, sq_nonneg (1 - Real.sqrt ρ)]

/-- The covariance-error double sum has a uniform bound independent of
sample size. A non-sharp L⁴ interpolation constant at most four suffices. -/
theorem nonstationary_covariance_geometric_sum_le {ρ C : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hC0 : 0 ≤ C) (hC4 : C ≤ 4) (n : ℕ) :
    (∑ i ∈ range n, ρ ^ i *
      (1 + 2 * C * ∑ j ∈ range (n - 1 - i), (Real.sqrt ρ) ^ (j + 1))) ≤
        17 / (1 - ρ) ^ 2 := by
  have hd : 0 < 1 - ρ := sub_pos.mpr hρ1
  have hcoeff : 0 ≤ 1 + 4 * C / (1 - ρ) := by positivity
  calc
    _ ≤ ∑ i ∈ range n, ρ ^ i * (1 + 4 * C / (1 - ρ)) := by
      apply sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hρ0 i)
      have h := mul_le_mul_of_nonneg_left
        (sum_range_sqrt_pow_succ_le hρ0 hρ1 (n - 1 - i))
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC0)
      calc
        _ ≤ 1 + 2 * C * (2 / (1 - ρ)) := by linarith
        _ = _ := by ring
    _ = (∑ i ∈ range n, ρ ^ i) * (1 + 4 * C / (1 - ρ)) := (sum_mul ..).symm
    _ ≤ (1 / (1 - ρ)) * (1 + 4 * C / (1 - ρ)) :=
      mul_le_mul_of_nonneg_right (sum_range_nonneg_pow_le hρ0 hρ1 n) hcoeff
    _ = ((1 - ρ) + 4 * C) / (1 - ρ) ^ 2 := by field_simp
    _ ≤ 17 / (1 - ρ) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      linarith

/-- Scaled form with the constant used in the paper's lazy-gap bound. -/
theorem nonstationary_covariance_error_le {ρ C M F : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hC0 : 0 ≤ C) (hC4 : C ≤ 4)
    (hM : 0 ≤ M) (n : ℕ) :
    M / (n : ℝ) ^ 2 *
      (∑ i ∈ range n, ρ ^ i *
        (1 + 2 * C * ∑ j ∈ range (n - 1 - i), (Real.sqrt ρ) ^ (j + 1))) * F ^ 2 ≤
      128 * M * F ^ 2 / ((n : ℝ) ^ 2 * (1 - ρ) ^ 2) := by
  calc
    _ ≤ M / (n : ℝ) ^ 2 * (17 / (1 - ρ) ^ 2) * F ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (nonstationary_covariance_geometric_sum_le
          hρ0 hρ1 hC0 hC4 n) (div_nonneg hM (sq_nonneg _))) (sq_nonneg _)
    _ ≤ M / (n : ℝ) ^ 2 * (128 / (1 - ρ) ^ 2) * F ^ 2 := by
      gcongr
      norm_num
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

end UniformRandomMALA.Concrete
