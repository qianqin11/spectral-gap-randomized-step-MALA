import UniformRandomMALA.Concrete.NonstationaryMSEArithmetic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Dist

/-!
# Finite covariance sums

The stationary geometric covariance term contributes the sharp factor
`2 / g - 1`. The error caused by a nonstationary initial law factors into
two geometric sums. The probability estimates establishing the entrywise
bound are proved separately in `NonstationaryMSEPairBounds`.
-/

namespace UniformRandomMALA.Concrete

open Finset

lemma sum_range_pow_natDist_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (n i : ℕ) (hi : i < n) :
    ∑ j ∈ range n, ρ ^ (Nat.dist i j) ≤ 2 / (1 - ρ) - 1 := by
  have hn : n = (i + 1) + (n - (i + 1)) := by omega
  have hleft : (∑ j ∈ range (i + 1), ρ ^ (Nat.dist i j)) =
      ∑ j ∈ range (i + 1), ρ ^ j := by
    calc
      _ = ∑ j ∈ range (i + 1), ρ ^ (i + 1 - 1 - j) := by
        apply sum_congr rfl
        intro j hj
        have hj' := mem_range.mp hj
        congr 1
        simp only [Nat.dist]
        omega
      _ = _ := sum_range_reflect (fun j => ρ ^ j) (i + 1)
  have hright : (∑ j ∈ range (n - (i + 1)), ρ ^ (Nat.dist i (i + 1 + j))) =
      ρ * ∑ j ∈ range (n - (i + 1)), ρ ^ j := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    have hd : Nat.dist i (i + 1 + j) = j + 1 := by simp only [Nat.dist]; omega
    rw [hd, pow_succ, mul_comm]
  calc
    _ = (∑ j ∈ range (i + 1), ρ ^ (Nat.dist i j)) +
        ∑ j ∈ range (n - (i + 1)), ρ ^ (Nat.dist i (i + 1 + j)) := by
      conv_lhs => rw [hn, sum_range_add]
    _ = (∑ j ∈ range (i + 1), ρ ^ j) +
        ρ * ∑ j ∈ range (n - (i + 1)), ρ ^ j := by rw [hleft, hright]
    _ ≤ 1 / (1 - ρ) + ρ * (1 / (1 - ρ)) :=
      add_le_add (sum_range_nonneg_pow_le hρ0 hρ1 _)
        (mul_le_mul_of_nonneg_left (sum_range_nonneg_pow_le hρ0 hρ1 _) hρ0)
    _ = _ := by field_simp [(sub_pos.mpr hρ1).ne']; ring

lemma sum_fin_pow_natDist_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    {n : ℕ} (i : Fin n) :
    ∑ j : Fin n, ρ ^ (Nat.dist i.val j.val) ≤ 2 / (1 - ρ) - 1 := by
  change (∑ j : Fin n, (fun j : ℕ => ρ ^ Nat.dist i.val j) j.val) ≤ _
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => ρ ^ Nat.dist i.val j) n]
  exact sum_range_pow_natDist_le hρ0 hρ1 n i i.isLt

lemma sum_fin_sqrt_pow_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (n : ℕ) :
    ∑ i : Fin n, (Real.sqrt ρ) ^ i.val ≤ 2 / (1 - ρ) := by
  have hr1 : Real.sqrt ρ < 1 := by
    nlinarith [Real.sq_sqrt hρ0, Real.sqrt_nonneg ρ]
  rw [Fin.sum_univ_eq_sum_range]
  calc
    _ ≤ 1 / (1 - Real.sqrt ρ) := sum_range_nonneg_pow_le (Real.sqrt_nonneg _) hr1 n
    _ ≤ 2 / (1 - ρ) := by
      rw [div_le_div_iff₀ (sub_pos.mpr hr1) (sub_pos.mpr hρ1)]
      nlinarith [Real.sq_sqrt hρ0, sq_nonneg (1 - Real.sqrt ρ)]

/-- Summing an actual covariance matrix only requires its entrywise bound.
The error constant `B` includes the initial-density and observable norms. -/
theorem nonstationary_matrix_sum_le {n : ℕ} (A : Fin n → Fin n → ℝ)
    {ρ V B : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hV : 0 ≤ V) (hB : 0 ≤ B)
    (hA : ∀ i j, A i j ≤ V * ρ ^ (Nat.dist i.val j.val) +
      B * (Real.sqrt ρ) ^ (i.val + j.val)) :
    (∑ i, ∑ j, A i j) ≤ (n : ℝ) * (2 / (1 - ρ) - 1) * V +
      4 * B / (1 - ρ) ^ 2 := by
  have hs : (∑ i : Fin n, (Real.sqrt ρ) ^ i.val) ^ 2 ≤ (2 / (1 - ρ)) ^ 2 := by
    exact pow_le_pow_left₀ (sum_nonneg fun i _ => pow_nonneg (Real.sqrt_nonneg _) _)
      (sum_fin_sqrt_pow_le hρ0 hρ1 n) 2
  have herr : (∑ i : Fin n, ∑ j : Fin n,
      B * (Real.sqrt ρ) ^ (i.val + j.val)) ≤ 4 * B / (1 - ρ) ^ 2 := by
    simp_rw [pow_add, ← mul_assoc, ← mul_sum]
    calc
      _ = B * (∑ i : Fin n, (Real.sqrt ρ) ^ i.val) ^ 2 := by
        rw [← sum_mul, ← mul_sum]
        ring
      _ ≤ B * (2 / (1 - ρ)) ^ 2 := mul_le_mul_of_nonneg_left hs hB
      _ = _ := by rw [div_pow]; ring
  calc
    _ ≤ ∑ i : Fin n, ∑ j : Fin n,
        (V * ρ ^ (Nat.dist i.val j.val) + B * (Real.sqrt ρ) ^ (i.val + j.val)) := by
      exact sum_le_sum fun i _ => sum_le_sum fun j _ => hA i j
    _ = (∑ i : Fin n, ∑ j : Fin n, V * ρ ^ (Nat.dist i.val j.val)) +
        ∑ i : Fin n, ∑ j : Fin n, B * (Real.sqrt ρ) ^ (i.val + j.val) := by
      simp only [sum_add_distrib]
    _ ≤ (∑ _i : Fin n, V * (2 / (1 - ρ) - 1)) + 4 * B / (1 - ρ) ^ 2 := by
      apply add_le_add _ herr
      apply sum_le_sum
      intro i _
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_fin_pow_natDist_le hρ0 hρ1 i) hV
    _ = _ := by simp; ring

end UniformRandomMALA.Concrete
