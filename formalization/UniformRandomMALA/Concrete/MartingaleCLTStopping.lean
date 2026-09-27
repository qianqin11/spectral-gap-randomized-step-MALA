import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Predictable stopping at a bounded variance clock

These deterministic inequalities are used pointwise for a triangular
martingale array. They control the stopped quadratic variation and its
squared increments directly from conditional Lindeberg tails.
-/

namespace UniformRandomMALA.Concrete

open Finset

noncomputable section

def varianceClock (v : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ range n, v k

def stoppedVariance (v : ℕ → ℝ) (C : ℝ) (k : ℕ) : ℝ :=
  if varianceClock v (k + 1) ≤ C then v k else 0

theorem varianceClock_mono {v : ℕ → ℝ} (hv : ∀ k, 0 ≤ v k) : Monotone (varianceClock v) := by
  intro n m hnm
  exact sum_le_sum_of_subset_of_nonneg (range_mono hnm) (fun i _ _ => hv i)

theorem le_varianceClock_succ {v : ℕ → ℝ} (hv : ∀ k, 0 ≤ v k) (k : ℕ) :
    v k ≤ varianceClock v (k + 1) := by
  rw [varianceClock, sum_range_succ]
  exact le_add_of_nonneg_left (sum_nonneg fun j _ => hv j)

theorem stoppedVariance_nonneg {v : ℕ → ℝ} (hv : ∀ k, 0 ≤ v k) (C : ℝ) (k : ℕ) :
    0 ≤ stoppedVariance v C k := by
  unfold stoppedVariance
  split_ifs
  · exact hv k
  · exact le_rfl

theorem stoppedVariance_le {v : ℕ → ℝ} (hv : ∀ k, 0 ≤ v k) (C : ℝ) (k : ℕ) :
    stoppedVariance v C k ≤ v k := by
  unfold stoppedVariance
  split_ifs <;> simp [hv]

theorem stoppedVariance_le_cap {v : ℕ → ℝ} (hv : ∀ k, 0 ≤ v k)
    {C : ℝ} (hC : 0 ≤ C) (k : ℕ) : stoppedVariance v C k ≤ C := by
  unfold stoppedVariance
  split_ifs with h
  · exact (le_varianceClock_succ hv k).trans h
  · exact hC

theorem sum_stoppedVariance_le_cap {v : ℕ → ℝ} (hv : ∀ k, 0 ≤ v k)
    {C : ℝ} (hC : 0 ≤ C) (n : ℕ) :
    (∑ k ∈ range n, stoppedVariance v C k) ≤ C := by
  induction n with
  | zero => simpa using hC
  | succ n ih =>
    by_cases hn : varianceClock v (n + 1) ≤ C
    · exact (sum_le_sum fun k _ => stoppedVariance_le hv C k).trans hn
    · rw [sum_range_succ, stoppedVariance, if_neg hn, add_zero]
      exact ih

theorem stoppedVariance_eq_of_total_le {v : ℕ → ℝ} (hv : ∀ k, 0 ≤ v k)
    {C : ℝ} {n k : ℕ} (hclock : varianceClock v n ≤ C) (hk : k < n) :
    stoppedVariance v C k = v k := by
  exact if_pos ((varianceClock_mono hv (Nat.succ_le_iff.mpr hk)).trans hclock)

/-- Conditional Lindeberg tails control the squared stopped variances.
The inputs `v k ≤ δ² + r k` come from splitting the conditional second
moment at the increment threshold `δ`. -/
theorem sum_sq_stoppedVariance_le
    {v r : ℕ → ℝ} (hv : ∀ k, 0 ≤ v k) (hr : ∀ k, 0 ≤ r k)
    {C : ℝ} (hC : 0 ≤ C) (δ : ℝ) (n : ℕ)
    (hvr : ∀ k < n, v k ≤ δ ^ 2 + r k) :
    (∑ k ∈ range n, stoppedVariance v C k ^ 2) ≤
      δ ^ 2 * C + C * ∑ k ∈ range n, r k := by
  have hpoint (k : ℕ) (hk : k ∈ range n) :
      stoppedVariance v C k ^ 2 ≤ δ ^ 2 * stoppedVariance v C k + C * r k := by
    have hv0 := stoppedVariance_nonneg hv C k
    have hvc := stoppedVariance_le_cap hv hC k
    have hbound := (stoppedVariance_le hv C k).trans (hvr k (mem_range.mp hk))
    have hm := mul_le_mul_of_nonneg_left hbound hv0
    have ht := mul_le_mul_of_nonneg_right hvc (hr k)
    nlinarith
  calc
    _ ≤ ∑ k ∈ range n, (δ ^ 2 * stoppedVariance v C k + C * r k) := sum_le_sum hpoint
    _ = δ ^ 2 * (∑ k ∈ range n, stoppedVariance v C k) +
        C * ∑ k ∈ range n, r k := by rw [sum_add_distrib, mul_sum, mul_sum]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (sum_stoppedVariance_le_cap hv hC n) (sq_nonneg δ)) le_rfl

end
end UniformRandomMALA.Concrete
