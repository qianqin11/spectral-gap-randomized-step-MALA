import UniformRandomMALA.Concrete.StationaryVariance

/-!
# The bounded Poisson-remainder route to stationary variance

For a Markov contraction with a bounded inverse of `I - P`, solving the
Poisson equation twice expresses its covariance sequence as a second
difference of a bounded sequence.  The identities here show directly that
this gives a limit of the actual scaled empirical-mean variances.  No
absolute convergence of the non-lazy covariance series is needed.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ProbabilityTheory

noncomputable section

theorem sum_secondDifference_shift (e : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, (e (k + 1) - 2 * e (k + 2) + e (k + 3))) =
      e 1 - e 2 - (e (n + 1) - e (n + 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Nat.add_assoc]
    ring

theorem covarianceIncrement_of_secondDifference {c e : ℕ → ℝ}
    (h : ∀ k, c k = e k - 2 * e (k + 1) + e (k + 2)) (n : ℕ) :
    covarianceIncrement c n = e 0 - e 2 - 2 * (e (n + 1) - e (n + 2)) := by
  unfold covarianceIncrement
  simp_rw [h]
  simp only [Nat.zero_add, Nat.add_assoc]
  rw [sum_secondDifference_shift]
  ring

/-- Exact finite-sample telescoping formula for a covariance sequence with
a second antidifference. -/
theorem sum_covarianceIncrement_of_secondDifference {c e : ℕ → ℝ}
    (h : ∀ k, c k = e k - 2 * e (k + 1) + e (k + 2)) (n : ℕ) :
    (∑ k ∈ Finset.range n, covarianceIncrement c k) =
      (n : ℝ) * (e 0 - e 2) - 2 * (e 1 - e (n + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, covarianceIncrement_of_secondDifference h]
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_assoc]
    ring

/-- Boundedness of the second antidifference makes the exact remainder
vanish after division by the sample size. -/
theorem covarianceCesaro_tendsto_of_bounded_secondDifference {c e : ℕ → ℝ}
    (h : ∀ k, c k = e k - 2 * e (k + 1) + e (k + 2))
    {M : ℝ} (he : ∀ n, |e n| ≤ M) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, covarianceIncrement c k)
      atTop (𝓝 (e 0 - e 2)) := by
  have hbound (n : ℕ) : |2 * (e 1 - e (n + 1))| ≤ 4 * M := by
    have ha := abs_sub (e 1) (e (n + 1))
    rw [abs_mul]
    norm_num only [show |(2 : ℝ)| = 2 from by norm_num]
    nlinarith [he 1, he (n + 1)]
  have hrem : Tendsto (fun n : ℕ => 2 * (e 1 - e (n + 1)) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_bdd_div_atTop_nhds_zero
      (Filter.Eventually.of_forall fun n => (abs_le.mp (hbound n)).1)
      (Filter.Eventually.of_forall fun n => (abs_le.mp (hbound n)).2)
      tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => (e 0 - e 2) - 2 * (e 1 - e (n + 1)) / (n : ℝ))
      atTop (𝓝 (e 0 - e 2)) := by
    simpa using tendsto_const_nhds.sub hrem
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  rw [sum_covarianceIncrement_of_secondDifference h]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- A genuine limit of the variances of sample means on finite path spaces.
The probability space may depend on the sample size; only the coordinate
covariance identities are shared across sizes. -/
theorem scaledSampleVariance_family_tendsto_of_bounded_secondDifference
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {μ : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
    {X : ∀ n, ℕ → Ω n → ℝ} (hX : ∀ n k, MemLp (X n k) 2 (μ n))
    {c e : ℕ → ℝ}
    (hcov : ∀ n i j, i + j < n → covariance (X n i) (X n (i + j)) (μ n) = c j)
    (heq : ∀ k, c k = e k - 2 * e (k + 1) + e (k + 2))
    {M : ℝ} (he : ∀ n, |e n| ≤ M) :
    Tendsto (fun n => scaledSampleVariance (μ n) (X n) n) atTop (𝓝 (e 0 - e 2)) := by
  apply (covarianceCesaro_tendsto_of_bounded_secondDifference heq he).congr'
  exact Filter.Eventually.of_forall fun n => by
    change (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, covarianceIncrement c k =
      scaledSampleVariance (μ n) (X n) n
    rw [scaledSampleVariance_eq,
      variance_sampleSum_eq_sum_covarianceIncrement_of_lt (hX n) n (hcov n)]

/-- Nonnegativity is a consequence of the genuine variance limit. -/
theorem secondDifference_limit_nonneg
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {μ : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
    {X : ∀ n, ℕ → Ω n → ℝ} (hX : ∀ n k, MemLp (X n k) 2 (μ n))
    {c e : ℕ → ℝ}
    (hcov : ∀ n i j, i + j < n → covariance (X n i) (X n (i + j)) (μ n) = c j)
    (heq : ∀ k, c k = e k - 2 * e (k + 1) + e (k + 2))
    {M : ℝ} (he : ∀ n, |e n| ≤ M) : 0 ≤ e 0 - e 2 := by
  apply ge_of_tendsto (scaledSampleVariance_family_tendsto_of_bounded_secondDifference
    hX hcov heq he)
  exact Filter.Eventually.of_forall fun n =>
    mul_nonneg (Nat.cast_nonneg n) (variance_nonneg _ _)

end
end UniformRandomMALA.Concrete
