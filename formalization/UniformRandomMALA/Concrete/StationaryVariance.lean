import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
# Variance limits of stationary sample averages

The definitions below use the ordinary variance of actual random variables
on a probability space.  Finite-sum identities express this variance through
the stationary covariance sequence.  Summability, or a bounded second
antidifference, then proves convergence of the scaled sample-mean variance.
These are probability and real-analysis foundations; a Markov application
must establish the covariance identities from its transition law.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The sum of the first `n` observations of an actual stochastic process. -/
def sampleSum (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, X k ω

/-- The empirical mean, with the empty empirical mean set to zero. -/
def sampleMean (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ * sampleSum X n ω

/-- The finite-time quantity whose limit defines stationary asymptotic
variance in the manuscript. -/
def scaledSampleVariance (μ : Measure Ω) (X : ℕ → Ω → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * variance (sampleMean X n) μ

theorem sampleSum_memLp {X : ℕ → Ω → ℝ} (hX : ∀ k, MemLp (X k) 2 μ) (n : ℕ) :
    MemLp (sampleSum X n) 2 μ :=
  memLp_finsetSum (Finset.range n) (fun k _ => hX k)

theorem scaledSampleVariance_eq (X : ℕ → Ω → ℝ) (n : ℕ) :
    scaledSampleVariance μ X n = (n : ℝ)⁻¹ * variance (sampleSum X n) μ := by
  unfold scaledSampleVariance sampleMean
  rw [variance_const_mul]
  by_cases hn : n = 0
  · simp [hn]
  · have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    field_simp

/-- The successive variance increment dictated by a stationary covariance
sequence. -/
def covarianceIncrement (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  c 0 + 2 * ∑ k ∈ Finset.range n, c (k + 1)

theorem covariance_sampleSum_next_of_le [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX : ∀ k, MemLp (X k) 2 μ) {c : ℕ → ℝ}
    (n : ℕ)
    (hcov : ∀ i j, i + j ≤ n → covariance (X i) (X (i + j)) μ = c j) :
    covariance (sampleSum X n) (X n) μ = ∑ k ∈ Finset.range n, c (k + 1) := by
  change covariance (fun ω => ∑ k ∈ Finset.range n, X k ω) (X n) μ = _
  rw [covariance_fun_sum_left' (fun i _ => hX i) (hX n)]
  calc
    (∑ i ∈ Finset.range n, covariance (X i) (X n) μ) =
        ∑ i ∈ Finset.range n, c (n - i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hin : i ≤ n := (Finset.mem_range.mp hi).le
      simpa only [Nat.add_sub_of_le hin] using hcov i (n - i) (by omega)
    _ = ∑ i ∈ Finset.range n, c ((n - 1 - i) + 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      have hin := Finset.mem_range.mp hi
      omega
    _ = ∑ k ∈ Finset.range n, c (k + 1) :=
      Finset.sum_range_reflect (fun k => c (k + 1)) n

theorem covariance_sampleSum_next [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX : ∀ k, MemLp (X k) 2 μ) {c : ℕ → ℝ}
    (hcov : ∀ i j, covariance (X i) (X (i + j)) μ = c j) (n : ℕ) :
    covariance (sampleSum X n) (X n) μ = ∑ k ∈ Finset.range n, c (k + 1) :=
  covariance_sampleSum_next_of_le hX n (fun i j _ => hcov i j)

/-- The finite-sample identity only needs covariance information for the
coordinates that occur in the sum, so it also applies to finite path laws. -/
theorem variance_sampleSum_eq_sum_covarianceIncrement_of_lt [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX : ∀ k, MemLp (X k) 2 μ) {c : ℕ → ℝ} (n : ℕ) :
    (∀ i j, i + j < n → covariance (X i) (X (i + j)) μ = c j) →
    variance (sampleSum X n) μ = ∑ k ∈ Finset.range n, covarianceIncrement c k := by
  induction n with
  | zero =>
    intro _
    change variance (0 : Ω → ℝ) μ = 0
    exact variance_zero μ
  | succ n ih =>
    intro hcov
    have hs : sampleSum X (n + 1) = fun ω => sampleSum X n ω + X n ω := by
      funext ω
      exact Finset.sum_range_succ _ _
    have hv : variance (X n) μ = c 0 := by
      rw [← covariance_self (hX n).aemeasurable]
      simpa using hcov n 0 (by omega)
    rw [hs, variance_fun_add (sampleSum_memLp hX n) (hX n),
      ih (fun i j hij => hcov i j (by omega)), hv,
      covariance_sampleSum_next_of_le hX n (fun i j hij => hcov i j (by omega)),
      Finset.sum_range_succ]
    unfold covarianceIncrement
    ring

/-- The exact finite-sample variance as a sum of covariance increments.
No limit or convergence hypothesis occurs in this identity. -/
theorem variance_sampleSum_eq_sum_covarianceIncrement [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX : ∀ k, MemLp (X k) 2 μ) {c : ℕ → ℝ}
    (hcov : ∀ i j, covariance (X i) (X (i + j)) μ = c j) (n : ℕ) :
    variance (sampleSum X n) μ = ∑ k ∈ Finset.range n, covarianceIncrement c k := by
  induction n with
  | zero =>
    change variance (0 : Ω → ℝ) μ = 0
    exact variance_zero μ
  | succ n ih =>
    have hs : sampleSum X (n + 1) = fun ω => sampleSum X n ω + X n ω := by
      funext ω
      exact Finset.sum_range_succ _ _
    have hv : variance (X n) μ = c 0 := by
      rw [← covariance_self (hX n).aemeasurable]
      simpa using hcov n 0
    rw [hs, variance_fun_add (sampleSum_memLp hX n) (hX n), ih, hv,
      covariance_sampleSum_next hX hcov n, Finset.sum_range_succ]
    unfold covarianceIncrement
    ring

theorem scaledSampleVariance_eq_cesaro [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX : ∀ k, MemLp (X k) 2 μ) {c : ℕ → ℝ}
    (hcov : ∀ i j, covariance (X i) (X (i + j)) μ = c j) (n : ℕ) :
    scaledSampleVariance μ X n =
      (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, covarianceIncrement c k := by
  rw [scaledSampleVariance_eq, variance_sampleSum_eq_sum_covarianceIncrement hX hcov]

/-- An absolutely summable stationary covariance sequence gives the actual
limit of `n * Var(sampleMean)`. -/
theorem scaledSampleVariance_tendsto_of_summable [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX : ∀ k, MemLp (X k) 2 μ) {c : ℕ → ℝ}
    (hcov : ∀ i j, covariance (X i) (X (i + j)) μ = c j)
    (hc : Summable (fun k => c (k + 1))) :
    Tendsto (scaledSampleVariance μ X) atTop
      (𝓝 (c 0 + 2 * ∑' k : ℕ, c (k + 1))) := by
  have hinc : Tendsto (covarianceIncrement c) atTop
      (𝓝 (c 0 + 2 * ∑' k : ℕ, c (k + 1))) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul hc.hasSum.tendsto_sum_nat)
  apply hinc.cesaro.congr'
  exact Filter.Eventually.of_forall fun n => (scaledSampleVariance_eq_cesaro hX hcov n).symm

end
end UniformRandomMALA.Concrete
