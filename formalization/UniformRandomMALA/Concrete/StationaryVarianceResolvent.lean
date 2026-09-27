import UniformRandomMALA.Concrete.StationaryVariancePoisson
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Poisson equations for contractions with a positive right gap

The inverse of `I - P` is constructed by the geometric series of the
half-lazy contraction.  Two applications supply a bounded second
antidifference of the covariance sequence, including for a non-lazy
contraction whose spectrum may approach minus one.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Half-lazification of a continuous linear operator. -/
def halfLazyOperator (P : E →L[ℝ] E) : E →L[ℝ] E :=
  (1 / 2 : ℝ) • (1 + P)

theorem halfLazyOperator_apply (P : E →L[ℝ] E) (x : E) :
    halfLazyOperator P x = (1 / 2 : ℝ) • (x + P x) := rfl

/-- A positive right-gap inequality makes the half-lazy operator a strict
norm contraction. This step uses only Hilbert geometry and contractivity. -/
theorem norm_halfLazyOperator_lt_one (P : E →L[ℝ] E) (hP : ‖P‖ ≤ 1)
    {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 2)
    (hgap : ∀ x : E, a * ‖x‖ ^ 2 ≤ ⟪x, x - P x⟫) :
    ‖halfLazyOperator P‖ < 1 := by
  have hq : 0 ≤ 1 - a / 2 := by linarith
  have hb : ‖halfLazyOperator P‖ ≤ Real.sqrt (1 - a / 2) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro x
    have hp : ‖P x‖ ≤ ‖x‖ := by
      simpa using (P.le_opNorm x).trans
        (mul_le_mul_of_nonneg_right hP (norm_nonneg x))
    have hp2 : ‖P x‖ ^ 2 ≤ ‖x‖ ^ 2 := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.2 hp
    have hc := hgap x
    rw [inner_sub_right, real_inner_self_eq_norm_sq] at hc
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x))).1
    rw [mul_pow, Real.sq_sqrt hq, halfLazyOperator_apply, norm_smul, mul_pow,
      norm_add_sq_real]
    norm_num only [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    nlinarith
  apply hb.trans_lt
  apply (Real.sqrt_lt' zero_lt_one).2
  linarith

/-- The Poisson resolvent, constructed from the half-lazy geometric series. -/
def poissonResolvent (P : E →L[ℝ] E) : E →L[ℝ] E :=
  (1 / 2 : ℝ) • ∑' n : ℕ, halfLazyOperator P ^ n

/-- The geometric-series construction solves the actual Poisson equation. -/
theorem poissonResolvent_sub [CompleteSpace E] (P : E →L[ℝ] E)
    (hP : ‖halfLazyOperator P‖ < 1) (f : E) :
    poissonResolvent P f - P (poissonResolvent P f) = f := by
  have hm := mul_neg_geom_series (halfLazyOperator P) hP
  have hf := congrArg (fun A : E →L[ℝ] E => A f) hm
  simp only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, halfLazyOperator_apply] at hf
  simp only [poissonResolvent, smul_apply, map_smul]
  convert hf using 1; module

/-- Coercivity bounds the norm of any Poisson solution. -/
theorem norm_poissonSolution_le (P : E →L[ℝ] E) {a : ℝ} (ha : 0 < a)
    (hgap : ∀ x : E, a * ‖x‖ ^ 2 ≤ ⟪x, x - P x⟫)
    {f u : E} (hu : u - P u = f) : ‖u‖ ≤ ‖f‖ / a := by
  have h := hgap u
  rw [hu] at h
  have hc := real_inner_le_norm u f
  by_cases hu0 : ‖u‖ = 0
  · rw [hu0]
    exact div_nonneg (norm_nonneg f) ha.le
  · have hup : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg u) (Ne.symm hu0)
    apply (le_div_iff₀ ha).2
    nlinarith

theorem poissonSolution_variance_bound (P : E →L[ℝ] E) {a : ℝ} (ha : 0 < a)
    (hgap : ∀ x : E, a * ‖x‖ ^ 2 ≤ ⟪x, x - P x⟫)
    {f u : E} (hu : u - P u = f) :
    2 * ⟪f, u⟫ - ‖f‖ ^ 2 ≤ (2 / a - 1) * ‖f‖ ^ 2 := by
  have hn := norm_poissonSolution_le P ha hgap hu
  have hc := (real_inner_le_norm f u).trans
    (mul_le_mul_of_nonneg_left hn (norm_nonneg f))
  have hi : ‖f‖ * (‖f‖ / a) = ‖f‖ ^ 2 / a := by ring
  rw [hi] at hc
  calc
    2 * ⟪f, u⟫ - ‖f‖ ^ 2 ≤ 2 * (‖f‖ ^ 2 / a) - ‖f‖ ^ 2 := by linarith
    _ = (2 / a - 1) * ‖f‖ ^ 2 := by ring

theorem operator_pow_apply_succ (P : E →L[ℝ] E) (n : ℕ) (x : E) :
    (P ^ n) (P x) = (P ^ (n + 1)) x := by
  rw [pow_succ]
  rfl

/-- Two Poisson solutions turn the covariance into a second difference. -/
theorem poisson_covariance_secondDifference (P : E →L[ℝ] E)
    {f u v : E} (hu : u - P u = f) (hv : v - P v = u) (n : ℕ) :
    ⟪f, (P ^ n) f⟫ =
      ⟪f, (P ^ n) v⟫ - 2 * ⟪f, (P ^ (n + 1)) v⟫ + ⟪f, (P ^ (n + 2)) v⟫ := by
  have hid : (P ^ n) f =
      ((P ^ n) v - (P ^ (n + 1)) v) -
      ((P ^ (n + 1)) v - (P ^ (n + 2)) v) := by
    rw [← hu, map_sub, operator_pow_apply_succ, ← hv]
    simp only [map_sub, operator_pow_apply_succ, Nat.add_assoc]
  rw [hid]
  simp only [inner_sub_right]
  ring

theorem poisson_covariance_remainder_bound (P : E →L[ℝ] E) (hP : ‖P‖ ≤ 1)
    (f v : E) (n : ℕ) : |⟪f, (P ^ n) v⟫| ≤ ‖f‖ * ‖v‖ := by
  have hv : ∀ n : ℕ, ‖(P ^ n) v‖ ≤ ‖v‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ']
      exact ((P.le_opNorm ((P ^ n) v)).trans
        (by simpa using mul_le_mul_of_nonneg_right hP (norm_nonneg ((P ^ n) v)))).trans ih
  exact (abs_real_inner_le_norm f ((P ^ n) v)).trans
    (mul_le_mul_of_nonneg_left (hv n) (norm_nonneg f))

theorem poisson_covariance_limit_eq (P : E →L[ℝ] E)
    {f u v : E} (hu : u - P u = f) (hv : v - P v = u) :
    ⟪f, v⟫ - ⟪f, (P ^ 2) v⟫ = 2 * ⟪f, u⟫ - ‖f‖ ^ 2 := by
  have h0 := poisson_covariance_secondDifference P hu hv 0
  simp only [pow_zero, pow_one, one_apply_eq_self, Nat.zero_add] at h0
  rw [real_inner_self_eq_norm_sq] at h0
  have h1 : ⟪f, u⟫ = ⟪f, v⟫ - ⟪f, P v⟫ := by rw [← hv, inner_sub_right]
  linarith

/-- The resolvent computes the genuine scaled-variance limit whenever the
finite-path covariances are represented by the contraction. -/
theorem scaledSampleVariance_family_tendsto_of_rightGap [CompleteSpace E]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {μ : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
    {X : ∀ n, ℕ → Ω n → ℝ} (hX : ∀ n k, MemLp (X n k) 2 (μ n))
    (P : E →L[ℝ] E) (hP : ‖P‖ ≤ 1) (f : E)
    {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 2)
    (hgap : ∀ x : E, a * ‖x‖ ^ 2 ≤ ⟪x, x - P x⟫)
    (hcov : ∀ n i j, i + j < n →
      covariance (X n i) (X n (i + j)) (μ n) = ⟪f, (P ^ j) f⟫) :
    Tendsto (fun n => scaledSampleVariance (μ n) (X n) n) atTop
      (𝓝 (2 * ⟪f, poissonResolvent P f⟫ - ‖f‖ ^ 2)) := by
  have hL := norm_halfLazyOperator_lt_one P hP ha ha2 hgap
  have hu := poissonResolvent_sub P hL f
  have hv := poissonResolvent_sub P hL (poissonResolvent P f)
  have h := scaledSampleVariance_family_tendsto_of_bounded_secondDifference
    hX hcov (poisson_covariance_secondDifference P hu hv)
    (poisson_covariance_remainder_bound P hP f
      (poissonResolvent P (poissonResolvent P f)))
  simpa only [pow_zero, one_apply_eq_self, poisson_covariance_limit_eq P hu hv] using h

/-- The exact spectral-gap upper bound for the resolvent variance. -/
theorem poissonResolvent_variance_le [CompleteSpace E]
    (P : E →L[ℝ] E) (hP : ‖P‖ ≤ 1) (f : E)
    {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 2)
    (hgap : ∀ x : E, a * ‖x‖ ^ 2 ≤ ⟪x, x - P x⟫) :
    2 * ⟪f, poissonResolvent P f⟫ - ‖f‖ ^ 2 ≤ (2 / a - 1) * ‖f‖ ^ 2 :=
  poissonSolution_variance_bound P ha hgap
    (poissonResolvent_sub P (norm_halfLazyOperator_lt_one P hP ha ha2 hgap) f)

end
end UniformRandomMALA.Concrete
