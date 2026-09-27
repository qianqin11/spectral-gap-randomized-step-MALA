import UniformRandomMALA.Concrete.VarianceSeparationHilbert
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# Positive pairs of reversible covariances

Pairing consecutive covariances avoids assuming positivity of the original
Markov operator. These identities also cover eigenvalues near minus one.
-/

namespace UniformRandomMALA.Concrete

open scoped RealInnerProductSpace

noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def operatorCovariance (P : E →L[ℝ] E) (f : E) (n : ℕ) : ℝ := ⟪f, (P ^ n) f⟫

def operatorCovariancePair (P : E →L[ℝ] E) (f : E) (n : ℕ) : ℝ :=
  operatorCovariance P f (2 * n) + operatorCovariance P f (2 * n + 1)

theorem inner_add_operator_nonneg (P : E →L[ℝ] E) (hP : ‖P‖ ≤ 1) (x : E) :
    0 ≤ ⟪x, x + P x⟫ := by
  simpa using inner_sub_operator_nonneg (-P) (by simpa using hP) x

theorem operator_pow_inner_symm (P : E →L[ℝ] E)
    (hsym : P.toLinearMap.IsSymmetric) (n : ℕ) (x y : E) :
    ⟪(P ^ n) x, y⟫ = ⟪x, (P ^ n) y⟫ := by
  change ⟪(P ^ n).toLinearMap x, y⟫ = ⟪x, (P ^ n).toLinearMap y⟫
  rw [ContinuousLinearMap.toLinearMap_pow]
  exact hsym.pow n x y

theorem operatorCovariance_add (P : E →L[ℝ] E)
    (hsym : P.toLinearMap.IsSymmetric) (f : E) (n m : ℕ) :
    operatorCovariance P f (n + m) = ⟪(P ^ n) f, (P ^ m) f⟫ := by
  rw [operatorCovariance, pow_add]
  exact (operator_pow_inner_symm P hsym n f ((P ^ m) f)).symm

theorem operatorCovariance_even (P : E →L[ℝ] E)
    (hsym : P.toLinearMap.IsSymmetric) (f : E) (n : ℕ) :
    operatorCovariance P f (2 * n) = ‖(P ^ n) f‖ ^ 2 := by
  rw [two_mul, operatorCovariance_add P hsym, real_inner_self_eq_norm_sq]

theorem operatorCovariance_even_antitone (P : E →L[ℝ] E) (hP : ‖P‖ ≤ 1)
    (hsym : P.toLinearMap.IsSymmetric) (f : E) :
    Antitone (fun n => operatorCovariance P f (2 * n)) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [operatorCovariance_even P hsym, operatorCovariance_even P hsym,
    show P ^ (n + 1) = P * P ^ n from pow_succ' P n]
  change ‖P ((P ^ n) f)‖ ^ 2 ≤ ‖(P ^ n) f‖ ^ 2
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
  simpa only [one_mul] using (P.le_opNorm ((P ^ n) f)).trans
    (mul_le_mul_of_nonneg_right hP (norm_nonneg _))

theorem operatorCovariancePair_eq (P : E →L[ℝ] E)
    (hsym : P.toLinearMap.IsSymmetric) (f : E) (n : ℕ) :
    operatorCovariancePair P f n = ⟪(P ^ n) f, (P ^ n) f + P ((P ^ n) f)⟫ := by
  rw [operatorCovariancePair, two_mul, operatorCovariance_add P hsym,
    show n + n + 1 = n + (n + 1) by omega, operatorCovariance_add P hsym,
    pow_succ']
  exact (inner_add_right _ _ _).symm

theorem operatorCovariancePair_nonneg (P : E →L[ℝ] E) (hP : ‖P‖ ≤ 1)
    (hsym : P.toLinearMap.IsSymmetric) (f : E) (n : ℕ) :
    0 ≤ operatorCovariancePair P f n := by
  rw [operatorCovariancePair_eq P hsym]
  exact inner_add_operator_nonneg P hP _

theorem operator_energy_apply_le (P : E →L[ℝ] E) (hP : ‖P‖ ≤ 1)
    (hsym : P.toLinearMap.IsSymmetric) (f : E) :
    ⟪P f, P f - P (P f)⟫ ≤ ⟪f, f - P f⟫ := by
  have h := inner_add_operator_nonneg P hP (f - P f)
  have hs : ⟪P f, P f⟫ = ⟪f, P (P f)⟫ := hsym f (P f)
  have hc : ⟪P f, f⟫ = ⟪f, P f⟫ := real_inner_comm _ _
  simp only [map_sub, inner_add_right, inner_sub_left, inner_sub_right] at h ⊢
  rw [hc, ← hs] at h
  linarith

theorem operator_energy_pow_le (P : E →L[ℝ] E) (hP : ‖P‖ ≤ 1)
    (hsym : P.toLinearMap.IsSymmetric) (f : E) (n : ℕ) :
    ⟪(P ^ n) f, (P ^ n) f - P ((P ^ n) f)⟫ ≤ ⟪f, f - P f⟫ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    exact (operator_energy_apply_le P hP hsym ((P ^ n) f)).trans ih

theorem operator_sqNorm_loss_le (P : E →L[ℝ] E) (f : E) :
    ‖f‖ ^ 2 - ‖P f‖ ^ 2 ≤ 2 * ⟪f, f - P f⟫ := by
  have h := sq_nonneg ‖f - P f‖
  rw [norm_sub_sq_real] at h
  rw [inner_sub_right, real_inner_self_eq_norm_sq]
  linarith

theorem operator_sqNorm_pow_lower (P : E →L[ℝ] E) (hP : ‖P‖ ≤ 1)
    (hsym : P.toLinearMap.IsSymmetric) (f : E) (n : ℕ) :
    ‖f‖ ^ 2 - 2 * n * ⟪f, f - P f⟫ ≤ ‖(P ^ n) f‖ ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := operator_sqNorm_loss_le P ((P ^ n) f)
    have he := operator_energy_pow_le P hP hsym f n
    rw [show P ^ (n + 1) = P * P ^ n from pow_succ' P n]
    change ‖f‖ ^ 2 - 2 * ((n + 1 : ℕ) : ℝ) * ⟪f, f - P f⟫ ≤ ‖P ((P ^ n) f)‖ ^ 2
    simp only [Nat.cast_add, Nat.cast_one]
    nlinarith

/-- A small Rayleigh energy forces a long sequence of positive paired
covariances. This estimate does not require a positive spectral gap. -/
theorem operatorCovariancePair_lower (P : E →L[ℝ] E) (hP : ‖P‖ ≤ 1)
    (hsym : P.toLinearMap.IsSymmetric) (f : E) (n : ℕ) :
    2 * ‖f‖ ^ 2 - (4 * n + 1) * ⟪f, f - P f⟫ ≤
      operatorCovariancePair P f n := by
  have he := operator_energy_pow_le P hP hsym f n
  have hn := operator_sqNorm_pow_lower P hP hsym f n
  rw [operatorCovariancePair_eq P hsym, inner_add_right, real_inner_self_eq_norm_sq]
  rw [inner_sub_right, real_inner_self_eq_norm_sq] at he
  nlinarith

end
end UniformRandomMALA.Concrete
