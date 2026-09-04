import UniformRandomMALA.Constants

/-!
# Arithmetic in the quantitative Gaussian-shift lemma

The analytic input is the integral lower bound obtained from the Mills
estimate.  Everything after that input is order/algebra and is formalized
here.
-/

namespace UniformRandomMALA

noncomputable section

lemma exp_neg_half_over_two_ge_quarter :
    (1 / 4 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) / 2 := by
  have h := Real.add_one_le_exp (-(1 / 2 : ℝ))
  norm_num at h ⊢
  linarith

lemma min_scaled_by_one_plus
    (a s : ℝ) (ha : 0 ≤ a) (hs : 0 ≤ s) :
    min 1 (s * (1 + a)) ≤ (1 + a) * min s 1 := by
  rcases le_total s 1 with hsone | hones
  · rw [min_eq_left hsone]
    have hle : min 1 (s * (1 + a)) ≤ s * (1 + a) := min_le_right _ _
    nlinarith
  · rw [min_eq_right hones]
    have hle : min 1 (s * (1 + a)) ≤ 1 := min_le_left _ _
    nlinarith

lemma sqrt_log_control
    (a ell : ℝ) (ha : 0 ≤ a) (hell : 0 ≤ ell)
    (hle : ell ≤ (1 + a) ^ 2) :
    Real.sqrt ell ≤ 1 + a := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt ell := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt ell) ^ 2 = ell := by
    simpa using Real.sq_sqrt hell
  nlinarith

/--
Last three lines of the proof of `lem:gaussian-shift`, isolated from the
normal-density integration step.
-/
theorem gaussian_shift_arithmetic
    (q a s ell delta : ℝ)
    (hq : 0 ≤ q) (ha : 0 ≤ a) (hs : 0 ≤ s) (hell : 0 ≤ ell)
    (hlog : ell ≤ (1 + a) ^ 2)
    (hintegral :
      q * (Real.exp (-(1 / 2 : ℝ)) / 2) *
          ((1 + a) * min s 1) ≤ delta) :
    q / 4 * min 1 (s * Real.sqrt ell) ≤ delta := by
  have hsqrt : Real.sqrt ell ≤ 1 + a :=
    sqrt_log_control a ell ha hell hlog
  have hsqrt_nonneg : 0 ≤ Real.sqrt ell := Real.sqrt_nonneg _
  have hsmul : s * Real.sqrt ell ≤ s * (1 + a) :=
    mul_le_mul_of_nonneg_left hsqrt hs
  have hminmono :
      min 1 (s * Real.sqrt ell) ≤ min 1 (s * (1 + a)) :=
    min_le_min (le_refl _) hsmul
  have hminbound :
      min 1 (s * Real.sqrt ell) ≤ (1 + a) * min s 1 :=
    le_trans hminmono (min_scaled_by_one_plus a s ha hs)
  have htarget_nonneg : 0 ≤ min 1 (s * Real.sqrt ell) := by
    apply min_nonneg_of_nonneg
    · norm_num
    · positivity
  have hbig_nonneg : 0 ≤ (1 + a) * min s 1 := by
    have hmins : 0 ≤ min s 1 := min_nonneg_of_nonneg hs (by norm_num)
    positivity
  have hcoef := exp_neg_half_over_two_ge_quarter
  have hqcoef : q * (1 / 4 : ℝ) ≤
      q * (Real.exp (-(1 / 2 : ℝ)) / 2) :=
    mul_le_mul_of_nonneg_left hcoef hq
  have hfirst :
      q / 4 * min 1 (s * Real.sqrt ell) ≤
        q * (1 / 4 : ℝ) * ((1 + a) * min s 1) := by
    have hscale : 0 ≤ q * (1 / 4 : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hminbound hscale
    nlinarith
  have hsecond :
      q * (1 / 4 : ℝ) * ((1 + a) * min s 1) ≤
        q * (Real.exp (-(1 / 2 : ℝ)) / 2) *
          ((1 + a) * min s 1) := by
    exact mul_le_mul_of_nonneg_right hqcoef hbig_nonneg
  exact le_trans (le_trans hfirst hsecond) hintegral

end

end UniformRandomMALA
