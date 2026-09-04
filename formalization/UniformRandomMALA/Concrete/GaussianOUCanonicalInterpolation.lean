import UniformRandomMALA.Concrete.GaussianOUCanonicalResidual

/-!
# Canonical Gaussian OU interpolation certificate

This module closes the analytic layer between the pointwise G3 residual and
the integrated Mehler flow.  The first lemmas isolate the joint time/space
chain rule for the canonical square-root field.
-/

namespace UniformRandomMALA.Concrete

open Function Set Metric MeasureTheory Filter ContinuousLinearMap ProbabilityTheory
open scoped Topology NNReal ENNReal ProbabilityTheory BigOperators

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [SecondCountableTopology E]

/-- The nested transition obtained by first following the outer Mehler path
and then the backward Mehler kernel. -/
def nestedGaussianOUTransition (t r : ℝ) (x z w : E) : E :=
  gaussianOUTransition (t - r) (gaussianOUTransition r x z) w

/-- Its derivative with respect to the splitting time. -/
def nestedGaussianOUTransitionTimeDeriv (t r : ℝ) (x z w : E) : E :=
  ouDriftCoeff (t - r) • gaussianOUTransition r x z +
    ouDriftCoeff (t - r) • gaussianOUTransitionTimeDeriv r x z -
    (ouDriftCoeff (t - r) ^ 2 / ouNoiseCoeff (t - r)) • w

theorem hasDerivAt_nestedGaussianOUTransition
    (t r : ℝ) (hr0 : 0 < r) (hrt : r < t) (x z w : E) :
    HasDerivAt (fun s => nestedGaussianOUTransition t s x z w)
      (nestedGaussianOUTransitionTimeDeriv t r x z w) r := by
  let lag : ℝ → ℝ := fun s => t - s
  have hlag : HasDerivAt lag (-1) r := by
    convert (hasDerivAt_const r t).sub (hasDerivAt_id r) using 1 <;>
      first | rfl | norm_num
  have ha := (hasDerivAt_ouDriftCoeff (t - r)).scomp r hlag
  have hb := (hasDerivAt_ouNoiseCoeff (sub_pos.2 hrt)).scomp r hlag
  have hy := hasDerivAt_gaussianOUTransition_time hr0 x z
  have hfirst := ha.smul hy
  have hsecond := hb.smul_const w
  have h := hfirst.add hsecond
  convert h using 1
  · funext s
    simp [nestedGaussianOUTransition, gaussianOUTransition, lag]
  · simp [nestedGaussianOUTransitionTimeDeriv, gaussianOUTransition, lag]
    module

theorem ouDriftCoeff_le_one {r : ℝ} (hr : 0 ≤ r) :
    ouDriftCoeff r ≤ 1 := by
  unfold ouDriftCoeff
  rw [Real.exp_le_one_iff]
  linarith

theorem ouNoiseCoeff_pos {r : ℝ} (hr : 0 < r) :
    0 < ouNoiseCoeff r := by
  change 0 < Real.sqrt (bobkovVarianceCoeff r)
  exact Real.sqrt_pos.2 (bobkovVarianceCoeff_pos hr)

def stdGaussianFirstMoment (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [SecondCountableTopology E] : ℝ :=
  ∫ x, ‖x‖ ∂stdGaussian E

theorem stdGaussianFirstMoment_nonneg :
    0 ≤ stdGaussianFirstMoment E :=
  integral_nonneg fun _ => norm_nonneg _

theorem normalProfile_endpoint_le
    {ε u : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hu : u ∈ Icc ε (1 - ε)) :
    normalProfile ε ≤ normalProfile u := by
  have hεIoo : ε ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith
  have h1εIoo : 1 - ε ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith
  have hmin := strictConcaveOn_normalProfile.concaveOn.min_le_of_mem_Icc
    hεIoo h1εIoo hu
  rw [normalProfile_one_sub hεIoo, min_self] at hmin
  exact hmin

theorem abs_deriv_normalProfile_le_endpointMax
    {ε u : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hu : u ∈ Icc ε (1 - ε)) :
    |deriv normalProfile u| ≤
      max |lowerQuantile standardGaussianMeasure ε|
        |lowerQuantile standardGaussianMeasure (1 - ε)| := by
  have hεIoo : ε ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith
  have h1εIoo : 1 - ε ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith
  have huIoo : u ∈ Ioo (0 : ℝ) 1 :=
    ⟨hε.trans_le hu.1, hu.2.trans_lt h1εIoo.2⟩
  have hlo := lowerQuantile_mono standardGaussianMeasure hu.1
    huIoo.2 hεIoo.1
  have hhi := lowerQuantile_mono standardGaussianMeasure hu.2
    h1εIoo.2 huIoo.1
  rw [deriv_normalProfile huIoo, abs_neg]
  apply abs_le.2
  constructor
  · calc
      -max |lowerQuantile standardGaussianMeasure ε|
          |lowerQuantile standardGaussianMeasure (1 - ε)| ≤
          -|lowerQuantile standardGaussianMeasure ε| :=
        neg_le_neg (le_max_left _ _)
      _ ≤ lowerQuantile standardGaussianMeasure ε := neg_abs_le _
      _ ≤ lowerQuantile standardGaussianMeasure u := hlo
  · exact hhi.trans ((le_abs_self _).trans (le_max_right _ _))

theorem inv_bobkovRadius_le_inv_endpoint
    {ε u c : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hu : u ∈ Icc ε (1 - ε)) (hc : 0 ≤ c)
    (v : E) :
    (Real.sqrt (normalProfile u ^ 2 + c * ‖v‖ ^ 2))⁻¹ ≤
      (normalProfile ε)⁻¹ := by
  have huIoo : u ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hu.1, hu.2]
  have hεIoo : ε ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith
  have hIε : 0 < normalProfile ε := normalProfile_pos hεIoo
  have hIu : 0 < normalProfile u := normalProfile_pos huIoo
  have hIle := normalProfile_endpoint_le hε hεhalf hu
  have hrad : 0 < normalProfile u ^ 2 + c * ‖v‖ ^ 2 := by
    nlinarith [mul_nonneg hc (sq_nonneg ‖v‖)]
  have hroot : normalProfile u ≤
      Real.sqrt (normalProfile u ^ 2 + c * ‖v‖ ^ 2) := by
    have hsqrtSq := Real.sq_sqrt hrad.le
    have hsqrt0 := Real.sqrt_nonneg
      (normalProfile u ^ 2 + c * ‖v‖ ^ 2)
    nlinarith [mul_nonneg hc (sq_nonneg ‖v‖)]
  exact (inv_le_inv₀ (Real.sqrt_pos.2 hrad) hIε).2 (hIle.trans hroot)

/-- Uniform coefficient estimate once the Mehler time is bounded away from
zero.  The deliberately coarse reciprocal bound is convenient for Gaussian
domination. -/
theorem ouTransitionTimeCoeff_le_inv_noise
    {δ r : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r) :
    |ouDriftCoeff r ^ 2 / ouNoiseCoeff r| ≤
      (ouNoiseCoeff δ)⁻¹ := by
  have hr : 0 < r := hδ.trans_le hδr
  have ha0 : 0 ≤ ouDriftCoeff r := (ouDriftCoeff_pos r).le
  have ha1 : ouDriftCoeff r ≤ 1 := ouDriftCoeff_le_one hr.le
  have hbδ : 0 < ouNoiseCoeff δ := ouNoiseCoeff_pos hδ
  have hbr : 0 < ouNoiseCoeff r := ouNoiseCoeff_pos hr
  have hbmono : ouNoiseCoeff δ ≤ ouNoiseCoeff r :=
    monotone_ouNoiseCoeff_on_nonneg hδ.le hr.le hδr
  rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hbr.le)]
  calc
    ouDriftCoeff r ^ 2 / ouNoiseCoeff r ≤
        1 / ouNoiseCoeff r := by
      apply div_le_div_of_nonneg_right _ hbr.le
      nlinarith
    _ ≤ 1 / ouNoiseCoeff δ := one_div_le_one_div_of_le hbδ hbmono
    _ = (ouNoiseCoeff δ)⁻¹ := one_div _

theorem norm_gaussianOUTransition_le_add
    {r : ℝ} (hr : 0 ≤ r) (x z : E) :
    ‖gaussianOUTransition r x z‖ ≤ ‖x‖ + ‖z‖ := by
  have ha0 : 0 ≤ ouDriftCoeff r := (ouDriftCoeff_pos r).le
  have ha1 : ouDriftCoeff r ≤ 1 := ouDriftCoeff_le_one hr
  have hb0 : 0 ≤ ouNoiseCoeff r := ouNoiseCoeff_nonneg r
  have hb1 : ouNoiseCoeff r ≤ 1 := by
    have hsumsq := ouDriftCoeff_sq_add_ouNoiseCoeff_sq hr
    nlinarith [sq_nonneg (ouDriftCoeff r), sq_nonneg (ouNoiseCoeff r)]
  unfold gaussianOUTransition
  calc
    ‖ouDriftCoeff r • x + ouNoiseCoeff r • z‖ ≤
        ‖ouDriftCoeff r • x‖ + ‖ouNoiseCoeff r • z‖ := norm_add_le _ _
    _ = ouDriftCoeff r * ‖x‖ + ouNoiseCoeff r * ‖z‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ha0, abs_of_nonneg hb0]
    _ ≤ 1 * ‖x‖ + 1 * ‖z‖ := add_le_add
      (mul_le_mul_of_nonneg_right ha1 (norm_nonneg x))
      (mul_le_mul_of_nonneg_right hb1 (norm_nonneg z))
    _ = ‖x‖ + ‖z‖ := by ring

theorem norm_gaussianOUTransitionTimeDeriv_le
    {δ r : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r) (x z : E) :
    ‖gaussianOUTransitionTimeDeriv r x z‖ ≤
      ‖x‖ + (ouNoiseCoeff δ)⁻¹ * ‖z‖ := by
  have hr : 0 ≤ r := (hδ.trans_le hδr).le
  have ha : |ouDriftCoeff r| ≤ 1 := by
    rw [abs_of_pos (ouDriftCoeff_pos r)]
    exact ouDriftCoeff_le_one hr
  have hk := ouTransitionTimeCoeff_le_inv_noise hδ hδr
  unfold gaussianOUTransitionTimeDeriv
  calc
    ‖(-ouDriftCoeff r) • x +
        (ouDriftCoeff r ^ 2 / ouNoiseCoeff r) • z‖ ≤
        ‖(-ouDriftCoeff r) • x‖ +
          ‖(ouDriftCoeff r ^ 2 / ouNoiseCoeff r) • z‖ := norm_add_le _ _
    _ = |ouDriftCoeff r| * ‖x‖ +
        |ouDriftCoeff r ^ 2 / ouNoiseCoeff r| * ‖z‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_neg]
    _ ≤ 1 * ‖x‖ + (ouNoiseCoeff δ)⁻¹ * ‖z‖ := add_le_add
      (mul_le_mul_of_nonneg_right ha (norm_nonneg x))
      (mul_le_mul_of_nonneg_right hk (norm_nonneg z))
    _ = ‖x‖ + (ouNoiseCoeff δ)⁻¹ * ‖z‖ := by ring

theorem norm_nestedGaussianOUTransitionTimeDeriv_le
    {t r δ₀ δ₁ : ℝ} (hδ₀ : 0 < δ₀) (hδ₀r : δ₀ ≤ r)
    (hδ₁ : 0 < δ₁) (hδ₁r : δ₁ ≤ t - r) (x z w : E) :
    ‖nestedGaussianOUTransitionTimeDeriv t r x z w‖ ≤
      2 * ‖x‖ + (1 + (ouNoiseCoeff δ₀)⁻¹) * ‖z‖ +
        (ouNoiseCoeff δ₁)⁻¹ * ‖w‖ := by
  have hr : 0 ≤ r := (hδ₀.trans_le hδ₀r).le
  have hlag : 0 ≤ t - r := (hδ₁.trans_le hδ₁r).le
  have ha0 : 0 ≤ ouDriftCoeff (t - r) := (ouDriftCoeff_pos (t - r)).le
  have ha1 : ouDriftCoeff (t - r) ≤ 1 := ouDriftCoeff_le_one hlag
  have hk := ouTransitionTimeCoeff_le_inv_noise hδ₁ hδ₁r
  have hy := norm_gaussianOUTransition_le_add hr x z
  have hv := norm_gaussianOUTransitionTimeDeriv_le hδ₀ hδ₀r x z
  unfold nestedGaussianOUTransitionTimeDeriv
  calc
    ‖ouDriftCoeff (t - r) • gaussianOUTransition r x z +
          ouDriftCoeff (t - r) • gaussianOUTransitionTimeDeriv r x z -
          (ouDriftCoeff (t - r) ^ 2 / ouNoiseCoeff (t - r)) • w‖ ≤
        ‖ouDriftCoeff (t - r) • gaussianOUTransition r x z‖ +
          ‖ouDriftCoeff (t - r) • gaussianOUTransitionTimeDeriv r x z‖ +
          ‖(ouDriftCoeff (t - r) ^ 2 / ouNoiseCoeff (t - r)) • w‖ := by
      exact (norm_sub_le _ _).trans
        (add_le_add (norm_add_le _ _) (le_refl _))
    _ = ouDriftCoeff (t - r) * ‖gaussianOUTransition r x z‖ +
          ouDriftCoeff (t - r) * ‖gaussianOUTransitionTimeDeriv r x z‖ +
          |ouDriftCoeff (t - r) ^ 2 / ouNoiseCoeff (t - r)| * ‖w‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha0]
    _ ≤ 1 * (‖x‖ + ‖z‖) +
          1 * (‖x‖ + (ouNoiseCoeff δ₀)⁻¹ * ‖z‖) +
          (ouNoiseCoeff δ₁)⁻¹ * ‖w‖ := by
      gcongr
    _ = 2 * ‖x‖ + (1 + (ouNoiseCoeff δ₀)⁻¹) * ‖z‖ +
          (ouNoiseCoeff δ₁)⁻¹ * ‖w‖ := by ring

theorem norm_integral_nestedGaussianOUDeriv_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (Dg : BoundedContinuousFunction E (E →L[ℝ] F))
    {t r δ₀ δ₁ : ℝ} (hδ₀ : 0 < δ₀) (hδ₀r : δ₀ ≤ r)
    (hδ₁ : 0 < δ₁) (hδ₁r : δ₁ ≤ t - r) (x z : E) :
    ‖∫ w, Dg (nestedGaussianOUTransition t r x z w)
        (nestedGaussianOUTransitionTimeDeriv t r x z w)
        ∂stdGaussian E‖ ≤
      ‖Dg‖ * (2 * ‖x‖ + (1 + (ouNoiseCoeff δ₀)⁻¹) * ‖z‖ +
        (ouNoiseCoeff δ₁)⁻¹ * stdGaussianFirstMoment E) := by
  let A : ℝ := 2 * ‖x‖ + (1 + (ouNoiseCoeff δ₀)⁻¹) * ‖z‖
  let K : ℝ := (ouNoiseCoeff δ₁)⁻¹
  let B : E → ℝ := fun w => ‖Dg‖ * (A + K * ‖w‖)
  have hnorm : Integrable (fun w : E => ‖w‖) (stdGaussian E) :=
    IsGaussian.integrable_id.norm
  have hBint : Integrable B (stdGaussian E) :=
    ((integrable_const A).add (hnorm.const_mul K)).const_mul ‖Dg‖
  calc
    ‖∫ w, Dg (nestedGaussianOUTransition t r x z w)
        (nestedGaussianOUTransitionTimeDeriv t r x z w)
        ∂stdGaussian E‖ ≤ ∫ w, B w ∂stdGaussian E := by
      apply norm_integral_le_of_norm_le hBint
      exact Filter.Eventually.of_forall fun w => by
        calc
          ‖Dg (nestedGaussianOUTransition t r x z w)
              (nestedGaussianOUTransitionTimeDeriv t r x z w)‖ ≤
              ‖Dg (nestedGaussianOUTransition t r x z w)‖ *
                ‖nestedGaussianOUTransitionTimeDeriv t r x z w‖ :=
            (Dg _).le_opNorm _
          _ ≤ ‖Dg‖ * ‖nestedGaussianOUTransitionTimeDeriv t r x z w‖ :=
            mul_le_mul_of_nonneg_right (Dg.norm_coe_le_norm _)
              (norm_nonneg _)
          _ ≤ ‖Dg‖ * (2 * ‖x‖ +
                (1 + (ouNoiseCoeff δ₀)⁻¹) * ‖z‖ +
                (ouNoiseCoeff δ₁)⁻¹ * ‖w‖) :=
            mul_le_mul_of_nonneg_left
              (norm_nestedGaussianOUTransitionTimeDeriv_le
                hδ₀ hδ₀r hδ₁ hδ₁r x z w) (norm_nonneg Dg)
          _ = B w := rfl
    _ = ‖Dg‖ * (2 * ‖x‖ + (1 + (ouNoiseCoeff δ₀)⁻¹) * ‖z‖ +
        (ouNoiseCoeff δ₁)⁻¹ * stdGaussianFirstMoment E) := by
      dsimp only [B]
      rw [integral_const_mul]
      change ‖Dg‖ * (∫ w : E, A + K * ‖w‖ ∂stdGaussian E) =
        ‖Dg‖ * (A + K * stdGaussianFirstMoment E)
      rw [integral_add (integrable_const A) (hnorm.const_mul K),
        integral_const_mul]
      simp [stdGaussianFirstMoment]

/-- Total derivative of the backward OU value along an outer Mehler
trajectory.  The proof differentiates the explicit nested Gaussian integral
and uses a first-moment Gaussian dominator. -/
theorem hasDerivAt_backwardGaussianOUValueBCF_transition
    (t r : ℝ) (hr0 : 0 < r) (hrt : r < t)
    (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (hDf : ∀ y, HasFDerivAt f (Df y) y) (x z : E) :
    HasDerivAt
      (fun s => backwardGaussianOUValueBCF t s f
        (gaussianOUTransition s x z))
      (backwardGaussianOUValueTimeDeriv t r Df
          (gaussianOUTransition r x z) +
        backwardGaussianOUDerivBCF t r Df
          (gaussianOUTransition r x z)
          (gaussianOUTransitionTimeDeriv r x z)) r := by
  let δ₀ : ℝ := r / 2
  let δ₁ : ℝ := (t - r) / 2
  let U : Set ℝ := Ioo δ₀ (t - δ₁)
  let B : E → ℝ := fun w => ‖Df‖ *
    (2 * ‖x‖ + (1 + (ouNoiseCoeff δ₀)⁻¹) * ‖z‖ +
      (ouNoiseCoeff δ₁)⁻¹ * ‖w‖)
  have hδ₀ : 0 < δ₀ := by dsimp [δ₀]; linarith
  have hδ₁ : 0 < δ₁ := by dsimp [δ₁]; linarith
  have hU : U ∈ nhds r := by
    apply Ioo_mem_nhds
    · dsimp [U, δ₀]
      linarith
    · dsimp [U, δ₁]
      linarith
  have hBint : Integrable B (stdGaussian E) := by
    have hnorm : Integrable (fun w : E => ‖w‖) (stdGaussian E) :=
      IsGaussian.integrable_id.norm
    exact ((integrable_const
      (2 * ‖x‖ + (1 + (ouNoiseCoeff δ₀)⁻¹) * ‖z‖)).add
        (hnorm.const_mul (ouNoiseCoeff δ₁)⁻¹)).const_mul ‖Df‖
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := stdGaussian E)
    (F := fun s w => f (nestedGaussianOUTransition t s x z w))
    (F' := fun s w => Df (nestedGaussianOUTransition t s x z w)
      (nestedGaussianOUTransitionTimeDeriv t s x z w))
    (bound := B) hU
  have hresult : HasDerivAt
      (fun s => ∫ w, f (nestedGaussianOUTransition t s x z w)
        ∂stdGaussian E)
      (∫ w, Df (nestedGaussianOUTransition t r x z w)
        (nestedGaussianOUTransitionTimeDeriv t r x z w)
        ∂stdGaussian E) r := by
    apply (hmain ?_ ?_ ?_ ?_ hBint ?_).2
    · exact Filter.Eventually.of_forall fun s =>
        (f.continuous.comp (by
          unfold nestedGaussianOUTransition gaussianOUTransition
          fun_prop)).aestronglyMeasurable
    · refine Integrable.of_bound
        (f.continuous.comp (by
          unfold nestedGaussianOUTransition gaussianOUTransition
          fun_prop)).aestronglyMeasurable ‖f‖ ?_
      exact Filter.Eventually.of_forall fun w => f.norm_coe_le_norm _
    · exact (show Continuous (fun w : E =>
          Df (nestedGaussianOUTransition t r x z w)
            (nestedGaussianOUTransitionTimeDeriv t r x z w)) by
        unfold nestedGaussianOUTransition
          nestedGaussianOUTransitionTimeDeriv gaussianOUTransition
          gaussianOUTransitionTimeDeriv
        fun_prop).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun w s hs => by
        have hsδ₀ : δ₀ ≤ s := hs.1.le
        have hsδ₁ : δ₁ ≤ t - s := by linarith [hs.2]
        calc
          ‖Df (nestedGaussianOUTransition t s x z w)
              (nestedGaussianOUTransitionTimeDeriv t s x z w)‖ ≤
              ‖Df (nestedGaussianOUTransition t s x z w)‖ *
                ‖nestedGaussianOUTransitionTimeDeriv t s x z w‖ :=
            (Df (nestedGaussianOUTransition t s x z w)).le_opNorm _
          _ ≤ ‖Df‖ *
                ‖nestedGaussianOUTransitionTimeDeriv t s x z w‖ :=
            mul_le_mul_of_nonneg_right (Df.norm_coe_le_norm _)
              (norm_nonneg _)
          _ ≤ ‖Df‖ *
              (2 * ‖x‖ + (1 + (ouNoiseCoeff δ₀)⁻¹) * ‖z‖ +
                (ouNoiseCoeff δ₁)⁻¹ * ‖w‖) :=
            mul_le_mul_of_nonneg_left
              (norm_nestedGaussianOUTransitionTimeDeriv_le
                hδ₀ hsδ₀ hδ₁ hsδ₁ x z w) (norm_nonneg Df)
          _ = B w := rfl
    · exact Filter.Eventually.of_forall fun w s hs => by
        exact (hDf _).comp_hasDerivAt s
          (hasDerivAt_nestedGaussianOUTransition t s
            (hδ₀.trans_le hs.1.le) (by linarith [hs.2]) x z w)
  have hfun :
      (fun s => backwardGaussianOUValueBCF t s f
        (gaussianOUTransition s x z)) =
      (fun s => ∫ w, f (nestedGaussianOUTransition t s x z w)
        ∂stdGaussian E) := by
    funext s
    rfl
  rw [hfun]
  apply hresult.congr_deriv
  let y := gaussianOUTransition r x z
  let yp := gaussianOUTransitionTimeDeriv r x z
  let a := ouDriftCoeff (t - r)
  have hlag : 0 < t - r := sub_pos.2 hrt
  have hvelInt := integrable_boundedCovector_gaussianOUTransitionTimeDeriv
    hlag Df y
  have hdirInt : Integrable (fun w =>
      Df (gaussianOUTransition (t - r) y w) (a • yp))
      (stdGaussian E) := by
    refine Integrable.of_bound
      (show Continuous (fun w =>
          Df (gaussianOUTransition (t - r) y w) (a • yp)) by
        unfold gaussianOUTransition
        fun_prop).aestronglyMeasurable (‖Df‖ * ‖a • yp‖) ?_
    exact Filter.Eventually.of_forall fun w =>
      (Df _).le_opNorm _ |>.trans
        (mul_le_mul_of_nonneg_right (Df.norm_coe_le_norm _)
          (norm_nonneg _))
  have hDfInt : Integrable (fun w =>
      Df (gaussianOUTransition (t - r) y w)) (stdGaussian E) := by
    refine Integrable.of_bound
      (Df.continuous.comp (by
        unfold gaussianOUTransition
        fun_prop)).aestronglyMeasurable ‖Df‖ ?_
    exact Filter.Eventually.of_forall fun w => Df.norm_coe_le_norm _
  have hdirEq :
      (a • ∫ w, Df (gaussianOUTransition (t - r) y w)
          ∂stdGaussian E) yp =
        ∫ w, Df (gaussianOUTransition (t - r) y w) (a • yp)
          ∂stdGaussian E := by
    rw [smul_apply, ContinuousLinearMap.integral_apply hDfInt]
    change a * (∫ w, Df (gaussianOUTransition (t - r) y w) yp
      ∂stdGaussian E) = _
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun w => by
      change a * Df (gaussianOUTransition (t - r) y w) yp =
        Df (gaussianOUTransition (t - r) y w) (a • yp)
      simp only [map_smul, smul_eq_mul]
  have hpoint (w : E) :
      nestedGaussianOUTransitionTimeDeriv t r x z w =
        -gaussianOUTransitionTimeDeriv (t - r) y w + a • yp := by
    simp [nestedGaussianOUTransitionTimeDeriv,
      gaussianOUTransitionTimeDeriv, y, yp, a]
    module
  rw [backwardGaussianOUValueTimeDeriv,
    backwardGaussianOUDerivBCF_apply]
  symm
  change
    -∫ w, Df (gaussianOUTransition (t - r) y w)
        (gaussianOUTransitionTimeDeriv (t - r) y w) ∂stdGaussian E +
      (a • ∫ w, Df (gaussianOUTransition (t - r) y w)
        ∂stdGaussian E) yp = _
  rw [hdirEq]
  rw [← integral_neg]
  have hnegInt : Integrable (fun w =>
      -Df (gaussianOUTransition (t - r) y w)
        (gaussianOUTransitionTimeDeriv (t - r) y w))
      (stdGaussian E) := hvelInt.neg
  rw [← integral_add hnegInt hdirInt]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun w => by
    change
      -Df (gaussianOUTransition (t - r) y w)
          (gaussianOUTransitionTimeDeriv (t - r) y w) +
        Df (gaussianOUTransition (t - r) y w) (a • yp) =
      Df (nestedGaussianOUTransition t r x z w)
        (nestedGaussianOUTransitionTimeDeriv t r x z w)
    rw [hpoint]
    change
      -Df (gaussianOUTransition (t - r) y w)
          (gaussianOUTransitionTimeDeriv (t - r) y w) +
        Df (gaussianOUTransition (t - r) y w) (a • yp) =
      Df (gaussianOUTransition (t - r) y w)
        (-gaussianOUTransitionTimeDeriv (t - r) y w + a • yp)
    simp only [map_add, map_neg, map_smul, smul_eq_mul]

/-- Banach-valued form of differentiation through a nested Mehler kernel. -/
theorem hasDerivAt_gaussianOUAverage_nested
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (t r : ℝ) (hr0 : 0 < r) (hrt : r < t)
    (g : BoundedContinuousFunction E F)
    (Dg : BoundedContinuousFunction E (E →L[ℝ] F))
    (hDg : ∀ y, HasFDerivAt g (Dg y) y) (x z : E) :
    HasDerivAt
      (fun s => ∫ w, g (nestedGaussianOUTransition t s x z w)
        ∂stdGaussian E)
      (∫ w, Dg (nestedGaussianOUTransition t r x z w)
        (nestedGaussianOUTransitionTimeDeriv t r x z w)
        ∂stdGaussian E) r := by
  let δ₀ : ℝ := r / 2
  let δ₁ : ℝ := (t - r) / 2
  let U : Set ℝ := Ioo δ₀ (t - δ₁)
  let B : E → ℝ := fun w => ‖Dg‖ *
    (2 * ‖x‖ + (1 + (ouNoiseCoeff δ₀)⁻¹) * ‖z‖ +
      (ouNoiseCoeff δ₁)⁻¹ * ‖w‖)
  have hδ₀ : 0 < δ₀ := by dsimp [δ₀]; linarith
  have hδ₁ : 0 < δ₁ := by dsimp [δ₁]; linarith
  have hU : U ∈ nhds r := by
    apply Ioo_mem_nhds
    · dsimp [U, δ₀]
      linarith
    · dsimp [U, δ₁]
      linarith
  have hBint : Integrable B (stdGaussian E) := by
    have hnorm : Integrable (fun w : E => ‖w‖) (stdGaussian E) :=
      IsGaussian.integrable_id.norm
    exact ((integrable_const
      (2 * ‖x‖ + (1 + (ouNoiseCoeff δ₀)⁻¹) * ‖z‖)).add
        (hnorm.const_mul (ouNoiseCoeff δ₁)⁻¹)).const_mul ‖Dg‖
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := stdGaussian E)
    (F := fun s w => g (nestedGaussianOUTransition t s x z w))
    (F' := fun s w => Dg (nestedGaussianOUTransition t s x z w)
      (nestedGaussianOUTransitionTimeDeriv t s x z w))
    (bound := B) hU
  apply (hmain ?_ ?_ ?_ ?_ hBint ?_).2
  · exact Filter.Eventually.of_forall fun s =>
      (g.continuous.comp (by
        unfold nestedGaussianOUTransition gaussianOUTransition
        fun_prop)).aestronglyMeasurable
  · refine Integrable.of_bound
      (g.continuous.comp (by
        unfold nestedGaussianOUTransition gaussianOUTransition
        fun_prop)).aestronglyMeasurable ‖g‖ ?_
    exact Filter.Eventually.of_forall fun w => g.norm_coe_le_norm _
  · exact (show Continuous (fun w : E =>
        Dg (nestedGaussianOUTransition t r x z w)
          (nestedGaussianOUTransitionTimeDeriv t r x z w)) by
      unfold nestedGaussianOUTransition
        nestedGaussianOUTransitionTimeDeriv gaussianOUTransition
        gaussianOUTransitionTimeDeriv
      fun_prop).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun w s hs => by
      have hsδ₀ : δ₀ ≤ s := hs.1.le
      have hsδ₁ : δ₁ ≤ t - s := by linarith [hs.2]
      calc
        ‖Dg (nestedGaussianOUTransition t s x z w)
            (nestedGaussianOUTransitionTimeDeriv t s x z w)‖ ≤
            ‖Dg (nestedGaussianOUTransition t s x z w)‖ *
              ‖nestedGaussianOUTransitionTimeDeriv t s x z w‖ :=
          (Dg (nestedGaussianOUTransition t s x z w)).le_opNorm _
        _ ≤ ‖Dg‖ * ‖nestedGaussianOUTransitionTimeDeriv t s x z w‖ :=
          mul_le_mul_of_nonneg_right (Dg.norm_coe_le_norm _)
            (norm_nonneg _)
        _ ≤ ‖Dg‖ *
            (2 * ‖x‖ + (1 + (ouNoiseCoeff δ₀)⁻¹) * ‖z‖ +
              (ouNoiseCoeff δ₁)⁻¹ * ‖w‖) :=
          mul_le_mul_of_nonneg_left
            (norm_nestedGaussianOUTransitionTimeDeriv_le
              hδ₀ hsδ₀ hδ₁ hsδ₁ x z w) (norm_nonneg Dg)
        _ = B w := rfl
  · exact Filter.Eventually.of_forall fun w s hs =>
      (hDg _).comp_hasDerivAt s
        (hasDerivAt_nestedGaussianOUTransition t s
          (hδ₀.trans_le hs.1.le) (by linarith [hs.2]) x z w)

/-- Total derivative of the backward Riesz gradient along an outer Mehler
trajectory. -/
theorem hasDerivAt_backwardGaussianOURieszGradientBCF_transition
    (t r : ℝ) (hr0 : 0 < r) (hrt : r < t)
    (Gf : BoundedContinuousFunction E E)
    (Hf : BoundedContinuousFunction E (E →L[ℝ] E))
    (hHf : ∀ y, HasFDerivAt Gf (Hf y) y) (x z : E) :
    HasDerivAt
      (fun s => backwardGaussianOURieszGradientBCF t s Gf
        (gaussianOUTransition s x z))
      (backwardGaussianOURieszGradientTimeDeriv t r Gf Hf
          (gaussianOUTransition r x z) +
        backwardGaussianOURieszHessianBCF t r Hf
          (gaussianOUTransition r x z)
          (gaussianOUTransitionTimeDeriv r x z)) r := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  let y := gaussianOUTransition r x z
  let yp := gaussianOUTransitionTimeDeriv r x z
  let a := ouDriftCoeff (t - r)
  have hlag : 0 < t - r := sub_pos.2 hrt
  have havg := hasDerivAt_gaussianOUAverage_nested
    t r hr0 hrt Gf Hf hHf x z
  have hlagMap : HasDerivAt (fun s : ℝ => t - s) (-1) r := by
    convert (hasDerivAt_const r t).sub (hasDerivAt_id r) using 1 <;>
      first | rfl | norm_num
  have ha := (hasDerivAt_ouDriftCoeff (t - r)).scomp r hlagMap
  have hprod := ha.smul havg
  have hfun :
      (fun s => backwardGaussianOURieszGradientBCF t s Gf
        (gaussianOUTransition s x z)) =
      (fun s => ouDriftCoeff (t - s) •
        ∫ w, Gf (nestedGaussianOUTransition t s x z w)
          ∂stdGaussian E) := by
    funext s
    rfl
  rw [hfun]
  apply hprod.congr_deriv
  have hvelInt : Integrable (fun w =>
      Hf (gaussianOUTransition (t - r) y w)
        (gaussianOUTransitionTimeDeriv (t - r) y w))
      (stdGaussian E) := by
    let K : ℝ := (ouNoiseCoeff (t - r))⁻¹
    let C : E → ℝ := fun w => ‖Hf‖ * (‖y‖ + K * ‖w‖)
    have hCint : Integrable C (stdGaussian E) := by
      have hnorm : Integrable (fun w : E => ‖w‖) (stdGaussian E) :=
        IsGaussian.integrable_id.norm
      exact ((integrable_const ‖y‖).add (hnorm.const_mul K)).const_mul ‖Hf‖
    apply hCint.mono'
    · exact (show Continuous (fun w =>
          Hf (gaussianOUTransition (t - r) y w)
            (gaussianOUTransitionTimeDeriv (t - r) y w)) by
        unfold gaussianOUTransition gaussianOUTransitionTimeDeriv
        fun_prop).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun w => by
        calc
          ‖Hf (gaussianOUTransition (t - r) y w)
              (gaussianOUTransitionTimeDeriv (t - r) y w)‖ ≤
              ‖Hf (gaussianOUTransition (t - r) y w)‖ *
                ‖gaussianOUTransitionTimeDeriv (t - r) y w‖ :=
            (Hf _).le_opNorm _
          _ ≤ ‖Hf‖ * ‖gaussianOUTransitionTimeDeriv (t - r) y w‖ :=
            mul_le_mul_of_nonneg_right (Hf.norm_coe_le_norm _)
              (norm_nonneg _)
          _ ≤ ‖Hf‖ * (‖y‖ + K * ‖w‖) :=
            mul_le_mul_of_nonneg_left
              (norm_gaussianOUTransitionTimeDeriv_le hlag le_rfl y w)
              (norm_nonneg Hf)
          _ = C w := rfl
  have hHInt : Integrable (fun w =>
      Hf (gaussianOUTransition (t - r) y w)) (stdGaussian E) := by
    refine Integrable.of_bound
      (Hf.continuous.comp (by
        unfold gaussianOUTransition
        fun_prop)).aestronglyMeasurable ‖Hf‖ ?_
    exact Filter.Eventually.of_forall fun w => Hf.norm_coe_le_norm _
  have hdirInt : Integrable (fun w =>
      Hf (gaussianOUTransition (t - r) y w) (a • yp))
      (stdGaussian E) := by
    refine Integrable.of_bound
      (show Continuous (fun w =>
          Hf (gaussianOUTransition (t - r) y w) (a • yp)) by
        unfold gaussianOUTransition
        fun_prop).aestronglyMeasurable (‖Hf‖ * ‖a • yp‖) ?_
    exact Filter.Eventually.of_forall fun w =>
      (Hf _).le_opNorm _ |>.trans
        (mul_le_mul_of_nonneg_right (Hf.norm_coe_le_norm _)
          (norm_nonneg _))
  have hdirEq :
      (a • ∫ w, Hf (gaussianOUTransition (t - r) y w)
          ∂stdGaussian E) yp =
        ∫ w, Hf (gaussianOUTransition (t - r) y w) (a • yp)
          ∂stdGaussian E := by
    rw [smul_apply, ContinuousLinearMap.integral_apply hHInt]
    change a • (∫ w, Hf (gaussianOUTransition (t - r) y w) yp
      ∂stdGaussian E) = _
    rw [← integral_smul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun w => by
      change a • Hf (gaussianOUTransition (t - r) y w) yp =
        Hf (gaussianOUTransition (t - r) y w) (a • yp)
      rw [map_smul]
  have hdirEq2 :
      (a ^ 2 • ∫ w, Hf (gaussianOUTransition (t - r) y w)
          ∂stdGaussian E) yp =
        a • ∫ w, Hf (gaussianOUTransition (t - r) y w) (a • yp)
          ∂stdGaussian E := by
    calc
      (a ^ 2 • ∫ w, Hf (gaussianOUTransition (t - r) y w)
          ∂stdGaussian E) yp =
          a • ((a • ∫ w, Hf (gaussianOUTransition (t - r) y w)
            ∂stdGaussian E) yp) := by
        simp [pow_two, smul_smul, smul_apply]
      _ = _ := congrArg (fun q : E => a • q) hdirEq
  have hpoint (w : E) :
      nestedGaussianOUTransitionTimeDeriv t r x z w =
        -gaussianOUTransitionTimeDeriv (t - r) y w + a • yp := by
    simp [nestedGaussianOUTransitionTimeDeriv,
      gaussianOUTransitionTimeDeriv, y, yp, a]
    module
  have hsplit :
      (∫ w, Hf (nestedGaussianOUTransition t r x z w)
          (nestedGaussianOUTransitionTimeDeriv t r x z w)
          ∂stdGaussian E) =
        -(∫ w, Hf (gaussianOUTransition (t - r) y w)
          (gaussianOUTransitionTimeDeriv (t - r) y w)
          ∂stdGaussian E) +
        ∫ w, Hf (gaussianOUTransition (t - r) y w) (a • yp)
          ∂stdGaussian E := by
    rw [← integral_neg]
    have hnegInt : Integrable (fun w =>
        -Hf (gaussianOUTransition (t - r) y w)
          (gaussianOUTransitionTimeDeriv (t - r) y w))
        (stdGaussian E) := hvelInt.neg
    rw [← integral_add hnegInt hdirInt]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun w => by
      change Hf (nestedGaussianOUTransition t r x z w)
          (nestedGaussianOUTransitionTimeDeriv t r x z w) =
        -Hf (gaussianOUTransition (t - r) y w)
            (gaussianOUTransitionTimeDeriv (t - r) y w) +
          Hf (gaussianOUTransition (t - r) y w) (a • yp)
      rw [hpoint]
      change Hf (gaussianOUTransition (t - r) y w)
          (-gaussianOUTransitionTimeDeriv (t - r) y w + a • yp) = _
      simp only [map_add, map_neg]
  rw [hsplit]
  rw [backwardGaussianOURieszGradientTimeDeriv,
    backwardGaussianOURieszHessianBCF_apply]
  simp only [Function.comp_apply, neg_smul, one_smul, neg_neg]
  change
    a • (-∫ w, Hf (gaussianOUTransition (t - r) y w)
        (gaussianOUTransitionTimeDeriv (t - r) y w) ∂stdGaussian E +
        ∫ w, Hf (gaussianOUTransition (t - r) y w) (a • yp)
          ∂stdGaussian E) +
      a • ∫ w, Gf (gaussianOUTransition (t - r) y w) ∂stdGaussian E =
      (a • ∫ w, Gf (gaussianOUTransition (t - r) y w)
          ∂stdGaussian E -
        a • ∫ w, Hf (gaussianOUTransition (t - r) y w)
          (gaussianOUTransitionTimeDeriv (t - r) y w)
          ∂stdGaussian E) +
      (a ^ 2 • ∫ w, Hf (gaussianOUTransition (t - r) y w)
          ∂stdGaussian E) yp
  rw [hdirEq2]
  simp only [smul_add, smul_neg, smul_smul]
  module

/-- Joint time/space chain rule for the canonical field, once the total
derivatives of its two backward OU inputs have been identified. -/
theorem hasDerivAt_canonicalGaussianBobkovQ_along
    (t : ℝ) (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (Hf : BoundedContinuousFunction E (E →L[ℝ] E))
    (ε : ℝ) (hε : 0 < ε) (hf : ∀ x, f x ∈ Icc ε (1 - ε))
    (y : ℝ → E) {s : ℝ} (hs : 0 ≤ s) {ys : E}
    (hy : HasDerivAt y ys s)
    (hu : HasDerivAt
      (fun r => backwardGaussianOUValueBCF t r f (y r))
      (backwardGaussianOUValueTimeDeriv t s Df (y s) +
        backwardGaussianOUDerivBCF t s Df (y s) ys) s)
    (hv : HasDerivAt
      (fun r => rieszGradientBCF
        (backwardGaussianOUDerivBCF t r Df) (y r))
      (backwardGaussianOURieszGradientTimeDeriv
          t s (rieszGradientBCF Df) Hf (y s) +
        backwardGaussianOURieszHessianBCF t s Hf (y s) ys) s) :
    HasDerivAt
      (fun r => canonicalGaussianBobkovQ t f Df ε hε hf r (y r))
      (canonicalGaussianBobkovQTimeDerivRiesz t s f Df Hf (y s) +
        canonicalGaussianBobkovQSpatialDerivBCF
          t s f Df Hf ε hε hf hs (y s) ys) s := by
  have husClosed := backwardGaussianOUValueBCF_mem_Icc
    t s f hf (y s)
  have hus : backwardGaussianOUValueBCF t s f (y s) ∈ Ioo (0 : ℝ) 1 :=
    ⟨hε.trans_le husClosed.1, husClosed.2.trans_lt (by linarith)⟩
  have hraw := hasDerivAt_bobkovSqrt_time hu hv
    (hasDerivAt_bobkovVarianceCoeff s) hus
    (bobkovVarianceCoeff_nonneg hs)
  have hfun :
      (fun r => canonicalGaussianBobkovQ t f Df ε hε hf r (y r)) =
      (fun r => Real.sqrt
      (normalProfile (backwardGaussianOUValueBCF t r f (y r)) ^ 2 +
        bobkovVarianceCoeff r *
          ‖rieszGradientBCF
            (backwardGaussianOUDerivBCF t r Df) (y r)‖ ^ 2)) := by
    funext r
    rw [canonicalGaussianBobkovQ_apply, norm_rieszGradientBCF]
    rfl
  rw [hfun]
  apply hraw.congr_deriv
  · simp only [canonicalGaussianBobkovQTimeDerivRiesz,
      canonicalGaussianBobkovQTimeDeriv,
      canonicalGaussianBobkovQSpatialDerivBCF,
      bobkovSpatialDerivBCF_apply, smul_apply, add_apply,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      norm_rieszGradientBCF, smul_eq_mul]
    rw [deriv_normalProfile hus]
    simp only [inner_add_right, real_inner_comm]
    field_simp
    ring

/-- The exact path derivative needed by differentiation under the outer
Mehler integral. -/
theorem hasDerivAt_canonicalGaussianBobkovQ_transition
    (t r : ℝ) (hr0 : 0 < r) (hrt : r < t)
    (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (hDf : ∀ y, HasFDerivAt f (Df y) y)
    (Hf : BoundedContinuousFunction E (E →L[ℝ] E))
    (hHf : ∀ y, HasFDerivAt (rieszGradientBCF Df) (Hf y) y)
    (ε : ℝ) (hε : 0 < ε) (hf : ∀ x, f x ∈ Icc ε (1 - ε))
    (x z : E) :
    HasDerivAt
      (fun s => canonicalGaussianBobkovQ t f Df ε hε hf s
        (gaussianOUTransition s x z))
      (canonicalGaussianBobkovQTimeDerivRiesz t r f Df Hf
          (gaussianOUTransition r x z) +
        canonicalGaussianBobkovQSpatialDerivBCF
          t r f Df Hf ε hε hf hr0.le
          (gaussianOUTransition r x z)
          (gaussianOUTransitionTimeDeriv r x z)) r := by
  let y : ℝ → E := fun s => gaussianOUTransition s x z
  have hy : HasDerivAt y (gaussianOUTransitionTimeDeriv r x z) r :=
    hasDerivAt_gaussianOUTransition_time hr0 x z
  have hu := hasDerivAt_backwardGaussianOUValueBCF_transition
    t r hr0 hrt f Df hDf x z
  have hvRaw := hasDerivAt_backwardGaussianOURieszGradientBCF_transition
    t r hr0 hrt (rieszGradientBCF Df) Hf hHf x z
  have hv : HasDerivAt
      (fun s => rieszGradientBCF
        (backwardGaussianOUDerivBCF t s Df) (y s))
      (backwardGaussianOURieszGradientTimeDeriv
          t r (rieszGradientBCF Df) Hf (y r) +
        backwardGaussianOURieszHessianBCF t r Hf (y r)
          (gaussianOUTransitionTimeDeriv r x z)) r := by
    convert hvRaw using 1
    funext s
    exact (backwardGaussianOURieszGradientBCF_rieszGradientBCF
      t s Df (y s)).symm
  exact hasDerivAt_canonicalGaussianBobkovQ_along
    t f Df Hf ε hε hf y hr0.le hy hu hv

theorem norm_backwardGaussianOUValuePathDeriv_le
    (t r : ℝ) (hr0 : 0 < r) (hrt : r < t)
    (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (hDf : ∀ y, HasFDerivAt f (Df y) y)
    {δ₀ δ₁ : ℝ} (hδ₀ : 0 < δ₀) (hδ₀r : δ₀ ≤ r)
    (hδ₁ : 0 < δ₁) (hδ₁r : δ₁ ≤ t - r) (x z : E) :
    ‖backwardGaussianOUValueTimeDeriv t r Df
          (gaussianOUTransition r x z) +
        backwardGaussianOUDerivBCF t r Df
          (gaussianOUTransition r x z)
          (gaussianOUTransitionTimeDeriv r x z)‖ ≤
      ‖Df‖ * (2 * ‖x‖ + (1 + (ouNoiseCoeff δ₀)⁻¹) * ‖z‖ +
        (ouNoiseCoeff δ₁)⁻¹ * stdGaussianFirstMoment E) := by
  have htarget := hasDerivAt_backwardGaussianOUValueBCF_transition
    t r hr0 hrt f Df hDf x z
  have hdirect := hasDerivAt_gaussianOUAverage_nested
    t r hr0 hrt f Df hDf x z
  have hfun :
      (fun s => backwardGaussianOUValueBCF t s f
        (gaussianOUTransition s x z)) =
      (fun s => ∫ w, f (nestedGaussianOUTransition t s x z w)
        ∂stdGaussian E) := by
    funext s
    rfl
  rw [hfun] at htarget
  rw [htarget.unique hdirect]
  exact norm_integral_nestedGaussianOUDeriv_le
    Df hδ₀ hδ₀r hδ₁ hδ₁r x z

theorem norm_backwardGaussianOURieszGradientPathDeriv_le
    (t r : ℝ) (hr0 : 0 < r) (hrt : r < t)
    (Gf : BoundedContinuousFunction E E)
    (Hf : BoundedContinuousFunction E (E →L[ℝ] E))
    (hHf : ∀ y, HasFDerivAt Gf (Hf y) y)
    {δ₀ δ₁ : ℝ} (hδ₀ : 0 < δ₀) (hδ₀r : δ₀ ≤ r)
    (hδ₁ : 0 < δ₁) (hδ₁r : δ₁ ≤ t - r) (x z : E) :
    ‖backwardGaussianOURieszGradientTimeDeriv t r Gf Hf
          (gaussianOUTransition r x z) +
        backwardGaussianOURieszHessianBCF t r Hf
          (gaussianOUTransition r x z)
          (gaussianOUTransitionTimeDeriv r x z)‖ ≤
      ‖Gf‖ + ‖Hf‖ *
        (2 * ‖x‖ + (1 + (ouNoiseCoeff δ₀)⁻¹) * ‖z‖ +
          (ouNoiseCoeff δ₁)⁻¹ * stdGaussianFirstMoment E) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  let a := ouDriftCoeff (t - r)
  have ha0 : 0 ≤ a := (ouDriftCoeff_pos (t - r)).le
  have ha1 : a ≤ 1 := ouDriftCoeff_le_one (sub_nonneg.2 hrt.le)
  have htarget := hasDerivAt_backwardGaussianOURieszGradientBCF_transition
    t r hr0 hrt Gf Hf hHf x z
  have havg := hasDerivAt_gaussianOUAverage_nested
    t r hr0 hrt Gf Hf hHf x z
  have hlagMap : HasDerivAt (fun s : ℝ => t - s) (-1) r := by
    convert (hasDerivAt_const r t).sub (hasDerivAt_id r) using 1 <;>
      first | rfl | norm_num
  have hcoeff := (hasDerivAt_ouDriftCoeff (t - r)).scomp r hlagMap
  have hdirect := hcoeff.smul havg
  have hfun :
      (fun s => backwardGaussianOURieszGradientBCF t s Gf
        (gaussianOUTransition s x z)) =
      (fun s => ouDriftCoeff (t - s) •
        ∫ w, Gf (nestedGaussianOUTransition t s x z w)
          ∂stdGaussian E) := by
    funext s
    rfl
  rw [hfun] at htarget
  have heq := htarget.unique hdirect
  rw [heq]
  simp only [Function.comp_apply, neg_smul, one_smul, neg_neg]
  calc
    ‖a • (∫ w, Hf (nestedGaussianOUTransition t r x z w)
          (nestedGaussianOUTransitionTimeDeriv t r x z w)
          ∂stdGaussian E) +
        a • ∫ w, Gf (nestedGaussianOUTransition t r x z w)
          ∂stdGaussian E‖ ≤
        ‖a • (∫ w, Hf (nestedGaussianOUTransition t r x z w)
          (nestedGaussianOUTransitionTimeDeriv t r x z w)
          ∂stdGaussian E)‖ +
        ‖a • ∫ w, Gf (nestedGaussianOUTransition t r x z w)
          ∂stdGaussian E‖ := norm_add_le _ _
    _ ≤ 1 * (‖Hf‖ *
          (2 * ‖x‖ + (1 + (ouNoiseCoeff δ₀)⁻¹) * ‖z‖ +
            (ouNoiseCoeff δ₁)⁻¹ * stdGaussianFirstMoment E)) +
        1 * ‖Gf‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha0]
      gcongr
      · exact norm_integral_nestedGaussianOUDeriv_le
          Hf hδ₀ hδ₀r hδ₁ hδ₁r x z
      · exact norm_gaussianOUAverage_le (t - r) Gf
          (gaussianOUTransition r x z)
    _ = ‖Gf‖ + ‖Hf‖ *
        (2 * ‖x‖ + (1 + (ouNoiseCoeff δ₀)⁻¹) * ‖z‖ +
          (ouNoiseCoeff δ₁)⁻¹ * stdGaussianFirstMoment E) := by ring

/-- Uniform affine-growth estimate for the complete canonical path
derivative.  This is the dominator used by the outer Mehler integral. -/
theorem norm_canonicalGaussianBobkovQPathDeriv_le
    (t r : ℝ) (hr0 : 0 < r) (hrt : r < t)
    (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (hDf : ∀ y, HasFDerivAt f (Df y) y)
    (Hf : BoundedContinuousFunction E (E →L[ℝ] E))
    (hHf : ∀ y, HasFDerivAt (rieszGradientBCF Df) (Hf y) y)
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hf : ∀ y, f y ∈ Icc ε (1 - ε))
    {δ₀ δ₁ : ℝ} (hδ₀ : 0 < δ₀) (hδ₀r : δ₀ ≤ r)
    (hδ₁ : 0 < δ₁) (hδ₁r : δ₁ ≤ t - r) (x z : E) :
    let Cxz := 2 * ‖x‖ + (1 + (ouNoiseCoeff δ₀)⁻¹) * ‖z‖ +
      (ouNoiseCoeff δ₁)⁻¹ * stdGaussianFirstMoment E
    let Kp := max |lowerQuantile standardGaussianMeasure ε|
      |lowerQuantile standardGaussianMeasure (1 - ε)|
    let Imax := (Real.sqrt (2 * Real.pi))⁻¹
    ‖canonicalGaussianBobkovQTimeDerivRiesz t r f Df Hf
          (gaussianOUTransition r x z) +
        canonicalGaussianBobkovQSpatialDerivBCF
          t r f Df Hf ε hε hf hr0.le
          (gaussianOUTransition r x z)
          (gaussianOUTransitionTimeDeriv r x z)‖ ≤
      (normalProfile ε)⁻¹ *
        (Imax * Kp * (‖Df‖ * Cxz) + ‖Df‖ ^ 2 +
          ‖Df‖ * (‖rieszGradientBCF Df‖ + ‖Hf‖ * Cxz)) := by
  dsimp only
  let y : ℝ → E := fun s => gaussianOUTransition s x z
  let du : ℝ := backwardGaussianOUValueTimeDeriv t r Df (y r) +
    backwardGaussianOUDerivBCF t r Df (y r)
      (gaussianOUTransitionTimeDeriv r x z)
  let dv : E := backwardGaussianOURieszGradientTimeDeriv
      t r (rieszGradientBCF Df) Hf (y r) +
    backwardGaussianOURieszHessianBCF t r Hf (y r)
      (gaussianOUTransitionTimeDeriv r x z)
  let u : ℝ := backwardGaussianOUValueBCF t r f (y r)
  let v : E := rieszGradientBCF (backwardGaussianOUDerivBCF t r Df) (y r)
  let c : ℝ := bobkovVarianceCoeff r
  let R : ℝ := Real.sqrt (normalProfile u ^ 2 + c * ‖v‖ ^ 2)
  let Cxz : ℝ := 2 * ‖x‖ + (1 + (ouNoiseCoeff δ₀)⁻¹) * ‖z‖ +
    (ouNoiseCoeff δ₁)⁻¹ * stdGaussianFirstMoment E
  let Kp : ℝ := max |lowerQuantile standardGaussianMeasure ε|
    |lowerQuantile standardGaussianMeasure (1 - ε)|
  let Imax : ℝ := (Real.sqrt (2 * Real.pi))⁻¹
  have hy : HasDerivAt y (gaussianOUTransitionTimeDeriv r x z) r :=
    hasDerivAt_gaussianOUTransition_time hr0 x z
  have hu := hasDerivAt_backwardGaussianOUValueBCF_transition
    t r hr0 hrt f Df hDf x z
  have hvRaw := hasDerivAt_backwardGaussianOURieszGradientBCF_transition
    t r hr0 hrt (rieszGradientBCF Df) Hf hHf x z
  have hv : HasDerivAt
      (fun s => rieszGradientBCF
        (backwardGaussianOUDerivBCF t s Df) (y s)) dv r := by
    convert hvRaw using 1
    funext s
    exact (backwardGaussianOURieszGradientBCF_rieszGradientBCF
      t s Df (y s)).symm
  have hu' : HasDerivAt
      (fun s => backwardGaussianOUValueBCF t s f (y s)) du r := hu
  have huClosed := backwardGaussianOUValueBCF_mem_Icc t r f hf (y r)
  have huIoo : u ∈ Ioo (0 : ℝ) 1 :=
    ⟨hε.trans_le huClosed.1, huClosed.2.trans_lt (by linarith)⟩
  have hraw := hasDerivAt_bobkovSqrt_time hu' hv
    (hasDerivAt_bobkovVarianceCoeff r) huIoo
    (bobkovVarianceCoeff_nonneg hr0.le)
  have htarget := hasDerivAt_canonicalGaussianBobkovQ_transition
    t r hr0 hrt f Df hDf Hf hHf ε hε hf x z
  have hfun :
      (fun s => canonicalGaussianBobkovQ t f Df ε hε hf s (y s)) =
      (fun s => Real.sqrt
        (normalProfile (backwardGaussianOUValueBCF t s f (y s)) ^ 2 +
          bobkovVarianceCoeff s *
            ‖rieszGradientBCF
              (backwardGaussianOUDerivBCF t s Df) (y s)‖ ^ 2)) := by
    funext s
    rw [canonicalGaussianBobkovQ_apply, norm_rieszGradientBCF]
    rfl
  rw [hfun] at htarget
  have heq := htarget.unique hraw
  rw [heq]
  have hc0 : 0 ≤ c := bobkovVarianceCoeff_nonneg hr0.le
  have hc1 : c ≤ 1 := (bobkovVarianceCoeff_lt_one r).le
  have h1c0 : 0 ≤ 1 - c := sub_nonneg.2 hc1
  have hdu : ‖du‖ ≤ ‖Df‖ * Cxz := by
    exact norm_backwardGaussianOUValuePathDeriv_le
      t r hr0 hrt f Df hDf hδ₀ hδ₀r hδ₁ hδ₁r x z
  have hdv : ‖dv‖ ≤ ‖rieszGradientBCF Df‖ + ‖Hf‖ * Cxz := by
    exact norm_backwardGaussianOURieszGradientPathDeriv_le
      t r hr0 hrt (rieszGradientBCF Df) Hf hHf
      hδ₀ hδ₀r hδ₁ hδ₁r x z
  have hvnorm : ‖v‖ ≤ ‖Df‖ := by
    simpa [v, y] using norm_backwardGaussianOUDerivBCF_le
      t r hrt.le Df (gaussianOUTransition r x z)
  have hI0 : 0 ≤ normalProfile u := (normalProfile_pos huIoo).le
  have hImax : normalProfile u ≤ Imax := by
    have h := normalProfileClosed_le_inv_sqrt_two_pi u
    rwa [normalProfileClosed_eq_normalProfile huIoo] at h
  have hImax0 : 0 ≤ Imax := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hKp0 : 0 ≤ Kp := (abs_nonneg _).trans (le_max_left _ _)
  have hIp : |-lowerQuantile standardGaussianMeasure u| ≤ Kp := by
    have h := abs_deriv_normalProfile_le_endpointMax hε hεhalf huClosed
    rw [deriv_normalProfile huIoo] at h
    simpa [Kp] using h
  have hrad : 0 < normalProfile u ^ 2 + c * ‖v‖ ^ 2 := by
    nlinarith [normalProfile_pos huIoo, mul_nonneg hc0 (sq_nonneg ‖v‖)]
  have hR : 0 < R := Real.sqrt_pos.2 hrad
  have hRinv : R⁻¹ ≤ (normalProfile ε)⁻¹ := by
    exact inv_bobkovRadius_le_inv_endpoint hε hεhalf huClosed hc0 v
  have hIεinv0 : 0 ≤ (normalProfile ε)⁻¹ := by
    exact (inv_pos.mpr (normalProfile_pos
      (show ε ∈ Ioo (0 : ℝ) 1 by constructor <;> linarith))).le
  have hform :
      (2 * normalProfile u * (-lowerQuantile standardGaussianMeasure u) * du +
          (2 * (1 - c)) * ‖v‖ ^ 2 +
          2 * c * inner ℝ v dv) / (2 * R) =
        R⁻¹ * (normalProfile u *
          (-lowerQuantile standardGaussianMeasure u) * du +
          (1 - c) * ‖v‖ ^ 2 + c * inner ℝ v dv) := by
    field_simp [hR.ne']
  rw [hform, Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hR)]
  calc
    R⁻¹ * |normalProfile u *
          (-lowerQuantile standardGaussianMeasure u) * du +
          (1 - c) * ‖v‖ ^ 2 + c * inner ℝ v dv| ≤
        R⁻¹ * (Imax * Kp * ‖du‖ + ‖v‖ ^ 2 + ‖v‖ * ‖dv‖) := by
      gcongr
      calc
        |normalProfile u * (-lowerQuantile standardGaussianMeasure u) * du +
            (1 - c) * ‖v‖ ^ 2 + c * inner ℝ v dv| ≤
            |normalProfile u * (-lowerQuantile standardGaussianMeasure u) * du| +
              |(1 - c) * ‖v‖ ^ 2| + |c * inner ℝ v dv| := by
          exact (abs_add_le _ _).trans
            (add_le_add (abs_add_le _ _) (le_refl _))
        _ ≤ Imax * Kp * ‖du‖ + ‖v‖ ^ 2 + ‖v‖ * ‖dv‖ := by
          have hterm1 :
              |normalProfile u * (-lowerQuantile standardGaussianMeasure u) * du| ≤
                Imax * Kp * ‖du‖ := by
            rw [abs_mul, abs_mul, abs_of_nonneg hI0]
            have hp := mul_le_mul hImax hIp (abs_nonneg _) hImax0
            simpa only [Real.norm_eq_abs] using
              mul_le_mul_of_nonneg_right hp (abs_nonneg du)
          have hterm2 : |(1 - c) * ‖v‖ ^ 2| ≤ ‖v‖ ^ 2 := by
            rw [abs_mul, abs_of_nonneg h1c0,
              abs_of_nonneg (sq_nonneg ‖v‖)]
            exact mul_le_of_le_one_left (sq_nonneg ‖v‖) (by linarith)
          have hterm3 : |c * inner ℝ v dv| ≤ ‖v‖ * ‖dv‖ := by
            rw [abs_mul, abs_of_nonneg hc0]
            have hinner := abs_real_inner_le_norm v dv
            exact (mul_le_mul_of_nonneg_left hinner hc0).trans
              (mul_le_of_le_one_left (mul_nonneg (norm_nonneg v) (norm_nonneg dv)) hc1)
          exact add_le_add (add_le_add hterm1 hterm2) hterm3
    _ ≤ (normalProfile ε)⁻¹ *
        (Imax * Kp * (‖Df‖ * Cxz) + ‖Df‖ ^ 2 +
          ‖Df‖ * (‖rieszGradientBCF Df‖ + ‖Hf‖ * Cxz)) := by
      have hCxz0 : 0 ≤ Cxz := by
        have hb0 : 0 ≤ (ouNoiseCoeff δ₀)⁻¹ :=
          (inv_pos.mpr (ouNoiseCoeff_pos hδ₀)).le
        have hb1 : 0 ≤ (ouNoiseCoeff δ₁)⁻¹ :=
          (inv_pos.mpr (ouNoiseCoeff_pos hδ₁)).le
        exact add_nonneg
          (add_nonneg (mul_nonneg (by norm_num) (norm_nonneg x))
            (mul_nonneg (add_nonneg (by norm_num) hb0) (norm_nonneg z)))
          (mul_nonneg hb1 stdGaussianFirstMoment_nonneg)
      have hA0 : 0 ≤ Imax * Kp * ‖du‖ + ‖v‖ ^ 2 + ‖v‖ * ‖dv‖ :=
        add_nonneg
          (add_nonneg (mul_nonneg (mul_nonneg hImax0 hKp0) (norm_nonneg du))
            (sq_nonneg ‖v‖))
          (mul_nonneg (norm_nonneg v) (norm_nonneg dv))
      have hAB :
          Imax * Kp * ‖du‖ + ‖v‖ ^ 2 + ‖v‖ * ‖dv‖ ≤
            Imax * Kp * (‖Df‖ * Cxz) + ‖Df‖ ^ 2 +
              ‖Df‖ * (‖rieszGradientBCF Df‖ + ‖Hf‖ * Cxz) := by
        apply add_le_add
        · apply add_le_add
          · exact mul_le_mul_of_nonneg_left hdu (mul_nonneg hImax0 hKp0)
          · nlinarith [norm_nonneg v, norm_nonneg Df]
        · exact mul_le_mul hvnorm hdv (norm_nonneg dv) (norm_nonneg Df)
      exact (mul_le_mul_of_nonneg_right hRinv hA0).trans
        (mul_le_mul_of_nonneg_left hAB hIεinv0)

def canonicalGaussianBobkovPathBound
    (t s ε : ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (Hf : BoundedContinuousFunction E (E →L[ℝ] E))
    (x z : E) : ℝ :=
  let Cxz := 2 * ‖x‖ + (1 + (ouNoiseCoeff (s / 2))⁻¹) * ‖z‖ +
    (ouNoiseCoeff ((t - s) / 2))⁻¹ * stdGaussianFirstMoment E
  let Kp := max |lowerQuantile standardGaussianMeasure ε|
    |lowerQuantile standardGaussianMeasure (1 - ε)|
  let Imax := (Real.sqrt (2 * Real.pi))⁻¹
  (normalProfile ε)⁻¹ *
    (Imax * Kp * (‖Df‖ * Cxz) + ‖Df‖ ^ 2 +
      ‖Df‖ * (‖rieszGradientBCF Df‖ + ‖Hf‖ * Cxz))

theorem integrable_canonicalGaussianBobkovPathBound
    (t s ε : ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (Hf : BoundedContinuousFunction E (E →L[ℝ] E))
    (x : E) :
    Integrable (canonicalGaussianBobkovPathBound t s ε Df Hf x)
      (stdGaussian E) := by
  let K0 : ℝ := (ouNoiseCoeff (s / 2))⁻¹
  let K1 : ℝ := (ouNoiseCoeff ((t - s) / 2))⁻¹
  let C0 : ℝ := 2 * ‖x‖ + K1 * stdGaussianFirstMoment E
  let C1 : ℝ := 1 + K0
  let Kp : ℝ := max |lowerQuantile standardGaussianMeasure ε|
    |lowerQuantile standardGaussianMeasure (1 - ε)|
  let Imax : ℝ := (Real.sqrt (2 * Real.pi))⁻¹
  let A : ℝ := (normalProfile ε)⁻¹ *
    (Imax * Kp * (‖Df‖ * C0) + ‖Df‖ ^ 2 +
      ‖Df‖ * (‖rieszGradientBCF Df‖ + ‖Hf‖ * C0))
  let B : ℝ := (normalProfile ε)⁻¹ *
    (Imax * Kp * (‖Df‖ * C1) + ‖Df‖ * (‖Hf‖ * C1))
  have hnorm : Integrable (fun z : E => ‖z‖) (stdGaussian E) :=
    IsGaussian.integrable_id.norm
  have hAB : Integrable (fun z : E => A + B * ‖z‖) (stdGaussian E) :=
    (integrable_const A).add (hnorm.const_mul B)
  apply hAB.congr
  exact Filter.Eventually.of_forall fun z => by
    simp only [canonicalGaussianBobkovPathBound]
    dsimp only [K0, K1, C0, C1, Kp, Imax, A, B]
    ring

/-- The canonical G3 certificate for terminal data with a bounded Riesz
Hessian and bounded Riesz third derivative. -/
def gaussianBobkovSmoothInterpolation_of_boundedThirdJet
    {n : ℕ}
    (t : ℝ) (ht : 0 ≤ t)
    (f : BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1))) ℝ)
    (Df : BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ))
    (hDf : ∀ y, HasFDerivAt f (Df y) y)
    (Hf : BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
        EuclideanSpace ℝ (Fin (n + 1))))
    (hHf : ∀ y, HasFDerivAt (rieszGradientBCF Df) (Hf y) y)
    (D3f : BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
        (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
          EuclideanSpace ℝ (Fin (n + 1)))))
    (M : ℝ) (hM : ∀ y, ‖D3f y‖ ≤ M)
    (hD3f : ∀ y, HasFDerivAt Hf (D3f y) y)
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hf : ∀ y, f y ∈ Icc ε (1 - ε))
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    GaussianBobkovSmoothInterpolation
      f (normalProfileCompBCF f ε hε hf) Df t x := by
  let G := EuclideanSpace ℝ (Fin (n + 1))
  let Q : ℝ → BoundedContinuousFunction G ℝ :=
    canonicalGaussianBobkovQ t f Df ε hε hf
  let Qt : ℝ → G → ℝ := fun s =>
    canonicalGaussianBobkovQTimeDerivRiesz t s f Df Hf
  let DQ : ℝ → BoundedContinuousFunction G (G →L[ℝ] ℝ) := fun s =>
    if hs : 0 ≤ s then
      canonicalGaussianBobkovQSpatialDerivBCF
        t s f Df Hf ε hε hf hs
    else 0
  let q1 : ℝ → Fin (n + 1) → BoundedContinuousFunction G ℝ := fun s i =>
    if hs : 0 ≤ s then
      canonicalGaussianBobkovQGradientCoordinateBCF
        t s f Df Hf ε hε hf hs (euclideanUnit i)
    else 0
  let q2 : ℝ → Fin (n + 1) → BoundedContinuousFunction G ℝ := fun s i =>
    if hs : 0 ≤ s then
      canonicalGaussianBobkovQHessianDiagonalBCF
        t s f Df Hf D3f M hM ε hε hf hs (euclideanUnit i)
    else 0
  let residual : ℝ → BoundedContinuousFunction G ℝ := fun s =>
    if hs : 0 ≤ s then
      canonicalGaussianBobkovResidualBCF t s f Df Hf ε hε hf hs
    else 0
  let U : ℝ → Set ℝ := fun s => Ioo (s / 2) (t - (t - s) / 2)
  let bound : ℝ → G → ℝ := fun s =>
    canonicalGaussianBobkovPathBound t s ε Df Hf x
  have hcontinuous : ContinuousOn
      (fun s => gaussianOUSemigroup s (Q s) x) (Icc 0 t) := by
    exact continuousOn_canonicalGaussianBobkovFlow t f Df ε hε hf x
  have hDQ : ∀ s ∈ Ioo 0 t, ∀ y,
      HasFDerivAt (Q s) (DQ s y) y := by
    intro s hs y
    simp only [Q, DQ, dif_pos hs.1.le]
    exact hasFDerivAt_canonicalGaussianBobkovQSpatialDerivBCF
      t f Df hDf Hf hHf ε hε hf hs.1.le y
  have hDcoord : ∀ s ∈ Ioo 0 t, ∀ y v,
      DQ s y v = ∑ i, q1 s i y * v i := by
    intro s hs y v
    simp only [DQ, q1, dif_pos hs.1.le]
    exact canonicalGaussianBobkovQSpatialDerivBCF_eq_sum_coordinates
      t f Df Hf ε hε hf hs.1.le y v
  have hq12 : ∀ s ∈ Ioo 0 t, ∀ (i : Fin (n + 1))
      (w : Fin n → ℝ) (r : ℝ),
      HasDerivAt
        (fun u => q1 s i (gaussianOUTransition s x
          (WithLp.toLp 2 (i.insertNth u w))))
        (ouNoiseCoeff s * q2 s i (gaussianOUTransition s x
          (WithLp.toLp 2 (i.insertNth r w)))) r := by
    intro s hs i w r
    simp only [q1, q2, dif_pos hs.1.le]
    exact hasDerivAt_canonicalGaussianBobkovQGradientCoordinate_transition
      t f Df hDf Hf hHf D3f M hM hD3f ε hε hf hs.1.le x i w r
  have hU : ∀ s ∈ Ioo 0 t, U s ∈ nhds s := by
    intro s hs
    change Ioo (s / 2) (t - (t - s) / 2) ∈ nhds s
    apply Ioo_mem_nhds
    · nlinarith [hs.1]
    · nlinarith [hs.2]
  have hboundInt : ∀ s ∈ Ioo 0 t,
      Integrable (bound s) (stdGaussian G) := by
    intro s _hs
    exact integrable_canonicalGaussianBobkovPathBound t s ε Df Hf x
  have hbound : ∀ s ∈ Ioo 0 t,
      ∀ᵐ z ∂stdGaussian G, ∀ r ∈ U s,
      ‖Qt r (gaussianOUTransition r x z) +
        DQ r (gaussianOUTransition r x z)
          (gaussianOUTransitionTimeDeriv r x z)‖ ≤ bound s z := by
    intro s hs
    exact Filter.Eventually.of_forall fun z r hr => by
      change r ∈ Ioo (s / 2) (t - (t - s) / 2) at hr
      have hr0 : 0 < r := by
        linarith [hr.1, hs.1]
      have hrt : r < t := by
        linarith [hr.2, hs.2]
      have hδ₀ : 0 < s / 2 := by linarith [hs.1]
      have hδ₁ : 0 < (t - s) / 2 := by linarith [hs.2]
      have hδ₀r : s / 2 ≤ r := by
        exact hr.1.le
      have hδ₁r : (t - s) / 2 ≤ t - r := by
        linarith [hr.2]
      simp only [Qt, DQ, dif_pos hr0.le, bound]
      exact norm_canonicalGaussianBobkovQPathDeriv_le
        t r hr0 hrt f Df hDf Hf hHf ε hε hεhalf hf
        hδ₀ hδ₀r hδ₁ hδ₁r x z
  have hjoint : ∀ s ∈ Ioo 0 t,
      ∀ᵐ z ∂stdGaussian G, ∀ r ∈ U s,
      HasDerivAt (fun u => Q u (gaussianOUTransition u x z))
        (Qt r (gaussianOUTransition r x z) +
          DQ r (gaussianOUTransition r x z)
            (gaussianOUTransitionTimeDeriv r x z)) r := by
    intro s hs
    exact Filter.Eventually.of_forall fun z r hr => by
      change r ∈ Ioo (s / 2) (t - (t - s) / 2) at hr
      have hr0 : 0 < r := by
        linarith [hr.1, hs.1]
      have hrt : r < t := by
        linarith [hr.2, hs.2]
      simp only [Q, Qt, DQ, dif_pos hr0.le]
      exact hasDerivAt_canonicalGaussianBobkovQ_transition
        t r hr0 hrt f Df hDf Hf hHf ε hε hf x z
  have hresidual : ∀ s ∈ Ioo 0 t, ∀ y,
      residual s y = Qt s y + gaussianOUGeneratorCoordinates
        (fun i z => q1 s i z) (fun i z => q2 s i z) y := by
    intro s hs y
    have h := canonicalGaussianBobkovQ_time_add_generator_eq_residual
      t s hs.2 hs.1.le f Df Hf hHf D3f M hM hD3f ε hε hf y
    simp only [residual, Qt, q1, q2, dif_pos hs.1.le,
      gaussianOUGeneratorCoordinates]
    rw [canonicalGaussianBobkovResidualBCF_apply]
    exact h.symm
  have hQtInt : ∀ s ∈ Ioo 0 t,
      Integrable (fun z => Qt s (gaussianOUTransition s x z))
        (stdGaussian G) := by
    intro s hs
    let rs := canonicalGaussianBobkovResidualBCF
      t s f Df Hf ε hε hf hs.1.le
    let q1s : Fin (n + 1) → BoundedContinuousFunction G ℝ := fun i =>
      canonicalGaussianBobkovQGradientCoordinateBCF
        t s f Df Hf ε hε hf hs.1.le (euclideanUnit i)
    let q2s : Fin (n + 1) → BoundedContinuousFunction G ℝ := fun i =>
      canonicalGaussianBobkovQHessianDiagonalBCF
        t s f Df Hf D3f M hM ε hε hf hs.1.le (euclideanUnit i)
    have hrs : Integrable (fun z => rs (gaussianOUTransition s x z))
        (stdGaussian G) := by
      refine Integrable.of_bound
        (rs.continuous.comp (by
          unfold gaussianOUTransition
          fun_prop)).aestronglyMeasurable ‖rs‖ ?_
      exact Filter.Eventually.of_forall fun z => rs.norm_coe_le_norm _
    have hgen := integrable_gaussianOUGeneratorCoordinates_transition
      s x q1s q2s
    apply (hrs.sub hgen).congr
    exact Filter.Eventually.of_forall fun z => by
      have heq := hresidual s hs (gaussianOUTransition s x z)
      change rs (gaussianOUTransition s x z) -
          gaussianOUGeneratorCoordinates
            (fun i y => q1s i y) (fun i y => q2s i y)
            (gaussianOUTransition s x z) =
        Qt s (gaussianOUTransition s x z)
      simp only [residual, q1, q2, dif_pos hs.1.le] at heq
      dsimp only [rs, q1s, q2s]
      rw [heq]
      ring
  have hG3 : ∀ s ∈ Ioo 0 t, ∀ y,
      ∃ (I Ip : ℝ) (v : G) (H : Fin (n + 1) → G),
        0 < I ∧ residual s y =
          bobkovSqrtResidual (bobkovVarianceCoeff s) I Ip v H := by
    intro s hs y
    refine ⟨normalProfile (backwardGaussianOUValueBCF t s f y),
      deriv normalProfile (backwardGaussianOUValueBCF t s f y),
      rieszGradientBCF (backwardGaussianOUDerivBCF t s Df) y,
      (fun i => backwardGaussianOURieszHessianBCF
        t s Hf y (euclideanUnit i)), ?_, ?_⟩
    · exact normalProfile_pos
        ⟨hε.trans_le (backwardGaussianOUValueBCF_mem_Icc t s f hf y).1,
          (backwardGaussianOUValueBCF_mem_Icc t s f hf y).2.trans_lt
            (by linarith)⟩
    · simp only [residual, dif_pos hs.1.le]
      exact canonicalGaussianBobkovResidualBCF_apply
        t s f Df Hf ε hε hf hs.1.le y
  let hSmooth : GaussianBobkovSmoothInterpolation
      f (normalProfileCompBCF f ε hε hf) Df t x :=
    GaussianBobkovSmoothInterpolation.ofSmoothGeneratorFamilyIntegrable
      Q residual Qt DQ q1 q2 U bound hcontinuous hDQ hDcoord hq12
      hU hboundInt hQtInt hbound hjoint hresidual hG3
      (canonicalGaussianBobkovQ_initial t f Df ε hε hf x)
      (canonicalGaussianBobkovQ_terminal t f Df ε hε hf)
  exact hSmooth

end
end UniformRandomMALA.Concrete
