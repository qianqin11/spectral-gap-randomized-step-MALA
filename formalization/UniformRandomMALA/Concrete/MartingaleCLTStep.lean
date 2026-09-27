import UniformRandomMALA.Concrete.MartingaleCLTCompensation

/-! # Conditional Taylor cancellation for one martingale increment -/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory Complex Filter
open scoped Topology ProbabilityTheory

noncomputable section
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem integrable_square_min (X : Ω → ℝ) (hX : MemLp X 2 μ) (t : ℝ) :
    Integrable (fun x => X x ^ 2 * min 1 |t * X x|) μ := by
  apply hX.integrable_sq.mono_nonneg
  · have hc : Continuous (fun y : ℝ => y ^ 2 * min 1 |t * y|) := by fun_prop
    exact hc.comp_aestronglyMeasurable hX.aestronglyMeasurable
  · exact Eventually.of_forall fun x => by positivity
  · exact Eventually.of_forall fun x => by
      simpa using mul_le_mul_of_nonneg_left (min_le_left (1 : ℝ) |t * X x|) (sq_nonneg (X x))

/-- An adapted weight cancels the first two Taylor terms. All random
variables are ordinary measurable functions; the hypotheses are the
conditional mean and conditional second moment of a martingale step. -/
theorem integral_compensated_step_eq_remainder
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {X V : Ω → ℝ} {Z : Ω → ℂ} {C M : ℝ}
    (hX : MemLp X 2 μ) (hmean : μ[X | m] =ᵐ[μ] 0)
    (hsecond : μ[fun x => X x ^ 2 | m] =ᵐ[μ] V)
    (hV : StronglyMeasurable[m] V) (hV0 : ∀ x, 0 ≤ V x) (hVC : ∀ x, V x ≤ C)
    (hZ : StronglyMeasurable[m] Z) (hZM : ∀ x, ‖Z x‖ ≤ M) (t : ℝ) :
    (∫ x, Z x * (Real.exp (t ^ 2 * V x / 2) : ℂ) *
      Complex.exp (Complex.I * (t * X x)) - Z x ∂μ) =
      ∫ x, compensatedStepRemainder t (X x) (V x) (Z x) ∂μ := by
  let W : Ω → ℂ := fun x => Z x * (Real.exp (t ^ 2 * V x / 2) : ℂ)
  have hW : StronglyMeasurable[m] W := by
    dsimp [W]
    fun_prop
  have hWb : ∀ x, ‖W x‖ ≤ M * Real.exp (t ^ 2 * C / 2) := by
    intro x
    simp only [W, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul (hZM x)
    · exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left (hVC x) (sq_nonneg t)])
    · positivity
    · exact (norm_nonneg (Z x)).trans (hZM x)
  have hWae : AEStronglyMeasurable[mΩ] W μ := (hW.mono hm).aestronglyMeasurable
  have hXi : Integrable X μ := hX.integrable (by norm_num)
  have hXW : Integrable (X • W) μ :=
    hXi.smul_bdd (M * Real.exp (t ^ 2 * C / 2)) hWae (Eventually.of_forall hWb)
  have hVi : Integrable V μ := by
    apply (integrable_const C).mono' (hV.mono hm).aestronglyMeasurable
    exact Eventually.of_forall fun x => by simpa [Real.norm_eq_abs, abs_of_nonneg (hV0 x)] using hVC x
  have hB : Integrable (fun x => X x ^ 2 - V x) μ := hX.integrable_sq.sub hVi
  have hBW : Integrable ((fun x => X x ^ 2 - V x) • W) μ :=
    hB.smul_bdd (M * Real.exp (t ^ 2 * C / 2)) hWae (Eventually.of_forall hWb)
  have hBmean : μ[fun x => X x ^ 2 - V x | m] =ᵐ[μ] 0 := by
    have hs := condExp_sub (m := m) (μ := μ) hX.integrable_sq hVi
    rw [condExp_of_stronglyMeasurable hm hV hVi] at hs
    filter_upwards [hs, hsecond] with x hx hv
    change μ[(fun x => X x ^ 2) - V | m] x = 0
    simpa only [Pi.sub_apply, hv, sub_self] using hx
  have hlinear := @integral_weighted_martingale_zero Ω mΩ μ _ m hm X W
    hXi hmean hW.aestronglyMeasurable hXW
  have hquadratic := @integral_weighted_martingale_zero Ω mΩ μ _ m hm
    (fun x => X x ^ 2 - V x) W hB hBmean hW.aestronglyMeasurable hBW
  have hR : Integrable (fun x => compensatedStepRemainder t (X x) (V x) (Z x)) μ := by
    have hTX : Integrable (fun x => characteristicTaylorRemainder t (X x)) μ := by
      apply (hX.integrable_sq.const_mul (4 * t ^ 2)).mono'
      · have hc : Continuous (characteristicTaylorRemainder t) := by
          unfold characteristicTaylorRemainder
          fun_prop
        exact hc.comp_aestronglyMeasurable hX.aestronglyMeasurable
      · exact Eventually.of_forall fun x => norm_characteristicTaylorRemainder_le_sq t (X x)
    have hfirst : Integrable (fun x => W x * characteristicTaylorRemainder t (X x)) μ := by
      exact hTX.bdd_mul hWae (Eventually.of_forall hWb)
    have hZb : MemLp Z 1 μ := MemLp.of_bound (hZ.mono hm).aestronglyMeasurable M
      (Eventually.of_forall hZM)
    have hsecondi : Integrable (fun x => Z x *
        ((Real.exp (t ^ 2 * V x / 2) * (1 - t ^ 2 * V x / 2) - 1 : ℝ) : ℂ)) μ := by
      have hF : StronglyMeasurable[mΩ] (fun x =>
          ((Real.exp (t ^ 2 * V x / 2) * (1 - t ^ 2 * V x / 2) - 1 : ℝ) : ℂ)) := by
        have hVm := hV.mono hm
        fun_prop
      have hFb : ∀ x, ‖((Real.exp (t ^ 2 * V x / 2) *
          (1 - t ^ 2 * V x / 2) - 1 : ℝ) : ℂ)‖ ≤
          Real.exp (t ^ 2 * C / 2) * (t ^ 2 * C / 2) ^ 2 := by
        intro x
        have hb : 0 ≤ t ^ 2 * V x / 2 := div_nonneg (mul_nonneg (sq_nonneg t) (hV0 x)) (by norm_num)
        have hbC : t ^ 2 * V x / 2 ≤ t ^ 2 * C / 2 := by
          nlinarith [mul_le_mul_of_nonneg_left (hVC x) (sq_nonneg t)]
        simpa only [Complex.norm_real, Real.norm_eq_abs] using
          (abs_exp_mul_one_sub_sub_one_le hb hbC).trans
            (mul_le_mul_of_nonneg_left ((sq_le_sq₀ hb (hb.trans hbC)).2 hbC) (Real.exp_pos _).le)
      exact (hZb.integrable (by norm_num)).mul_bdd hF.aestronglyMeasurable (Eventually.of_forall hFb)
    exact hfirst.add hsecondi
  simp_rw [compensatedStep_expansion]
  change (∫ x, (compensatedStepRemainder t (X x) (V x) (Z x) +
    (Complex.I * (t : ℂ)) * (X x • W x)) -
    ((t : ℂ) ^ 2 / 2) * ((X x ^ 2 - V x) • W x) ∂μ) = _
  have hlin : Integrable (fun x => (Complex.I * (t : ℂ)) * (X x • W x)) μ := hXW.const_mul _
  have hquad : Integrable (fun x => ((t : ℂ) ^ 2 / 2) * ((X x ^ 2 - V x) • W x)) μ := hBW.const_mul _
  have hsum : Integrable (fun x => compensatedStepRemainder t (X x) (V x) (Z x) +
      (Complex.I * (t : ℂ)) * (X x • W x)) μ := hR.add hlin
  rw [integral_sub hsum hquad,
    integral_add hR hlin, integral_const_mul, integral_const_mul]
  simp only [W, hlinear, hquadratic, mul_zero, add_zero, sub_zero]

/-- Quantitative one-step estimate, with the linear and quadratic
conditional moments canceled exactly. -/
theorem norm_integral_compensated_step_le
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {X V : Ω → ℝ} {Z : Ω → ℂ} {C M : ℝ} (hM : 0 ≤ M)
    (hX : MemLp X 2 μ) (hmean : μ[X | m] =ᵐ[μ] 0)
    (hsecond : μ[fun x => X x ^ 2 | m] =ᵐ[μ] V)
    (hV : StronglyMeasurable[m] V) (hV0 : ∀ x, 0 ≤ V x) (hVC : ∀ x, V x ≤ C)
    (hZ : StronglyMeasurable[m] Z) (hZM : ∀ x, ‖Z x‖ ≤ M) (t : ℝ) :
    ‖∫ x, Z x * (Real.exp (t ^ 2 * V x / 2) : ℂ) *
      Complex.exp (Complex.I * (t * X x)) - Z x ∂μ‖ ≤
      M * Real.exp (t ^ 2 * C / 2) *
        (4 * t ^ 2 * (∫ x, X x ^ 2 * min 1 |t * X x| ∂μ) +
          (t ^ 2 / 2) ^ 2 * ∫ x, V x ^ 2 ∂μ) := by
  rw [@integral_compensated_step_eq_remainder Ω mΩ μ _ m hm X V Z C M
    hX hmean hsecond hV hV0 hVC hZ hZM t]
  have hVsq : Integrable (fun x => V x ^ 2) μ := by
    have hmem : MemLp V 2 μ := MemLp.of_bound (hV.mono hm).aestronglyMeasurable C
      (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs, abs_of_nonneg (hV0 x)] using hVC x)
    exact hmem.integrable_sq
  have hsmall := @integrable_square_min Ω mΩ μ X hX t
  have hbound : Integrable (fun x => M * Real.exp (t ^ 2 * C / 2) *
      (4 * t ^ 2 * (X x ^ 2 * min 1 |t * X x|) + (t ^ 2 / 2) ^ 2 * V x ^ 2)) μ :=
    ((hsmall.const_mul _).add (hVsq.const_mul _)).const_mul _
  have h := norm_integral_le_of_norm_le hbound (Eventually.of_forall fun x => by
    simpa only [mul_assoc] using
      norm_compensatedStepRemainder_le hM (hV0 x) (hVC x) t (X x) (hZM x))
  have hi : Integrable (fun x => 4 * t ^ 2 * (X x ^ 2 * min 1 |t * X x|)) μ :=
    hsmall.const_mul _
  have hj : Integrable (fun x => (t ^ 2 / 2) ^ 2 * V x ^ 2) μ := hVsq.const_mul _
  rw [integral_const_mul, integral_add hi hj, integral_const_mul, integral_const_mul] at h
  exact h

end
end UniformRandomMALA.Concrete
