import UniformRandomMALA.Concrete.GaussianCDF
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Elementary Mills bounds for the standard Gaussian

This file proves the two estimates used in Appendix C by one-dimensional
calculus.  The proof integrates the derivative of
`c * φ(x) / (1 + x)` on a half-line.  It does not appeal to an external
probability or asymptotic theorem.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

noncomputable section

namespace Concrete

theorem normalTailReal_eq_integral (a : ℝ) :
    normalTailReal a = ∫ x in Ioi a, normalDensity x := by
  rw [normalTailReal, normalTail_eq_integral,
    ENNReal.toReal_ofReal]
  exact integral_nonneg_of_ae
    (ae_restrict_of_forall_mem measurableSet_Ioi fun x _ => normalDensity_nonneg x)

theorem continuous_normalDensity : Continuous normalDensity := by
  rw [show normalDensity = fun x : ℝ =>
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) by
    funext x
    exact normalDensity_def x]
  fun_prop

theorem hasDerivAt_normalDensity (x : ℝ) :
    HasDerivAt normalDensity (-x * normalDensity x) x := by
  let c : ℝ := (Real.sqrt (2 * Real.pi))⁻¹
  have hinner : HasDerivAt (fun y : ℝ => -(y ^ 2) / 2) (-x) x := by
    convert ((hasDerivAt_pow 2 x).neg.div_const 2) using 1
    all_goals first | rfl | ring
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2) / 2))
      (Real.exp (-(x ^ 2) / 2) * (-x)) x :=
    (Real.hasDerivAt_exp _).comp x hinner
  have hmul := (hasDerivAt_const x c).mul hexp
  convert hmul using 1
  all_goals try rfl
  · funext y
    simpa [c] using normalDensity_def y
  · rw [normalDensity_def]
    ring

theorem normalDensity_tendsto_atTop :
    Tendsto normalDensity atTop (𝓝 0) := by
  have hquad : Tendsto (fun x : ℝ => x ^ 2 / 2) atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (by norm_num : (2 : ℕ) ≠ 0)).atTop_div_const
      (by norm_num)
  have hexp : Tendsto (fun x : ℝ => Real.exp (-(x ^ 2 / 2))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hquad
  rw [show normalDensity = fun x : ℝ =>
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2)) by
    funext x
    rw [normalDensity_def]
    congr 2
    ring]
  simpa using tendsto_const_nhds.mul hexp

/-- The standard Gaussian density also vanishes at negative infinity. -/
theorem normalDensity_tendsto_atBot :
    Tendsto normalDensity atBot (nhds 0) := by
  have h := normalDensity_tendsto_atTop.comp tendsto_neg_atBot_atTop
  apply h.congr'
  exact Eventually.of_forall fun x => by
    change normalDensity (-x) = normalDensity x
    rw [normalDensity_def, normalDensity_def]
    congr 3
    ring

/-- The auxiliary functions whose derivatives give both Mills estimates. -/
def millsAux (c x : ℝ) : ℝ := c * normalDensity x / (1 + x)

def millsAuxDeriv (c x : ℝ) : ℝ :=
  -(c * normalDensity x * (x ^ 2 + x + 1) / (1 + x) ^ 2)

theorem hasDerivAt_millsAux
    (c x : ℝ) (hx : x ≠ -1) :
    HasDerivAt (millsAux c) (millsAuxDeriv c x) x := by
  have hnum := (hasDerivAt_const x c).mul (hasDerivAt_normalDensity x)
  have hden : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
    simpa using (hasDerivAt_id x).const_add 1
  have hden_ne : 1 + x ≠ 0 := by
    intro hzero
    apply hx
    linarith
  have hdiv := hnum.div hden hden_ne
  unfold millsAux millsAuxDeriv
  convert hdiv using 1
  all_goals try rfl
  field_simp [hden_ne]
  simp only [Pi.mul_apply]
  ring

theorem millsAux_tendsto_atTop (c : ℝ) :
    Tendsto (millsAux c) atTop (𝓝 0) := by
  have hnum : Tendsto (fun x => c * normalDensity x) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul normalDensity_tendsto_atTop
  have hden : Tendsto (fun x : ℝ => 1 + x) atTop atTop :=
    tendsto_atTop_add_const_left atTop (1 : ℝ)
      (tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop)
  exact hnum.div_atTop hden

private theorem millsAuxDeriv_nonpos
    (c : ℝ) (hc : 0 ≤ c) {x : ℝ} (hx : 0 ≤ x) :
    millsAuxDeriv c x ≤ 0 := by
  unfold millsAuxDeriv
  have hden : 0 < (1 + x) ^ 2 := sq_pos_of_pos (by linarith)
  have hpoly : 0 ≤ x ^ 2 + x + 1 := by nlinarith [sq_nonneg x]
  have hnum : 0 ≤ c * normalDensity x * (x ^ 2 + x + 1) :=
    mul_nonneg (mul_nonneg hc (normalDensity_nonneg x)) hpoly
  have hfrac : 0 ≤
      c * normalDensity x * (x ^ 2 + x + 1) / (1 + x) ^ 2 :=
    div_nonneg hnum hden.le
  linarith

private theorem neg_millsAuxDeriv_one_le_density
    {x : ℝ} (hx : 0 ≤ x) :
    -millsAuxDeriv 1 x ≤ normalDensity x := by
  unfold millsAuxDeriv
  have hden : 0 < (1 + x) ^ 2 := sq_pos_of_pos (by linarith)
  simp only [one_mul, neg_neg]
  rw [div_le_iff₀ hden]
  have hd := normalDensity_nonneg x
  have hdx : 0 ≤ normalDensity x * x := mul_nonneg hd hx
  nlinarith

private theorem density_le_neg_millsAuxDeriv_two
    {x : ℝ} (hx : 0 ≤ x) :
    normalDensity x ≤ -millsAuxDeriv 2 x := by
  unfold millsAuxDeriv
  have hden : 0 < (1 + x) ^ 2 := sq_pos_of_pos (by linarith)
  simp only [neg_neg]
  rw [le_div_iff₀ hden]
  have hd := normalDensity_nonneg x
  have hsquare : 0 ≤ normalDensity x * x ^ 2 :=
    mul_nonneg hd (sq_nonneg x)
  nlinarith

/-- Lower Mills estimate in Lemma C.1. -/
theorem mills_lower (a : ℝ) (ha : 0 ≤ a) :
    normalDensity a / (1 + a) ≤ normalTailReal a := by
  have hderiv : ∀ x ∈ Ici a,
      HasDerivAt (millsAux 1) (millsAuxDeriv 1 x) x := by
    intro x hx
    apply hasDerivAt_millsAux
    change a ≤ x at hx
    linarith
  have hderivNonpos : ∀ x ∈ Ioi a, millsAuxDeriv 1 x ≤ 0 := by
    intro x hx
    exact millsAuxDeriv_nonpos 1 (by norm_num) (ha.trans hx.le)
  have hint : IntegrableOn (millsAuxDeriv 1) (Ioi a) :=
    integrableOn_Ioi_deriv_of_nonpos' hderiv hderivNonpos
      (millsAux_tendsto_atTop 1)
  have hftc := integral_Ioi_of_hasDerivAt_of_nonpos'
    hderiv hderivNonpos (millsAux_tendsto_atTop 1)
  have hnegint : (∫ x in Ioi a, -millsAuxDeriv 1 x) = millsAux 1 a := by
    rw [MeasureTheory.integral_neg, hftc]
    simp
  have hmono : (∫ x in Ioi a, -millsAuxDeriv 1 x) ≤
      ∫ x in Ioi a, normalDensity x := by
    exact setIntegral_mono_on hint.neg integrable_normalDensity.integrableOn
      measurableSet_Ioi fun x hx =>
        neg_millsAuxDeriv_one_le_density (ha.trans hx.le)
  rw [hnegint] at hmono
  rw [normalTailReal_eq_integral]
  simpa [millsAux] using hmono

/-- Upper Mills estimate in Lemma C.1. -/
theorem mills_upper (a : ℝ) (ha : 0 ≤ a) :
    normalTailReal a ≤ 2 * normalDensity a / (1 + a) := by
  have hderiv : ∀ x ∈ Ici a,
      HasDerivAt (millsAux 2) (millsAuxDeriv 2 x) x := by
    intro x hx
    apply hasDerivAt_millsAux
    change a ≤ x at hx
    linarith
  have hderivNonpos : ∀ x ∈ Ioi a, millsAuxDeriv 2 x ≤ 0 := by
    intro x hx
    exact millsAuxDeriv_nonpos 2 (by norm_num) (ha.trans hx.le)
  have hint : IntegrableOn (millsAuxDeriv 2) (Ioi a) :=
    integrableOn_Ioi_deriv_of_nonpos' hderiv hderivNonpos
      (millsAux_tendsto_atTop 2)
  have hftc := integral_Ioi_of_hasDerivAt_of_nonpos'
    hderiv hderivNonpos (millsAux_tendsto_atTop 2)
  have hnegint : (∫ x in Ioi a, -millsAuxDeriv 2 x) = millsAux 2 a := by
    rw [MeasureTheory.integral_neg, hftc]
    simp
  have hmono : (∫ x in Ioi a, normalDensity x) ≤
      ∫ x in Ioi a, -millsAuxDeriv 2 x := by
    exact setIntegral_mono_on integrable_normalDensity.integrableOn hint.neg
      measurableSet_Ioi fun x hx =>
        density_le_neg_millsAuxDeriv_two (ha.trans hx.le)
  rw [hnegint] at hmono
  rw [normalTailReal_eq_integral]
  simpa [millsAux] using hmono

end Concrete

end

end UniformRandomMALA
