import UniformRandomMALA.Concrete.EuclideanTarget
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv

/-!
# From Hessian bounds to the first-order potential interface

This module supplies the coordinate-free calculus bridge from the assumptions
stated in the paper to the interface used by the randomized-MALA proof.  The
Hessian is the actual second Fréchet derivative of `U`, evaluated as a
quadratic form.  The gradient stored in the resulting `FirstOrderPotential`
is mathlib's Riesz gradient `gradient U`; it is not an independently recorded
vector field.

The two Taylor inequalities are obtained by restricting `U` to an affine
line and applying the one-dimensional second-derivative criterion for
convexity.  The Lipschitz bound is then derived from the Taylor inequalities
through the elementary Baillon--Haddad argument.  In particular, the
construction does not assume the conclusion it is intended to prove.
-/

namespace UniformRandomMALA.Concrete

open scoped Gradient RealInnerProductSpace

noncomputable section

variable {d : ℕ}

local instance realNormedAddCommGroupIP : NormedAddCommGroup ℝ :=
  Real.normedAddCommGroup
local instance realNormedSpaceIP : NormedSpace ℝ ℝ :=
  RCLike.toInnerProductSpaceReal.toNormedSpace

private abbrev IPHasDerivAt (f : ℝ → ℝ) (f' x : ℝ) : Prop :=
  @HasDerivAt ℝ _ ℝ realNormedAddCommGroupIP.toAddCommGroup
    realNormedSpaceIP.toModule _ _ f f' x

private lemma IPHasDerivAt.toStandard {f : ℝ → ℝ} {f' x : ℝ}
    (h : IPHasDerivAt f f' x) : HasDerivAt f f' x := by
  rw [IPHasDerivAt, HasDerivAt, HasDerivAtFilter] at h
  rw [HasDerivAt, HasDerivAtFilter]
  constructor
  simpa [ContinuousLinearMap.toSpanSingleton] using h.isLittleOTVS



/-- A `C²` Euclidean potential whose actual second Fréchet derivative lies
between `m I` and `L I` as a quadratic form. -/
structure HessianBoundedPotential (d : ℕ) where
  U : State d → ℝ
  m : ℝ
  L : ℝ
  hd : 0 < d
  hm : 0 < m
  hmL : m ≤ L
  contDiff_U : ContDiff ℝ 2 U
  hessian_lower : ∀ x v,
    m * ‖v‖ ^ 2 ≤ iteratedFDeriv ℝ 2 U x ![v, v]
  hessian_upper : ∀ x v,
    iteratedFDeriv ℝ 2 U x ![v, v] ≤ L * ‖v‖ ^ 2

namespace HessianBoundedPotential

variable (V : HessianBoundedPotential d)

lemma line_hasDerivAt (x v : State d) (s : ℝ) :
    HasDerivAt (fun r : ℝ => V.U (x + r • v))
      (fderiv ℝ V.U (x + s • v) v) s := by
  have ha : HasDerivAt (fun r : ℝ => x + r • v) v s := by
    simpa using ((hasDerivAt_id s).smul_const v).const_add x
  simpa [Function.comp_def] using
    (V.contDiff_U.differentiable (by norm_num) (x + s • v) |>.hasFDerivAt
      |>.comp s ha.hasFDerivAt |>.hasDerivAt)

lemma line_deriv_hasDerivAt (x v : State d) (s : ℝ) :
    HasDerivAt (fun r : ℝ => fderiv ℝ V.U (x + r • v) v)
      (iteratedFDeriv ℝ 2 V.U (x + s • v) ![v, v]) s := by
  have ha : HasDerivAt (fun r : ℝ => x + r • v) v s := by
    simpa using ((hasDerivAt_id s).smul_const v).const_add x
  have hd : HasFDerivAt (fderiv ℝ V.U)
      (fderiv ℝ (fderiv ℝ V.U) (x + s • v)) (x + s • v) :=
    (V.contDiff_U.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) (x + s • v) |>.hasFDerivAt
  have happ := hd.clm_apply (hasFDerivAt_const (x := x + s • v) v)
  have hcomp := happ.comp s ha.hasFDerivAt
  simpa [iteratedFDeriv_two_apply, Function.comp_def,
    ContinuousLinearMap.flip_apply] using hcomp.hasDerivAt

lemma lowerResidual_hasDerivAt (x v : State d) (s : ℝ) :
    HasDerivAt
      (fun r : ℝ => V.U (x + r • v) - V.U x -
        r * fderiv ℝ V.U x v - (V.m / 2) * r ^ 2 * ‖v‖ ^ 2)
      (fderiv ℝ V.U (x + s • v) v - fderiv ℝ V.U x v -
        V.m * s * ‖v‖ ^ 2) s := by
  have hlin : HasDerivAt (fun r : ℝ => r * fderiv ℝ V.U x v)
      (fderiv ℝ V.U x v) s := by
    simpa using (hasDerivAt_id s).mul_const (fderiv ℝ V.U x v)
  have hquad : HasDerivAt (fun r : ℝ => (V.m / 2) * r ^ 2 * ‖v‖ ^ 2)
      (V.m * s * ‖v‖ ^ 2) s := by
    have hraw : HasDerivAt (fun r : ℝ => (V.m / 2) * r ^ 2 * ‖v‖ ^ 2)
        ((V.m / 2) * (2 * s) * ‖v‖ ^ 2) s := by
      simpa [id_eq] using
        (((hasDerivAt_id s).pow 2).const_mul (V.m / 2)).mul_const (‖v‖ ^ 2)
    exact hraw.congr_deriv (by ring)
  have h := (((V.line_hasDerivAt x v s).sub_const (V.U x)).sub hlin).sub hquad
  apply IPHasDerivAt.toStandard
  convert h using 1
  funext r
  simp only [Pi.sub_apply]

lemma lowerResidual_deriv_hasDerivAt (x v : State d) (s : ℝ) :
    HasDerivAt
      (fun r : ℝ => fderiv ℝ V.U (x + r • v) v - fderiv ℝ V.U x v -
        V.m * r * ‖v‖ ^ 2)
      (iteratedFDeriv ℝ 2 V.U (x + s • v) ![v, v] - V.m * ‖v‖ ^ 2) s := by
  have hlin : HasDerivAt (fun r : ℝ => V.m * r * ‖v‖ ^ 2)
      (V.m * ‖v‖ ^ 2) s := by
    simpa [id_eq, mul_assoc] using
      ((hasDerivAt_id s).const_mul V.m).mul_const (‖v‖ ^ 2)
  have h := ((V.line_deriv_hasDerivAt x v s).sub_const (fderiv ℝ V.U x v)).sub hlin
  apply IPHasDerivAt.toStandard
  convert h using 1
  funext r
  simp only [Pi.sub_apply]

lemma lowerTaylor (x y : State d) :
    V.U x + @inner ℝ (State d) _ (∇ V.U x) (y - x) +
      (V.m / 2) * ‖y - x‖ ^ 2 ≤ V.U y := by
  let v : State d := y - x
  let g : ℝ → ℝ := fun r => V.U (x + r • v) - V.U x -
    r * fderiv ℝ V.U x v - (V.m / 2) * r ^ 2 * ‖v‖ ^ 2
  let g' : ℝ → ℝ := fun r => fderiv ℝ V.U (x + r • v) v - fderiv ℝ V.U x v -
    V.m * r * ‖v‖ ^ 2
  let g'' : ℝ → ℝ := fun r => iteratedFDeriv ℝ 2 V.U (x + r • v) ![v, v] -
    V.m * ‖v‖ ^ 2
  have hg1 : ∀ s, HasDerivAt g (g' s) s := fun s => V.lowerResidual_hasDerivAt x v s
  have hg2 : ∀ s, HasDerivAt g' (g'' s) s := fun s => V.lowerResidual_deriv_hasDerivAt x v s
  have hconv : ConvexOn ℝ Set.univ g := by
    apply convexOn_of_hasDerivWithinAt2_nonneg convex_univ
      (continuous_iff_continuousAt.mpr (fun s => (hg1 s).continuousAt)).continuousOn
      (fun s _ => (hg1 s).hasDerivWithinAt)
      (fun s _ => (hg2 s).hasDerivWithinAt)
    intro s hs
    dsimp [g'']
    exact sub_nonneg.mpr (V.hessian_lower (x + s • v) v)
  have hslope := hconv.le_slope_of_hasDerivAt (by simp) (by simp) zero_lt_one (hg1 0)
  dsimp [g, g', v] at hslope
  rw [inner_gradient_left]
  rw [map_sub]
  simp [slope] at hslope
  linarith

lemma upperResidual_hasDerivAt (x v : State d) (s : ℝ) :
    HasDerivAt
      (fun r : ℝ => V.U x + r * fderiv ℝ V.U x v +
        (V.L / 2) * r ^ 2 * ‖v‖ ^ 2 - V.U (x + r • v))
      (fderiv ℝ V.U x v + V.L * s * ‖v‖ ^ 2 -
        fderiv ℝ V.U (x + s • v) v) s := by
  have hlin : HasDerivAt (fun r : ℝ => r * fderiv ℝ V.U x v)
      (fderiv ℝ V.U x v) s := by
    simpa using (hasDerivAt_id s).mul_const (fderiv ℝ V.U x v)
  have hquad : HasDerivAt (fun r : ℝ => (V.L / 2) * r ^ 2 * ‖v‖ ^ 2)
      (V.L * s * ‖v‖ ^ 2) s := by
    have hraw : HasDerivAt (fun r : ℝ => (V.L / 2) * r ^ 2 * ‖v‖ ^ 2)
        ((V.L / 2) * (2 * s) * ‖v‖ ^ 2) s := by
      simpa [id_eq] using
        (((hasDerivAt_id s).pow 2).const_mul (V.L / 2)).mul_const (‖v‖ ^ 2)
    exact hraw.congr_deriv (by ring)
  have h := ((hlin.const_add (V.U x)).add hquad).sub (V.line_hasDerivAt x v s)
  apply IPHasDerivAt.toStandard
  convert h using 1
  funext r
  simp only [Pi.sub_apply, Pi.add_apply]

lemma upperResidual_deriv_hasDerivAt (x v : State d) (s : ℝ) :
    HasDerivAt
      (fun r : ℝ => fderiv ℝ V.U x v + V.L * r * ‖v‖ ^ 2 -
        fderiv ℝ V.U (x + r • v) v)
      (V.L * ‖v‖ ^ 2 - iteratedFDeriv ℝ 2 V.U (x + s • v) ![v, v]) s := by
  have hlin : HasDerivAt (fun r : ℝ => V.L * r * ‖v‖ ^ 2)
      (V.L * ‖v‖ ^ 2) s := by
    simpa [id_eq, mul_assoc] using
      ((hasDerivAt_id s).const_mul V.L).mul_const (‖v‖ ^ 2)
  have h := (hlin.const_add (fderiv ℝ V.U x v)).sub (V.line_deriv_hasDerivAt x v s)
  apply IPHasDerivAt.toStandard
  convert h using 1
  funext r
  simp only [Pi.sub_apply]

lemma upperTaylor (x y : State d) :
    V.U y ≤ V.U x + @inner ℝ (State d) _ (∇ V.U x) (y - x) +
      (V.L / 2) * ‖y - x‖ ^ 2 := by
  let v : State d := y - x
  let g : ℝ → ℝ := fun r => V.U x + r * fderiv ℝ V.U x v +
    (V.L / 2) * r ^ 2 * ‖v‖ ^ 2 - V.U (x + r • v)
  let g' : ℝ → ℝ := fun r => fderiv ℝ V.U x v + V.L * r * ‖v‖ ^ 2 -
    fderiv ℝ V.U (x + r • v) v
  let g'' : ℝ → ℝ := fun r => V.L * ‖v‖ ^ 2 -
    iteratedFDeriv ℝ 2 V.U (x + r • v) ![v, v]
  have hg1 : ∀ s, HasDerivAt g (g' s) s := fun s => V.upperResidual_hasDerivAt x v s
  have hg2 : ∀ s, HasDerivAt g' (g'' s) s := fun s => V.upperResidual_deriv_hasDerivAt x v s
  have hconv : ConvexOn ℝ Set.univ g := by
    apply convexOn_of_hasDerivWithinAt2_nonneg convex_univ
      (continuous_iff_continuousAt.mpr (fun s => (hg1 s).continuousAt)).continuousOn
      (fun s _ => (hg1 s).hasDerivWithinAt)
      (fun s _ => (hg2 s).hasDerivWithinAt)
    intro s hs
    dsimp [g'']
    exact sub_nonneg.mpr (V.hessian_upper (x + s • v) v)
  have hslope := hconv.le_slope_of_hasDerivAt (by simp) (by simp) zero_lt_one (hg1 0)
  dsimp [g, g', v] at hslope
  rw [inner_gradient_left]
  rw [map_sub]
  simp [slope] at hslope
  linarith

lemma hL : 0 < V.L := lt_of_lt_of_le V.hm V.hmL

lemma gradientDiff_sq_div_twoL_le_bregman (x y : State d) :
    ‖∇ V.U x - ∇ V.U y‖ ^ 2 / (2 * V.L) ≤
      V.U x - V.U y - @inner ℝ (State d) _ (∇ V.U y) (x - y) := by
  let q : State d := ∇ V.U x - ∇ V.U y
  let z : State d := x - (1 / V.L) • q
  have hupper := V.upperTaylor x z
  have hlower := V.lowerTaylor y z
  have hmterm : 0 ≤ (V.m / 2) * ‖z - y‖ ^ 2 :=
    mul_nonneg (div_nonneg V.hm.le (by norm_num)) (sq_nonneg _)
  have hlower' :
      V.U y + @inner ℝ (State d) _ (∇ V.U y) (z - y) ≤ V.U z := by
    linarith
  have hzsubx : z - x = -(1 / V.L) • q := by
    dsimp [z]
    module
  have hzsuby : z - y = (x - y) - (1 / V.L) • q := by
    dsimp [z]
    module
  have hinnerQX :
      @inner ℝ (State d) _ (∇ V.U x) (z - x) =
        -(1 / V.L) * @inner ℝ (State d) _ (∇ V.U x) q := by
    rw [hzsubx, inner_smul_right]
  have hinnerQY :
      @inner ℝ (State d) _ (∇ V.U y) (z - y) =
        @inner ℝ (State d) _ (∇ V.U y) (x - y) -
          (1 / V.L) * @inner ℝ (State d) _ (∇ V.U y) q := by
    rw [hzsuby, inner_sub_right, inner_smul_right]
  have hnorm : ‖z - x‖ ^ 2 = (1 / V.L) ^ 2 * ‖q‖ ^ 2 := by
    rw [hzsubx, norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (div_nonneg zero_le_one V.hL.le)]
    ring
  rw [hinnerQX, hnorm] at hupper
  rw [hinnerQY] at hlower'
  have hcombine := hlower'.trans hupper
  have hinnerDiff :
      @inner ℝ (State d) _ (∇ V.U x) q -
          @inner ℝ (State d) _ (∇ V.U y) q = ‖q‖ ^ 2 := by
    rw [← inner_sub_left]
    dsimp [q]
    exact real_inner_self_eq_norm_sq _
  have hL := V.hL
  dsimp [q] at hcombine hinnerDiff ⊢
  field_simp [ne_of_gt hL] at hcombine ⊢
  nlinarith

lemma gradient_cocoercive (x y : State d) :
    ‖∇ V.U x - ∇ V.U y‖ ^ 2 / V.L ≤
      @inner ℝ (State d) _ (∇ V.U x - ∇ V.U y) (x - y) := by
  have hxy := V.gradientDiff_sq_div_twoL_le_bregman x y
  have hyx := V.gradientDiff_sq_div_twoL_le_bregman y x
  have hnorm : ‖∇ V.U y - ∇ V.U x‖ ^ 2 = ‖∇ V.U x - ∇ V.U y‖ ^ 2 := by
    rw [← neg_sub, norm_neg]
  have hsub : y - x = -(x - y) := by module
  rw [hnorm, hsub, inner_neg_right] at hyx
  have hsum := add_le_add hxy hyx
  have hsum' :
      ‖∇ V.U x - ∇ V.U y‖ ^ 2 / V.L ≤
        @inner ℝ (State d) _ (∇ V.U x) (x - y) -
          @inner ℝ (State d) _ (∇ V.U y) (x - y) := by
    calc
      ‖∇ V.U x - ∇ V.U y‖ ^ 2 / V.L =
          ‖∇ V.U x - ∇ V.U y‖ ^ 2 / (2 * V.L) +
            ‖∇ V.U x - ∇ V.U y‖ ^ 2 / (2 * V.L) := by ring
      _ ≤ (V.U x - V.U y - @inner ℝ (State d) _ (∇ V.U y) (x - y)) +
          (V.U y - V.U x - -@inner ℝ (State d) _ (∇ V.U x) (x - y)) := hsum
      _ = @inner ℝ (State d) _ (∇ V.U x) (x - y) -
          @inner ℝ (State d) _ (∇ V.U y) (x - y) := by ring
  simpa [inner_sub_left] using hsum'

lemma norm_gradient_sub_le (x y : State d) :
    ‖∇ V.U x - ∇ V.U y‖ ≤ V.L * ‖x - y‖ := by
  let a := ‖∇ V.U x - ∇ V.U y‖
  let b := ‖x - y‖
  have hcoco := V.gradient_cocoercive x y
  have hcs : @inner ℝ (State d) _ (∇ V.U x - ∇ V.U y) (x - y) ≤ a * b :=
    le_trans (le_abs_self _) (abs_real_inner_le_norm _ _)
  have hsq : a ^ 2 ≤ V.L * (a * b) := by
    have hm := (div_le_iff₀ V.hL).mp hcoco
    dsimp [a, b]
    nlinarith [mul_le_mul_of_nonneg_right hcs V.hL.le]
  by_cases ha : a = 0
  · change a ≤ V.L * b
    rw [ha]
    exact mul_nonneg V.hL.le (by dsimp [b]; positivity)
  · have ha_pos : 0 < a := lt_of_le_of_ne (norm_nonneg _) (Ne.symm ha)
    nlinarith

lemma gradient_lipschitz :
    LipschitzWith ⟨V.L, V.hL.le⟩ (∇ V.U) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ‖∇ V.U x - ∇ V.U y‖ ≤ V.L * ‖x - y‖
  exact V.norm_gradient_sub_le x y

lemma continuous_gradient : Continuous (∇ V.U) := by
  exact (InnerProductSpace.toDual ℝ (State d)).symm.continuous.comp
    (V.contDiff_U.continuous_fderiv (by norm_num))

def toFirstOrderPotential : FirstOrderPotential d where
  U := V.U
  gradU := ∇ V.U
  m := V.m
  L := V.L
  hd := V.hd
  hm := V.hm
  hmL := V.hmL
  continuous_U := V.contDiff_U.continuous
  continuous_gradU := V.continuous_gradient
  lowerTaylor := V.lowerTaylor
  upperTaylor := V.upperTaylor
  grad_lipschitz := V.gradient_lipschitz

end HessianBoundedPotential
end
end UniformRandomMALA.Concrete
