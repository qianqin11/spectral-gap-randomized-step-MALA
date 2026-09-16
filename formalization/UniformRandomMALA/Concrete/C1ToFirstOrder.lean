import UniformRandomMALA.Concrete.EuclideanTarget
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# From the manuscript's first-order assumptions to the concrete interface

`C1Potential` uses the actual Riesz gradient of a continuously differentiable
potential. Strong convexity is stated by its first-order supporting inequality,
and smoothness by a Lipschitz bound on that gradient. In particular, no Hessian,
second derivative, upper Taylor bound, or analytic certificate is an input.

The upper Taylor bound is the usual descent lemma (Nesterov, 2004,
Theorem 2.1.5). Here it is proved by differentiating along an affine line and
applying the one-dimensional monotonicity theorem. The resulting record feeds
the existing discrete-time proof without changing its mathematical assumptions.
-/

namespace UniformRandomMALA.Concrete

open scoped Gradient RealInnerProductSpace

noncomputable section

variable {d : ℕ}

local instance c1RealNormedAddCommGroupIP : NormedAddCommGroup ℝ :=
  Real.normedAddCommGroup
local instance c1RealNormedSpaceIP : NormedSpace ℝ ℝ :=
  RCLike.toInnerProductSpaceReal.toNormedSpace

private abbrev C1IPHasDerivAt (f : ℝ → ℝ) (f' x : ℝ) : Prop :=
  @HasDerivAt ℝ _ ℝ c1RealNormedAddCommGroupIP.toAddCommGroup
    c1RealNormedSpaceIP.toModule _ _ f f' x

private lemma C1IPHasDerivAt.toStandard {f : ℝ → ℝ} {f' x : ℝ}
    (h : C1IPHasDerivAt f f' x) : HasDerivAt f f' x := by
  rw [C1IPHasDerivAt, HasDerivAt, HasDerivAtFilter] at h
  rw [HasDerivAt, HasDerivAtFilter]
  constructor
  simpa [ContinuousLinearMap.toSpanSingleton] using h.isLittleOTVS

/-- Exactly the revised standing assumptions: `C¹`, positive strong convexity,
and a globally Lipschitz actual gradient. -/
structure C1Potential (d : ℕ) where
  U : State d → ℝ
  m : ℝ
  L : ℝ
  hd : 0 < d
  hm : 0 < m
  hmL : m ≤ L
  contDiff_U : ContDiff ℝ 1 U
  lowerTaylor : ∀ x y,
    U x + @inner ℝ (State d) _ (∇ U x) (y - x) +
      (m / 2) * ‖y - x‖ ^ 2 ≤ U y
  gradient_lipschitz : LipschitzWith ⟨L, le_of_lt (lt_of_lt_of_le hm hmL)⟩ (∇ U)

namespace C1Potential

variable (V : C1Potential d)

lemma hL : 0 < V.L := lt_of_lt_of_le V.hm V.hmL

lemma line_hasDerivAt (x v : State d) (s : ℝ) :
    HasDerivAt (fun r : ℝ => V.U (x + r • v))
      (fderiv ℝ V.U (x + s • v) v) s := by
  have ha : HasDerivAt (fun r : ℝ => x + r • v) v s := by
    simpa using ((hasDerivAt_id s).smul_const v).const_add x
  simpa [Function.comp_def] using
    (V.contDiff_U.differentiable (by norm_num) (x + s • v) |>.hasFDerivAt
      |>.comp s ha.hasFDerivAt |>.hasDerivAt)

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
  apply C1IPHasDerivAt.toStandard
  convert h using 1
  funext r
  simp only [Pi.sub_apply, Pi.add_apply]

lemma upperResidual_deriv_nonneg (x v : State d) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ fderiv ℝ V.U x v + V.L * s * ‖v‖ ^ 2 -
      fderiv ℝ V.U (x + s • v) v := by
  have hnorm := V.gradient_lipschitz.norm_sub_le (x + s • v) x
  change ‖∇ V.U (x + s • v) - ∇ V.U x‖ ≤
    V.L * ‖(x + s • v) - x‖ at hnorm
  have hnorm' : ‖∇ V.U (x + s • v) - ∇ V.U x‖ ≤ V.L * s * ‖v‖ := by
    simpa [norm_smul, Real.norm_of_nonneg hs, mul_assoc] using hnorm
  have hinner :
      @inner ℝ (State d) _ (∇ V.U (x + s • v)) v -
          @inner ℝ (State d) _ (∇ V.U x) v ≤
        ‖∇ V.U (x + s • v) - ∇ V.U x‖ * ‖v‖ := by
    rw [← inner_sub_left]
    exact (le_abs_self _).trans (abs_real_inner_le_norm _ _)
  have hmul := mul_le_mul_of_nonneg_right hnorm' (norm_nonneg v)
  rw [inner_gradient_left, inner_gradient_left] at hinner
  nlinarith

/-- The descent lemma from a Lipschitz actual gradient, without using `C²`. -/
lemma upperTaylor (x y : State d) :
    V.U y ≤ V.U x + @inner ℝ (State d) _ (∇ V.U x) (y - x) +
      (V.L / 2) * ‖y - x‖ ^ 2 := by
  let v : State d := y - x
  let g : ℝ → ℝ := fun r => V.U x + r * fderiv ℝ V.U x v +
    (V.L / 2) * r ^ 2 * ‖v‖ ^ 2 - V.U (x + r • v)
  let g' : ℝ → ℝ := fun r => fderiv ℝ V.U x v + V.L * r * ‖v‖ ^ 2 -
    fderiv ℝ V.U (x + r • v) v
  have hg : ∀ s, HasDerivAt g (g' s) s :=
    fun s => V.upperResidual_hasDerivAt x v s
  have hcont : ContinuousOn g (Set.Icc (0 : ℝ) 1) :=
    (continuous_iff_continuousAt.mpr (fun s => (hg s).continuousAt)).continuousOn
  have hmono : MonotoneOn g (Set.Icc (0 : ℝ) 1) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hcont
      (fun s _ => (hg s).differentiableAt.differentiableWithinAt)
      (fun s hs => by
        rw [(hg s).deriv]
        have hs' : s ∈ Set.Ioo (0 : ℝ) 1 := by
          simpa only [interior_Icc] using hs
        exact V.upperResidual_deriv_nonneg x v hs'.1.le)
  have hendpoint := hmono
    (Set.left_mem_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1))
    (Set.right_mem_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1))
    (by norm_num : (0 : ℝ) ≤ 1)
  dsimp [g, v] at hendpoint
  rw [inner_gradient_left, map_sub]
  norm_num at hendpoint
  linarith

/-- The adapter supplies the internal upper Taylor field rather than assuming it. -/
def toFirstOrderPotential : FirstOrderPotential d where
  U := V.U
  gradU := ∇ V.U
  m := V.m
  L := V.L
  hd := V.hd
  hm := V.hm
  hmL := V.hmL
  continuous_U := V.contDiff_U.continuous
  continuous_gradU := V.gradient_lipschitz.continuous
  lowerTaylor := V.lowerTaylor
  upperTaylor := V.upperTaylor
  grad_lipschitz := V.gradient_lipschitz

@[simp] lemma toFirstOrderPotential_U : V.toFirstOrderPotential.U = V.U := rfl

@[simp] lemma toFirstOrderPotential_gradU :
    V.toFirstOrderPotential.gradU = ∇ V.U := rfl

@[simp] lemma toFirstOrderPotential_m : V.toFirstOrderPotential.m = V.m := rfl

@[simp] lemma toFirstOrderPotential_L : V.toFirstOrderPotential.L = V.L := rfl

end C1Potential

end

end UniformRandomMALA.Concrete
