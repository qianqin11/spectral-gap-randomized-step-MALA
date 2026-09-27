import UniformRandomMALA.Concrete.NonconvexPotential

/-! # Two-sided first-order Taylor control without convexity

The absolute Taylor remainder is the local analytic input used by the
random-walk Metropolis rejection-bias expansion. It requires only the
globally Lipschitz actual gradient.
-/

namespace UniformRandomMALA.Concrete.NonconvexPotential
open MeasureTheory
open scoped Gradient RealInnerProductSpace
noncomputable section
variable {d : ℕ} (V : NonconvexPotential d)

lemma lowerResidual_hasDerivAt (x v : State d) (s : ℝ) :
    HasDerivAt
      (fun r : ℝ => V.U (x + r • v) - V.U x - r * fderiv ℝ V.U x v +
        (V.L / 2) * r ^ 2 * ‖v‖ ^ 2)
      (fderiv ℝ V.U (x + s • v) v - fderiv ℝ V.U x v + V.L * s * ‖v‖ ^ 2) s := by
  have hlin : HasDerivAt (fun r : ℝ => r * fderiv ℝ V.U x v)
      (fderiv ℝ V.U x v) s := by
    simpa using (hasDerivAt_id s).mul_const (fderiv ℝ V.U x v)
  have h := (((V.line_hasDerivAt x v s).sub_const (V.U x)).sub hlin).const_mul 2
    |>.add (V.upperResidual_hasDerivAt x v s)
  have h' := h.congr_deriv (show
    2 * (fderiv ℝ V.U (x + s • v) v - fderiv ℝ V.U x v) +
      (fderiv ℝ V.U x v + V.L * s * ‖v‖ ^ 2 - fderiv ℝ V.U (x + s • v) v) =
    fderiv ℝ V.U (x + s • v) v - fderiv ℝ V.U x v + V.L * s * ‖v‖ ^ 2 by ring)
  have heq : (fun r : ℝ => V.U (x + r • v) - V.U x - r * fderiv ℝ V.U x v +
      (V.L / 2) * r ^ 2 * ‖v‖ ^ 2) =
      (fun r : ℝ => 2 * (V.U (x + r • v) - V.U x - r * fderiv ℝ V.U x v) +
       (V.U x + r * fderiv ℝ V.U x v +
         (V.L / 2) * r ^ 2 * ‖v‖ ^ 2 - V.U (x + r • v))) := by
    funext r
    ring
  rw [heq, HasDerivAt, HasDerivAtFilter]
  rw [HasDerivAt, HasDerivAtFilter] at h'
  constructor
  simpa [ContinuousLinearMap.toSpanSingleton] using h'.isLittleOTVS

lemma lowerResidual_deriv_nonneg (x v : State d) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ fderiv ℝ V.U (x + s • v) v - fderiv ℝ V.U x v + V.L * s * ‖v‖ ^ 2 := by
  have hnorm := V.gradient_lipschitz.norm_sub_le x (x + s • v)
  change ‖∇ V.U x - ∇ V.U (x + s • v)‖ ≤ V.L * ‖x - (x + s • v)‖ at hnorm
  have hnorm' : ‖∇ V.U x - ∇ V.U (x + s • v)‖ ≤ V.L * s * ‖v‖ := by
    simpa [norm_smul, Real.norm_of_nonneg hs, mul_assoc] using hnorm
  have hinner := real_inner_le_norm (∇ V.U x - ∇ V.U (x + s • v)) v
  rw [inner_sub_left, inner_gradient_left, inner_gradient_left] at hinner
  have hmul := mul_le_mul_of_nonneg_right hnorm' (norm_nonneg v)
  nlinarith

/-- The lower Taylor estimate has curvature `−L`; it asserts no convexity. -/
lemma lowerTaylor (x y : State d) :
    V.U x + @inner ℝ (State d) _ (V.gradU x) (y - x) -
      (V.L / 2) * ‖y - x‖ ^ 2 ≤ V.U y := by
  let v := y - x
  let g : ℝ → ℝ := fun r => V.U (x + r • v) - V.U x - r * fderiv ℝ V.U x v +
    (V.L / 2) * r ^ 2 * ‖v‖ ^ 2
  let g' : ℝ → ℝ := fun r => fderiv ℝ V.U (x + r • v) v - fderiv ℝ V.U x v +
    V.L * r * ‖v‖ ^ 2
  have hg : ∀ s, HasDerivAt g (g' s) s := fun s => V.lowerResidual_hasDerivAt x v s
  have hcont : ContinuousOn g (Set.Icc (0 : ℝ) 1) :=
    (continuous_iff_continuousAt.mpr (fun s => (hg s).continuousAt)).continuousOn
  have hmono : MonotoneOn g (Set.Icc (0 : ℝ) 1) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hcont
      (fun s _ => (hg s).differentiableAt.differentiableWithinAt)
      (fun s hs => by
        rw [(hg s).deriv]
        have hs' : s ∈ Set.Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using hs
        exact V.lowerResidual_deriv_nonneg x v hs'.1.le)
  have hend := hmono
    (Set.left_mem_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1))
    (Set.right_mem_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1))
    (by norm_num : (0 : ℝ) ≤ 1)
  dsimp [g, v] at hend
  change V.U x + inner ℝ (∇ V.U x) (y - x) - _ ≤ V.U y
  rw [inner_gradient_left, map_sub]
  norm_num at hend
  linarith

theorem abs_taylor_remainder_le (x y : State d) :
    |V.U y - V.U x - @inner ℝ (State d) _ (V.gradU x) (y - x)| ≤
      (V.L / 2) * ‖y - x‖ ^ 2 := by
  have hu := V.upperTaylor x y
  have hl := V.lowerTaylor x y
  change V.U y ≤ V.U x + inner ℝ (V.gradU x) (y - x) + _ at hu
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end
end UniformRandomMALA.Concrete.NonconvexPotential
