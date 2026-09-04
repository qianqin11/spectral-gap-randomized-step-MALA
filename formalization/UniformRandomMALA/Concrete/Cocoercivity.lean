import UniformRandomMALA.Concrete.EuclideanTarget
import UniformRandomMALA.BaillonHaddad

/-!
# Elementary cocoercivity for the concrete potential

This file derives the exact Baillon--Haddad inequality used by Proposition
3.2 directly from the recorded lower and upper Taylor inequalities.  It does
not import a convex-analysis Baillon--Haddad theorem.
-/

namespace UniformRandomMALA

open scoped RealInnerProductSpace

noncomputable section

namespace Concrete.FirstOrderPotential

variable {d : ℕ} (V : Concrete.FirstOrderPotential d)

/-- One-sided Baillon--Haddad: the Bregman divergence controls the squared
gradient difference.  The proof applies the smooth upper Taylor bound at one
explicit descent point and the convex lower Taylor bound at the comparison
point. -/
theorem gradDiff_sq_div_twoL_le_bregman (x y : State d) :
    ‖V.gradU x - V.gradU y‖ ^ 2 / (2 * V.L) ≤
      V.U x - V.U y -
        @inner ℝ (State d) _ (V.gradU y) (x - y) := by
  let g : State d := V.gradU x - V.gradU y
  let z : State d := x - (1 / V.L) • g
  have hupper := V.upperTaylor x z
  have hlower := V.lowerTaylor y z
  have hmterm : 0 ≤ (V.m / 2) * ‖z - y‖ ^ 2 :=
    mul_nonneg (div_nonneg V.hm.le (by norm_num)) (sq_nonneg _)
  have hlower' :
      V.U y + @inner ℝ (State d) _ (V.gradU y) (z - y) ≤ V.U z := by
    linarith
  have hzsubx : z - x = -(1 / V.L) • g := by
    dsimp [z]
    module
  have hzsuby : z - y = (x - y) - (1 / V.L) • g := by
    dsimp [z]
    module
  have hinnerGX :
      @inner ℝ (State d) _ (V.gradU x) (z - x) =
        -(1 / V.L) *
          @inner ℝ (State d) _ (V.gradU x) g := by
    rw [hzsubx, inner_smul_right]
  have hinnerGY :
      @inner ℝ (State d) _ (V.gradU y) (z - y) =
        @inner ℝ (State d) _ (V.gradU y) (x - y) -
          (1 / V.L) * @inner ℝ (State d) _ (V.gradU y) g := by
    rw [hzsuby, inner_sub_right, inner_smul_right]
  have hnorm : ‖z - x‖ ^ 2 = (1 / V.L) ^ 2 * ‖g‖ ^ 2 := by
    rw [hzsubx, norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (div_nonneg zero_le_one V.hL.le)]
    ring
  rw [hinnerGX, hnorm] at hupper
  rw [hinnerGY] at hlower'
  have hcombine := hlower'.trans hupper
  have hinnerDiff :
      @inner ℝ (State d) _ (V.gradU x) g -
          @inner ℝ (State d) _ (V.gradU y) g = ‖g‖ ^ 2 := by
    rw [← inner_sub_left]
    dsimp [g]
    exact real_inner_self_eq_norm_sq _
  have hL := V.hL
  dsimp [g] at hcombine hinnerDiff ⊢
  field_simp [ne_of_gt hL] at hcombine ⊢
  nlinarith

/-- Concrete cocoercivity of the recorded gradient. -/
theorem gradU_cocoercive (x y : State d) :
    ‖V.gradU x - V.gradU y‖ ^ 2 / V.L ≤
      @inner ℝ (State d) _ (V.gradU x - V.gradU y) (x - y) := by
  have hxy := V.gradDiff_sq_div_twoL_le_bregman x y
  have hyx := V.gradDiff_sq_div_twoL_le_bregman y x
  have hnorm : ‖V.gradU y - V.gradU x‖ ^ 2 =
      ‖V.gradU x - V.gradU y‖ ^ 2 := by
    rw [← neg_sub, norm_neg]
  have hsub : y - x = -(x - y) := by module
  rw [hnorm, hsub, inner_neg_right] at hyx
  have hsum := add_le_add hxy hyx
  have hsum' :
      ‖V.gradU x - V.gradU y‖ ^ 2 / V.L ≤
        @inner ℝ (State d) _ (V.gradU x) (x - y) -
          @inner ℝ (State d) _ (V.gradU y) (x - y) := by
    calc
      ‖V.gradU x - V.gradU y‖ ^ 2 / V.L =
          ‖V.gradU x - V.gradU y‖ ^ 2 / (2 * V.L) +
            ‖V.gradU x - V.gradU y‖ ^ 2 / (2 * V.L) := by ring
      _ ≤ (V.U x - V.U y -
            @inner ℝ (State d) _ (V.gradU y) (x - y)) +
          (V.U y - V.U x -
            -@inner ℝ (State d) _ (V.gradU x) (x - y)) := hsum
      _ = @inner ℝ (State d) _ (V.gradU x) (x - y) -
          @inner ℝ (State d) _ (V.gradU y) (x - y) := by ring
  simpa [inner_sub_left] using hsum'

/-- The concrete proposal mean `x - h gradU x` is nonexpansive for
`0 ≤ h ≤ 2/L`. -/
theorem norm_proposalMean_sub_le (h : ℝ) (hh : 0 ≤ h)
    (hhL : h ≤ 2 / V.L) (x y : State d) :
    ‖(x - h • V.gradU x) - (y - h • V.gradU y)‖ ≤ ‖x - y‖ := by
  have hsqIdentity :
      ‖(x - h • V.gradU x) - (y - h • V.gradU y)‖ ^ 2 =
        ‖x - y‖ ^ 2 -
          2 * h * @inner ℝ (State d) _
            (V.gradU x - V.gradU y) (x - y) +
          h ^ 2 * ‖V.gradU x - V.gradU y‖ ^ 2 := by
    rw [show (x - h • V.gradU x) - (y - h • V.gradU y) =
        (x - y) - h • (V.gradU x - V.gradU y) by module]
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hh, inner_smul_right, real_inner_comm]
    ring
  have hsq := proposal_mean_nonexpansive_sq V.L h
    (‖x - y‖ ^ 2) (‖V.gradU x - V.gradU y‖ ^ 2)
    (@inner ℝ (State d) _ (V.gradU x - V.gradU y) (x - y))
    V.hL hh hhL (sq_nonneg _) (V.gradU_cocoercive x y)
  rw [← hsqIdentity] at hsq
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

end Concrete.FirstOrderPotential

end

end UniformRandomMALA
