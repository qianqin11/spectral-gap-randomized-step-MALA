import UniformRandomMALA.Concrete.NonconvexGradientMGF

/-! # Target inputs for the nonconvex Euler–RWM comparison

Normalization cancels in the Metropolis ratio. The required fourth gradient
moment follows from the proved exponential moment, with no position-moment
or convexity assumption.
-/

namespace UniformRandomMALA.Concrete.NonconvexPotential
open MeasureTheory
open scoped ENNReal
noncomputable section
variable {d : ℕ} (V : NonconvexPotential d)

lemma targetDensity_ratio (x y : State d) :
    V.targetDensity y / V.targetDensity x =
      ENNReal.ofReal (Real.exp (V.U x - V.U y)) := by
  have hmass : V.boltzmannFiniteMeasure.mass ≠ 0 :=
    V.boltzmannFiniteMeasure.mass_nonzero_iff.mpr V.boltzmannFiniteMeasure_ne_zero
  unfold targetDensity boltzmannDensity boltzmannWeight
  rw [ENNReal.mul_div_mul_left]
  · rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos (-V.U x))]
    congr 1
    rw [← Real.exp_sub]
    congr 1
    ring
  · exact ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top
  · exact ENNReal.inv_ne_top.mpr (ENNReal.coe_ne_zero.mpr hmass)

theorem integrable_gradU_norm_fourth :
    Integrable (fun x : State d => ‖V.gradU x‖ ^ 4)
      (V.target : Measure (State d)) := by
  have hL := V.hL
  let c : ℝ := 1 / (4 * V.L)
  have hc : 0 < c := by dsimp [c]; positivity
  have hs : 2 * V.L * c < 1 := by
    dsimp [c]
    rw [mul_one_div, div_lt_one (by positivity)]
    linarith [V.hL]
  have hExp := V.integrable_exp_mul_gradU_norm_sq c hc.le hs
  have hMajor := hExp.const_mul (2 / c ^ 2)
  apply hMajor.mono
  · exact (V.continuous_gradU.norm.pow 4).aestronglyMeasurable
  · exact ae_of_all _ fun x => by
      have hpow := Real.pow_div_factorial_le_exp
        (x := c * ‖V.gradU x‖ ^ 2) (by positivity) 2
      norm_num [Nat.factorial] at hpow
      have hbound : ‖V.gradU x‖ ^ 4 ≤
          2 / c ^ 2 * Real.exp (c * ‖V.gradU x‖ ^ 2) := by
        apply (mul_le_mul_iff_of_pos_left (sq_pos_of_pos hc)).mp
        field_simp
        nlinarith [hpow]
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) 4),
        Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hbound

end
end UniformRandomMALA.Concrete.NonconvexPotential
