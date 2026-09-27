import UniformRandomMALA.Concrete.NonconvexMALA
import UniformRandomMALA.DiscreteTime.Recursion
import Mathlib.Tactic

/-!
# Euler stability without convexity

The Euler--RWM comparison only needs bounded growth of the deterministic
Euler map over a fixed horizon. The factor `1 + L δ` replaces the
nonexpansive estimate used in the strongly convex proof. The resulting
affine recursion retains the vanishing `√δ` endpoint error.
-/

namespace UniformRandomMALA
open scoped RealInnerProductSpace
noncomputable section

namespace Concrete.NonconvexPotential
variable {d : ℕ} (V : NonconvexPotential d)

/-- Lipschitz growth of the actual Euler drift mean. -/
theorem norm_proposalMean_sub_le_growth (δ : ℝ) (hδ : 0 ≤ δ) (x y : State d) :
    ‖V.proposalMean δ x - V.proposalMean δ y‖ ≤ (1 + V.L * δ) * ‖x - y‖ := by
  have heq : V.proposalMean δ x - V.proposalMean δ y =
      (x - y) - δ • (V.gradU x - V.gradU y) := by
    simp only [proposalMean]
    module
  have hgrad := V.gradient_lipschitz.norm_sub_le x y
  change ‖V.gradU x - V.gradU y‖ ≤ V.L * ‖x - y‖ at hgrad
  rw [heq]
  calc
    _ ≤ ‖x - y‖ + ‖δ • (V.gradU x - V.gradU y)‖ := norm_sub_le _ _
    _ = ‖x - y‖ + δ * ‖V.gradU x - V.gradU y‖ := by
      rw [norm_smul, Real.norm_of_nonneg hδ]
    _ ≤ ‖x - y‖ + δ * (V.L * ‖x - y‖) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hgrad hδ)
    _ = _ := by ring

/-- Squared-distance growth, suitable for the finite coupling recurrence. -/
theorem sq_norm_proposalMean_sub_le_growth (δ : ℝ) (hδ : 0 ≤ δ) (x y : State d) :
    ‖V.proposalMean δ x - V.proposalMean δ y‖ ^ 2 ≤
      (1 + V.L * δ) ^ 2 * ‖x - y‖ ^ 2 := by
  simpa only [mul_pow] using
    pow_le_pow_left₀ (norm_nonneg _) (V.norm_proposalMean_sub_le_growth δ hδ x y) 2

end Concrete.NonconvexPotential

namespace DiscreteTime

/-- A dimension-independent growth coefficient for the nonconvex
Euler--RWM recurrence. It need not be small: the horizon is fixed. -/
def nonconvexEulerGrowth (L : ℝ) : ℝ := 1 + 4 * L + 2 * L ^ 2

lemma nonconvexEulerGrowth_nonneg {L : ℝ} (hL : 0 ≤ L) :
    0 ≤ nonconvexEulerGrowth L := by unfold nonconvexEulerGrowth; positivity

lemma nonconvexEulerGrowth_step {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (1 + δ) * (1 + L * δ) ^ 2 ≤ 1 + nonconvexEulerGrowth L * δ := by
  have hp : 0 ≤ L * δ * (1 - δ) * (2 + 2 * L + L * δ) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hL hδ) (sub_nonneg.mpr hδ1))
      (by positivity)
  unfold nonconvexEulerGrowth
  nlinarith only [hp]

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The cross term is handled before integration using its mean bias,
avoiding a fixed factor greater than one at each time step. -/
theorem biased_pair_quadratic_bound (D b : E) (S ε Q R : ℝ)
    (hε : 0 < ε) (hD : ‖D‖ ≤ Q * R) :
    ‖D‖ ^ 2 + 2 * ⟪D, b⟫ + S ≤
      (1 + ε) * Q ^ 2 * R ^ 2 + S + ‖b‖ ^ 2 / ε := by
  have hcross := real_inner_le_norm D b
  have hyoung : 2 * ‖D‖ * ‖b‖ ≤ ε * ‖D‖ ^ 2 + ‖b‖ ^ 2 / ε := by
    rw [show ε * ‖D‖ ^ 2 + ‖b‖ ^ 2 / ε =
      (ε ^ 2 * ‖D‖ ^ 2 + ‖b‖ ^ 2) / ε by field_simp]
    rw [le_div_iff₀ hε]
    nlinarith [sq_nonneg (ε * ‖D‖ - ‖b‖)]
  have hsq : ‖D‖ ^ 2 ≤ Q ^ 2 * R ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg D) hD 2
  have hmul := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 1 + ε by linarith)
  nlinarith

end Hilbert

/-- The discrete Gronwall estimate remains uniform in the mesh when the
one-step coefficient grows by an arbitrary fixed multiple of the step. -/
theorem coupling_recursion_bound_fixed_horizon_exp
    (a : ℕ → ℝ) (c δ B h : ℝ) (n : ℕ)
    (hc : 0 ≤ c) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (ha0 : a 0 ≤ 0)
    (hstep : ∀ k : ℕ, a (k + 1) ≤ (1 + c * δ) * a k + B * δ * Real.sqrt δ)
    (hhorizon : (n : ℝ) * δ = h) :
    a n ≤ B * h * Real.sqrt δ * Real.exp (c * h) := by
  have hfinite := coupling_recursion_bound_fixed_horizon a c δ B h n hc hδ hB ha0 hstep hhorizon
  have hbase : 1 + c * δ ≤ Real.exp (c * δ) := by
    simpa only [add_comm] using Real.add_one_le_exp (c * δ)
  have hpow : (1 + c * δ) ^ n ≤ Real.exp (c * h) := by
    calc
      _ ≤ (Real.exp (c * δ)) ^ n := pow_le_pow_left₀ (by positivity) hbase n
      _ = Real.exp ((n : ℝ) * (c * δ)) := (Real.exp_nat_mul _ _).symm
      _ = _ := by congr 1; rw [← hhorizon]; ring
  have hh : 0 ≤ h := by rw [← hhorizon]; positivity
  exact hfinite.trans (mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (mul_nonneg hB hh) (Real.sqrt_nonneg δ)))

end DiscreteTime
end
end UniformRandomMALA
