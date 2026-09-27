import UniformRandomMALA.Concrete.NonconvexPotential

/-!
# Subcritical gradient exponential moments without convexity

This is the target-moment input to the rejection proof. It follows from
the Gaussian-convolution argument using only a Lipschitz gradient and an
integrable Boltzmann weight. In particular, no moment of the position is
assumed.
-/

namespace UniformRandomMALA.Concrete.NonconvexPotential

open MeasureTheory ProbabilityTheory
noncomputable section
variable {d : ℕ} (V : NonconvexPotential d)

private lemma subcritical_parameter {c : ℝ} (hc : 0 < c)
    (hsmall : 2 * V.L * c < 1) :
    let a := (1 - 2 * V.L * c) / (4 * c)
    0 < a ∧ a + V.L / 2 = 1 / (4 * c) := by
  dsimp
  constructor
  · exact div_pos (sub_pos.mpr hsmall) (by positivity)
  · field_simp
    ring

theorem integrable_exp_mul_gradU_norm_sq
    (c : ℝ) (hc : 0 ≤ c) (hsmall : 2 * V.L * c < 1) :
    Integrable (fun x => Real.exp (c * ‖V.gradU x‖ ^ 2))
      (V.target : Measure (State d)) := by
  rcases eq_or_lt_of_le hc with rfl | hc
  · simp
  let a := (1 - 2 * V.L * c) / (4 * c)
  obtain ⟨ha, hab⟩ := V.subcritical_parameter hc hsmall
  have h := V.integrable_exp_gradU_norm_sq a ha
  convert h using 1
  ext x
  congr 1
  rw [hab]
  field_simp

/-- A convenient integer-power version of the sharper Gaussian-convolution
bound, with the same form as the finite-Euler target-moment interface. -/
theorem integral_exp_mul_gradU_norm_sq_le
    (c : ℝ) (hc : 0 ≤ c) (hsmall : 2 * V.L * c < 1) :
    (∫ x, Real.exp (c * ‖V.gradU x‖ ^ 2) ∂(V.target : Measure (State d))) ≤
      ((1 - 2 * V.L * c) ^ d)⁻¹ := by
  rcases eq_or_lt_of_le hc with rfl | hc
  · simp
  let a := (1 - 2 * V.L * c) / (4 * c)
  let b := a + V.L / 2
  obtain ⟨ha, hab⟩ := V.subcritical_parameter hc hsmall
  have hb : 0 < b := add_pos ha (half_pos V.hL)
  have hδ : 0 < 1 - 2 * V.L * c := sub_pos.mpr hsmall
  have hratio : (Real.pi / a) / (Real.pi / b) = (1 - 2 * V.L * c)⁻¹ := by
    dsimp [b]
    rw [hab]
    dsimp [a]
    field_simp [Real.pi_ne_zero]
  have hbase : 1 ≤ (1 - 2 * V.L * c)⁻¹ := by
    rw [← one_div, one_le_div hδ]
    nlinarith [mul_pos V.hL hc]
  calc
    _ = ∫ x, Real.exp (‖V.gradU x‖ ^ 2 / (4 * b))
        ∂(V.target : Measure (State d)) := by
      congr 1
      ext x
      congr 1
      dsimp [b]
      rw [hab]
      field_simp
    _ ≤ (Real.pi / a) ^ ((d : ℝ) / 2) / (Real.pi / b) ^ ((d : ℝ) / 2) :=
      V.integral_exp_gradU_norm_sq_le a ha
    _ = ((1 - 2 * V.L * c)⁻¹) ^ ((d : ℝ) / 2) := by
      rw [← Real.div_rpow (div_pos Real.pi_pos ha).le (div_pos Real.pi_pos hb).le,
        hratio]
    _ ≤ ((1 - 2 * V.L * c)⁻¹) ^ (d : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hbase (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
    _ = _ := by rw [Real.rpow_natCast, inv_pow]

end
end UniformRandomMALA.Concrete.NonconvexPotential
