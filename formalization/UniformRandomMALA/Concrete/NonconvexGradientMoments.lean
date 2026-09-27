import UniformRandomMALA.Concrete.EuclideanTarget
import Mathlib.MeasureTheory.Group.Integral

/-!
# Gradient exponential moments without convexity

The upper Taylor inequality and integrability of the Boltzmann weight are
enough to control exponential moments of the gradient. The proof averages
the upper Taylor inequality against a translated Gaussian and uses Tonelli.
It does not require a minimizer, convexity, or moments of the position.

This is an analytic prerequisite for the full nonconvex scope of Proposition
B.1 (`prop:stationary-rejection`), not a rejection estimate by itself.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

noncomputable section

private lemma integrable_exp_neg_norm_sq {d : ℕ} {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : State d => Real.exp (-b * ‖z‖ ^ 2)) := by
  have hc := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := State d) (b := (b : ℂ)) (c := 0) (w := 0)
    (by exact_mod_cast hb)
  refine hc.norm.congr ?_
  filter_upwards with z
  rw [show (↑‖z‖ : ℂ) ^ 2 = ↑(‖z‖ ^ 2) by norm_cast]
  simp [Complex.norm_exp]
  left
  simp [pow_two, Complex.mul_re]

lemma lintegral_exp_neg_norm_sq {d : ℕ} {b : ℝ} (hb : 0 < b) :
    (∫⁻ z : State d, ENNReal.ofReal (Real.exp (-b * ‖z‖ ^ 2))) =
      ENNReal.ofReal ((Real.pi / b) ^ ((d : ℝ) / 2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_norm_sq hb)
    (ae_of_all _ fun _ => (Real.exp_pos _).le)]
  congr 1
  simpa using GaussianFourier.integral_rexp_neg_mul_sq_norm (V := State d) hb

/-- Completing the square in a Gaussian integral, with no probability
normalization hidden in the statement. -/
lemma lintegral_exp_neg_norm_sq_sub_inner {d : ℕ} {b : ℝ} (hb : 0 < b)
    (g : State d) :
    (∫⁻ z : State d, ENNReal.ofReal (Real.exp (-b * ‖z‖ ^ 2 - inner ℝ g z))) =
      ENNReal.ofReal (Real.exp (‖g‖ ^ 2 / (4 * b))) *
        ENNReal.ofReal ((Real.pi / b) ^ ((d : ℝ) / 2)) := by
  have halg (z : State d) :
      -b * ‖z‖ ^ 2 - inner ℝ g z =
        ‖g‖ ^ 2 / (4 * b) - b * ‖z + (1 / (2 * b)) • g‖ ^ 2 := by
    rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, real_inner_comm z g]
    field_simp
    ring
  simp_rw [halg, sub_eq_add_neg, ← neg_mul, Real.exp_add,
    ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [lintegral_const_mul _ (by fun_prop)]
  congr 1
  rw [lintegral_add_right_eq_self
    (fun z : State d => ENNReal.ofReal (Real.exp (-b * ‖z‖ ^ 2))) ((1 / (2 * b)) • g)]
  exact lintegral_exp_neg_norm_sq hb

/-- A Gaussian convolution bounds the unnormalized gradient exponential
moment. Only the upper Taylor inequality is used; the potential need not be
convex, and the position need not have any finite moments. -/
theorem boltzmann_gradient_exponential_lintegral_bound {d : ℕ}
    (U : State d → ℝ) (g : State d → State d)
    (hU : Measurable U) (hg : Measurable g)
    (L a : ℝ) (hL : 0 < L) (ha : 0 < a)
    (hupper : ∀ x y, U y ≤ U x + inner ℝ (g x) (y - x) + (L / 2) * ‖y - x‖ ^ 2) :
    ENNReal.ofReal ((Real.pi / (a + L / 2)) ^ ((d : ℝ) / 2)) *
      (∫⁻ x : State d, ENNReal.ofReal
        (Real.exp (-U x + ‖g x‖ ^ 2 / (4 * (a + L / 2))))) ≤
    ENNReal.ofReal ((Real.pi / a) ^ ((d : ℝ) / 2)) *
      (∫⁻ x : State d, ENNReal.ofReal (Real.exp (-U x))) := by
  let b := a + L / 2
  have hb : 0 < b := by dsimp [b]; positivity
  have hleft (x : State d) :
      (∫⁻ z : State d, ENNReal.ofReal
        (Real.exp (-U x - b * ‖z‖ ^ 2 - inner ℝ (g x) z))) =
      ENNReal.ofReal (Real.exp (-U x + ‖g x‖ ^ 2 / (4 * b))) *
        ENNReal.ofReal ((Real.pi / b) ^ ((d : ℝ) / 2)) := by
    have he (z : State d) : -U x - b * ‖z‖ ^ 2 - inner ℝ (g x) z =
        -U x + (-b * ‖z‖ ^ 2 - inner ℝ (g x) z) := by ring
    simp_rw [he, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    rw [lintegral_const_mul _ (by fun_prop), lintegral_exp_neg_norm_sq_sub_inner hb]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  have hright (z : State d) :
      (∫⁻ x : State d, ENNReal.ofReal (Real.exp (-U (x + z) - a * ‖z‖ ^ 2))) =
      ENNReal.ofReal (Real.exp (-a * ‖z‖ ^ 2)) *
        (∫⁻ x : State d, ENNReal.ofReal (Real.exp (-U x))) := by
    have he (x : State d) : -U (x + z) - a * ‖z‖ ^ 2 =
        -a * ‖z‖ ^ 2 + -U (x + z) := by ring
    simp_rw [he, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    rw [lintegral_const_mul _ (by fun_prop)]
    congr 1
    exact lintegral_add_right_eq_self
      (fun x : State d => ENNReal.ofReal (Real.exp (-U x))) z
  calc
    _ = ∫⁻ x : State d, ∫⁻ z : State d, ENNReal.ofReal
        (Real.exp (-U x - b * ‖z‖ ^ 2 - inner ℝ (g x) z)) := by
      simp_rw [hleft]
      rw [lintegral_mul_const _ (by fun_prop)]
      exact mul_comm _ _
    _ ≤ ∫⁻ x : State d, ∫⁻ z : State d,
        ENNReal.ofReal (Real.exp (-U (x + z) - a * ‖z‖ ^ 2)) := by
      apply lintegral_mono
      intro x
      apply lintegral_mono
      intro z
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have h := hupper x (x + z)
      simp only [add_sub_cancel_left] at h
      dsimp [b]
      linarith
    _ = ∫⁻ z : State d, ∫⁻ x : State d,
        ENNReal.ofReal (Real.exp (-U (x + z) - a * ‖z‖ ^ 2)) := by
      apply lintegral_lintegral_swap
      fun_prop
    _ = _ := by
      simp_rw [hright]
      rw [lintegral_mul_const _ (by fun_prop), lintegral_exp_neg_norm_sq ha]

/-- Integrability of the unnormalized gradient exponential tilt. -/
theorem boltzmann_gradient_exponential_integrable {d : ℕ}
    (U : State d → ℝ) (g : State d → State d)
    (hU : Measurable U) (hg : Measurable g)
    (L a : ℝ) (hL : 0 < L) (ha : 0 < a)
    (hZ : Integrable (fun x => Real.exp (-U x)))
    (hupper : ∀ x y, U y ≤ U x + inner ℝ (g x) (y - x) + (L / 2) * ‖y - x‖ ^ 2) :
    Integrable (fun x => Real.exp (-U x + ‖g x‖ ^ 2 / (4 * (a + L / 2)))) := by
  refine ⟨(by fun_prop), ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => (Real.exp_pos _).le)]
  have hZfin : (∫⁻ x, ENNReal.ofReal (Real.exp (-U x))) < ∞ :=
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => (Real.exp_pos _).le)).mp hZ.2
  have hbound := boltzmann_gradient_exponential_lintegral_bound U g hU hg L a hL ha hupper
  have hright : ENNReal.ofReal ((Real.pi / a) ^ ((d : ℝ) / 2)) *
      (∫⁻ x : State d, ENNReal.ofReal (Real.exp (-U x))) < ∞ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hZfin
  exact ENNReal.lt_top_of_mul_ne_top_right (lt_of_le_of_lt hbound hright).ne
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (div_pos Real.pi_pos (by positivity)) _)).ne'

/-- The same exponential moment as a Bochner-integrable function under the
Boltzmann measure, without a convexity assumption. -/
theorem integrable_gradient_exponential_boltzmann {d : ℕ}
    (U : State d → ℝ) (g : State d → State d)
    (hU : Measurable U) (hg : Measurable g)
    (L a : ℝ) (hL : 0 < L) (ha : 0 < a)
    (hZ : Integrable (fun x => Real.exp (-U x)))
    (hupper : ∀ x y, U y ≤ U x + inner ℝ (g x) (y - x) + (L / 2) * ‖y - x‖ ^ 2) :
    Integrable (fun x => Real.exp (‖g x‖ ^ 2 / (4 * (a + L / 2))))
      (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-U x)))) := by
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, ← Real.exp_add] using
    boltzmann_gradient_exponential_integrable U g hU hg L a hL ha hZ hupper

end
end UniformRandomMALA.Concrete
