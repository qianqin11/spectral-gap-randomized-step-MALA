import UniformRandomMALA.Concrete.MarkovCLTApproximation

/-!
# Negligible finite-prefix contributions to characteristic functions

Almost-surely vanishing perturbations suffice here because the complex
exponentials are bounded. No moment assumption on the initial observations
is needed.
-/

namespace UniformRandomMALA.Concrete
open MeasureTheory ProbabilityTheory Filter Complex
open scoped ENNReal Topology
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

theorem norm_exp_I_sub_exp_I (x y : ℝ) :
    ‖Complex.exp (Complex.I * x) - Complex.exp (Complex.I * y)‖ =
      ‖Complex.exp (Complex.I * (x - y)) - 1‖ := by
  have heq : Complex.exp (Complex.I * x) - Complex.exp (Complex.I * y) =
      Complex.exp (Complex.I * y) * (Complex.exp (Complex.I * (x - y)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    ring
  rw [heq, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]

theorem characteristic_expectation_sub_tendsto_zero_of_ae_sub_tendsto
    (μ : Measure Ω) [IsFiniteMeasure μ] (X Y : ℕ → Ω → ℝ)
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (hsub : ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω - Y n ω) atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun n => (∫ ω, Complex.exp (Complex.I * ((t * X n ω : ℝ) : ℂ)) ∂μ) -
      ∫ ω, Complex.exp (Complex.I * ((t * Y n ω : ℝ) : ℂ)) ∂μ) atTop (𝓝 0) := by
  have hmX (n : ℕ) : Measurable (fun ω => Complex.exp (Complex.I * ((t * X n ω : ℝ) : ℂ))) := by
    fun_prop
  have hmY (n : ℕ) : Measurable (fun ω => Complex.exp (Complex.I * ((t * Y n ω : ℝ) : ℂ))) := by
    fun_prop
  have hiX (n : ℕ) : Integrable (fun ω => Complex.exp (Complex.I * ((t * X n ω : ℝ) : ℂ))) μ :=
    (integrable_const (1 : ℝ)).mono' (hmX n).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Complex.norm_exp_I_mul_ofReal])
  have hiY (n : ℕ) : Integrable (fun ω => Complex.exp (Complex.I * ((t * Y n ω : ℝ) : ℂ))) μ :=
    (integrable_const (1 : ℝ)).mono' (hmY n).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Complex.norm_exp_I_mul_ofReal])
  have ht := tendsto_integral_of_dominated_convergence
    (F := fun n ω => Complex.exp (Complex.I * ((t * X n ω : ℝ) : ℂ)) -
      Complex.exp (Complex.I * ((t * Y n ω : ℝ) : ℂ))) (f := fun _ => (0 : ℂ)) (fun _ => (2 : ℝ))
    (fun n => ((hmX n).sub (hmY n)).aestronglyMeasurable) (integrable_const 2)
    (fun n => ae_of_all _ fun ω => by
      have h := norm_sub_le (Complex.exp (Complex.I * ((t * X n ω : ℝ) : ℂ)))
        (Complex.exp (Complex.I * ((t * Y n ω : ℝ) : ℂ)))
      simpa only [Complex.norm_exp_I_mul_ofReal, one_add_one_eq_two] using h)
    (hsub.mono fun ω hω => ?_)
  · simpa only [integral_sub (hiX _) (hiY _), integral_zero] using ht
  · apply tendsto_zero_iff_norm_tendsto_zero.2
    have heq (n : ℕ) :
        ‖Complex.exp (Complex.I * ((t * X n ω : ℝ) : ℂ)) -
          Complex.exp (Complex.I * ((t * Y n ω : ℝ) : ℂ))‖ =
        ‖Complex.exp (Complex.I * ((t * (X n ω - Y n ω) : ℝ) : ℂ)) - 1‖ := by
      rw [norm_exp_I_sub_exp_I]
      simp only [Complex.ofReal_mul, Complex.ofReal_sub, mul_sub]
    simp_rw [heq]
    have hc : Continuous (fun z : ℝ => Complex.exp (Complex.I * ((t * z : ℝ) : ℂ)) - 1) := by fun_prop
    simpa only [Function.comp_apply, mul_zero, Complex.ofReal_zero,
      Complex.exp_zero, sub_self, norm_zero] using ((hc.tendsto 0).comp hω).norm

end
end UniformRandomMALA.Concrete
