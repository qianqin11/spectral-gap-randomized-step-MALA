import Mathlib.MeasureTheory.Integral.Prod

/-!
# Product-space exponential comparison

The finite Euler construction starts with an independent target point and a
finite Gaussian innovation vector.  The only independence fact needed by the
energy MGF is therefore ordinary factorization on a product measure.  This
file packages that step without conditional expectations or an abstract
independence API.
-/

namespace UniformRandomMALA

open MeasureTheory

noncomputable section

namespace DiscreteTime

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- If an energy on a product space is bounded by a sum of one-coordinate
energies, its exponential integral is bounded by the product of the two
one-coordinate MGFs. -/
theorem integral_exp_productEnergy_le
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (J : X × Y → ℝ) (f : X → ℝ) (g : Y → ℝ)
    (lambda A B : ℝ)
    (hlambda : 0 ≤ lambda)
    (hJ : ∀ p : X × Y, J p ≤ A * f p.1 + B * g p.2)
    (hJmeas : AEStronglyMeasurable J (μ.prod ν))
    (hf : Integrable (fun x => Real.exp (lambda * A * f x)) μ)
    (hg : Integrable (fun y => Real.exp (lambda * B * g y)) ν) :
    (∫ p, Real.exp (lambda * J p) ∂(μ.prod ν)) ≤
      (∫ x, Real.exp (lambda * A * f x) ∂μ) *
        ∫ y, Real.exp (lambda * B * g y) ∂ν := by
  let F : X → ℝ := fun x => Real.exp (lambda * A * f x)
  let G : Y → ℝ := fun y => Real.exp (lambda * B * g y)
  have hprod : Integrable (fun p : X × Y => F p.1 * G p.2) (μ.prod ν) :=
    hf.mul_prod hg
  have hpoint : ∀ p : X × Y,
      Real.exp (lambda * J p) ≤ F p.1 * G p.2 := by
    intro p
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hscaled := mul_le_mul_of_nonneg_left (hJ p) hlambda
    nlinarith
  have hleft : Integrable (fun p : X × Y => Real.exp (lambda * J p))
      (μ.prod ν) := by
    have hcont : Continuous (fun u : ℝ => Real.exp (lambda * u)) := by fun_prop
    have hmeas : AEStronglyMeasurable
        (fun p : X × Y => Real.exp (lambda * J p)) (μ.prod ν) :=
      hcont.aestronglyMeasurable.comp_aemeasurable hJmeas.aemeasurable
    apply hprod.mono hmeas
    exact ae_of_all _ fun p => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        Real.norm_eq_abs, abs_of_pos
          (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
      exact hpoint p
  calc
    (∫ p, Real.exp (lambda * J p) ∂(μ.prod ν)) ≤
        ∫ p, F p.1 * G p.2 ∂(μ.prod ν) :=
      integral_mono hleft hprod hpoint
    _ = (∫ x, F x ∂μ) * ∫ y, G y ∂ν := integral_prod_mul F G
    _ = (∫ x, Real.exp (lambda * A * f x) ∂μ) *
        ∫ y, Real.exp (lambda * B * g y) ∂ν := rfl

end DiscreteTime

end

end UniformRandomMALA
