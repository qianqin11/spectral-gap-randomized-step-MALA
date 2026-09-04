import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Exact finite-dimensional Gaussian moment-generating identities

The discrete likelihood comparison repeatedly integrates exponentials of
linear Gaussian functionals.  This file derives that identity from
Mathlib's one-dimensional Gaussian MGF after mapping the standard Gaussian
measure by a continuous linear functional.  This is the one-step square
completion needed by the finite-kernel recursion; no stochastic exponential
is involved.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory

noncomputable section

namespace DiscreteTime

section StandardGaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Exponentials of linear functionals are integrable under a standard
finite-dimensional Gaussian measure. -/
theorem integrable_exp_mul_strongDual_stdGaussian
    (L : StrongDual ℝ E) (t : ℝ) :
    Integrable (fun z => Real.exp (t * L z)) (stdGaussian E) := by
  have hmap : Measure.map L (stdGaussian E) =
      gaussianReal 0 (‖L‖ ^ 2).toNNReal := by
    simpa [integral_strongDual_stdGaussian, variance_dual_stdGaussian] using
      (IsGaussian.map_eq_gaussianReal (μ := stdGaussian E) L)
  have hReal : Integrable (fun x => Real.exp (t * x))
      (Measure.map L (stdGaussian E)) := by
    rw [hmap]
    exact integrable_exp_mul_gaussianReal t
  change Integrable
    ((fun x : ℝ => Real.exp (t * x)) ∘ (L : E → ℝ)) (stdGaussian E)
  exact hReal.comp_measurable L.measurable

/-- Exact MGF of a continuous linear functional of a standard Gaussian:

`E exp(t L(Z)) = exp(t^2 ||L||^2 / 2)`.
-/
theorem integral_exp_mul_strongDual_stdGaussian
    (L : StrongDual ℝ E) (t : ℝ) :
    (∫ z, Real.exp (t * L z) ∂stdGaussian E) =
      Real.exp (‖L‖ ^ 2 * t ^ 2 / 2) := by
  have hmap : Measure.map L (stdGaussian E) =
      gaussianReal 0 (‖L‖ ^ 2).toNNReal := by
    simpa [integral_strongDual_stdGaussian, variance_dual_stdGaussian] using
      (IsGaussian.map_eq_gaussianReal (μ := stdGaussian E) L)
  have hmgf := mgf_gaussianReal hmap t
  rw [mgf] at hmgf
  simpa [Real.coe_toNNReal (‖L‖ ^ 2) (sq_nonneg ‖L‖)] using hmgf

/-- Adding a deterministic constant to the Gaussian exponent is handled by
one scalar multiplication outside the integral. -/
theorem integrable_exp_add_mul_strongDual_stdGaussian
    (L : StrongDual ℝ E) (t c : ℝ) :
    Integrable (fun z => Real.exp (c + t * L z)) (stdGaussian E) := by
  have hbase := integrable_exp_mul_strongDual_stdGaussian L t
  have hscaled : Integrable
      (fun z => Real.exp c * Real.exp (t * L z)) (stdGaussian E) :=
    hbase.const_mul _
  apply hscaled.congr
  exact ae_of_all _ fun z => by
    change Real.exp c * Real.exp (t * L z) = Real.exp (c + t * L z)
    exact (Real.exp_add _ _).symm

/-- Exact affine-exponent identity. -/
theorem integral_exp_add_mul_strongDual_stdGaussian
    (L : StrongDual ℝ E) (t c : ℝ) :
    (∫ z, Real.exp (c + t * L z) ∂stdGaussian E) =
      Real.exp (c + ‖L‖ ^ 2 * t ^ 2 / 2) := by
  calc
    (∫ z, Real.exp (c + t * L z) ∂stdGaussian E) =
        ∫ z, Real.exp c * Real.exp (t * L z) ∂stdGaussian E := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        change Real.exp (c + t * L z) =
          Real.exp c * Real.exp (t * L z)
        exact Real.exp_add _ _
    _ = Real.exp c *
        (∫ z, Real.exp (t * L z) ∂stdGaussian E) := by
      rw [integral_const_mul]
    _ = Real.exp c * Real.exp (‖L‖ ^ 2 * t ^ 2 / 2) := by
      rw [integral_exp_mul_strongDual_stdGaussian]
    _ = Real.exp (c + ‖L‖ ^ 2 * t ^ 2 / 2) := by
      rw [Real.exp_add]

/-- The normalized likelihood for shifting a standard Gaussian in the
direction of the linear functional `L`. -/
def gaussianLinearLikelihood (L : StrongDual ℝ E) (z : E) : ℝ :=
  Real.exp (L z - ‖L‖ ^ 2 / 2)

theorem measurable_gaussianLinearLikelihood (L : StrongDual ℝ E) :
    Measurable (gaussianLinearLikelihood L) := by
  unfold gaussianLinearLikelihood
  fun_prop

theorem gaussianLinearLikelihood_pos (L : StrongDual ℝ E) (z : E) :
    0 < gaussianLinearLikelihood L z :=
  Real.exp_pos _

/-- Exact powered likelihood moment obtained from the same one-step Gaussian
square completion:

`E ell_L(Z)^p = exp(p(p-1)||L||^2/2)`.
-/
theorem integrable_gaussianLinearLikelihood_rpow
    (L : StrongDual ℝ E) (p : ℝ) :
    Integrable (fun z => (gaussianLinearLikelihood L z) ^ p)
      (stdGaussian E) := by
  have heq : (fun z => (gaussianLinearLikelihood L z) ^ p) =
      fun z => Real.exp ((-p * ‖L‖ ^ 2 / 2) + p * L z) := by
    funext z
    rw [gaussianLinearLikelihood,
      Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  rw [heq]
  exact integrable_exp_add_mul_strongDual_stdGaussian L p
    (-p * ‖L‖ ^ 2 / 2)

theorem integral_gaussianLinearLikelihood_rpow
    (L : StrongDual ℝ E) (p : ℝ) :
    (∫ z, (gaussianLinearLikelihood L z) ^ p ∂stdGaussian E) =
      Real.exp (p * (p - 1) * ‖L‖ ^ 2 / 2) := by
  have heq : (fun z => (gaussianLinearLikelihood L z) ^ p) =
      fun z => Real.exp ((-p * ‖L‖ ^ 2 / 2) + p * L z) := by
    funext z
    rw [gaussianLinearLikelihood,
      Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  rw [heq, integral_exp_add_mul_strongDual_stdGaussian]
  congr 1
  ring

/-- In particular, the normalized one-step likelihood has mean one. -/
theorem integral_gaussianLinearLikelihood (L : StrongDual ℝ E) :
    (∫ z, gaussianLinearLikelihood L z ∂stdGaussian E) = 1 := by
  simpa [Real.rpow_one] using
    integral_gaussianLinearLikelihood_rpow L 1

end StandardGaussian

end DiscreteTime

end

end UniformRandomMALA
