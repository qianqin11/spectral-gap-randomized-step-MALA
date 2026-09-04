import UniformRandomMALA.DiscreteTime.GaussianMGF
import Mathlib.Probability.Moments.CovarianceBilin

/-!
# A positive-part identity for a finite-dimensional standard Gaussian

The elementary Euler/RWM coupling uses the cancellation

`E[Z max (L Z, 0)] = (1 / 2) Riesz(L)`.

This file proves it without Gaussian integration by parts.  The proof has
two finite-dimensional ingredients:

* invariance of the standard Gaussian under `z ↦ -z`, which replaces the
  positive part by one half of the linear integrand;
* the already available covariance identity for the standard Gaussian.

This form is deliberately close to the paper proof and avoids any
continuous-time stochastic calculus.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace

noncomputable section

namespace DiscreteTime

section StandardGaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private def gaussianPositivePartIntegrand (L : StrongDual ℝ E) (z : E) : E :=
  max (L z) 0 • z

private def gaussianLinearVectorIntegrand (L : StrongDual ℝ E) (z : E) : E :=
  L z • z

private theorem integrable_gaussianPositivePartIntegrand (L : StrongDual ℝ E) :
    Integrable (gaussianPositivePartIntegrand L) (stdGaussian E) := by
  have h2 : Integrable (fun z : E => ‖z‖ ^ 2) (stdGaussian E) :=
    IsGaussian.memLp_two_id.integrable_norm_pow (by norm_num)
  have hdom : Integrable (fun z : E => ‖L‖ * ‖z‖ ^ 2) (stdGaussian E) :=
    h2.const_mul ‖L‖
  apply hdom.mono' (by unfold gaussianPositivePartIntegrand; fun_prop)
  exact ae_of_all _ fun z => by
    rw [gaussianPositivePartIntegrand, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (le_max_right _ _), pow_two]
    have hmax : max (L z) 0 ≤ ‖L‖ * ‖z‖ := by
      apply max_le
      · calc
          L z ≤ |L z| := le_abs_self _
          _ = ‖L z‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖L‖ * ‖z‖ := L.le_opNorm z
      · positivity
    calc
      max (L z) 0 * ‖z‖ ≤ (‖L‖ * ‖z‖) * ‖z‖ :=
        mul_le_mul_of_nonneg_right hmax (norm_nonneg _)
      _ = ‖L‖ * (‖z‖ * ‖z‖) := by ring

/-- The positive-part vector integrand has a finite Bochner integral under
the standard Gaussian. -/
theorem integrable_gaussianPositivePart_smul (L : StrongDual ℝ E) :
    Integrable (fun z => max (L z) 0 • z) (stdGaussian E) :=
  integrable_gaussianPositivePartIntegrand L

private theorem integrable_gaussianLinearVectorIntegrand (L : StrongDual ℝ E) :
    Integrable (gaussianLinearVectorIntegrand L) (stdGaussian E) := by
  have h2 : Integrable (fun z : E => ‖z‖ ^ 2) (stdGaussian E) :=
    IsGaussian.memLp_two_id.integrable_norm_pow (by norm_num)
  have hdom : Integrable (fun z : E => ‖L‖ * ‖z‖ ^ 2) (stdGaussian E) :=
    h2.const_mul ‖L‖
  apply hdom.mono' (by unfold gaussianLinearVectorIntegrand; fun_prop)
  exact ae_of_all _ fun z => by
    rw [gaussianLinearVectorIntegrand, norm_smul, pow_two]
    calc
      ‖L z‖ * ‖z‖ ≤ (‖L‖ * ‖z‖) * ‖z‖ :=
        mul_le_mul_of_nonneg_right (L.le_opNorm z) (norm_nonneg _)
      _ = ‖L‖ * (‖z‖ * ‖z‖) := by ring

private theorem gaussian_neg_measurePreserving :
    MeasurePreserving (LinearIsometryEquiv.neg ℝ : E → E)
      (stdGaussian E) (stdGaussian E) := by
  refine ⟨(LinearIsometryEquiv.neg ℝ : E ≃ₗᵢ[ℝ] E).continuous.measurable, ?_⟩
  simpa using stdGaussian_map (E := E)
    (LinearIsometryEquiv.neg ℝ : E ≃ₗᵢ[ℝ] E)

private theorem integral_gaussianPositivePart_eq_half_linear (L : StrongDual ℝ E) :
    (∫ z, gaussianPositivePartIntegrand L z ∂stdGaussian E) =
      (1 / 2 : ℝ) •
        (∫ z, gaussianLinearVectorIntegrand L z ∂stdGaussian E) := by
  let H := gaussianPositivePartIntegrand L
  let G := gaussianLinearVectorIntegrand L
  have hH : Integrable H (stdGaussian E) :=
    integrable_gaussianPositivePartIntegrand L
  have hneg : Integrable (fun z => H (-z)) (stdGaussian E) := by
    change Integrable (H ∘ (LinearIsometryEquiv.neg ℝ : E ≃ₗᵢ[ℝ] E))
      (stdGaussian E)
    exact (gaussian_neg_measurePreserving (E := E)).integrable_comp
      hH.aestronglyMeasurable |>.2 hH
  have hinv : (∫ z, H (-z) ∂stdGaussian E) =
      ∫ z, H z ∂stdGaussian E :=
    (gaussian_neg_measurePreserving (E := E)).integral_comp
      (LinearIsometryEquiv.neg ℝ : E ≃ₗᵢ[ℝ] E).toHomeomorph.measurableEmbedding H
  have hpoint : ∀ z, H z + H (-z) = G z := by
    intro z
    change max (L z) 0 • z + max (L (-z)) 0 • (-z) = L z • z
    rw [map_neg, smul_neg, ← sub_eq_add_neg, ← sub_smul,
      max_zero_sub_max_neg_zero_eq_self]
  calc
    (∫ z, H z ∂stdGaussian E) =
        (1 / 2 : ℝ) • ((2 : ℝ) • ∫ z, H z ∂stdGaussian E) := by
      simp [smul_smul]
    _ = (1 / 2 : ℝ) •
        ((∫ z, H z ∂stdGaussian E) + ∫ z, H z ∂stdGaussian E) := by
      rw [two_smul]
    _ = (1 / 2 : ℝ) •
        ((∫ z, H z ∂stdGaussian E) + ∫ z, H (-z) ∂stdGaussian E) := by
      rw [hinv]
    _ = (1 / 2 : ℝ) •
        (∫ z, H z + H (-z) ∂stdGaussian E) := by
      rw [integral_add hH hneg]
    _ = (1 / 2 : ℝ) • (∫ z, G z ∂stdGaussian E) := by
      congr 1
      apply integral_congr_ae
      exact ae_of_all _ hpoint

private theorem integral_gaussianLinearVectorIntegrand (L : StrongDual ℝ E) :
    (∫ z, gaussianLinearVectorIntegrand L z ∂stdGaussian E) =
      (toDual ℝ E).symm L := by
  let v : E := (toDual ℝ E).symm L
  have hLv : (toDualMap ℝ E) v = L := by
    rw [← toDual_apply_eq_toDualMap_apply]
    simp [v]
  have hG := integrable_gaussianLinearVectorIntegrand L
  apply (toDualMap ℝ E).injective
  ext y
  change ⟪(∫ z, gaussianLinearVectorIntegrand L z ∂stdGaussian E), y⟫ = ⟪v, y⟫
  rw [real_inner_comm]
  change (toDualMap ℝ E y)
    (∫ z, gaussianLinearVectorIntegrand L z ∂stdGaussian E) = _
  rw [← (toDualMap ℝ E y).integral_comp_comm hG]
  have hcov := congrArg (fun B => B v y)
    (covarianceBilin_stdGaussian (E := E))
  rw [covarianceBilin_apply IsGaussian.memLp_two_id] at hcov
  simp only [integral_id_stdGaussian, id_eq, sub_zero] at hcov
  rw [innerSL_apply_apply ℝ v y] at hcov
  rw [← hLv]
  simpa only [gaussianLinearVectorIntegrand, map_smul,
    toDualMap_apply_apply, smul_eq_mul, mul_comm] using hcov

/-- If `Z` is a standard Gaussian and `L` is a continuous linear
functional, then the positive half-space selected by `L` carries exactly
half of the vector covariance in the direction represented by `L`.

This is the exact cancellation used in the first-order expansion of the
RWM rejection displacement. -/
theorem integral_gaussianPositivePart_smul (L : StrongDual ℝ E) :
    (∫ z, max (L z) 0 • z ∂stdGaussian E) =
      (1 / 2 : ℝ) • (toDual ℝ E).symm L := by
  change (∫ z, gaussianPositivePartIntegrand L z ∂stdGaussian E) = _
  rw [integral_gaussianPositivePart_eq_half_linear,
    integral_gaussianLinearVectorIntegrand]

/-- Scaled form used by the Euler/RWM coupling.  For an increment
`s = sqrt (2 δ) Z` and `q = ⟪g, s⟫`, one has

`E[q₊ s] = δ g`.

This is the exact first-order drift cancellation; no limiting argument is
present in the statement or proof. -/
theorem integral_scaledGaussian_positivePart_smul
    (δ : ℝ) (hδ : 0 ≤ δ) (g : E) :
    (∫ z, max (⟪g, Real.sqrt (2 * δ) • z⟫) 0 •
      (Real.sqrt (2 * δ) • z) ∂stdGaussian E) = δ • g := by
  let a : ℝ := Real.sqrt (2 * δ)
  let L : StrongDual ℝ E := a • (toDualMap ℝ E g)
  have hbase := integral_gaussianPositivePart_smul (E := E) L
  have hRiesz : (toDual ℝ E).symm L = a • g := by
    apply (toDual ℝ E).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    simp only [L, map_smul, toDual_apply_eq_toDualMap_apply]
  calc
    (∫ z, max (⟪g, Real.sqrt (2 * δ) • z⟫) 0 •
        (Real.sqrt (2 * δ) • z) ∂stdGaussian E) =
        ∫ z, a • (max (L z) 0 • z) ∂stdGaussian E := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        have hLz : L z = a * ⟪g, z⟫ := by
          change (a • (toDualMap ℝ E g) : StrongDual ℝ E) z = _
          rfl
        change max (⟪g, a • z⟫) 0 • (a • z) =
          a • (max (L z) 0 • z)
        rw [hLz]
        simp only [inner_smul_right, smul_smul]
        congr 1
        ring
    _ = a • (∫ z, max (L z) 0 • z ∂stdGaussian E) := by
      rw [integral_smul]
    _ = a • ((1 / 2 : ℝ) • (toDual ℝ E).symm L) := by
      rw [hbase]
    _ = δ • g := by
      rw [hRiesz, smul_smul, smul_smul]
      congr 1
      dsimp [a]
      have hsqrt : (Real.sqrt (2 * δ)) ^ 2 = 2 * δ := by
        rw [Real.sq_sqrt]
        positivity
      nlinarith

end StandardGaussian

end DiscreteTime

end

end UniformRandomMALA
