import UniformRandomMALA.Concrete.GaussianRampThirdDerivative

/-!
# Higher spatial fields for the backward Gaussian OU flow

This module transports bounded Riesz gradients and Hessians through the
backward Mehler semigroup.  Third derivatives are transported after fixing a
direction; this supplies the coordinate derivatives needed by the generator
without requiring a Bochner integral in a third-level operator space.
-/

namespace UniformRandomMALA.Concrete

open Function Set Metric MeasureTheory Filter ContinuousLinearMap ProbabilityTheory
open scoped Convolution Topology NNReal ENNReal ProbabilityTheory

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [SecondCountableTopology E]

/-- A backward OU gradient represented from the terminal Riesz gradient. -/
def backwardGaussianOURieszGradientBCF (t s : ℝ)
    (Gf : BoundedContinuousFunction E E) :
    BoundedContinuousFunction E E := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact ouDriftCoeff (t - s) • gaussianOUAverageBCF (t - s) Gf

@[simp] theorem backwardGaussianOURieszGradientBCF_apply (t s : ℝ)
    (Gf : BoundedContinuousFunction E E) (x : E) :
    backwardGaussianOURieszGradientBCF t s Gf x =
      ouDriftCoeff (t - s) •
        ∫ z, Gf (gaussianOUTransition (t - s) x z) ∂stdGaussian E := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  rfl

/-- The bounded Riesz Hessian transported by the backward OU semigroup. -/
def backwardGaussianOURieszHessianBCF (t s : ℝ)
    (Hf : BoundedContinuousFunction E (E →L[ℝ] E)) :
    BoundedContinuousFunction E (E →L[ℝ] E) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact (ouDriftCoeff (t - s) ^ 2) • gaussianOUAverageBCF (t - s) Hf

@[simp] theorem backwardGaussianOURieszHessianBCF_apply (t s : ℝ)
    (Hf : BoundedContinuousFunction E (E →L[ℝ] E)) (x : E) :
    backwardGaussianOURieszHessianBCF t s Hf x =
      (ouDriftCoeff (t - s) ^ 2) •
        ∫ z, Hf (gaussianOUTransition (t - s) x z) ∂stdGaussian E := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  rfl

theorem hasFDerivAt_backwardGaussianOURieszGradientBCF
    (t s : ℝ)
    (Gf : BoundedContinuousFunction E E)
    (Hf : BoundedContinuousFunction E (E →L[ℝ] E))
    (hHf : ∀ y, HasFDerivAt Gf (Hf y) y) (x : E) :
    HasFDerivAt (backwardGaussianOURieszGradientBCF t s Gf)
      (backwardGaussianOURieszHessianBCF t s Hf x) x := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have havg := hasFDerivAt_gaussianOUAverage (t - s) Gf Hf hHf x
  have hscaled := havg.const_smul (ouDriftCoeff (t - s))
  change HasFDerivAt
    (ouDriftCoeff (t - s) • gaussianOUAverage (t - s) Gf)
    ((ouDriftCoeff (t - s) ^ 2) •
      gaussianOUAverage (t - s) Hf x) x
  simpa [gaussianOUAverage, smul_smul, pow_two] using hscaled

/-- Riesz representation commutes with the backward OU gradient average. -/
theorem backwardGaussianOURieszGradientBCF_rieszGradientBCF
    (t s : ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ)) (x : E) :
    backwardGaussianOURieszGradientBCF t s (rieszGradientBCF Df) x =
      rieszGradientBCF (backwardGaussianOUDerivBCF t s Df) x := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  let L :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hint : Integrable
      (fun z => Df (gaussianOUTransition (t - s) x z)) (stdGaussian E) := by
    refine Integrable.of_bound
      (Df.continuous.comp (by
        unfold gaussianOUTransition
        fun_prop)).aestronglyMeasurable ‖Df‖ ?_
    exact Filter.Eventually.of_forall fun z => Df.norm_coe_le_norm _
  change ouDriftCoeff (t - s) •
      (∫ z, L (Df (gaussianOUTransition (t - s) x z)) ∂stdGaussian E) =
    L (ouDriftCoeff (t - s) •
      ∫ z, Df (gaussianOUTransition (t - s) x z) ∂stdGaussian E)
  rw [L.integral_comp_comm hint, L.map_smul]

theorem hasFDerivAt_rieszGradient_backwardGaussianOU_of_rieszHessian
    (t s : ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (Hf : BoundedContinuousFunction E (E →L[ℝ] E))
    (hHf : ∀ y, HasFDerivAt (rieszGradientBCF Df) (Hf y) y) (x : E) :
    HasFDerivAt (rieszGradientBCF (backwardGaussianOUDerivBCF t s Df))
      (backwardGaussianOURieszHessianBCF t s Hf x) x := by
  have h := hasFDerivAt_backwardGaussianOURieszGradientBCF
    t s (rieszGradientBCF Df) Hf hHf x
  convert h using 1
  funext y
  exact (backwardGaussianOURieszGradientBCF_rieszGradientBCF t s Df y).symm

/-- A fixed directional contraction of a bounded Riesz third derivative. -/
def rieszD3DirectionBCF
    (D3f : BoundedContinuousFunction E (E →L[ℝ] (E →L[ℝ] E)))
    (e : E) (M : ℝ) (hM : ∀ y, ‖D3f y‖ ≤ M) :
    BoundedContinuousFunction E (E →L[ℝ] E) :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun y => D3f y e)
    ((ContinuousLinearMap.apply ℝ (E →L[ℝ] E) e).continuous.comp
      D3f.continuous)
    (M * ‖e‖) (fun y =>
      (D3f y).le_opNorm e |>.trans
        (mul_le_mul_of_nonneg_right (hM y) (norm_nonneg e)))

/-- The fixed-direction derivative of the transported Riesz Hessian. -/
def backwardGaussianOURieszHessianDirectionalDerivBCF (t s : ℝ)
    (D3f : BoundedContinuousFunction E (E →L[ℝ] (E →L[ℝ] E)))
    (e : E) (M : ℝ) (hM : ∀ y, ‖D3f y‖ ≤ M) :
    BoundedContinuousFunction E (E →L[ℝ] E) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact (ouDriftCoeff (t - s) ^ 3) • gaussianOUAverageBCF (t - s)
    (rieszD3DirectionBCF D3f e M hM)

theorem hasDerivAt_backwardGaussianOURieszHessian_line
    (t s : ℝ)
    (Hf : BoundedContinuousFunction E (E →L[ℝ] E))
    (D3f : BoundedContinuousFunction E (E →L[ℝ] (E →L[ℝ] E)))
    (M : ℝ) (hM : ∀ y, ‖D3f y‖ ≤ M)
    (hD3f : ∀ y, HasFDerivAt Hf (D3f y) y)
    (x e : E) (r : ℝ) :
    HasDerivAt
      (fun u => backwardGaussianOURieszHessianBCF t s Hf (x + u • e))
      (backwardGaussianOURieszHessianDirectionalDerivBCF
        t s D3f e M hM (x + r • e)) r := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  let a := ouDriftCoeff (t - s)
  let b := ouNoiseCoeff (t - s)
  let De := rieszD3DirectionBCF D3f e M hM
  have hline : ∀ z u, HasDerivAt
      (fun u : ℝ => Hf (gaussianOUTransition (t - s) (x + u • e) z))
      (a • De (gaussianOUTransition (t - s) (x + u • e) z)) u := by
    intro z u
    have haff : HasDerivAt
        (fun u : ℝ => gaussianOUTransition (t - s) (x + u • e) z)
        (a • e) u := by
      convert (((hasDerivAt_const u x).add ((hasDerivAt_id u).smul_const e))
        |>.const_smul a |>.add_const (b • z)) using 1 <;>
        simp [a, b, gaussianOUTransition, add_assoc, add_comm, smul_add]
    have hc := (hD3f _).comp_hasDerivAt u haff
    change HasDerivAt
      (fun u : ℝ => Hf (gaussianOUTransition (t - s) (x + u • e) z))
      (a • D3f (gaussianOUTransition (t - s) (x + u • e) z) e) u
    simpa [Function.comp_def, a, smul_smul] using hc
  have hdiff := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (x₀ := r) (s := Set.univ) (μ := stdGaussian E)
    (F := fun u z => Hf (gaussianOUTransition (t - s) (x + u • e) z))
    (F' := fun u z => a • De
      (gaussianOUTransition (t - s) (x + u • e) z))
    (bound := fun _ : E => |a| * (M * ‖e‖)) Filter.univ_mem
  have hresult : HasDerivAt
      (fun u => ∫ z, Hf (gaussianOUTransition (t - s) (x + u • e) z)
        ∂stdGaussian E)
      (∫ z, a • De (gaussianOUTransition (t - s) (x + r • e) z)
        ∂stdGaussian E) r := by
    apply (hdiff ?_ ?_ ?_ ?_ (integrable_const _) ?_).2
    · exact Filter.Eventually.of_forall fun u =>
        (show Continuous (fun z : E =>
            Hf (gaussianOUTransition (t - s) (x + u • e) z)) by
          unfold gaussianOUTransition
          fun_prop).aestronglyMeasurable
    · refine Integrable.of_bound
        (show Continuous (fun z : E =>
            Hf (gaussianOUTransition (t - s) (x + r • e) z)) by
          unfold gaussianOUTransition
          fun_prop).aestronglyMeasurable ‖Hf‖ ?_
      exact Filter.Eventually.of_forall fun z => Hf.norm_coe_le_norm _
    · exact (show Continuous (fun z : E => a • De
          (gaussianOUTransition (t - s) (x + r • e) z)) by
        unfold gaussianOUTransition
        fun_prop).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun z u _ => by
        rw [norm_smul, Real.norm_eq_abs]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg a)
        change ‖D3f (gaussianOUTransition (t - s) (x + u • e) z) e‖ ≤ M * ‖e‖
        exact (D3f _).le_opNorm e |>.trans
          (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg e))
    · exact Filter.Eventually.of_forall fun z u _ => hline z u
  have hscaled := hresult.const_smul (a ^ 2)
  change HasDerivAt
    (fun u => (a ^ 2) • gaussianOUAverage (t - s) Hf (x + u • e))
    ((a ^ 3) • gaussianOUAverage (t - s)
      (rieszD3DirectionBCF D3f e M hM) (x + r • e)) r
  have hderiv :
      (a ^ 2) • ∫ z, a • De
          (gaussianOUTransition (t - s) (x + r • e) z) ∂stdGaussian E =
        (a ^ 3) • gaussianOUAverage (t - s)
          (rieszD3DirectionBCF D3f e M hM) (x + r • e) := by
    rw [integral_smul]
    simp only [De, gaussianOUAverage, smul_smul, pow_succ]
  have hscaled' := hscaled.congr_deriv hderiv
  apply hscaled'.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun u => rfl

end
end UniformRandomMALA.Concrete
