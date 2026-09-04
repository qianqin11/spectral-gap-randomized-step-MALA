import UniformRandomMALA.Concrete.GaussianRampMollification

/-!
# Bounded Riesz third derivatives for Gaussian ramp mollifications

The canonical G3 generator computation needs one derivative beyond the
bounded covector Hessian.  Iterating covector-valued Fréchet derivatives
directly runs into a third-level operator-topology limitation.  This module
applies the Riesz isometry first, represents the resulting Hessian as an
operator `E →L E`, and proves that operator field globally Lipschitz by its
compact-kernel convolution formula.  Its derivative is therefore a bounded
continuous `E →L (E →L E)` field.
-/

namespace UniformRandomMALA.Concrete

open Function Set Metric MeasureTheory Filter ContinuousLinearMap ProbabilityTheory
open scoped Convolution Topology NNReal ENNReal ProbabilityTheory

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [SecondCountableTopology E]

local notation "volE" => (Measure.addHaar : Measure E)

set_option maxHeartbeats 5000000

def gaussianRampMollifierGradient (n : ℕ) (x : E) : E :=
  (InnerProductSpace.toDual ℝ E).symm
    (fderiv ℝ ((gaussianRampMollifier (E := E) n).normed volE) x)

theorem continuous_gaussianRampMollifierGradient (n : ℕ) :
    Continuous (gaussianRampMollifierGradient (E := E) n) := by
  exact (InnerProductSpace.toDual ℝ E).symm.continuous.comp
    ((gaussianRampMollifier (E := E) n).contDiff_normed (n := 1)
      |>.continuous_fderiv (by norm_num))

theorem hasCompactSupport_gaussianRampMollifierGradient (n : ℕ) :
    HasCompactSupport (gaussianRampMollifierGradient (E := E) n) := by
  change HasCompactSupport
    ((InnerProductSpace.toDual ℝ E).symm ∘
      fderiv ℝ ((gaussianRampMollifier (E := E) n).normed volE))
  exact ((gaussianRampMollifier (E := E) n).hasCompactSupport_normed.fderiv ℝ)
    |>.comp_left (map_zero _)

theorem contDiff_one_gaussianRampMollifierGradient (n : ℕ) :
    ContDiff ℝ 1 (gaussianRampMollifierGradient (E := E) n) := by
  have hk : ContDiff ℝ 1
      (fderiv ℝ ((gaussianRampMollifier (E := E) n).normed volE)) := by
    apply (gaussianRampMollifier (E := E) n).contDiff_normed (n := 2)
      |>.fderiv_right (m := 1)
    norm_num
  exact (InnerProductSpace.toDual ℝ E).symm.contDiff.comp hk

def vectorScalarAction : E →L[ℝ] ℝ →L[ℝ] E :=
  (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).flip

@[simp] theorem vectorScalarAction_apply (v : E) (r : ℝ) :
    vectorScalarAction v r = r • v := by
  simp [vectorScalarAction]

def operatorScalarAction :
    (E →L[ℝ] E) →L[ℝ] ℝ →L[ℝ] (E →L[ℝ] E) :=
  vectorScalarAction.precompL E

@[simp] theorem operatorScalarAction_apply (H : E →L[ℝ] E) (r : ℝ) :
    operatorScalarAction H r = r • H := by
  ext v
  simp [operatorScalarAction]

def gaussianRampMollifiedGradientExplicit
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) : E → E :=
  gaussianRampMollifierGradient n ⋆[vectorScalarAction, volE]
    (⇑(gaussianRampExpanded hh A n))

def gaussianRampMollifiedRieszHessianExplicit
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) : E → E →L[ℝ] E :=
  fderiv ℝ (gaussianRampMollifierGradient n) ⋆[operatorScalarAction, volE]
    (⇑(gaussianRampExpanded hh A n))

theorem hasFDerivAt_gaussianRampMollifiedGradientExplicit
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) (x : E) :
    HasFDerivAt (gaussianRampMollifiedGradientExplicit hh A n)
      (gaussianRampMollifiedRieszHessianExplicit hh A n x) x := by
  exact (hasCompactSupport_gaussianRampMollifierGradient (E := E) n)
    |>.hasFDerivAt_convolution_left vectorScalarAction
      (contDiff_one_gaussianRampMollifierGradient (E := E) n)
      (gaussianRampExpanded hh A n).continuous.locallyIntegrable x

def gaussianRampMollifiedGradient
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) (x : E) : E :=
  (InnerProductSpace.toDual ℝ E).symm
    (fderiv ℝ (gaussianRampMollified hh A n) x)

theorem gaussianRampMollifiedGradient_eq_explicit
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) :
    gaussianRampMollifiedGradient hh A n =
      gaussianRampMollifiedGradientExplicit hh A n := by
  let L := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv
    |>.toContinuousLinearMap
  let k := fderiv ℝ ((gaussianRampMollifier (E := E) n).normed volE)
  let g : BoundedContinuousFunction E ℝ := gaussianRampExpanded hh A n
  have hkcont : Continuous k :=
    (gaussianRampMollifier (E := E) n).contDiff_normed (n := 1)
      |>.continuous_fderiv (by norm_num)
  have hkcomp : HasCompactSupport k :=
    (gaussianRampMollifier (E := E) n).hasCompactSupport_normed.fderiv ℝ
  have hconv : ConvolutionExists k (⇑g)
      firstDerivativeScalarAction volE :=
    hkcomp.convolutionExists_left firstDerivativeScalarAction hkcont
      g.continuous.locallyIntegrable
  funext x
  rw [gaussianRampMollifiedGradient, fderiv_gaussianRampMollified_eq_explicitD1]
  change L (∫ z, firstDerivativeScalarAction (k z) (g (x - z)) ∂volE) =
    ∫ z, vectorScalarAction (gaussianRampMollifierGradient n z)
      (g (x - z)) ∂volE
  rw [← L.integral_comp_comm (hconv x).integrable]
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    simp [L, k, gaussianRampMollifierGradient]

def gaussianRampMollifiedRieszHessian
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) (x : E) : E →L[ℝ] E :=
  fderiv ℝ (gaussianRampMollifiedGradient hh A n) x

theorem gaussianRampMollifiedRieszHessian_eq_explicit
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) :
    gaussianRampMollifiedRieszHessian hh A n =
      gaussianRampMollifiedRieszHessianExplicit hh A n := by
  funext x
  unfold gaussianRampMollifiedRieszHessian
  rw [gaussianRampMollifiedGradient_eq_explicit hh A n]
  exact (hasFDerivAt_gaussianRampMollifiedGradientExplicit hh A n x).fderiv

def gaussianRampMollifiedRieszHessianLipschitzConstant
    {h : ℝ} (hh : 0 < h) (n : ℕ) : ℝ≥0 :=
  h.toNNReal⁻¹ * Real.toNNReal (∫ z, ‖fderiv ℝ
      (gaussianRampMollifierGradient (E := E) n) z‖ ∂volE)

theorem lipschitzWith_gaussianRampMollifiedRieszHessianExplicit
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) :
    LipschitzWith (gaussianRampMollifiedRieszHessianLipschitzConstant
      (E := E) hh n) (gaussianRampMollifiedRieszHessianExplicit hh A n) := by
  let k := fderiv ℝ (gaussianRampMollifierGradient (E := E) n)
  let g : BoundedContinuousFunction E ℝ := gaussianRampExpanded hh A n
  have hkcont : Continuous k :=
    (contDiff_one_gaussianRampMollifierGradient (E := E) n)
      |>.continuous_fderiv (by norm_num)
  have hkcomp : HasCompactSupport k :=
    (hasCompactSupport_gaussianRampMollifierGradient (E := E) n).fderiv ℝ
  simpa [gaussianRampMollifiedRieszHessianLipschitzConstant,
    gaussianRampMollifiedRieszHessianExplicit, k, g] using
    (lipschitzWith_convolution_left_smul k g operatorScalarAction
      operatorScalarAction_apply hkcomp hkcont
      (lipschitzWith_gaussianRamp hh
        (cthickening (gaussianRampMollifierRadius n) A)) volE)

theorem lipschitzWith_gaussianRampMollifiedRieszHessian
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) :
    LipschitzWith (gaussianRampMollifiedRieszHessianLipschitzConstant
      (E := E) hh n) (gaussianRampMollifiedRieszHessian hh A n) := by
  rw [gaussianRampMollifiedRieszHessian_eq_explicit hh A n]
  exact lipschitzWith_gaussianRampMollifiedRieszHessianExplicit hh A n

theorem contDiff_two_gaussianRampMollifiedGradient
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) :
    ContDiff ℝ 2 (gaussianRampMollifiedGradient hh A n) := by
  let L := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv
    |>.toContinuousLinearMap
  have hf3 : ContDiff ℝ 3 (gaussianRampMollified hh A n) :=
    (contDiff_gaussianRampMollified hh A n).of_le
      (WithTop.coe_le_coe.2 (OrderTop.le_top (3 : ℕ∞)))
  have hDf2 : ContDiff ℝ 2
      (fderiv ℝ (gaussianRampMollified hh A n)) := by
    apply hf3.fderiv_right (m := 2)
    norm_num
  exact L.contDiff.comp hDf2

def gaussianRampMollifiedRieszD3
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) (x : E) :
    E →L[ℝ] (E →L[ℝ] E) :=
  fderiv ℝ (gaussianRampMollifiedRieszHessian hh A n) x

theorem contDiff_one_gaussianRampMollifiedRieszHessian
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) :
    ContDiff ℝ 1 (gaussianRampMollifiedRieszHessian hh A n) := by
  apply (contDiff_two_gaussianRampMollifiedGradient hh A n)
    |>.fderiv_right (m := 1)
  norm_num

theorem continuous_gaussianRampMollifiedRieszD3
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) :
    Continuous (gaussianRampMollifiedRieszD3 hh A n) :=
  (contDiff_one_gaussianRampMollifiedRieszHessian hh A n)
    |>.continuous_fderiv (by norm_num)

theorem hasFDerivAt_gaussianRampMollifiedRieszHessian
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) (x : E) :
    HasFDerivAt (gaussianRampMollifiedRieszHessian hh A n)
      (gaussianRampMollifiedRieszD3 hh A n x) x :=
  ((contDiff_one_gaussianRampMollifiedRieszHessian hh A n)
    |>.differentiable (by norm_num) x).hasFDerivAt

theorem norm_gaussianRampMollifiedRieszD3_le
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) (x : E) :
    ‖gaussianRampMollifiedRieszD3 hh A n x‖ ≤
      gaussianRampMollifiedRieszHessianLipschitzConstant (E := E) hh n := by
  unfold gaussianRampMollifiedRieszD3
  exact norm_fderiv_le_of_lipschitz ℝ
    (lipschitzWith_gaussianRampMollifiedRieszHessian hh A n)

def gaussianRampMollifiedRieszD3BCF
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) :
    BoundedContinuousFunction E (E →L[ℝ] (E →L[ℝ] E)) :=
  let C : ℝ :=
    gaussianRampMollifiedRieszHessianLipschitzConstant (E := E) hh n
  BoundedContinuousFunction.ofNormedAddCommGroup
    (gaussianRampMollifiedRieszD3 hh A n)
    (continuous_gaussianRampMollifiedRieszD3 hh A n) C
    (fun x => norm_gaussianRampMollifiedRieszD3_le hh A n x)

@[simp] theorem gaussianRampMollifiedRieszD3BCF_apply
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) (x : E) :
    gaussianRampMollifiedRieszD3BCF hh A n x =
      gaussianRampMollifiedRieszD3 hh A n x := rfl

end
end UniformRandomMALA.Concrete
