import UniformRandomMALA.Concrete.GaussianBobkovDiagonal

/-!
# Canonical Gaussian OU Bobkov diagonal fields

This module combines the backward OU value, Riesz gradient, Riesz Hessian,
and fixed-direction third derivative into the bounded spatial fields required
by the finite-coordinate OU generator theorem.  It proves the canonical
square root has the bundled covector derivative, expands that covector in
Euclidean coordinates, and verifies the exact `Fin.insertNth` line-derivative
hypothesis for every diagonal coordinate.
-/

namespace UniformRandomMALA.Concrete

open Function Set Metric MeasureTheory Filter ContinuousLinearMap ProbabilityTheory
open scoped Topology NNReal ENNReal ProbabilityTheory BigOperators

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [SecondCountableTopology E]

/-- The bounded covector field represented by the canonical Bobkov spatial
gradient formula. -/
def bobkovSpatialDerivBCF
    (c : ℝ) (hc : 0 ≤ c)
    (u : BoundedContinuousFunction E ℝ)
    (D : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (v : BoundedContinuousFunction E E)
    (H : BoundedContinuousFunction E (E →L[ℝ] E))
    (ε : ℝ) (hε : 0 < ε) (hu : ∀ x, u x ∈ Icc ε (1 - ε)) :
    BoundedContinuousFunction E (E →L[ℝ] ℝ) :=
  let I := normalProfileCompBCF u ε hε hu
  let Ip := normalProfileDerivCompBCF u ε hε hu
  let Rinv := bobkovInvRadiusBCF c hc u v ε hε hu
  boundedContinuousSMul Rinv
    (boundedContinuousSMul (I * Ip) D + c • boundedContinuousInnerComp v H)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [SecondCountableTopology E] in
@[simp] theorem bobkovSpatialDerivBCF_apply
    (c : ℝ) (hc : 0 ≤ c)
    (u : BoundedContinuousFunction E ℝ)
    (D : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (v : BoundedContinuousFunction E E)
    (H : BoundedContinuousFunction E (E →L[ℝ] E))
    (ε : ℝ) (hε : 0 < ε) (hu : ∀ x, u x ∈ Icc ε (1 - ε))
    (x : E) :
    bobkovSpatialDerivBCF c hc u D v H ε hε hu x =
      (Real.sqrt (normalProfile (u x) ^ 2 + c * ‖v x‖ ^ 2))⁻¹ •
        ((normalProfile (u x) * deriv normalProfile (u x)) • D x +
          c • (innerSL ℝ (v x)).comp (H x)) := by
  rfl

theorem bobkovSpatialDerivBCF_apply_unit
    (c : ℝ) (hc : 0 ≤ c)
    (u : BoundedContinuousFunction E ℝ)
    (D : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (v : BoundedContinuousFunction E E)
    (H : BoundedContinuousFunction E (E →L[ℝ] E))
    (ε : ℝ) (hε : 0 < ε) (hu : ∀ x, u x ∈ Icc ε (1 - ε))
    (x e : E) (hDe : D x e = inner ℝ (v x) e) :
    bobkovSpatialDerivBCF c hc u D v H ε hε hu x e =
      bobkovSpatialGradientCoordinate c (u x) (v x) (H x e) e := by
  rw [bobkovSpatialDerivBCF_apply]
  simp only [add_apply, smul_apply,
    smul_eq_mul, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  rw [hDe]
  simp [bobkovSpatialGradientCoordinate, div_eq_mul_inv]
  ring

/-- The canonical bounded spatial derivative field at a fixed interpolation
time, expressed using transported Riesz Hessian data. -/
def canonicalGaussianBobkovQSpatialDerivBCF
    (t s : ℝ)
    (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (Hf : BoundedContinuousFunction E (E →L[ℝ] E))
    (ε : ℝ) (hε : 0 < ε) (hf : ∀ x, f x ∈ Icc ε (1 - ε))
    (hs : 0 ≤ s) :
    BoundedContinuousFunction E (E →L[ℝ] ℝ) :=
  bobkovSpatialDerivBCF (bobkovVarianceCoeff s)
    (bobkovVarianceCoeff_nonneg hs)
    (backwardGaussianOUValueBCF t s f)
    (backwardGaussianOUDerivBCF t s Df)
    (rieszGradientBCF (backwardGaussianOUDerivBCF t s Df))
    (backwardGaussianOURieszHessianBCF t s Hf)
    ε hε (backwardGaussianOUValueBCF_mem_Icc t s f hf)

theorem hasFDerivAt_canonicalGaussianBobkovQSpatialDerivBCF
    (t : ℝ) (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (hDf : ∀ y, HasFDerivAt f (Df y) y)
    (Hf : BoundedContinuousFunction E (E →L[ℝ] E))
    (hHf : ∀ y, HasFDerivAt (rieszGradientBCF Df) (Hf y) y)
    (ε : ℝ) (hε : 0 < ε) (hf : ∀ x, f x ∈ Icc ε (1 - ε))
    {s : ℝ} (hs : 0 ≤ s) (x : E) :
    HasFDerivAt (canonicalGaussianBobkovQ t f Df ε hε hf s)
      (canonicalGaussianBobkovQSpatialDerivBCF
        t s f Df Hf ε hε hf hs x) x := by
  have hH := hasFDerivAt_rieszGradient_backwardGaussianOU_of_rieszHessian
    t s Df Hf hHf x
  have hraw := hasFDerivAt_canonicalGaussianBobkovQ_of_gradientDerivative
    t f Df hDf ε hε hf hs hH
  apply hraw.congr_fderiv
  ext e
  have hxClosed := backwardGaussianOUValueBCF_mem_Icc t s f hf x
  have hx : backwardGaussianOUValueBCF t s f x ∈ Ioo (0 : ℝ) 1 :=
    ⟨hε.trans_le hxClosed.1, hxClosed.2.trans_lt (by linarith)⟩
  simp only [canonicalGaussianBobkovQSpatialDerivBCF,
    bobkovSpatialDerivBCF_apply,
    smul_apply, add_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, two_smul,
    smul_eq_mul, norm_rieszGradientBCF]
  rw [deriv_normalProfile hx]
  ring

/-- One bounded coordinate of the canonical spatial gradient. -/
def canonicalGaussianBobkovQGradientCoordinateBCF
    (t s : ℝ)
    (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (Hf : BoundedContinuousFunction E (E →L[ℝ] E))
    (ε : ℝ) (hε : 0 < ε) (hf : ∀ x, f x ∈ Icc ε (1 - ε))
    (hs : 0 ≤ s) (e : E) : BoundedContinuousFunction E ℝ :=
  bobkovSpatialGradientCoordinateBCF
    (bobkovVarianceCoeff s) (bobkovVarianceCoeff_nonneg hs)
    (backwardGaussianOUValueBCF t s f)
    (rieszGradientBCF (backwardGaussianOUDerivBCF t s Df))
    (backwardGaussianOURieszHessianBCF t s Hf) e
    ε hε (backwardGaussianOUValueBCF_mem_Icc t s f hf)

/-- The matching bounded diagonal Hessian field. -/
def canonicalGaussianBobkovQHessianDiagonalBCF
    (t s : ℝ)
    (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (Hf : BoundedContinuousFunction E (E →L[ℝ] E))
    (D3f : BoundedContinuousFunction E (E →L[ℝ] (E →L[ℝ] E)))
    (M : ℝ) (hM : ∀ y, ‖D3f y‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) (hf : ∀ x, f x ∈ Icc ε (1 - ε))
    (hs : 0 ≤ s) (e : E) : BoundedContinuousFunction E ℝ :=
  bobkovSpatialHessianDiagonalBCF
    (bobkovVarianceCoeff s) (bobkovVarianceCoeff_nonneg hs)
    (backwardGaussianOUValueBCF t s f)
    (rieszGradientBCF (backwardGaussianOUDerivBCF t s Df))
    (backwardGaussianOURieszHessianBCF t s Hf)
    (backwardGaussianOURieszHessianDirectionalDerivBCF
      t s D3f e M hM) e
    ε hε (backwardGaussianOUValueBCF_mem_Icc t s f hf)

theorem canonicalGaussianBobkovQSpatialDerivBCF_apply_eq_coordinate
    (t : ℝ) (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (Hf : BoundedContinuousFunction E (E →L[ℝ] E))
    (ε : ℝ) (hε : 0 < ε) (hf : ∀ x, f x ∈ Icc ε (1 - ε))
    {s : ℝ} (hs : 0 ≤ s) (x e : E) :
    canonicalGaussianBobkovQSpatialDerivBCF
        t s f Df Hf ε hε hf hs x e =
      canonicalGaussianBobkovQGradientCoordinateBCF
        t s f Df Hf ε hε hf hs e x := by
  apply bobkovSpatialDerivBCF_apply_unit
  exact (inner_rieszGradientBCF
    (backwardGaussianOUDerivBCF t s Df) x e).symm

theorem hasDerivAt_canonicalGaussianBobkovQGradientCoordinate_line
    (t : ℝ) (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (hDf : ∀ y, HasFDerivAt f (Df y) y)
    (Hf : BoundedContinuousFunction E (E →L[ℝ] E))
    (hHf : ∀ y, HasFDerivAt (rieszGradientBCF Df) (Hf y) y)
    (D3f : BoundedContinuousFunction E (E →L[ℝ] (E →L[ℝ] E)))
    (M : ℝ) (hM : ∀ y, ‖D3f y‖ ≤ M)
    (hD3f : ∀ y, HasFDerivAt Hf (D3f y) y)
    (ε : ℝ) (hε : 0 < ε) (hf : ∀ x, f x ∈ Icc ε (1 - ε))
    {s : ℝ} (hs : 0 ≤ s) (x e : E) (r : ℝ) :
    HasDerivAt
      (fun a => canonicalGaussianBobkovQGradientCoordinateBCF
        t s f Df Hf ε hε hf hs e (x + a • e))
      (canonicalGaussianBobkovQHessianDiagonalBCF
        t s f Df Hf D3f M hM ε hε hf hs e (x + r • e)) r := by
  let u : ℝ → ℝ := fun a => backwardGaussianOUValueBCF t s f (x + a • e)
  let v : ℝ → E := fun a =>
    rieszGradientBCF (backwardGaussianOUDerivBCF t s Df) (x + a • e)
  let H : ℝ → E →L[ℝ] E := fun a =>
    backwardGaussianOURieszHessianBCF t s Hf (x + a • e)
  let Ke := backwardGaussianOURieszHessianDirectionalDerivBCF
    t s D3f e M hM (x + r • e)
  have hline : HasDerivAt (fun a : ℝ => x + a • e) e r := by
    have hline' : HasDerivAt
        (((fun _ : ℝ => x) + fun a => a • e)) e r := by
      simpa only [id_eq, zero_add, one_smul] using
        (hasDerivAt_const r x).add ((hasDerivAt_id r).smul_const e)
    have hfun : (fun a : ℝ => x + a • e) =
        ((fun _ : ℝ => x) + fun a => a • e) := by
      funext a
      rfl
    rw [hfun]
    exact hline'
  have huRaw := (hasFDerivAt_backwardGaussianOUValueBCF
    t s f Df hDf (x + r • e)).comp_hasDerivAt r hline
  have hu : HasDerivAt u (inner ℝ (v r) e) r := by
    simpa [u, v, Function.comp_def, inner_rieszGradientBCF] using huRaw
  have hv : HasDerivAt v (H r e) r := by
    have h := (hasFDerivAt_rieszGradient_backwardGaussianOU_of_rieszHessian
      t s Df Hf hHf (x + r • e)).comp_hasDerivAt r hline
    simpa [v, H, Function.comp_def] using h
  have hH : HasDerivAt H Ke r := by
    simpa [H, Ke] using hasDerivAt_backwardGaussianOURieszHessian_line
      t s Hf D3f M hM hD3f x e r
  have hurClosed := backwardGaussianOUValueBCF_mem_Icc
    t s f hf (x + r • e)
  have hur : u r ∈ Ioo (0 : ℝ) 1 :=
    ⟨hε.trans_le hurClosed.1, hurClosed.2.trans_lt (by linarith)⟩
  have h := hasDerivAt_bobkovSpatialGradientCoordinate
    e hu hv hH hur (bobkovVarianceCoeff_nonneg hs)
  simpa [canonicalGaussianBobkovQGradientCoordinateBCF,
    canonicalGaussianBobkovQHessianDiagonalBCF, u, v, H, Ke] using h

theorem canonicalGaussianBobkovQSpatialDerivBCF_eq_sum_coordinates
    {n : ℕ}
    (t : ℝ)
    (f : BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1))) ℝ)
    (Df : BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ))
    (Hf : BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
        EuclideanSpace ℝ (Fin (n + 1))))
    (ε : ℝ) (hε : 0 < ε) (hf : ∀ x, f x ∈ Icc ε (1 - ε))
    {s : ℝ} (hs : 0 ≤ s)
    (y z : EuclideanSpace ℝ (Fin (n + 1))) :
    canonicalGaussianBobkovQSpatialDerivBCF
        t s f Df Hf ε hε hf hs y z =
      ∑ i, canonicalGaussianBobkovQGradientCoordinateBCF
        t s f Df Hf ε hε hf hs (euclideanUnit i) y * z i := by
  rw [covector_eq_sum_coordinates]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact canonicalGaussianBobkovQSpatialDerivBCF_apply_eq_coordinate
    t f Df Hf ε hε hf hs y (euclideanUnit i)

theorem hasDerivAt_canonicalGaussianBobkovQGradientCoordinate_transition
    {n : ℕ}
    (t : ℝ)
    (f : BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1))) ℝ)
    (Df : BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ))
    (hDf : ∀ y, HasFDerivAt f (Df y) y)
    (Hf : BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
        EuclideanSpace ℝ (Fin (n + 1))))
    (hHf : ∀ y, HasFDerivAt (rieszGradientBCF Df) (Hf y) y)
    (D3f : BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
        (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
          EuclideanSpace ℝ (Fin (n + 1)))))
    (M : ℝ) (hM : ∀ y, ‖D3f y‖ ≤ M)
    (hD3f : ∀ y, HasFDerivAt Hf (D3f y) y)
    (ε : ℝ) (hε : 0 < ε) (hf : ∀ x, f x ∈ Icc ε (1 - ε))
    {s : ℝ} (hs : 0 ≤ s)
    (x : EuclideanSpace ℝ (Fin (n + 1)))
    (i : Fin (n + 1)) (w : Fin n → ℝ) (r : ℝ) :
    HasDerivAt
      (fun a => canonicalGaussianBobkovQGradientCoordinateBCF
        t s f Df Hf ε hε hf hs (euclideanUnit i)
        (gaussianOUTransition s x (WithLp.toLp 2 (i.insertNth a w))))
      (ouNoiseCoeff s * canonicalGaussianBobkovQHessianDiagonalBCF
        t s f Df Hf D3f M hM ε hε hf hs (euclideanUnit i)
        (gaussianOUTransition s x (WithLp.toLp 2 (i.insertNth r w)))) r := by
  let e : EuclideanSpace ℝ (Fin (n + 1)) := euclideanUnit i
  let z0 : EuclideanSpace ℝ (Fin (n + 1)) :=
    WithLp.toLp 2 (i.insertNth (α := fun _ => ℝ) (0 : ℝ) w)
  let y0 := ouDriftCoeff s • x + ouNoiseCoeff s • z0
  let a := ouNoiseCoeff s
  have hpath : (fun u => gaussianOUTransition s x
      (WithLp.toLp 2 (i.insertNth u w))) =
      (fun u : ℝ => y0 + (a * u) • e) := by
    funext u
    rw [insertNth_toLp_eq_affine]
    simp only [gaussianOUTransition, y0, z0, a, e, smul_add, smul_smul]
    module
  have hline := hasDerivAt_canonicalGaussianBobkovQGradientCoordinate_line
    t f Df hDf Hf hHf D3f M hM hD3f ε hε hf hs y0 e (a * r)
  have hscale : HasDerivAt (fun u : ℝ => a * u) a r := by
    simpa [mul_comm] using (hasDerivAt_id r).const_mul a
  have hcomp := hline.scomp r hscale
  have hpathApply (u : ℝ) : gaussianOUTransition s x
      (WithLp.toLp 2 (i.insertNth u w)) = y0 + (a * u) • e :=
    congrFun hpath u
  have hcomp' : HasDerivAt
      (fun u => canonicalGaussianBobkovQGradientCoordinateBCF
        t s f Df Hf ε hε hf hs e (y0 + (a * u) • e))
      (a * canonicalGaussianBobkovQHessianDiagonalBCF
        t s f Df Hf D3f M hM ε hε hf hs e
          (y0 + (a * r) • e)) r := by
    simpa [Function.comp_def, mul_smul, smul_eq_mul] using hcomp
  rw [hpathApply r]
  change HasDerivAt
    (fun u => canonicalGaussianBobkovQGradientCoordinateBCF
      t s f Df Hf ε hε hf hs e
        (gaussianOUTransition s x (WithLp.toLp 2 (i.insertNth u w))))
    (a * canonicalGaussianBobkovQHessianDiagonalBCF
      t s f Df Hf D3f M hM ε hε hf hs e
        (y0 + (a * r) • e)) r
  apply hcomp'.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun u =>
    congrArg (fun y => canonicalGaussianBobkovQGradientCoordinateBCF
      t s f Df Hf ε hε hf hs e y) (hpathApply u)

end
end UniformRandomMALA.Concrete
