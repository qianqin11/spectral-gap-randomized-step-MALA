import UniformRandomMALA.Concrete.GaussianOUCoordinateFields

/-!
# Diagonal calculus for the canonical Gaussian Bobkov field

The OU generator only needs the diagonal entries of the spatial Hessian.
This module constructs those entries as bounded continuous scalar fields and
proves their chain rule using a fixed-direction derivative of the transported
Hessian.  Consequently no Bochner integral in the full third-order operator
space is required.
-/

namespace UniformRandomMALA.Concrete

open Function Set Metric MeasureTheory Filter ContinuousLinearMap ProbabilityTheory
open scoped Topology NNReal ENNReal ProbabilityTheory BigOperators

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The first normal-profile derivative, composed with an interior-valued
bounded continuous function. -/
def normalProfileDerivCompBCF
    (u : BoundedContinuousFunction E ℝ)
    (ε : ℝ) (hε : 0 < ε) (hu : ∀ x, u x ∈ Icc ε (1 - ε)) :
    BoundedContinuousFunction E ℝ where
  toFun := fun x => deriv normalProfile (u x)
  continuous_toFun := continuous_iff_continuousAt.2 fun x =>
    (hasDerivAt_deriv_normalProfile
      ⟨hε.trans_le (hu x).1, (hu x).2.trans_lt (by linarith)⟩).continuousAt.comp
        u.continuous.continuousAt
  map_bounded' := by
    have hcont : ContinuousOn (deriv normalProfile) (Icc ε (1 - ε)) := by
      intro a ha
      exact (hasDerivAt_deriv_normalProfile
        ⟨hε.trans_le ha.1, ha.2.trans_lt (by linarith)⟩).continuousAt.continuousWithinAt
    have himage : Bornology.IsBounded
        (deriv normalProfile '' Icc ε (1 - ε)) :=
      (isCompact_Icc.image_of_continuousOn hcont).isBounded
    apply Metric.isBounded_range_iff.mp
    exact himage.subset fun y hy => by
      rcases hy with ⟨x, rfl⟩
      exact ⟨u x, hu x, rfl⟩

omit [InnerProductSpace ℝ E] in
@[simp] theorem normalProfileDerivCompBCF_apply
    (u : BoundedContinuousFunction E ℝ)
    (ε : ℝ) (hε : 0 < ε) (hu : ∀ x, u x ∈ Icc ε (1 - ε)) (x : E) :
    normalProfileDerivCompBCF u ε hε hu x = deriv normalProfile (u x) := rfl

/-- The reciprocal normal profile, composed with an interior-valued bounded
continuous function. -/
def normalProfileInvCompBCF
    (u : BoundedContinuousFunction E ℝ)
    (ε : ℝ) (hε : 0 < ε) (hu : ∀ x, u x ∈ Icc ε (1 - ε)) :
    BoundedContinuousFunction E ℝ where
  toFun := fun x => (normalProfile (u x))⁻¹
  continuous_toFun := continuous_iff_continuousAt.2 fun x =>
    ((hasDerivAt_normalProfile
      ⟨hε.trans_le (hu x).1, (hu x).2.trans_lt (by linarith)⟩).continuousAt.comp
        u.continuous.continuousAt).inv₀
      (normalProfile_pos
        ⟨hε.trans_le (hu x).1, (hu x).2.trans_lt (by linarith)⟩).ne'
  map_bounded' := by
    have hcont : ContinuousOn (fun a => (normalProfile a)⁻¹)
        (Icc ε (1 - ε)) := by
      intro a ha
      exact ((hasDerivAt_normalProfile
        ⟨hε.trans_le ha.1, ha.2.trans_lt (by linarith)⟩).continuousAt).inv₀
          (normalProfile_pos
            ⟨hε.trans_le ha.1, ha.2.trans_lt (by linarith)⟩).ne'
        |>.continuousWithinAt
    have himage : Bornology.IsBounded
        ((fun a => (normalProfile a)⁻¹) '' Icc ε (1 - ε)) :=
      (isCompact_Icc.image_of_continuousOn hcont).isBounded
    apply Metric.isBounded_range_iff.mp
    exact himage.subset fun y hy => by
      rcases hy with ⟨x, rfl⟩
      exact ⟨u x, hu x, rfl⟩

omit [InnerProductSpace ℝ E] in
@[simp] theorem normalProfileInvCompBCF_apply
    (u : BoundedContinuousFunction E ℝ)
    (ε : ℝ) (hε : 0 < ε) (hu : ∀ x, u x ∈ Icc ε (1 - ε)) (x : E) :
    normalProfileInvCompBCF u ε hε hu x = (normalProfile (u x))⁻¹ := rfl

/-- Pointwise real inner products of bounded vector fields are bounded and
continuous. -/
def boundedContinuousInner
    (v w : BoundedContinuousFunction E E) :
    BoundedContinuousFunction E ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => inner ℝ (v x) (w x))
    (v.continuous.inner w.continuous)
    (‖v‖ * ‖w‖) (fun x => by
      rw [Real.norm_eq_abs]
      exact (abs_real_inner_le_norm (v x) (w x)).trans
        (mul_le_mul (v.norm_coe_le_norm x) (w.norm_coe_le_norm x)
          (norm_nonneg _) (norm_nonneg _)))

@[simp] theorem boundedContinuousInner_apply
    (v w : BoundedContinuousFunction E E) (x : E) :
    boundedContinuousInner v w x = inner ℝ (v x) (w x) := rfl

/-- Inner product with one fixed vector as a bounded scalar field. -/
def boundedContinuousInnerRight
    (v : BoundedContinuousFunction E E) (e : E) :
    BoundedContinuousFunction E ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => inner ℝ (v x) e)
    (v.continuous.inner continuous_const)
    (‖v‖ * ‖e‖) (fun x => by
      rw [Real.norm_eq_abs]
      exact (abs_real_inner_le_norm (v x) e).trans
        (mul_le_mul_of_nonneg_right (v.norm_coe_le_norm x) (norm_nonneg e)))

@[simp] theorem boundedContinuousInnerRight_apply
    (v : BoundedContinuousFunction E E) (e x : E) :
    boundedContinuousInnerRight v e x = inner ℝ (v x) e := rfl

/-- Evaluate every operator in a bounded operator field at one fixed vector. -/
def boundedContinuousApply
    (H : BoundedContinuousFunction E (E →L[ℝ] E)) (e : E) :
    BoundedContinuousFunction E E :=
  ((ContinuousLinearMap.apply ℝ E) e).compLeftContinuousBounded E H

@[simp] theorem boundedContinuousApply_apply
    (H : BoundedContinuousFunction E (E →L[ℝ] E)) (e x : E) :
    boundedContinuousApply H e x = H x e := rfl

/-- Pointwise scalar multiplication of two bounded continuous fields. -/
def boundedContinuousSMul
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a : BoundedContinuousFunction E ℝ)
    (v : BoundedContinuousFunction E F) :
    BoundedContinuousFunction E F :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => a x • v x) (a.continuous.smul v.continuous)
    (‖a‖ * ‖v‖) (fun x => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (a.norm_coe_le_norm x) (v.norm_coe_le_norm x)
        (norm_nonneg _) (norm_nonneg _))

omit [InnerProductSpace ℝ E] in
@[simp] theorem boundedContinuousSMul_apply
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a : BoundedContinuousFunction E ℝ)
    (v : BoundedContinuousFunction E F) (x : E) :
    boundedContinuousSMul a v x = a x • v x := rfl

/-- The covector field `z ↦ ⟨v,H z⟩` formed pointwise from bounded
vector and operator fields. -/
def boundedContinuousInnerComp
    (v : BoundedContinuousFunction E E)
    (H : BoundedContinuousFunction E (E →L[ℝ] E)) :
    BoundedContinuousFunction E (E →L[ℝ] ℝ) :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => (innerSL ℝ (v x)).comp (H x))
    (by fun_prop) (‖v‖ * ‖H‖) (fun x => by
      calc
        ‖(innerSL ℝ (v x)).comp (H x)‖ ≤
            ‖innerSL ℝ (v x)‖ * ‖H x‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ = ‖v x‖ * ‖H x‖ := by rw [innerSL_apply_norm]
        _ ≤ ‖v‖ * ‖H‖ := mul_le_mul
          (v.norm_coe_le_norm x) (H.norm_coe_le_norm x)
          (norm_nonneg _) (norm_nonneg _))

@[simp] theorem boundedContinuousInnerComp_apply
    (v : BoundedContinuousFunction E E)
    (H : BoundedContinuousFunction E (E →L[ℝ] E)) (x : E) :
    boundedContinuousInnerComp v H x = (innerSL ℝ (v x)).comp (H x) := rfl

/-- The reciprocal square-root radius in the canonical Bobkov field.  Its
uniform bound follows from the positive normal-profile component. -/
def bobkovInvRadiusBCF
    (c : ℝ) (hc : 0 ≤ c)
    (u : BoundedContinuousFunction E ℝ)
    (v : BoundedContinuousFunction E E)
    (ε : ℝ) (hε : 0 < ε) (hu : ∀ x, u x ∈ Icc ε (1 - ε)) :
    BoundedContinuousFunction E ℝ :=
  let Iinv := normalProfileInvCompBCF u ε hε hu
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => (Real.sqrt (normalProfile (u x) ^ 2 + c * ‖v x‖ ^ 2))⁻¹)
    (by
      apply continuous_iff_continuousAt.2
      intro x
      have hx : u x ∈ Ioo (0 : ℝ) 1 :=
        ⟨hε.trans_le (hu x).1, (hu x).2.trans_lt (by linarith)⟩
      have hrad : 0 < normalProfile (u x) ^ 2 + c * ‖v x‖ ^ 2 := by
        nlinarith [normalProfile_pos hx, mul_nonneg hc (sq_nonneg ‖v x‖)]
      have hI : ContinuousAt (fun y => normalProfile (u y)) x :=
        (hasDerivAt_normalProfile hx).continuousAt.comp u.continuous.continuousAt
      exact (Real.continuous_sqrt.continuousAt.comp
        ((hI.pow 2).add (continuousAt_const.mul
          ((continuous_norm.comp v.continuous).continuousAt.pow 2)))).inv₀
            (Real.sqrt_pos.2 hrad).ne')
    ‖Iinv‖ (fun x => by
      have hx : u x ∈ Ioo (0 : ℝ) 1 :=
        ⟨hε.trans_le (hu x).1, (hu x).2.trans_lt (by linarith)⟩
      let I := normalProfile (u x)
      let R := Real.sqrt (I ^ 2 + c * ‖v x‖ ^ 2)
      have hI : 0 < I := normalProfile_pos hx
      have hrad : 0 < I ^ 2 + c * ‖v x‖ ^ 2 := by
        nlinarith [hI, mul_nonneg hc (sq_nonneg ‖v x‖)]
      have hR : 0 < R := Real.sqrt_pos.2 hrad
      have hIR : I ≤ R := by
        have hR2 := Real.sq_sqrt hrad.le
        nlinarith [mul_nonneg hc (sq_nonneg ‖v x‖)]
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
      calc
        R⁻¹ ≤ I⁻¹ := (inv_le_inv₀ hR hI).2 hIR
        _ = ‖Iinv x‖ := by
          change I⁻¹ = |I⁻¹|
          rw [abs_of_pos (inv_pos.mpr hI)]
        _ ≤ ‖Iinv‖ := Iinv.norm_coe_le_norm x)

omit [InnerProductSpace ℝ E] in
@[simp] theorem bobkovInvRadiusBCF_apply
    (c : ℝ) (hc : 0 ≤ c)
    (u : BoundedContinuousFunction E ℝ)
    (v : BoundedContinuousFunction E E)
    (ε : ℝ) (hε : 0 < ε) (hu : ∀ x, u x ∈ Icc ε (1 - ε)) (x : E) :
    bobkovInvRadiusBCF c hc u v ε hε hu x =
      (Real.sqrt (normalProfile (u x) ^ 2 + c * ‖v x‖ ^ 2))⁻¹ := rfl

/-- One coordinate of the spatial gradient of the canonical Bobkov square root. -/
def bobkovSpatialGradientCoordinate
    (c u : ℝ) (v He e : E) : ℝ :=
  (normalProfile u * deriv normalProfile u * inner ℝ v e +
      c * inner ℝ v He) /
    Real.sqrt (normalProfile u ^ 2 + c * ‖v‖ ^ 2)

/-- The corresponding diagonal entry of its spatial Hessian. -/
def bobkovSpatialHessianDiagonal
    (c u : ℝ) (v He : E) (Ke : E →L[ℝ] E) (e : E) : ℝ :=
  let I := normalProfile u
  let Ip := deriv normalProfile u
  let ge := inner ℝ v e
  let N := I * Ip * ge + c * inner ℝ v He
  let Np := (Ip ^ 2 - 1) * ge ^ 2 +
    I * Ip * inner ℝ He e +
    c * (‖He‖ ^ 2 + inner ℝ v (Ke e))
  let R := Real.sqrt (I ^ 2 + c * ‖v‖ ^ 2)
  Np / R - N ^ 2 / R ^ 3

/-- The bounded field formed by one coordinate of the spatial Bobkov
gradient. -/
def bobkovSpatialGradientCoordinateBCF
    (c : ℝ) (hc : 0 ≤ c)
    (u : BoundedContinuousFunction E ℝ)
    (v : BoundedContinuousFunction E E)
    (H : BoundedContinuousFunction E (E →L[ℝ] E)) (e : E)
    (ε : ℝ) (hε : 0 < ε) (hu : ∀ x, u x ∈ Icc ε (1 - ε)) :
    BoundedContinuousFunction E ℝ :=
  let I := normalProfileCompBCF u ε hε hu
  let Ip := normalProfileDerivCompBCF u ε hε hu
  let ec := BoundedContinuousFunction.const E e
  let ge := boundedContinuousInner v ec
  let He := boundedContinuousApply H e
  let N := I * Ip * ge + c • boundedContinuousInner v He
  N * bobkovInvRadiusBCF c hc u v ε hε hu

@[simp] theorem bobkovSpatialGradientCoordinateBCF_apply
    (c : ℝ) (hc : 0 ≤ c)
    (u : BoundedContinuousFunction E ℝ)
    (v : BoundedContinuousFunction E E)
    (H : BoundedContinuousFunction E (E →L[ℝ] E)) (e : E)
    (ε : ℝ) (hε : 0 < ε) (hu : ∀ x, u x ∈ Icc ε (1 - ε)) (x : E) :
    bobkovSpatialGradientCoordinateBCF c hc u v H e ε hε hu x =
      bobkovSpatialGradientCoordinate c (u x) (v x) (H x e) e := by
  simp [bobkovSpatialGradientCoordinateBCF,
    bobkovSpatialGradientCoordinate, div_eq_mul_inv]

/-- The bounded field formed by the matching diagonal entry of the spatial
Bobkov Hessian.  Only the fixed-direction derivative `Ke` of `H` is needed. -/
def bobkovSpatialHessianDiagonalBCF
    (c : ℝ) (hc : 0 ≤ c)
    (u : BoundedContinuousFunction E ℝ)
    (v : BoundedContinuousFunction E E)
    (H Ke : BoundedContinuousFunction E (E →L[ℝ] E)) (e : E)
    (ε : ℝ) (hε : 0 < ε) (hu : ∀ x, u x ∈ Icc ε (1 - ε)) :
    BoundedContinuousFunction E ℝ :=
  let I := normalProfileCompBCF u ε hε hu
  let Ip := normalProfileDerivCompBCF u ε hε hu
  let ec := BoundedContinuousFunction.const E e
  let ge := boundedContinuousInner v ec
  let He := boundedContinuousApply H e
  let Kee := boundedContinuousApply Ke e
  let hee := boundedContinuousInner He ec
  let N := I * Ip * ge + c • boundedContinuousInner v He
  let Np := (Ip ^ 2 - 1) * ge ^ 2 + I * Ip * hee +
    c • (He.normComp ^ 2 + boundedContinuousInner v Kee)
  let Rinv := bobkovInvRadiusBCF c hc u v ε hε hu
  Np * Rinv - N ^ 2 * Rinv ^ 3

@[simp] theorem bobkovSpatialHessianDiagonalBCF_apply
    (c : ℝ) (hc : 0 ≤ c)
    (u : BoundedContinuousFunction E ℝ)
    (v : BoundedContinuousFunction E E)
    (H Ke : BoundedContinuousFunction E (E →L[ℝ] E)) (e : E)
    (ε : ℝ) (hε : 0 < ε) (hu : ∀ x, u x ∈ Icc ε (1 - ε)) (x : E) :
    bobkovSpatialHessianDiagonalBCF c hc u v H Ke e ε hε hu x =
      bobkovSpatialHessianDiagonal c (u x) (v x) (H x e) (Ke x) e := by
  simp [bobkovSpatialHessianDiagonalBCF, bobkovSpatialHessianDiagonal,
    div_eq_mul_inv]
  left
  ring

theorem hasDerivAt_bobkovSpatialGradientCoordinate
    {u : ℝ → ℝ} {v : ℝ → E} {H : ℝ → E →L[ℝ] E}
    {r c : ℝ} {Ke : E →L[ℝ] E} (e : E)
    (hu : HasDerivAt u (inner ℝ (v r) e) r)
    (hv : HasDerivAt v (H r e) r)
    (hH : HasDerivAt H Ke r)
    (hur : u r ∈ Ioo (0 : ℝ) 1) (hc : 0 ≤ c) :
    HasDerivAt
      (fun a => bobkovSpatialGradientCoordinate c (u a) (v a) (H a e) e)
      (bobkovSpatialHessianDiagonal c (u r) (v r) (H r e) Ke e) r := by
  have hec : HasDerivAt (fun _ : ℝ => e) 0 r := hasDerivAt_const r e
  have hHeCurve : HasDerivAt (fun a => H a e) (Ke e) r := by
    have h := ((ContinuousLinearMap.apply ℝ E) e).hasFDerivAt.comp_hasDerivAt r hH
    simpa [Function.comp_def] using h
  have hgeCurve : HasDerivAt (fun a => inner ℝ (v a) e)
      (inner ℝ (H r e) e) r := by
    simpa using hv.inner ℝ hec
  have hvHe : HasDerivAt (fun a => inner ℝ (v a) (H a e))
      (inner ℝ (H r e) (H r e) + inner ℝ (v r) (Ke e)) r := by
    simpa [add_comm] using hv.inner ℝ hHeCurve
  have hI := (hasDerivAt_normalProfile hur).comp r hu
  have hIp := (hasDerivAt_deriv_normalProfile hur).comp r hu
  have hI' : HasDerivAt (normalProfile ∘ u)
      (deriv normalProfile (u r) * inner ℝ (v r) e) r := by
    simpa [deriv_normalProfile hur] using hI
  have hIp' : HasDerivAt (deriv normalProfile ∘ u)
      (deriv (deriv normalProfile) (u r) * inner ℝ (v r) e) r := by
    simpa [deriv_succ_normalProfile hur] using hIp
  have hN := ((hI'.mul hIp').mul hgeCurve).add (hvHe.const_mul c)
  have hA := (hI'.pow 2).add ((hv.norm_sq).const_mul c)
  have hApos : 0 < normalProfile (u r) ^ 2 + c * ‖v r‖ ^ 2 := by
    have hIp0 := normalProfile_pos hur
    nlinarith [mul_nonneg hc (sq_nonneg ‖v r‖)]
  have hR := hA.sqrt hApos.ne'
  have hquot := hN.div hR (Real.sqrt_pos.2 hApos).ne'
  apply hquot.congr_deriv
  simp only [bobkovSpatialHessianDiagonal, Function.comp_apply,
    Pi.mul_apply, Pi.add_apply, Pi.pow_apply]
  rw [deriv_succ_normalProfile hur]
  rw [real_inner_self_eq_norm_sq]
  have hIne : normalProfile (u r) ≠ 0 := (normalProfile_pos hur).ne'
  field_simp [hIne, Real.sqrt_pos.2 hApos |>.ne']
  ring_nf

end
end UniformRandomMALA.Concrete
