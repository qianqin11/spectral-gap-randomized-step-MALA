import UniformRandomMALA.Concrete.GaussianOUCanonicalDiagonalFields

/-!
# Backward Gaussian OU generator identities

This module proves the backward Kolmogorov equations needed by the canonical
Bobkov interpolation.  All Gaussian integration by parts is performed one
Euclidean coordinate at a time.  The gradient equation transports fixed
third-derivative directions, avoiding Bochner integration in a third-level
operator space.
-/

namespace UniformRandomMALA.Concrete

open Function Set Metric MeasureTheory Filter ContinuousLinearMap ProbabilityTheory
open scoped Topology NNReal ENNReal ProbabilityTheory BigOperators

noncomputable section

theorem hasDerivAt_rieszCoordinate_transition
    {n : ℕ}
    (Gf : BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1))))
    (Hf : BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
        EuclideanSpace ℝ (Fin (n + 1))))
    (hHf : ∀ y, HasFDerivAt Gf (Hf y) y)
    (s : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1)))
    (i : Fin (n + 1)) (w : Fin n → ℝ) (r : ℝ) :
    HasDerivAt
      (fun u => inner ℝ
        (Gf (gaussianOUTransition s x
          (WithLp.toLp 2 (i.insertNth u w)))) (euclideanUnit i))
      (ouNoiseCoeff s * inner ℝ
        (Hf (gaussianOUTransition s x
          (WithLp.toLp 2 (i.insertNth r w))) (euclideanUnit i))
        (euclideanUnit i)) r := by
  let z0 : EuclideanSpace ℝ (Fin (n + 1)) :=
    WithLp.toLp 2 (i.insertNth (α := fun _ => ℝ) (0 : ℝ) w)
  let y0 := ouDriftCoeff s • x + ouNoiseCoeff s • z0
  let c := ouNoiseCoeff s • euclideanUnit i
  have hfun : (fun u => gaussianOUTransition s x
      (WithLp.toLp 2 (i.insertNth u w))) =
      ((fun _ : ℝ => y0) + fun u => u • c) := by
    funext u
    rw [insertNth_toLp_eq_affine]
    simp only [Pi.add_apply, gaussianOUTransition, z0, y0, c,
      smul_add, smul_smul]
    module
  have hcurve := (hasDerivAt_const r y0).add
    ((hasDerivAt_id r).smul_const c)
  have hcurve' : HasDerivAt
      (((fun _ : ℝ => y0) + fun u => u • c)) c r := by
    simpa only [id_eq, zero_add, one_smul] using hcurve
  rw [← hfun] at hcurve'
  have hG := (hHf _).comp_hasDerivAt r hcurve'
  have he := hasDerivAt_const r (euclideanUnit i)
  have hinner := hG.inner ℝ he
  simpa [c, smul_eq_mul, Function.comp_def, inner_smul_left] using hinner

theorem backwardGaussianOUValueTimeDeriv_eq_neg_generator
    {n : ℕ}
    (t s : ℝ) (hst : s < t)
    (Df : BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ))
    (Hf : BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
        EuclideanSpace ℝ (Fin (n + 1))))
    (hHf : ∀ y, HasFDerivAt (rieszGradientBCF Df) (Hf y) y)
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    backwardGaussianOUValueTimeDeriv t s Df x =
      -∑ i, (inner ℝ
          (backwardGaussianOURieszHessianBCF t s Hf x (euclideanUnit i))
          (euclideanUnit i) -
        x i * inner ℝ
          (rieszGradientBCF (backwardGaussianOUDerivBCF t s Df) x)
          (euclideanUnit i)) := by
  let G := EuclideanSpace ℝ (Fin (n + 1))
  let τ := t - s
  let a := ouDriftCoeff τ
  let b := ouNoiseCoeff τ
  let Gf := rieszGradientBCF Df
  let q1 : Fin (n + 1) → BoundedContinuousFunction G ℝ := fun i =>
    boundedContinuousInnerRight Gf (euclideanUnit i)
  let q2 : Fin (n + 1) → BoundedContinuousFunction G ℝ := fun i =>
    boundedContinuousInnerRight
      (boundedContinuousApply Hf (euclideanUnit i)) (euclideanUnit i)
  have hτ : 0 < τ := sub_pos.2 hst
  have hb : 0 < b := by
    dsimp only [b, ouNoiseCoeff]
    exact Real.sqrt_pos.2 (bobkovVarianceCoeff_pos hτ)
  have hGint : Integrable
      (fun z : G => Gf (gaussianOUTransition τ x z)) (stdGaussian G) := by
    refine Integrable.of_bound
      (Gf.continuous.comp (by
        unfold gaussianOUTransition
        fun_prop)).aestronglyMeasurable ‖Gf‖ ?_
    exact Filter.Eventually.of_forall fun z => Gf.norm_coe_le_norm _
  have hHint : Integrable
      (fun z : G => Hf (gaussianOUTransition τ x z)) (stdGaussian G) := by
    refine Integrable.of_bound
      (Hf.continuous.comp (by
        unfold gaussianOUTransition
        fun_prop)).aestronglyMeasurable ‖Hf‖ ?_
    exact Filter.Eventually.of_forall fun z => Hf.norm_coe_le_norm _
  have hq1int (i : Fin (n + 1)) : Integrable
      (fun z : G => q1 i (gaussianOUTransition τ x z)) (stdGaussian G) := by
    exact ((innerSL ℝ (euclideanUnit i))).integrable_comp hGint |>.congr
      (Filter.Eventually.of_forall fun z => by
        simp [q1, Gf, real_inner_comm])
  have hq2int (i : Fin (n + 1)) : Integrable
      (fun z : G => q2 i (gaussianOUTransition τ x z)) (stdGaussian G) := by
    have hHe := ((ContinuousLinearMap.apply ℝ G) (euclideanUnit i)).integrable_comp hHint
    exact ((innerSL ℝ (euclideanUnit i))).integrable_comp hHe |>.congr
      (Filter.Eventually.of_forall fun z => by
        simp [q2, real_inner_comm])
  have hzq1int (i : Fin (n + 1)) : Integrable
      (fun z : G => z i * q1 i (gaussianOUTransition τ x z))
      (stdGaussian G) := by
    have hnorm : Integrable (fun z : G => ‖z‖) (stdGaussian G) :=
      IsGaussian.integrable_id.norm
    refine (hnorm.const_mul ‖q1 i‖).mono'
      ((EuclideanSpace.proj i).continuous.mul
        ((q1 i).continuous.comp (by
          unfold gaussianOUTransition
          fun_prop))).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |z i| * |q1 i (gaussianOUTransition τ x z)| ≤ ‖z‖ * ‖q1 i‖ := by
          gcongr
          · simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z i
          · simpa [Real.norm_eq_abs] using (q1 i).norm_coe_le_norm _
        _ = ‖q1 i‖ * ‖z‖ := mul_comm _ _
  have hibp (i : Fin (n + 1)) :
      ∫ z : G, z i * q1 i (gaussianOUTransition τ x z) ∂stdGaussian G =
        b * ∫ z : G, q2 i (gaussianOUTransition τ x z) ∂stdGaussian G := by
    apply integral_coordinate_mul_transition_eq (q1 i) (q2 i) x i
    intro w r
    simpa [q1, q2, Gf] using
      hasDerivAt_rieszCoordinate_transition Gf Hf hHf τ x i w r
  have hB (i : Fin (n + 1)) :
      inner ℝ (rieszGradientBCF (backwardGaussianOUDerivBCF t s Df) x)
          (euclideanUnit i) =
        a * ∫ z : G, q1 i (gaussianOUTransition τ x z) ∂stdGaussian G := by
    rw [← backwardGaussianOURieszGradientBCF_rieszGradientBCF t s Df x]
    rw [backwardGaussianOURieszGradientBCF_apply]
    rw [real_inner_smul_left]
    change a * inner ℝ
        (∫ z : G, Gf (gaussianOUTransition τ x z) ∂stdGaussian G)
        (euclideanUnit i) =
      a * ∫ z : G, q1 i (gaussianOUTransition τ x z) ∂stdGaussian G
    congr 1
    calc
      inner ℝ
          (∫ z : G, Gf (gaussianOUTransition τ x z) ∂stdGaussian G)
          (euclideanUnit i) =
          inner ℝ (euclideanUnit i)
            (∫ z : G, Gf (gaussianOUTransition τ x z) ∂stdGaussian G) :=
        real_inner_comm _ _
      _ = ∫ z : G, inner ℝ (euclideanUnit i)
          (Gf (gaussianOUTransition τ x z)) ∂stdGaussian G := by
        simpa using
          ((innerSL ℝ (euclideanUnit i)).integral_comp_comm hGint).symm
      _ = ∫ z : G, q1 i (gaussianOUTransition τ x z) ∂stdGaussian G := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by
          simp [q1, Gf, real_inner_comm]
  have hC (i : Fin (n + 1)) :
      inner ℝ (backwardGaussianOURieszHessianBCF t s Hf x
          (euclideanUnit i)) (euclideanUnit i) =
        a ^ 2 * ∫ z : G, q2 i (gaussianOUTransition τ x z) ∂stdGaussian G := by
    rw [backwardGaussianOURieszHessianBCF_apply]
    rw [smul_apply, real_inner_smul_left]
    change a ^ 2 * inner ℝ
        ((∫ z : G, Hf (gaussianOUTransition τ x z) ∂stdGaussian G)
          (euclideanUnit i)) (euclideanUnit i) =
      a ^ 2 * ∫ z : G, q2 i (gaussianOUTransition τ x z) ∂stdGaussian G
    congr 1
    rw [ContinuousLinearMap.integral_apply hHint]
    have hHe :=
      ((ContinuousLinearMap.apply ℝ G) (euclideanUnit i)).integrable_comp hHint
    calc
      inner ℝ
          (∫ z : G, Hf (gaussianOUTransition τ x z) (euclideanUnit i)
            ∂stdGaussian G) (euclideanUnit i) =
          inner ℝ (euclideanUnit i)
            (∫ z : G, Hf (gaussianOUTransition τ x z) (euclideanUnit i)
              ∂stdGaussian G) := real_inner_comm _ _
      _ = ∫ z : G, inner ℝ (euclideanUnit i)
          (Hf (gaussianOUTransition τ x z) (euclideanUnit i))
          ∂stdGaussian G := by
        simpa using
          ((innerSL ℝ (euclideanUnit i)).integral_comp_comm hHe).symm
      _ = ∫ z : G, q2 i (gaussianOUTransition τ x z) ∂stdGaussian G := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by
          simp [q2, real_inner_comm]
  have hdirectPoint (z : G) :
      Df (gaussianOUTransition τ x z)
          (gaussianOUTransitionTimeDeriv τ x z) =
        ∑ i, ((-a * x i) * q1 i (gaussianOUTransition τ x z) +
          (a ^ 2 / b) * (z i * q1 i (gaussianOUTransition τ x z))) := by
    rw [covector_eq_sum_coordinates]
    apply Finset.sum_congr rfl
    intro i _
    simp only [gaussianOUTransitionTimeDeriv, a, b, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul]
    rw [show covectorCoordinateBCF Df i (gaussianOUTransition τ x z) =
      q1 i (gaussianOUTransition τ x z) by
        change Df _ (euclideanUnit i) =
          inner ℝ (rieszGradientBCF Df _) (euclideanUnit i)
        exact (inner_rieszGradientBCF Df _ _).symm]
    ring
  have hcoord (i : Fin (n + 1)) :
      (∫ z : G, ((-a * x i) * q1 i (gaussianOUTransition τ x z) +
          (a ^ 2 / b) * (z i * q1 i (gaussianOUTransition τ x z)))
          ∂stdGaussian G) =
        inner ℝ (backwardGaussianOURieszHessianBCF t s Hf x
            (euclideanUnit i)) (euclideanUnit i) -
          x i * inner ℝ
            (rieszGradientBCF (backwardGaussianOUDerivBCF t s Df) x)
            (euclideanUnit i) := by
    rw [integral_add
      ((hq1int i).const_mul (-a * x i))
      ((hzq1int i).const_mul (a ^ 2 / b)),
      integral_const_mul, integral_const_mul, hibp i, hB i, hC i]
    field_simp [hb.ne']
    ring
  unfold backwardGaussianOUValueTimeDeriv
  rw [integral_congr_ae (Filter.Eventually.of_forall hdirectPoint)]
  rw [integral_finsetSum]
  · congr 1
    exact Finset.sum_congr rfl fun i _ => hcoord i
  · intro i _
    exact ((hq1int i).const_mul (-a * x i)).add
      ((hzq1int i).const_mul (a ^ 2 / b))

/-- The backward-time derivative of a Riesz gradient transported directly
through the Mehler semigroup.  This avoids forming a Bochner integral in an
iterated covector space. -/
def backwardGaussianOURieszGradientTimeDeriv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [SecondCountableTopology E]
    (t s : ℝ) (Gf : BoundedContinuousFunction E E)
    (Hf : BoundedContinuousFunction E (E →L[ℝ] E)) (x : E) : E :=
  ouDriftCoeff (t - s) • gaussianOUAverage (t - s) Gf x -
    ouDriftCoeff (t - s) •
      (∫ z, Hf (gaussianOUTransition (t - s) x z)
        (gaussianOUTransitionTimeDeriv (t - s) x z) ∂stdGaussian E)

theorem hasDerivAt_backwardGaussianOURieszGradientBCF_time
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [SecondCountableTopology E]
    (t s : ℝ) (hst : s < t)
    (Gf : BoundedContinuousFunction E E)
    (Hf : BoundedContinuousFunction E (E →L[ℝ] E))
    (hHf : ∀ y, HasFDerivAt Gf (Hf y) y) (x : E) :
    HasDerivAt (fun r => backwardGaussianOURieszGradientBCF t r Gf x)
      (backwardGaussianOURieszGradientTimeDeriv t s Gf Hf x) s := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hlag : 0 < t - s := sub_pos.2 hst
  have havg := hasDerivAt_gaussianOUAverage_time_direct
    hlag Gf Hf hHf x
  have hcoeff := hasDerivAt_ouDriftCoeff (t - s)
  have hproduct := hcoeff.smul havg
  have hinner : HasDerivAt (fun r : ℝ => t - r) (-1) s := by
    convert (hasDerivAt_const s t).sub (hasDerivAt_id s) using 1 <;>
      first | rfl | norm_num
  have hcomp := hproduct.scomp s hinner
  simpa [backwardGaussianOURieszGradientBCF,
    backwardGaussianOURieszGradientTimeDeriv, Function.comp_def,
    gaussianOUAverage, sub_eq_add_neg, add_comm, add_left_comm,
    add_assoc] using hcomp

theorem hasDerivAt_rieszHessianCoordinate_transition
    {n : ℕ}
    (Hf : BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
        EuclideanSpace ℝ (Fin (n + 1))))
    (D3f : BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
        (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
          EuclideanSpace ℝ (Fin (n + 1)))))
    (hD3f : ∀ y, HasFDerivAt Hf (D3f y) y)
    (s : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1)))
    (i j : Fin (n + 1)) (w : Fin n → ℝ) (r : ℝ) :
    HasDerivAt
      (fun u => inner ℝ
        (Hf (gaussianOUTransition s x
          (WithLp.toLp 2 (i.insertNth u w))) (euclideanUnit i))
        (euclideanUnit j))
      (ouNoiseCoeff s * inner ℝ
        (D3f (gaussianOUTransition s x
          (WithLp.toLp 2 (i.insertNth r w)))
          (euclideanUnit i) (euclideanUnit i))
        (euclideanUnit j)) r := by
  let z0 : EuclideanSpace ℝ (Fin (n + 1)) :=
    WithLp.toLp 2 (i.insertNth (α := fun _ => ℝ) (0 : ℝ) w)
  let y0 := ouDriftCoeff s • x + ouNoiseCoeff s • z0
  let c := ouNoiseCoeff s • euclideanUnit i
  have hfun : (fun u => gaussianOUTransition s x
      (WithLp.toLp 2 (i.insertNth u w))) =
      ((fun _ : ℝ => y0) + fun u => u • c) := by
    funext u
    rw [insertNth_toLp_eq_affine]
    simp only [Pi.add_apply, gaussianOUTransition, z0, y0, c,
      smul_add, smul_smul]
    module
  have hcurve := (hasDerivAt_const r y0).add
    ((hasDerivAt_id r).smul_const c)
  have hcurve' : HasDerivAt
      (((fun _ : ℝ => y0) + fun u => u • c)) c r := by
    simpa only [id_eq, zero_add, one_smul] using hcurve
  rw [← hfun] at hcurve'
  have hH := (hD3f _).comp_hasDerivAt r hcurve'
  have happ := ((ContinuousLinearMap.apply ℝ _)
    (euclideanUnit i)).hasFDerivAt.comp_hasDerivAt r hH
  have he := hasDerivAt_const r (euclideanUnit j)
  have hinner := happ.inner ℝ he
  simpa [c, Function.comp_def, real_inner_smul_left, smul_smul] using hinner

@[simp] theorem rieszD3DirectionBCF_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [SecondCountableTopology E]
    (D3f : BoundedContinuousFunction E (E →L[ℝ] (E →L[ℝ] E)))
    (e : E) (M : ℝ) (hM : ∀ y, ‖D3f y‖ ≤ M) (y : E) :
    rieszD3DirectionBCF D3f e M hM y = D3f y e := rfl

theorem euclidean_eq_sum_smul_unit
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : EuclideanSpace ℝ ι) :
    v = ∑ i, v i • euclideanUnit i := by
  apply WithLp.ofLp_injective 2
  ext j
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, euclideanUnit,
    Finset.sum_apply]
  symm
  calc
    ∑ i, v i * ((Pi.single i (1 : ℝ) : ι → ℝ) j) =
        ∑ i, ((Pi.single i (v i) : ι → ℝ) j) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : j = i <;> simp [h]
    _ = v j := Fintype.sum_pi_single j (fun i => v i)

@[simp] theorem inner_euclideanUnit_right
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : EuclideanSpace ℝ ι) (j : ι) :
    inner ℝ v (euclideanUnit j) = v j := by
  simpa [euclideanUnit] using
    (EuclideanSpace.inner_single_right (𝕜 := ℝ) j (1 : ℝ) v)

theorem continuousLinearMap_apply_eq_sum_euclidean
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : EuclideanSpace ℝ ι →L[ℝ] F) (v : EuclideanSpace ℝ ι) :
    L v = ∑ i, v i • L (euclideanUnit i) := by
  rw [euclidean_eq_sum_smul_unit v, map_sum]
  simp

/-- The vector of diagonal third spatial derivatives of the transported
Riesz gradient. -/
def backwardGaussianOULaplacianGradient
    {n : ℕ} (t s : ℝ)
    (D3f : BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
        (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
          EuclideanSpace ℝ (Fin (n + 1)))))
    (M : ℝ) (hM : ∀ y, ‖D3f y‖ ≤ M)
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun j => ∑ i, inner ℝ
    (backwardGaussianOURieszHessianDirectionalDerivBCF
      t s D3f (euclideanUnit i) M hM x (euclideanUnit i))
    (euclideanUnit j))

theorem backwardGaussianOURieszGradientTimeDeriv_eq_neg_generator
    {n : ℕ}
    (t s : ℝ) (hst : s < t)
    (Gf : BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1))))
    (Hf : BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
        EuclideanSpace ℝ (Fin (n + 1))))
    (D3f : BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
        (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
          EuclideanSpace ℝ (Fin (n + 1)))))
    (M : ℝ) (hM : ∀ y, ‖D3f y‖ ≤ M)
    (hD3f : ∀ y, HasFDerivAt Hf (D3f y) y)
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    backwardGaussianOURieszGradientTimeDeriv t s Gf Hf x =
      -backwardGaussianOULaplacianGradient t s D3f M hM x +
        backwardGaussianOURieszGradientBCF t s Gf x +
        ∑ i, x i •
          backwardGaussianOURieszHessianBCF t s Hf x (euclideanUnit i) := by
  let G := EuclideanSpace ℝ (Fin (n + 1))
  let τ := t - s
  let a := ouDriftCoeff τ
  let b := ouNoiseCoeff τ
  let q1 : Fin (n + 1) → Fin (n + 1) →
      BoundedContinuousFunction G ℝ := fun i j =>
    boundedContinuousInnerRight
      (boundedContinuousApply Hf (euclideanUnit i)) (euclideanUnit j)
  let q2 : Fin (n + 1) → Fin (n + 1) →
      BoundedContinuousFunction G ℝ := fun i j =>
    boundedContinuousInnerRight
      (boundedContinuousApply
        (rieszD3DirectionBCF D3f (euclideanUnit i) M hM)
        (euclideanUnit i)) (euclideanUnit j)
  have hτ : 0 < τ := sub_pos.2 hst
  have ha : 0 < a := ouDriftCoeff_pos τ
  have hb : 0 < b := by
    dsimp only [b, ouNoiseCoeff]
    exact Real.sqrt_pos.2 (bobkovVarianceCoeff_pos hτ)
  have hHint : Integrable
      (fun z : G => Hf (gaussianOUTransition τ x z)) (stdGaussian G) := by
    refine Integrable.of_bound
      (Hf.continuous.comp (by
        unfold gaussianOUTransition
        fun_prop)).aestronglyMeasurable ‖Hf‖ ?_
    exact Filter.Eventually.of_forall fun z => Hf.norm_coe_le_norm _
  have hqint (q : BoundedContinuousFunction G ℝ) : Integrable
      (fun z : G => q (gaussianOUTransition τ x z)) (stdGaussian G) := by
    refine Integrable.of_bound
      (q.continuous.comp (by
        unfold gaussianOUTransition
        fun_prop)).aestronglyMeasurable ‖q‖ ?_
    exact Filter.Eventually.of_forall fun z => q.norm_coe_le_norm _
  have hq1int (i j : Fin (n + 1)) : Integrable
      (fun z : G => q1 i j (gaussianOUTransition τ x z))
      (stdGaussian G) := hqint (q1 i j)
  have hq2int (i j : Fin (n + 1)) : Integrable
      (fun z : G => q2 i j (gaussianOUTransition τ x z))
      (stdGaussian G) := hqint (q2 i j)
  have hzq1int (i j : Fin (n + 1)) : Integrable
      (fun z : G => z i * q1 i j (gaussianOUTransition τ x z))
      (stdGaussian G) := by
    have hnorm : Integrable (fun z : G => ‖z‖) (stdGaussian G) :=
      IsGaussian.integrable_id.norm
    refine (hnorm.const_mul ‖q1 i j‖).mono'
      ((EuclideanSpace.proj i).continuous.mul
        ((q1 i j).continuous.comp (by
          unfold gaussianOUTransition
          fun_prop))).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |z i| * |q1 i j (gaussianOUTransition τ x z)| ≤
            ‖z‖ * ‖q1 i j‖ := by
          gcongr
          · simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z i
          · simpa [Real.norm_eq_abs] using (q1 i j).norm_coe_le_norm _
        _ = ‖q1 i j‖ * ‖z‖ := mul_comm _ _
  have hibp (i j : Fin (n + 1)) :
      ∫ z : G, z i * q1 i j (gaussianOUTransition τ x z) ∂stdGaussian G =
        b * ∫ z : G, q2 i j (gaussianOUTransition τ x z) ∂stdGaussian G := by
    apply integral_coordinate_mul_transition_eq (q1 i j) (q2 i j) x i
    intro w r
    simpa [q1, q2] using
      hasDerivAt_rieszHessianCoordinate_transition
        Hf D3f hD3f τ x i j w r
  have hHcoord (i j : Fin (n + 1)) :
      inner ℝ (backwardGaussianOURieszHessianBCF t s Hf x
          (euclideanUnit i)) (euclideanUnit j) =
        a ^ 2 * ∫ z : G, q1 i j (gaussianOUTransition τ x z)
          ∂stdGaussian G := by
    rw [backwardGaussianOURieszHessianBCF_apply]
    rw [smul_apply, real_inner_smul_left]
    change a ^ 2 * inner ℝ
        ((∫ z : G, Hf (gaussianOUTransition τ x z) ∂stdGaussian G)
          (euclideanUnit i)) (euclideanUnit j) =
      a ^ 2 * ∫ z : G, q1 i j (gaussianOUTransition τ x z)
        ∂stdGaussian G
    congr 1
    rw [ContinuousLinearMap.integral_apply hHint]
    have hHe :=
      ((ContinuousLinearMap.apply ℝ G) (euclideanUnit i)).integrable_comp hHint
    calc
      inner ℝ
          (∫ z : G, Hf (gaussianOUTransition τ x z) (euclideanUnit i)
            ∂stdGaussian G) (euclideanUnit j) =
          inner ℝ (euclideanUnit j)
            (∫ z : G, Hf (gaussianOUTransition τ x z) (euclideanUnit i)
              ∂stdGaussian G) := real_inner_comm _ _
      _ = ∫ z : G, inner ℝ (euclideanUnit j)
          (Hf (gaussianOUTransition τ x z) (euclideanUnit i))
          ∂stdGaussian G := by
        simpa using
          ((innerSL ℝ (euclideanUnit j)).integral_comp_comm hHe).symm
      _ = ∫ z : G, q1 i j (gaussianOUTransition τ x z)
          ∂stdGaussian G := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by
          simp [q1, real_inner_comm]
  have hKcoord (i j : Fin (n + 1)) :
      inner ℝ
          (backwardGaussianOURieszHessianDirectionalDerivBCF
            t s D3f (euclideanUnit i) M hM x (euclideanUnit i))
          (euclideanUnit j) =
        a ^ 3 * ∫ z : G, q2 i j (gaussianOUTransition τ x z)
          ∂stdGaussian G := by
    let De := rieszD3DirectionBCF D3f (euclideanUnit i) M hM
    have hDeint : Integrable
        (fun z : G => De (gaussianOUTransition τ x z))
        (stdGaussian G) := by
      refine Integrable.of_bound
        (De.continuous.comp (by
          unfold gaussianOUTransition
          fun_prop)).aestronglyMeasurable ‖De‖ ?_
      exact Filter.Eventually.of_forall fun z => De.norm_coe_le_norm _
    change inner ℝ
        (((a ^ 3) •
          (∫ z : G, De (gaussianOUTransition τ x z) ∂stdGaussian G))
          (euclideanUnit i)) (euclideanUnit j) = _
    rw [smul_apply, real_inner_smul_left]
    congr 1
    rw [ContinuousLinearMap.integral_apply hDeint]
    have hDee :=
      ((ContinuousLinearMap.apply ℝ G) (euclideanUnit i)).integrable_comp hDeint
    calc
      inner ℝ
          (∫ z : G, De (gaussianOUTransition τ x z) (euclideanUnit i)
            ∂stdGaussian G) (euclideanUnit j) =
          inner ℝ (euclideanUnit j)
            (∫ z : G, De (gaussianOUTransition τ x z) (euclideanUnit i)
              ∂stdGaussian G) := real_inner_comm _ _
      _ = ∫ z : G, inner ℝ (euclideanUnit j)
          (De (gaussianOUTransition τ x z) (euclideanUnit i))
          ∂stdGaussian G := by
        simpa using
          ((innerSL ℝ (euclideanUnit j)).integral_comp_comm hDee).symm
      _ = ∫ z : G, q2 i j (gaussianOUTransition τ x z)
          ∂stdGaussian G := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by
          simp [q2, De, real_inner_comm]
  have hdirectPoint (j : Fin (n + 1)) (z : G) :
      inner ℝ
          (Hf (gaussianOUTransition τ x z)
            (gaussianOUTransitionTimeDeriv τ x z))
          (euclideanUnit j) =
        ∑ i, ((-a * x i) * q1 i j (gaussianOUTransition τ x z) +
          (a ^ 2 / b) *
            (z i * q1 i j (gaussianOUTransition τ x z))) := by
    rw [continuousLinearMap_apply_eq_sum_euclidean
      (Hf (gaussianOUTransition τ x z))
      (gaussianOUTransitionTimeDeriv τ x z)]
    rw [sum_inner]
    simp only [real_inner_smul_left]
    apply Finset.sum_congr rfl
    intro i _
    simp only [gaussianOUTransitionTimeDeriv, a, b, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul]
    change ((-a * x i + a ^ 2 / b * z i) *
        inner ℝ (Hf (gaussianOUTransition τ x z) (euclideanUnit i))
          (euclideanUnit j)) = _
    simp only [q1, boundedContinuousInnerRight_apply,
      boundedContinuousApply_apply]
    ring
  have hcoord (i j : Fin (n + 1)) :
      a * ∫ z : G,
          ((-a * x i) * q1 i j (gaussianOUTransition τ x z) +
            (a ^ 2 / b) *
              (z i * q1 i j (gaussianOUTransition τ x z)))
          ∂stdGaussian G =
        inner ℝ
          (backwardGaussianOURieszHessianDirectionalDerivBCF
            t s D3f (euclideanUnit i) M hM x (euclideanUnit i))
          (euclideanUnit j) -
        x i * inner ℝ
          (backwardGaussianOURieszHessianBCF t s Hf x (euclideanUnit i))
          (euclideanUnit j) := by
    rw [integral_add
      ((hq1int i j).const_mul (-a * x i))
      ((hzq1int i j).const_mul (a ^ 2 / b)),
      integral_const_mul, integral_const_mul, hibp i j,
      hHcoord i j, hKcoord i j]
    field_simp [hb.ne']
    ring
  have hvelnorm (z : G) :
      ‖gaussianOUTransitionTimeDeriv τ x z‖ ≤
        a * ‖x‖ + (a ^ 2 / b) * ‖z‖ := by
    unfold gaussianOUTransitionTimeDeriv
    calc
      ‖(-a) • x + (a ^ 2 / b) • z‖ ≤
          ‖(-a) • x‖ + ‖(a ^ 2 / b) • z‖ := norm_add_le _ _
      _ = a * ‖x‖ + (a ^ 2 / b) * ‖z‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_neg, abs_of_pos ha, abs_of_pos (div_pos (sq_pos_of_pos ha) hb)]
  have hrawInt : Integrable
      (fun z : G => Hf (gaussianOUTransition τ x z)
        (gaussianOUTransitionTimeDeriv τ x z)) (stdGaussian G) := by
    have hnorm : Integrable (fun z : G => ‖z‖) (stdGaussian G) :=
      IsGaussian.integrable_id.norm
    have hbound : Integrable
        (fun z : G => ‖Hf‖ * (a * ‖x‖ + (a ^ 2 / b) * ‖z‖))
        (stdGaussian G) :=
      ((integrable_const (a * ‖x‖)).add
        (hnorm.const_mul (a ^ 2 / b))).const_mul ‖Hf‖
    refine hbound.mono'
      (show AEStronglyMeasurable
        (fun z : G => Hf (gaussianOUTransition τ x z)
          (gaussianOUTransitionTimeDeriv τ x z)) (stdGaussian G) by
        exact (show Continuous
          (fun z : G => Hf (gaussianOUTransition τ x z)
            (gaussianOUTransitionTimeDeriv τ x z)) by
          unfold gaussianOUTransition gaussianOUTransitionTimeDeriv
          fun_prop).aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall fun z => by
      calc
        ‖Hf (gaussianOUTransition τ x z)
            (gaussianOUTransitionTimeDeriv τ x z)‖ ≤
            ‖Hf (gaussianOUTransition τ x z)‖ *
              ‖gaussianOUTransitionTimeDeriv τ x z‖ :=
          (Hf (gaussianOUTransition τ x z)).le_opNorm _
        _ ≤ ‖Hf‖ * (a * ‖x‖ + (a ^ 2 / b) * ‖z‖) := by
          gcongr
          exact Hf.norm_coe_le_norm _
          exact hvelnorm z
  have hrawCoord (j : Fin (n + 1)) :
      a * inner ℝ
          (∫ z : G, Hf (gaussianOUTransition τ x z)
            (gaussianOUTransitionTimeDeriv τ x z) ∂stdGaussian G)
          (euclideanUnit j) =
        ∑ i, (inner ℝ
            (backwardGaussianOURieszHessianDirectionalDerivBCF
              t s D3f (euclideanUnit i) M hM x (euclideanUnit i))
            (euclideanUnit j) -
          x i * inner ℝ
            (backwardGaussianOURieszHessianBCF t s Hf x (euclideanUnit i))
            (euclideanUnit j)) := by
    have hinnerInt :
        inner ℝ
            (∫ z : G, Hf (gaussianOUTransition τ x z)
              (gaussianOUTransitionTimeDeriv τ x z) ∂stdGaussian G)
            (euclideanUnit j) =
          ∫ z : G, inner ℝ
            (Hf (gaussianOUTransition τ x z)
              (gaussianOUTransitionTimeDeriv τ x z))
            (euclideanUnit j) ∂stdGaussian G := by
      calc
        inner ℝ
            (∫ z : G, Hf (gaussianOUTransition τ x z)
              (gaussianOUTransitionTimeDeriv τ x z) ∂stdGaussian G)
            (euclideanUnit j) =
            inner ℝ (euclideanUnit j)
              (∫ z : G, Hf (gaussianOUTransition τ x z)
                (gaussianOUTransitionTimeDeriv τ x z) ∂stdGaussian G) :=
          real_inner_comm _ _
        _ = ∫ z : G, inner ℝ (euclideanUnit j)
            (Hf (gaussianOUTransition τ x z)
              (gaussianOUTransitionTimeDeriv τ x z))
            ∂stdGaussian G := by
          simpa using
            ((innerSL ℝ (euclideanUnit j)).integral_comp_comm hrawInt).symm
        _ = ∫ z : G, inner ℝ
            (Hf (gaussianOUTransition τ x z)
              (gaussianOUTransitionTimeDeriv τ x z))
            (euclideanUnit j) ∂stdGaussian G := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun z => real_inner_comm _ _
    rw [hinnerInt]
    rw [integral_congr_ae (Filter.Eventually.of_forall (hdirectPoint j))]
    rw [integral_finsetSum]
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => hcoord i j
    · intro i _
      exact ((hq1int i j).const_mul (-a * x i)).add
        ((hzq1int i j).const_mul (a ^ 2 / b))
  ext j
  rw [← inner_euclideanUnit_right
    (backwardGaussianOURieszGradientTimeDeriv t s Gf Hf x) j]
  rw [← inner_euclideanUnit_right
    (-backwardGaussianOULaplacianGradient t s D3f M hM x +
      backwardGaussianOURieszGradientBCF t s Gf x +
      ∑ i, x i •
        backwardGaussianOURieszHessianBCF t s Hf x (euclideanUnit i)) j]
  have htimeCoord :
      inner ℝ (backwardGaussianOURieszGradientTimeDeriv t s Gf Hf x)
          (euclideanUnit j) =
        inner ℝ (backwardGaussianOURieszGradientBCF t s Gf x)
          (euclideanUnit j) -
        a * inner ℝ
          (∫ z : EuclideanSpace ℝ (Fin (n + 1)),
            Hf (gaussianOUTransition τ x z)
              (gaussianOUTransitionTimeDeriv τ x z)
            ∂stdGaussian (EuclideanSpace ℝ (Fin (n + 1))))
          (euclideanUnit j) := by
    rw [backwardGaussianOURieszGradientBCF_apply]
    simp only [backwardGaussianOURieszGradientTimeDeriv, inner_sub_left,
      real_inner_smul_left, a, τ, gaussianOUAverage]
  rw [htimeCoord]
  have hrawCoord' := hrawCoord j
  dsimp only [G] at hrawCoord'
  rw [hrawCoord']
  simp only [inner_add_left, inner_neg_left, sum_inner,
    real_inner_smul_left, backwardGaussianOULaplacianGradient,
    inner_euclideanUnit_right]
  rw [Finset.sum_sub_distrib]
  ring

end
end UniformRandomMALA.Concrete

