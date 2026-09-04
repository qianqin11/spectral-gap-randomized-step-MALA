import UniformRandomMALA.Concrete.GaussianOUHigherFields

/-!
# Coordinate fields for the Gaussian OU generator

This module turns bounded covector and bilinear fields on finite-dimensional
Euclidean space into their scalar coordinate fields.  Its main result proves
the coordinate-line derivative after a Gaussian OU transition in precisely
the `Fin.insertNth` form used by the generator-coordinate integration theorem.
-/

namespace UniformRandomMALA.Concrete

open Function Set Metric MeasureTheory Filter ContinuousLinearMap ProbabilityTheory
open scoped Topology NNReal ENNReal ProbabilityTheory BigOperators

noncomputable section

variable {ι : Type*} [DecidableEq ι]

local notation "E" => EuclideanSpace ℝ ι

def euclideanUnit (i : ι) : E := EuclideanSpace.single i 1

@[simp] theorem euclideanUnit_apply (i j : ι) :
    euclideanUnit i j = if i = j then 1 else 0 := by
  simp only [euclideanUnit, PiLp.single_apply]
  by_cases h : i = j
  · subst j
    simp
  · have h' : j ≠ i := fun hji => h hji.symm
    simp [h, h']

variable [Fintype ι]

@[simp] theorem norm_euclideanUnit (i : ι) : ‖euclideanUnit i‖ = 1 := by
  simp [euclideanUnit]

def covectorCoordinateBCF
    (Dq : BoundedContinuousFunction E (E →L[ℝ] ℝ)) (i : ι) :
    BoundedContinuousFunction E ℝ :=
  ((ContinuousLinearMap.apply ℝ ℝ) (euclideanUnit i))
    |>.compLeftContinuousBounded E Dq

@[simp] theorem covectorCoordinateBCF_apply
    (Dq : BoundedContinuousFunction E (E →L[ℝ] ℝ)) (i : ι) (y : E) :
    covectorCoordinateBCF Dq i y = Dq y (euclideanUnit i) := rfl

def bilinearDiagonalBCF
    (D2q : BoundedContinuousFunction E (E →L[ℝ] (E →L[ℝ] ℝ)))
    (i : ι) (M : ℝ) (hM : ∀ y, ‖D2q y‖ ≤ M) :
    BoundedContinuousFunction E ℝ :=
  let e := euclideanUnit i
  let L1 := (ContinuousLinearMap.apply ℝ ℝ) e
  let L2 := (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ)) e
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun y => D2q y e e)
    ((L1.comp L2).continuous.comp D2q.continuous)
    M (fun y => by
      calc
        ‖D2q y e e‖ ≤ ‖D2q y e‖ * ‖e‖ := (D2q y e).le_opNorm e
        _ ≤ (‖D2q y‖ * ‖e‖) * ‖e‖ := by
          gcongr
          exact (D2q y).le_opNorm e
        _ = ‖D2q y‖ := by simp [e]
        _ ≤ M := hM y)

@[simp] theorem bilinearDiagonalBCF_apply
    (D2q : BoundedContinuousFunction E (E →L[ℝ] (E →L[ℝ] ℝ)))
    (i : ι) (M : ℝ) (hM : ∀ y, ‖D2q y‖ ≤ M) (y : E) :
    bilinearDiagonalBCF D2q i M hM y =
      D2q y (euclideanUnit i) (euclideanUnit i) := rfl

theorem covector_eq_sum_coordinates
    (Dq : BoundedContinuousFunction E (E →L[ℝ] ℝ)) (y v : E) :
    Dq y v = ∑ i, covectorCoordinateBCF Dq i y * v i := by
  have hv : v = ∑ i, v i • euclideanUnit i := by
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
  rw [hv, map_sum]
  simp [mul_comm]

theorem hasFDerivAt_covectorCoordinateBCF
    (Dq : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (D2q : BoundedContinuousFunction E (E →L[ℝ] (E →L[ℝ] ℝ)))
    (hD2q : ∀ y, HasFDerivAt Dq (D2q y) y) (i : ι) (y : E) :
    HasFDerivAt (covectorCoordinateBCF Dq i)
      (((ContinuousLinearMap.apply ℝ ℝ) (euclideanUnit i)).comp (D2q y)) y := by
  exact ((ContinuousLinearMap.apply ℝ ℝ) (euclideanUnit i)).hasFDerivAt.comp y
    (hD2q y)

theorem insertNth_toLp_eq_affine
    {n : ℕ} (i : Fin (n + 1)) (w : Fin n → ℝ) (u : ℝ) :
    WithLp.toLp 2 (i.insertNth u w) =
      WithLp.toLp 2 (i.insertNth 0 w) +
        u • euclideanUnit i := by
  apply congrArg (WithLp.toLp 2)
  apply (Fin.insertNth_eq_iff).2
  constructor
  · simp [euclideanUnit]
  · ext j
    simp [euclideanUnit, Fin.removeNth]

theorem hasDerivAt_covectorCoordinate_transition
    {n : ℕ}
    (Dq : BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ))
    (D2q : BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
        (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)))
    (M : ℝ) (hM : ∀ y, ‖D2q y‖ ≤ M)
    (hD2q : ∀ y, HasFDerivAt Dq (D2q y) y)
    (s : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1)))
    (i : Fin (n + 1)) (w : Fin n → ℝ) (r : ℝ) :
    HasDerivAt
      (fun u => covectorCoordinateBCF Dq i
        (gaussianOUTransition s x (WithLp.toLp 2 (i.insertNth u w))))
      (ouNoiseCoeff s * bilinearDiagonalBCF D2q i M hM
        (gaussianOUTransition s x (WithLp.toLp 2 (i.insertNth r w)))) r := by
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
  have hc := (hasFDerivAt_covectorCoordinateBCF Dq D2q hD2q i _)
    |>.comp_hasDerivAt r hcurve'
  change HasDerivAt
    ((⇑(covectorCoordinateBCF Dq i)) ∘
      fun u => gaussianOUTransition s x (WithLp.toLp 2 (i.insertNth u w)))
    (ouNoiseCoeff s * D2q
      (gaussianOUTransition s x (WithLp.toLp 2 (i.insertNth r w)))
        (euclideanUnit i) (euclideanUnit i)) r
  simpa [c, smul_eq_mul, smul_smul] using hc

/-- Coordinate Gaussian integration by parts after a Mehler transition.
This is the reusable scalar core of the generator-coordinate proof. -/
theorem integral_coordinate_mul_transition_eq
    {n : ℕ} {t : ℝ}
    (q1 q2 : BoundedContinuousFunction
      (EuclideanSpace ℝ (Fin (n + 1))) ℝ)
    (x : EuclideanSpace ℝ (Fin (n + 1)))
    (i : Fin (n + 1))
    (hq12 : ∀ (w : Fin n → ℝ) (r : ℝ),
      HasDerivAt
        (fun u => q1 (gaussianOUTransition t x
          (WithLp.toLp 2 (i.insertNth u w))))
        (ouNoiseCoeff t * q2 (gaussianOUTransition t x
          (WithLp.toLp 2 (i.insertNth r w)))) r) :
    ∫ z, z i * q1 (gaussianOUTransition t x z)
        ∂stdGaussian (EuclideanSpace ℝ (Fin (n + 1))) =
      ouNoiseCoeff t * ∫ z, q2 (gaussianOUTransition t x z)
        ∂stdGaussian (EuclideanSpace ℝ (Fin (n + 1))) := by
  let G := EuclideanSpace ℝ (Fin (n + 1))
  let b := ouNoiseCoeff t
  have hq1int : Integrable
      (fun z : G => q1 (gaussianOUTransition t x z)) (stdGaussian G) := by
    refine Integrable.of_bound
      (q1.continuous.comp (by
        unfold gaussianOUTransition
        fun_prop)).aestronglyMeasurable ‖q1‖ ?_
    exact Filter.Eventually.of_forall fun z => q1.norm_coe_le_norm _
  have hq2int : Integrable
      (fun z : G => q2 (gaussianOUTransition t x z)) (stdGaussian G) := by
    refine Integrable.of_bound
      (q2.continuous.comp (by
        unfold gaussianOUTransition
        fun_prop)).aestronglyMeasurable ‖q2‖ ?_
    exact Filter.Eventually.of_forall fun z => q2.norm_coe_le_norm _
  have hzq1int : Integrable
      (fun z : G => z i * q1 (gaussianOUTransition t x z))
      (stdGaussian G) := by
    have hnorm : Integrable (fun z : G => ‖z‖) (stdGaussian G) :=
      IsGaussian.integrable_id.norm
    refine (hnorm.const_mul ‖q1‖).mono'
      ((EuclideanSpace.proj i).continuous.mul
        (q1.continuous.comp (by
          unfold gaussianOUTransition
          fun_prop))).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |z i| * |q1 (gaussianOUTransition t x z)| ≤ ‖z‖ * ‖q1‖ := by
          gcongr
          · simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z i
          · simpa [Real.norm_eq_abs] using q1.norm_coe_le_norm
              (gaussianOUTransition t x z)
        _ = ‖q1‖ * ‖z‖ := mul_comm _ _
  have hraw := integral_partial_stdGaussian_eq_integral_mul i
    (g := fun z : G => q1 (gaussianOUTransition t x z))
    (gi := fun z : G => b * q2 (gaussianOUTransition t x z))
    (by
      intro w r
      have h := hq12 w r
      simpa [G, b, gaussianOUTransition, add_comm, add_left_comm,
        add_assoc] using h)
    (hq2int.const_mul b) hzq1int hq1int
  rw [integral_const_mul] at hraw
  simpa [b] using hraw.symm

end
end UniformRandomMALA.Concrete
