import UniformRandomMALA.Concrete.GaussianOUBackwardPDE

/-!
# Canonical Gaussian OU Bobkov residual

This module combines the backward value and Riesz-gradient Kolmogorov
equations with the diagonal spatial calculus.  The resulting pointwise
time-plus-generator expression is identified exactly with the explicit
nonnegative Bobkov square-root residual.
-/

namespace UniformRandomMALA.Concrete

open Function Set Metric MeasureTheory Filter ContinuousLinearMap ProbabilityTheory
open scoped Topology NNReal ENNReal ProbabilityTheory BigOperators

noncomputable section

/-- The G3 square-root residual bundled as a bounded continuous field.
All factors are bounded: the reciprocal radius is controlled by the
positive normal-profile component, and the remaining factors are bounded
transported gradient and Hessian fields. -/
def bobkovSqrtResidualBCF
    {n : Type*} [Fintype n] [DecidableEq n]
    (c : ℝ) (hc : 0 ≤ c)
    (u : BoundedContinuousFunction (EuclideanSpace ℝ n) ℝ)
    (v : BoundedContinuousFunction (EuclideanSpace ℝ n)
      (EuclideanSpace ℝ n))
    (H : BoundedContinuousFunction (EuclideanSpace ℝ n)
      (EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n))
    (ε : ℝ) (hε : 0 < ε) (hu : ∀ x, u x ∈ Icc ε (1 - ε)) :
    BoundedContinuousFunction (EuclideanSpace ℝ n) ℝ :=
  let I := normalProfileCompBCF u ε hε hu
  let Ip := normalProfileDerivCompBCF u ε hε hu
  let Rinv := bobkovInvRadiusBCF c hc u v ε hε hu
  let He : n → BoundedContinuousFunction (EuclideanSpace ℝ n)
      (EuclideanSpace ℝ n) := fun i => boundedContinuousApply H (euclideanUnit i)
  let N : n → BoundedContinuousFunction (EuclideanSpace ℝ n) ℝ := fun i =>
    I * Ip * boundedContinuousInnerRight v (euclideanUnit i) +
      c • boundedContinuousInner v (He i)
  (2 • (Ip ^ 2 * v.normComp ^ 2 + c • ∑ i, (He i).normComp ^ 2)) *
      ((2 : ℝ)⁻¹ • Rinv) -
    (∑ i, (2 • N i) ^ 2) * ((4 : ℝ)⁻¹ • Rinv ^ 3)

@[simp] theorem bobkovSqrtResidualBCF_apply
    {n : Type*} [Fintype n] [DecidableEq n]
    (c : ℝ) (hc : 0 ≤ c)
    (u : BoundedContinuousFunction (EuclideanSpace ℝ n) ℝ)
    (v : BoundedContinuousFunction (EuclideanSpace ℝ n)
      (EuclideanSpace ℝ n))
    (H : BoundedContinuousFunction (EuclideanSpace ℝ n)
      (EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n))
    (ε : ℝ) (hε : 0 < ε) (hu : ∀ x, u x ∈ Icc ε (1 - ε))
    (x : EuclideanSpace ℝ n) :
    bobkovSqrtResidualBCF c hc u v H ε hε hu x =
      bobkovSqrtResidual c (normalProfile (u x))
        (deriv normalProfile (u x)) (v x)
        (fun i => H x (euclideanUnit i)) := by
  simp [bobkovSqrtResidualBCF, bobkovSqrtResidual, div_eq_mul_inv]
  ring

/-- The canonical residual field at a fixed interpolation time. -/
def canonicalGaussianBobkovResidualBCF
    {n : Type*} [Fintype n] [DecidableEq n]
    (t s : ℝ)
    (f : BoundedContinuousFunction (EuclideanSpace ℝ n) ℝ)
    (Df : BoundedContinuousFunction (EuclideanSpace ℝ n)
      (EuclideanSpace ℝ n →L[ℝ] ℝ))
    (Hf : BoundedContinuousFunction (EuclideanSpace ℝ n)
      (EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n))
    (ε : ℝ) (hε : 0 < ε) (hf : ∀ x, f x ∈ Icc ε (1 - ε))
    (hs : 0 ≤ s) :
    BoundedContinuousFunction (EuclideanSpace ℝ n) ℝ :=
  bobkovSqrtResidualBCF (bobkovVarianceCoeff s)
    (bobkovVarianceCoeff_nonneg hs)
    (backwardGaussianOUValueBCF t s f)
    (rieszGradientBCF (backwardGaussianOUDerivBCF t s Df))
    (backwardGaussianOURieszHessianBCF t s Hf)
    ε hε (backwardGaussianOUValueBCF_mem_Icc t s f hf)

@[simp] theorem canonicalGaussianBobkovResidualBCF_apply
    {n : Type*} [Fintype n] [DecidableEq n]
    (t s : ℝ)
    (f : BoundedContinuousFunction (EuclideanSpace ℝ n) ℝ)
    (Df : BoundedContinuousFunction (EuclideanSpace ℝ n)
      (EuclideanSpace ℝ n →L[ℝ] ℝ))
    (Hf : BoundedContinuousFunction (EuclideanSpace ℝ n)
      (EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n))
    (ε : ℝ) (hε : 0 < ε) (hf : ∀ x, f x ∈ Icc ε (1 - ε))
    (hs : 0 ≤ s) (x : EuclideanSpace ℝ n) :
    canonicalGaussianBobkovResidualBCF t s f Df Hf ε hε hf hs x =
      bobkovSqrtResidual (bobkovVarianceCoeff s)
        (normalProfile (backwardGaussianOUValueBCF t s f x))
        (deriv normalProfile (backwardGaussianOUValueBCF t s f x))
        (rieszGradientBCF (backwardGaussianOUDerivBCF t s Df) x)
        (fun i => backwardGaussianOURieszHessianBCF
          t s Hf x (euclideanUnit i)) := by
  exact bobkovSqrtResidualBCF_apply
    (bobkovVarianceCoeff s) (bobkovVarianceCoeff_nonneg hs)
    (backwardGaussianOUValueBCF t s f)
    (rieszGradientBCF (backwardGaussianOUDerivBCF t s Df))
    (backwardGaussianOURieszHessianBCF t s Hf)
    ε hε (backwardGaussianOUValueBCF_mem_Icc t s f hf) x

theorem bobkovQ_time_add_generator_eq_residual_of_PDE
    {n : Type*} [Fintype n] [DecidableEq n]
    (x v lapGrad : EuclideanSpace ℝ n)
    (H : n → EuclideanSpace ℝ n)
    (u I Ip c : ℝ)
    (hI : I = normalProfile u)
    (hIp : Ip = deriv normalProfile u)
    (hu : u ∈ Ioo (0 : ℝ) 1)
    (hc : 0 ≤ c) :
    let Lu : ℝ := ∑ i, (inner ℝ (H i) (euclideanUnit i) - x i * v i)
    let us : ℝ := -Lu
    let vs : EuclideanSpace ℝ n :=
      -lapGrad + v + ∑ i, x i • H i
    let Qt : ℝ :=
      (2 * I * Ip * us + 2 * (1 - c) * ‖v‖ ^ 2 +
          2 * c * ∑ j, v j * vs j) /
        (2 * Real.sqrt (I ^ 2 + c * ‖v‖ ^ 2))
    let LQ : ℝ :=
      ((Ip ^ 2 - 1) * ‖v‖ ^ 2 +
          I * Ip * ∑ i, H i i +
          c * (∑ i, ‖H i‖ ^ 2 + ∑ j, v j * lapGrad j) -
          ∑ i, x i * (I * Ip * v i + c * ∑ j, v j * H i j)) /
        Real.sqrt (I ^ 2 + c * ‖v‖ ^ 2) -
      (∑ i, (I * Ip * v i + c * ∑ j, v j * H i j) ^ 2) /
        (Real.sqrt (I ^ 2 + c * ‖v‖ ^ 2)) ^ 3
    Qt + LQ = bobkovSqrtResidual c I Ip v H := by
  dsimp only
  have hprofile : I * deriv (deriv normalProfile) u = -1 := by
    rw [hI]
    exact normalProfile_mul_secondDeriv hu
  have hrad : 0 < I ^ 2 + c * ‖v‖ ^ 2 := by
    have hIpos : 0 < I := by rw [hI]; exact normalProfile_pos hu
    nlinarith [mul_nonneg hc (sq_nonneg ‖v‖)]
  have hR : 0 < Real.sqrt (I ^ 2 + c * ‖v‖ ^ 2) :=
    Real.sqrt_pos.2 hrad
  have hinnerCoords (w : EuclideanSpace ℝ n) :
      inner ℝ v w = ∑ j, v j * w j := by
    simpa [PiLp.inner_apply, mul_comm]
  have hsumCoord (j : n) :
      (∑ i, x i • H i) j = ∑ i, x i * H i j := by
    simp
  have hradicand := bobkov_canonical_radicand_residual_identity
    x v lapGrad H I Ip (deriv (deriv normalProfile) u) c (2 * (1 - c))
      (by simpa [hIp] using hprofile) rfl
  dsimp only at hradicand
  rw [hprofile] at hradicand
  have htime :
      (∑ j, v j * (-lapGrad j + v j + ∑ i, x i * H i j)) =
        -(∑ j, v j * lapGrad j) + ∑ j, (v j) ^ 2 +
          ∑ i, x i * (∑ j, v j * H i j) := by
    simp_rw [mul_add, mul_neg, Finset.sum_add_distrib,
      Finset.sum_neg_distrib]
    rw [bobkov_cross_sum_comm (fun i => x i) (fun j => v j)
      (fun i j => H i j)]
    ring
  rw [htime, ← EuclideanSpace.real_norm_sq_eq v] at hradicand
  have hsumN :
      (∑ i, x i * (I * Ip * v i + c * ∑ j, v j * H i j)) =
        I * Ip * ∑ i, x i * v i +
          c * ∑ i, x i * (∑ j, v j * H i j) := by
    calc
      ∑ i, x i * (I * Ip * v i + c * ∑ j, v j * H i j) =
          ∑ i, (I * Ip * (x i * v i) +
            c * (x i * ∑ j, v j * H i j)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, I * Ip * (x i * v i)) +
          ∑ i, c * (x i * ∑ j, v j * H i j) :=
        Finset.sum_add_distrib
      _ = _ := by rw [← Finset.mul_sum, ← Finset.mul_sum]
  unfold bobkovSqrtResidual
  simp_rw [inner_euclideanUnit_right, hinnerCoords]
  simp only [PiLp.add_apply, PiLp.neg_apply]
  simp_rw [hsumCoord]
  rw [htime, hsumN, ← EuclideanSpace.real_norm_sq_eq v]
  field_simp [hR.ne']
  rw [← Finset.mul_sum]
  norm_num
  linear_combination
    Real.sqrt (I ^ 2 + c * ‖v‖ ^ 2) ^ 2 * hradicand

theorem sum_bobkovSpatial_diagonal_generator_eq_aggregated
    {n : Type*} [Fintype n] [DecidableEq n]
    (x v lapGrad : EuclideanSpace ℝ n)
    (H : n → EuclideanSpace ℝ n)
    (Ke : n → EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n)
    (c u : ℝ)
    (hlap : ∀ j, lapGrad j = ∑ i, inner ℝ (Ke i (euclideanUnit i))
      (euclideanUnit j)) :
    ∑ i, (bobkovSpatialHessianDiagonal c u v (H i) (Ke i)
          (euclideanUnit i) -
        x i * bobkovSpatialGradientCoordinate c u v (H i)
          (euclideanUnit i)) =
      let I := normalProfile u
      let Ip := deriv normalProfile u
      ((Ip ^ 2 - 1) * ‖v‖ ^ 2 +
          I * Ip * ∑ i, H i i +
          c * (∑ i, ‖H i‖ ^ 2 + ∑ j, v j * lapGrad j) -
          ∑ i, x i * (I * Ip * v i + c * ∑ j, v j * H i j)) /
        Real.sqrt (I ^ 2 + c * ‖v‖ ^ 2) -
      (∑ i, (I * Ip * v i + c * ∑ j, v j * H i j) ^ 2) /
        (Real.sqrt (I ^ 2 + c * ‖v‖ ^ 2)) ^ 3 := by
  dsimp only
  let I := normalProfile u
  let Ip := deriv normalProfile u
  let R := Real.sqrt (I ^ 2 + c * ‖v‖ ^ 2)
  let Np : n → ℝ := fun i =>
    (Ip ^ 2 - 1) * (v i) ^ 2 +
      I * Ip * inner ℝ (H i) (euclideanUnit i) +
      c * (‖H i‖ ^ 2 + inner ℝ v (Ke i (euclideanUnit i)))
  have hinnerCoords (w : EuclideanSpace ℝ n) :
      inner ℝ v w = ∑ j, v j * w j := by
    simpa [PiLp.inner_apply, mul_comm]
  have hsumK :
      ∑ i, inner ℝ v (Ke i (euclideanUnit i)) =
        ∑ j, v j * lapGrad j := by
    simp_rw [hinnerCoords]
    calc
      ∑ i, ∑ j, v j * (Ke i (euclideanUnit i)) j =
          ∑ j, ∑ i, v j * (Ke i (euclideanUnit i)) j :=
        Finset.sum_comm
      _ = ∑ j, v j * (∑ i, (Ke i (euclideanUnit i)) j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
      _ = ∑ j, v j * lapGrad j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hlap j]
        simp only [inner_euclideanUnit_right]
  have hNpSum :
      ∑ i, Np i =
        (Ip ^ 2 - 1) * ‖v‖ ^ 2 +
          I * Ip * ∑ i, H i i +
          c * (∑ i, ‖H i‖ ^ 2 + ∑ j, v j * lapGrad j) := by
    simp only [Np, inner_euclideanUnit_right]
    rw [← hsumK]
    calc
      ∑ x, ((Ip ^ 2 - 1) * v x ^ 2 + I * Ip * H x x +
          c * (‖H x‖ ^ 2 + inner ℝ v (Ke x (euclideanUnit x)))) =
          (Ip ^ 2 - 1) * (∑ x, v x ^ 2) +
            I * Ip * ∑ x, H x x +
            c * ((∑ x, ‖H x‖ ^ 2) +
              ∑ x, inner ℝ v (Ke x (euclideanUnit x))) := by
        simp_rw [mul_add, Finset.sum_add_distrib]
        rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
          ← Finset.mul_sum]
      _ = _ := by rw [← EuclideanSpace.real_norm_sq_eq v]
  have hNpSum' := hNpSum
  simp only [Np, inner_euclideanUnit_right] at hNpSum'
  simp_rw [hinnerCoords] at hNpSum'
  simp only [bobkovSpatialHessianDiagonal, bobkovSpatialGradientCoordinate]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [inner_euclideanUnit_right]
  simp_rw [hinnerCoords]
  rw [← Finset.sum_div, ← Finset.sum_div]
  have hdrift :
      ∑ i, x i *
          ((I * Ip * v i + c * ∑ j, v j * H i j) / R) =
        (∑ i, x i * (I * Ip * v i + c * ∑ j, v j * H i j)) / R := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hdrift, hNpSum']
  dsimp only [I, Ip, R]
  ring

/-- The direct Riesz-data version of the canonical Bobkov time derivative. -/
def canonicalGaussianBobkovQTimeDerivRiesz
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [SecondCountableTopology E]
    (t s : ℝ) (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (Hf : BoundedContinuousFunction E (E →L[ℝ] E)) (x : E) : ℝ :=
  canonicalGaussianBobkovQTimeDeriv t f Df s x
    (backwardGaussianOUValueTimeDeriv t s Df x)
    (backwardGaussianOURieszGradientTimeDeriv
      t s (rieszGradientBCF Df) Hf x)

theorem hasDerivAt_canonicalGaussianBobkovQ_time_of_rieszHessian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [SecondCountableTopology E]
    (t : ℝ) (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (hDf : ∀ y, HasFDerivAt f (Df y) y)
    (Hf : BoundedContinuousFunction E (E →L[ℝ] E))
    (hHf : ∀ y, HasFDerivAt (rieszGradientBCF Df) (Hf y) y)
    (ε : ℝ) (hε : 0 < ε) (hf : ∀ x, f x ∈ Icc ε (1 - ε))
    {s : ℝ} (hs : 0 ≤ s) (hst : s < t) (x : E) :
    HasDerivAt
      (fun r => canonicalGaussianBobkovQ t f Df ε hε hf r x)
      (canonicalGaussianBobkovQTimeDerivRiesz t s f Df Hf x) s := by
  have hu := hasDerivAt_backwardGaussianOUValueBCF_time
    t s hst f Df hDf x
  have hvRaw := hasDerivAt_backwardGaussianOURieszGradientBCF_time
    t s hst (rieszGradientBCF Df) Hf hHf x
  have hv : HasDerivAt
      (fun r => rieszGradientBCF
        (backwardGaussianOUDerivBCF t r Df) x)
      (backwardGaussianOURieszGradientTimeDeriv
        t s (rieszGradientBCF Df) Hf x) s := by
    convert hvRaw using 1
    funext r
    exact (backwardGaussianOURieszGradientBCF_rieszGradientBCF
      t r Df x).symm
  simpa [canonicalGaussianBobkovQTimeDerivRiesz,
    canonicalGaussianBobkovQTimeDeriv] using
      hasDerivAt_canonicalGaussianBobkovQ_of_backwardTimeDerivatives
        t f Df ε hε hf hs x hu hv

theorem canonicalGaussianBobkovQ_time_add_generator_eq_residual
    {n : ℕ}
    (t s : ℝ) (hst : s < t) (hs : 0 ≤ s)
    (f : BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1))) ℝ)
    (Df : BoundedContinuousFunction (EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ))
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
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    canonicalGaussianBobkovQTimeDerivRiesz t s f Df Hf x +
        ∑ i, (canonicalGaussianBobkovQHessianDiagonalBCF
            t s f Df Hf D3f M hM ε hε hf hs (euclideanUnit i) x -
          x i * canonicalGaussianBobkovQGradientCoordinateBCF
            t s f Df Hf ε hε hf hs (euclideanUnit i) x) =
      bobkovSqrtResidual (bobkovVarianceCoeff s)
        (normalProfile (backwardGaussianOUValueBCF t s f x))
        (deriv normalProfile (backwardGaussianOUValueBCF t s f x))
        (rieszGradientBCF (backwardGaussianOUDerivBCF t s Df) x)
        (fun i => backwardGaussianOURieszHessianBCF
          t s Hf x (euclideanUnit i)) := by
  let G := EuclideanSpace ℝ (Fin (n + 1))
  let u := backwardGaussianOUValueBCF t s f x
  let I := normalProfile u
  let Ip := deriv normalProfile u
  let c := bobkovVarianceCoeff s
  let v := rieszGradientBCF (backwardGaussianOUDerivBCF t s Df) x
  let Hb := backwardGaussianOURieszHessianBCF t s Hf x
  let H : Fin (n + 1) → G := fun i => Hb (euclideanUnit i)
  let Ke : Fin (n + 1) → G →L[ℝ] G := fun i =>
    backwardGaussianOURieszHessianDirectionalDerivBCF
      t s D3f (euclideanUnit i) M hM x
  let lapGrad := backwardGaussianOULaplacianGradient t s D3f M hM x
  let us := backwardGaussianOUValueTimeDeriv t s Df x
  let vs := backwardGaussianOURieszGradientTimeDeriv
    t s (rieszGradientBCF Df) Hf x
  have huClosed := backwardGaussianOUValueBCF_mem_Icc t s f hf x
  have hu : u ∈ Ioo (0 : ℝ) 1 :=
    ⟨hε.trans_le huClosed.1, huClosed.2.trans_lt (by linarith)⟩
  have hus : us = -∑ i, (H i i - x i * v i) := by
    simpa only [us, H, Hb, v, inner_euclideanUnit_right] using
      backwardGaussianOUValueTimeDeriv_eq_neg_generator
        t s hst Df Hf hHf x
  have hvs : vs = -lapGrad + v + ∑ i, x i • H i := by
    have h := backwardGaussianOURieszGradientTimeDeriv_eq_neg_generator
      t s hst (rieszGradientBCF Df) Hf D3f M hM hD3f x
    rw [backwardGaussianOURieszGradientBCF_rieszGradientBCF
      t s Df x] at h
    simpa [vs, lapGrad, H, Hb, v] using h
  have hlap (j : Fin (n + 1)) :
      lapGrad j = ∑ i, inner ℝ (Ke i (euclideanUnit i))
        (euclideanUnit j) := by
    rfl
  have hgen := sum_bobkovSpatial_diagonal_generator_eq_aggregated
    x v lapGrad H Ke c u hlap
  dsimp only at hgen
  have hinnerCoords (w : G) :
      inner ℝ v w = ∑ j, v j * w j := by
    simpa [PiLp.inner_apply, mul_comm]
  have hsumCoord (j : Fin (n + 1)) :
      (∑ i, x i • H i) j = ∑ i, x i * H i j := by
    change (WithLp.ofLp (∑ i, x i • H i)) j = _
    rw [WithLp.ofLp_sum]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [WithLp.ofLp_smul]
    rfl
  have hinnerVs :
      inner ℝ v (-lapGrad + v + ∑ i, x i • H i) =
        ∑ j, v j * (-lapGrad j + v j + ∑ i, x i * H i j) := by
    rw [hinnerCoords]
    apply Finset.sum_congr rfl
    intro j _
    change v j * (-lapGrad + v + ∑ i, x i • H i) j = _
    congr 1
    rw [WithLp.ofLp_add, WithLp.ofLp_add, WithLp.ofLp_neg]
    simp only [Pi.add_apply, Pi.neg_apply]
    rw [hsumCoord]
  have htime :
      canonicalGaussianBobkovQTimeDerivRiesz t s f Df Hf x =
        (2 * I * Ip * (-∑ i, (H i i - x i * v i)) +
            2 * (1 - c) * ‖v‖ ^ 2 +
            2 * c * ∑ j, v j *
              (-lapGrad j + v j + ∑ i, x i * H i j)) /
          (2 * Real.sqrt (I ^ 2 + c * ‖v‖ ^ 2)) := by
    change canonicalGaussianBobkovQTimeDeriv t f Df s x us vs = _
    unfold canonicalGaussianBobkovQTimeDeriv
    change
      (2 * I * (-lowerQuantile standardGaussianMeasure u) * us +
          2 * (1 - c) * ‖backwardGaussianOUDerivBCF t s Df x‖ ^ 2 +
          2 * c * inner ℝ v vs) /
        (2 * Real.sqrt
          (I ^ 2 + c * ‖backwardGaussianOUDerivBCF t s Df x‖ ^ 2)) = _
    have hnorm : ‖backwardGaussianOUDerivBCF t s Df x‖ = ‖v‖ := by
      symm
      exact norm_rieszGradientBCF (backwardGaussianOUDerivBCF t s Df) x
    rw [hus, hvs, hinnerVs, hnorm]
    rw [← deriv_normalProfile hu]
  have halg := bobkovQ_time_add_generator_eq_residual_of_PDE
    x v lapGrad H u I Ip c rfl rfl hu (bobkovVarianceCoeff_nonneg hs)
  dsimp only at halg
  have hHfield (i : Fin (n + 1)) :
      canonicalGaussianBobkovQHessianDiagonalBCF
          t s f Df Hf D3f M hM ε hε hf hs (euclideanUnit i) x =
        bobkovSpatialHessianDiagonal c u v (H i) (Ke i)
          (euclideanUnit i) := by
    simp [canonicalGaussianBobkovQHessianDiagonalBCF,
      c, u, v, H, Hb, Ke]
  have hGfield (i : Fin (n + 1)) :
      canonicalGaussianBobkovQGradientCoordinateBCF
          t s f Df Hf ε hε hf hs (euclideanUnit i) x =
        bobkovSpatialGradientCoordinate c u v (H i)
          (euclideanUnit i) := by
    simp [canonicalGaussianBobkovQGradientCoordinateBCF,
      c, u, v, H, Hb]
  rw [htime]
  simp_rw [hHfield, hGfield]
  rw [hgen]
  simpa [c, u, I, Ip, v, H, Hb] using halg

end
end UniformRandomMALA.Concrete
