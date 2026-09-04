import UniformRandomMALA.Concrete.GaussianOUCanonicalInterpolation
import UniformRandomMALA.Concrete.FiniteEulerEnlargement
import UniformRandomMALA.Concrete.FiniteEulerTargetIdentification
import UniformRandomMALA.Concrete.UniversalConstants
import Mathlib.Algebra.Group.Ext

/-!
# Canonical OU interpolation for the mollified Gaussian ramp

This module specializes the bounded-third-jet interpolation certificate to
the concrete compact-kernel ramp mollifiers.  It then feeds the resulting
levelwise Bobkov inequalities through the G5 closed-strip limit.
-/

namespace UniformRandomMALA

open Function Set Metric MeasureTheory Filter ContinuousLinearMap
  ProbabilityTheory
open scoped Topology NNReal ENNReal ProbabilityTheory

noncomputable section

namespace Concrete

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [SecondCountableTopology E]

/-- Bakry--Ledoux enlargement is preserved by an isometric measurable
change of coordinates. -/
theorem bakryLedouxEnlargement_map_linearIsometryEquiv
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    [SecondCountableTopology F]
    (mu : Measure E) [IsProbabilityMeasure mu]
    {m : ℝ} {Phi PhiInv : ℝ → ℝ}
    (hBL : BakryLedouxEnlargement mu m Phi PhiInv)
    (L : E ≃ₗᵢ[ℝ] F) :
    BakryLedouxEnlargement (Measure.map L mu) m Phi PhiInv := by
  intro A hA hA0 hA1 r hr
  have h := enlargement_map_of_lipschitzWith mu hBL L
    L.isometry.lipschitz (by norm_num : 0 < (1 : ℝ))
    A hA hA0 hA1 r hr
  simpa using h

@[simp] theorem rieszGradientBCF_smul
    (c : ℝ) (D : BoundedContinuousFunction E (E →L[ℝ] ℝ)) :
    rieszGradientBCF (c • D) = c • rieszGradientBCF D := by
  ext x
  change (InnerProductSpace.toDual ℝ E).symm (c • D x) =
    c • (InnerProductSpace.toDual ℝ E).symm (D x)
  exact map_smul (InnerProductSpace.toDual ℝ E).symm c (D x)

@[simp] theorem rieszGradientBCF_gaussianRampMollifiedDerivBCF
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) :
    (⇑(rieszGradientBCF (gaussianRampMollifiedDerivBCF hh A n))) =
      gaussianRampMollifiedGradient hh A n := by
  rfl

/-- The bounded Riesz transform of the covector Hessian agrees with the
iterated derivative used by the concrete third-derivative construction. -/
theorem rieszHessianBCF_gaussianRampMollifiedD2BCF
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) :
    (⇑(rieszHessianBCF (gaussianRampMollifiedD2BCF hh A n))) =
      gaussianRampMollifiedRieszHessian hh A n := by
  funext x
  let L :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hD := hasFDerivAt_fderiv_gaussianRampMollified hh A n x
  have hcomp := L.hasFDerivAt.comp x hD
  have hfun : (L ∘ fderiv ℝ
      (gaussianRampMollified hh A n)) =
      gaussianRampMollifiedGradient hh A n := by
    funext y
    rfl
  rw [hfun] at hcomp
  simpa [L, rieszHessianBCF, gaussianRampMollifiedRieszHessian]
    using hcomp.fderiv.symm

section EuclideanRamp

variable {m : ℕ}
local notation "G" => EuclideanSpace ℝ (Fin (m + 1))

/-- Every concrete mollified distance ramp satisfies the closed-profile
Bobkov functional inequality.  The canonical interpolation is applied only
after affine endpoint truncation, so its normal profile stays uniformly away
from the singular endpoints. -/
theorem gaussianRampMollified_bobkov
    {h : ℝ} (hh : 0 < h)
    (A : Set (EuclideanSpace ℝ (Fin (m + 1)))) (n : ℕ) :
    normalProfileClosed
        (∫ y, gaussianRampMollifiedBCF hh A n y ∂
          stdGaussian (EuclideanSpace ℝ (Fin (m + 1)))) ≤
      ∫ y, Real.sqrt
        (normalProfileClosed (gaussianRampMollifiedBCF hh A n y) ^ 2 +
          ‖gaussianRampMollifiedDerivBCF hh A n y‖ ^ 2) ∂
          stdGaussian (EuclideanSpace ℝ (Fin (m + 1))) := by
  have hAddG : (inferInstance : AddCommGroup G) =
      (inferInstance : NormedAddCommGroup G).toAddCommGroup := by
    apply AddCommGroup.ext
    rfl
  have hModuleG : (inferInstance : Module ℝ G) =
      (inferInstance : NormedSpace ℝ G).toModule := by
    apply Module.ext
    rfl
  have hTopG : (inferInstance : TopologicalSpace G) =
      (inferInstance : PseudoMetricSpace G).toUniformSpace.toTopologicalSpace := by
    rfl
  have hAddR : (inferInstance : AddCommGroup ℝ) =
      (inferInstance : NormedAddCommGroup ℝ).toAddCommGroup := by
    apply AddCommGroup.ext
    rfl
  have hModuleR : (inferInstance : Module ℝ ℝ) =
      (inferInstance : NormedSpace ℝ ℝ).toModule := by
    apply Module.ext
    rfl
  have hAddH : (inferInstance : AddCommGroup (G →L[ℝ] G)) =
      (inferInstance : NormedAddCommGroup (G →L[ℝ] G)).toAddCommGroup := by
    apply AddCommGroup.ext
    rfl
  have hModuleH : (inferInstance : Module ℝ (G →L[ℝ] G)) =
      (inferInstance : NormedSpace ℝ (G →L[ℝ] G)).toModule := by
    apply Module.ext
    rfl
  have hTopH : (inferInstance : TopologicalSpace (G →L[ℝ] G)) =
      (inferInstance : PseudoMetricSpace (G →L[ℝ] G)).toUniformSpace.toTopologicalSpace := by
    rfl
  let g := gaussianRampMollifiedBCF hh A n
  let Dg := gaussianRampMollifiedDerivBCF hh A n
  let Hg := rieszHessianBCF (gaussianRampMollifiedD2BCF hh A n)
  let D3g := gaussianRampMollifiedRieszD3BCF hh A n
  have hDg : ∀ y, HasFDerivAt g (Dg y) y := by
    intro y
    have hraw := ((contDiff_gaussianRampMollified hh A n)
      |>.differentiable (by simp) y).hasFDerivAt
    convert hraw using 1 <;> rfl
  have hHg : ∀ y, HasFDerivAt (rieszGradientBCF Dg) (Hg y) y := by
    intro y
    have hraw := ((contDiff_two_gaussianRampMollifiedGradient hh A n)
      |>.differentiable (by norm_num) y).hasFDerivAt
    have hraw' : HasFDerivAt
        (gaussianRampMollifiedGradient hh A n)
        (gaussianRampMollifiedRieszHessian hh A n y) y := by
      simpa [gaussianRampMollifiedRieszHessian] using hraw
    convert hraw' using 1
    · exact rieszGradientBCF_gaussianRampMollifiedDerivBCF hh A n
    · exact congrFun
        (rieszHessianBCF_gaussianRampMollifiedD2BCF hh A n) y
  have hD3g : ∀ y, HasFDerivAt Hg (D3g y) y := by
    intro y
    have hraw := hasFDerivAt_gaussianRampMollifiedRieszHessian hh A n y
    simpa [Hg, D3g,
      rieszHessianBCF_gaussianRampMollifiedD2BCF] using hraw
  apply gaussianBobkov_functionalClosed_of_smoothInterpolations
    g Dg (gaussianRampMollified_mem_Icc hh A n) 0
  intro e he0 he1 t ht
  let c : ℝ := 1 - 2 * e
  let Lc : (G →L[ℝ] G) →L[ℝ] (G →L[ℝ] G) :=
    ((ContinuousLinearMap.apply ℝ (G →L[ℝ] G)) c).comp
      (operatorScalarAction (E := G))
  let L3 : (G →L[ℝ] (G →L[ℝ] G)) →L[ℝ]
      (G →L[ℝ] (G →L[ℝ] G)) :=
    (ContinuousLinearMap.compL ℝ G (G →L[ℝ] G) (G →L[ℝ] G)) Lc
  let ge := bobkovTruncationBCF e g
  let De := c • Dg
  let He := Lc.compLeftContinuousBounded G Hg
  let D3e := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun y => L3 (D3g y))
    (by fun_prop)
    (‖Lc‖ * gaussianRampMollifiedRieszHessianLipschitzConstant
      (E := G) hh n)
    (fun y => by
      change ‖Lc.comp (gaussianRampMollifiedRieszD3 hh A n y)‖ ≤ _
      calc
        ‖Lc.comp (gaussianRampMollifiedRieszD3 hh A n y)‖ ≤
            ‖Lc‖ * ‖gaussianRampMollifiedRieszD3 hh A n y‖ :=
          Lc.opNorm_comp_le _
        _ ≤ ‖Lc‖ * gaussianRampMollifiedRieszHessianLipschitzConstant
            (E := G) hh n :=
          mul_le_mul_of_nonneg_left
            (norm_gaussianRampMollifiedRieszD3_le hh A n y)
            (norm_nonneg Lc))
  have hDe : ∀ y, HasFDerivAt ge (De y) y := by
    intro y
    have hscaled := (hDg y).const_smul c
    have hshifted := HasFDerivAt.const_add e hscaled
    change HasFDerivAt (bobkovTruncationBCF e g) (c • Dg y) y
    convert hshifted using 1
    funext z
    simp [bobkovTruncationBCF, c]
  have hHe : ∀ y, HasFDerivAt (rieszGradientBCF De) (He y) y := by
    intro y
    have hscaled := (hHg y).const_smul c
    change HasFDerivAt (rieszGradientBCF (c • Dg)) (Lc (Hg y)) y
    rw [rieszGradientBCF_smul]
    convert hscaled using 1 <;>
      first
      | exact hAddG
      | exact hModuleG
      | exact hTopG
      | exact hAddH
      | exact hModuleH
      | exact hTopH
      | rfl
  have hD3e : ∀ y, HasFDerivAt He (D3e y) y := by
    intro y
    have hcomp := Lc.hasFDerivAt.comp y (hD3g y)
    convert hcomp using 1 <;>
      first
      | exact hAddG
      | exact hModuleG
      | exact hTopG
      | exact hAddH
      | exact hModuleH
      | exact hTopH
      | rfl
  exact gaussianBobkovSmoothInterpolation_of_boundedThirdJet
    t ht ge De hDe He hHe D3e
      (‖Lc‖ * gaussianRampMollifiedRieszHessianLipschitzConstant
        (E := G) hh n)
      (fun y => by
        change ‖Lc.comp (gaussianRampMollifiedRieszD3 hh A n y)‖ ≤ _
        calc
          ‖Lc.comp (gaussianRampMollifiedRieszD3 hh A n y)‖ ≤
              ‖Lc‖ * ‖gaussianRampMollifiedRieszD3 hh A n y‖ :=
            Lc.opNorm_comp_le _
          _ ≤ ‖Lc‖ * gaussianRampMollifiedRieszHessianLipschitzConstant
              (E := G) hh n :=
            mul_le_mul_of_nonneg_left
              (norm_gaussianRampMollifiedRieszD3_le hh A n y)
              (norm_nonneg Lc)) hD3e
      e he0 he1 (bobkovTruncationBCF_mem_Icc e g
        (gaussianRampMollified_mem_Icc hh A n) he1) 0

/-- Unconditional G5 closed-strip bound in every positive Euclidean
dimension. -/
theorem gaussianRampClosedStripBound_euclidean :
    GaussianRampClosedStripBound (E := G) := by
  intro h hh A hA
  let a := concreteGaussianRampSmoothApproximation hh A
  apply gaussianRampClosedStripBound_of_approximation hh hA a
  intro n
  simpa [a, concreteGaussianRampSmoothApproximation] using
    gaussianRampMollified_bobkov hh A n

/-- The sharp standard-Gaussian Bakry--Ledoux enlargement inequality,
obtained with no remaining interpolation or mollification premise. -/
theorem bakryLedouxEnlargement_stdGaussian_euclidean :
    BakryLedouxEnlargement (stdGaussian G) 1
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure) := by
  exact bakryLedouxEnlargement_of_closedStrip
    (gaussianRampClosedStripBound_euclidean (m := m))

end EuclideanRamp

/-- The standard-Gaussian enlargement theorem for an arbitrary finite
coordinate type.  Nonempty coordinate types are reindexed isometrically to
`Fin (m+1)`; the zero-dimensional case is vacuous because every measurable
set has probability zero or one. -/
theorem bakryLedouxEnlargement_stdGaussian_finiteIndex
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    BakryLedouxEnlargement (stdGaussian (EuclideanSpace ℝ ι)) 1
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure) := by
  by_cases hι : Nonempty ι
  · letI : Nonempty ι := hι
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero
      (Fintype.card_ne_zero (α := ι))
    let e : Fin (m + 1) ≃ ι :=
      (finCongr hm.symm).trans (Fintype.equivFin ι).symm
    let L : EuclideanSpace ℝ (Fin (m + 1)) ≃ₗᵢ[ℝ]
        EuclideanSpace ℝ ι :=
      LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
    have hmap := bakryLedouxEnlargement_map_linearIsometryEquiv
      (stdGaussian (EuclideanSpace ℝ (Fin (m + 1))))
      (bakryLedouxEnlargement_stdGaussian_euclidean (m := m)) L
    rw [stdGaussian_map L] at hmap
    exact hmap
  · letI : IsEmpty ι := ⟨fun i => hι ⟨i⟩⟩
    intro A _hA hA0 hA1 _r _hr
    by_cases hA : A.Nonempty
    · have hAuniv : A = Set.univ := by
        apply Set.eq_univ_of_forall
        intro x
        obtain ⟨y, hy⟩ := hA
        simpa [Subsingleton.elim x y] using hy
      rw [hAuniv] at hA1
      simpa using hA1
    · rw [not_nonempty_iff_eq_empty.mp hA] at hA0
      simpa using hA0

end Concrete

namespace DiscreteTime

open Concrete

variable {d : ℕ}

/-- Unconditional Bakry--Ledoux enlargement for the normalized strongly
log-concave target.  Endpoint identification is the elementary diagonal
finite-Euler convergence theorem, rather than an SDE construction. -/
theorem target_bakryLedoux
    (V : FirstOrderPotential d) (x0 : State d) :
    BakryLedouxEnlargement (V.target : Measure (State d)) V.m
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure) := by
  apply finiteEulerEndpointLimit_bakryLedoux
    V (finiteEulerTargetDiagonalSteps V)
    (finiteEulerTargetDiagonalDelta V)
    (finiteEulerTargetDiagonalDelta_pos V)
    (fun k => by
      have hmesh := finiteEulerTargetDiagonal_mesh V k
      nlinarith [V.hm])
    (tendsto_finiteEulerTargetDiagonalDelta V)
    x0
    (fun _ => bakryLedouxEnlargement_stdGaussian_finiteIndex)
    (tendsto_finiteEulerTargetDiagonalEndpointLaw V x0)

end DiscreteTime

namespace Concrete.FirstOrderPotential

variable {d : ℕ}

/-- The concrete master-gap theorem with Bakry--Ledoux discharged by the
canonical OU/ramp construction and the discrete finite-Euler limit. -/
theorem masterRHS_spectralGap_lower
    (V : FirstOrderPotential d)
    (p : Parameters) (hmatch : PotentialParametersMatch V p)
    (hc0 : p.c0 ≤ concreteGapConstant)
    (hbSmall : p.b0 ≤ proposition32CrSmall)
    (hbLarge : proposition32CrLarge * p.b0 ≤ 1 / 16)
    (hchoice : ExceptionalBudgetParameterChoice p) :
    ENNReal.ofReal p.masterRHS ≤
      spectralGap (V.target : Measure (State d))
        (V.uniformMALA p.H p.hH) := by
  exact V.masterRHS_spectralGap_lower_of_bakryLedoux
    p hmatch hc0 hbSmall hbLarge hchoice
    (DiscreteTime.target_bakryLedoux V 0)

/-- Fully unconditional displayed master bound with all universal constants
fixed by `universalParameters`. -/
theorem universal_masterRHS_spectralGap_lower
    (V : FirstOrderPotential d) (H : ℝ) (hH : 0 < H) :
    let p := V.universalParameters H hH
    ENNReal.ofReal p.masterRHS ≤
      spectralGap (V.target : Measure (State d))
        (V.uniformMALA p.H p.hH) := by
  exact V.universal_masterRHS_spectralGap_lower_of_bakryLedoux
    H hH (DiscreteTime.target_bakryLedoux V 0)

end Concrete.FirstOrderPotential

end

end UniformRandomMALA
