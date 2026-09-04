import UniformRandomMALA.Concrete.LadderComponents

/-!
# Global concrete gap from Bakry--Ledoux

This module closes the elementary proof chain after Proposition 3.2.  Its
main theorem has one analytic premise, the Bakry--Ledoux enlargement
inequality.  The remaining hypotheses are explicit numerical parameter
choices and the definitional identification of the abstract arithmetic
parameters with the concrete potential.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

namespace Concrete

/-- A concrete universal gap coefficient common to the safe and ladder
components. -/
def concreteGapConstant : ℝ := 1 / (12 * (2 : ℝ) ^ 30)

lemma concreteGapConstant_pos : 0 < concreteGapConstant := by
  unfold concreteGapConstant
  positivity

lemma concreteGapConstant_le_safe :
    concreteGapConstant ≤ Real.log 2 / (2 : ℝ) ^ 28 := by
  unfold concreteGapConstant
  have hlog := Real.log_two_gt_d9
  norm_num at hlog ⊢
  nlinarith

namespace FirstOrderPotential

variable {d : ℕ} (V : FirstOrderPotential d)

/-- The concrete safe step is the abstract safe scale truncated at the user
endpoint. -/
lemma safeStep_eq_min_safeScale
    (p : Parameters) (hmatch : PotentialParametersMatch V p) :
    V.safeStep p.H p.b0 = min p.H p.safeScale := by
  unfold safeStep Parameters.safeScale Parameters.baseFactor
    Parameters.safeShape
  rw [hmatch.dimension, hmatch.smoothness]
  congr 1
  field_simp [V.hL.ne', V.dimension_real_pos.ne']

/-- Safe-component certificate with the same universal coefficient used by
the ladder. -/
theorem safe_truncated_spectralGap_lower_of_bakryLedoux
    (p : Parameters) (hmatch : PotentialParametersMatch V p)
    (hBL : BakryLedouxEnlargement
      (V.target : Measure (State d)) V.m
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure)) :
    ENNReal.ofReal
        (concreteGapConstant * (p.m / p.H) *
          (min p.H p.safeScale) ^ 2) ≤
      spectralGap (V.target : Measure (State d))
        (V.uniformMALA p.H p.hH) := by
  have hscale : 0 ≤ (p.m / p.H) * (min p.H p.safeScale) ^ 2 :=
    mul_nonneg (div_nonneg p.m_nonneg p.H_nonneg) (sq_nonneg _)
  have hreal :
      concreteGapConstant * (p.m / p.H) *
          (min p.H p.safeScale) ^ 2 ≤
        p.m * (min p.H p.safeScale) ^ 2 * Real.log 2 /
          ((2 : ℝ) ^ 28 * p.H) := by
    have hs := mul_le_mul_of_nonneg_right concreteGapConstant_le_safe hscale
    field_simp [p.hH.ne'] at hs ⊢
    nlinarith
  calc
    ENNReal.ofReal
        (concreteGapConstant * (p.m / p.H) *
          (min p.H p.safeScale) ^ 2) ≤
        ENNReal.ofReal
          (p.m * (min p.H p.safeScale) ^ 2 * Real.log 2 /
            ((2 : ℝ) ^ 28 * p.H)) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal
          (V.m * (V.safeStep p.H p.b0) ^ 2 * Real.log 2 /
            ((2 : ℝ) ^ 28 * p.H)) := by
      rw [hmatch.strongConvexity, V.safeStep_eq_min_safeScale p hmatch]
    _ ≤ spectralGap (V.target : Measure (State d))
        (V.uniformMALA p.H p.hH) :=
      V.safe_spectralGap_lower_of_bakryLedoux p.H p.b0 p.hH p.hb0
        p.hb0_half hBL

/-- Concrete master-scale gap theorem.  Apart from explicit numerical
admissibility conditions, Bakry--Ledoux is its sole analytic hypothesis. -/
theorem global_spectralGap_lower_of_bakryLedoux
    (p : Parameters) (hmatch : PotentialParametersMatch V p)
    (hbSmall : p.b0 ≤ proposition32CrSmall)
    (hbLarge : proposition32CrLarge * p.b0 ≤ 1 / 16)
    (hchoice : ExceptionalBudgetParameterChoice p)
    (hBL : BakryLedouxEnlargement
      (V.target : Measure (State d)) V.m
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure)) :
    ENNReal.ofReal
        (concreteGapConstant * (p.m / p.H) *
          (min p.H p.certifiedScale) ^ 2) ≤
      spectralGap (V.target : Measure (State d))
        (V.uniformMALA p.H p.hH) := by
  by_cases hsmall : p.pStar < p.d
  · by_cases hrs : p.rejectionScale ≤ p.safeScale
    · rw [p.certifiedScale_eq_max_scales, max_eq_right hrs]
      exact V.safe_truncated_spectralGap_lower_of_bakryLedoux p hmatch hBL
    · have hsr : p.safeScale ≤ p.rejectionScale := le_of_not_ge hrs
      rw [p.certifiedScale_eq_max_scales, max_eq_left hsr]
      simpa only [concreteGapConstant] using
        V.ladder_truncated_spectralGap_lower_of_bakryLedoux p hmatch
          hsmall hbSmall hbLarge hchoice hBL
  · have hlarge : p.d ≤ p.pStar := le_of_not_gt hsmall
    rw [p.certifiedScale_eq_safeScale_of_dim_le_moment hlarge]
    exact V.safe_truncated_spectralGap_lower_of_bakryLedoux p hmatch hBL

/-- Version phrased with the `masterRHS` field of `Parameters`. -/
theorem masterRHS_spectralGap_lower_of_bakryLedoux
    (p : Parameters) (hmatch : PotentialParametersMatch V p)
    (hc0 : p.c0 ≤ concreteGapConstant)
    (hbSmall : p.b0 ≤ proposition32CrSmall)
    (hbLarge : proposition32CrLarge * p.b0 ≤ 1 / 16)
    (hchoice : ExceptionalBudgetParameterChoice p)
    (hBL : BakryLedouxEnlargement
      (V.target : Measure (State d)) V.m
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure)) :
    ENNReal.ofReal p.masterRHS ≤
      spectralGap (V.target : Measure (State d))
        (V.uniformMALA p.H p.hH) := by
  have hfactor : 0 ≤ (p.m / p.H) * (min p.H p.certifiedScale) ^ 2 :=
    mul_nonneg (div_nonneg p.m_nonneg p.H_nonneg) (sq_nonneg _)
  have hrhs : p.masterRHS ≤
      concreteGapConstant * (p.m / p.H) *
        (min p.H p.certifiedScale) ^ 2 := by
    unfold Parameters.masterRHS
    have := mul_le_mul_of_nonneg_right hc0 hfactor
    nlinarith
  exact (ENNReal.ofReal_le_ofReal hrhs).trans
    (V.global_spectralGap_lower_of_bakryLedoux p hmatch hbSmall hbLarge
      hchoice hBL)

end FirstOrderPotential
end Concrete
end
end UniformRandomMALA
