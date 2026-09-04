import UniformRandomMALA.Concrete.GlobalFromBakryLedoux

/-!
# Explicit universal constants

This module chooses `b₀`, `A₀`, and `c₀` once and proves every numerical
admissibility condition required by the concrete master-gap theorem.  The
final declaration therefore has Bakry--Ledoux as its only mathematical
hypothesis (apart from positivity of the requested endpoint).
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

namespace Concrete
namespace FirstOrderPotential

/-- Explicit small universal constant satisfying both Proposition 3.2
constraints and the safe-component constraint. -/
def concreteB0 : ℝ :=
  min (1 / 2 : ℝ)
    (min proposition32CrSmall (1 / (16 * proposition32CrLarge)))

lemma concreteB0_pos : 0 < concreteB0 := by
  unfold concreteB0
  apply lt_min (by norm_num)
  exact lt_min proposition32CrSmall_pos
    (one_div_pos.mpr (mul_pos (by norm_num) proposition32CrLarge_pos))

lemma concreteB0_le_half : concreteB0 ≤ 1 / 2 := min_le_left _ _

lemma concreteB0_le_small : concreteB0 ≤ proposition32CrSmall :=
  (min_le_right _ _).trans (min_le_left _ _)

lemma concreteB0_large_control :
    proposition32CrLarge * concreteB0 ≤ 1 / 16 := by
  have hb : concreteB0 ≤ 1 / (16 * proposition32CrLarge) :=
    (min_le_right _ _).trans (min_le_right _ _)
  calc
    proposition32CrLarge * concreteB0 ≤
        proposition32CrLarge * (1 / (16 * proposition32CrLarge)) :=
      mul_le_mul_of_nonneg_left hb proposition32CrLarge_pos.le
    _ = 1 / 16 := by
      field_simp [proposition32CrLarge_pos.ne']

/-- Positive coefficient multiplying the moment in the exceptional-budget
exponent. -/
def exceptionalBudgetSlope : ℝ := Real.log 16 - 1 / 2

lemma exceptionalBudgetSlope_pos : 0 < exceptionalBudgetSlope := by
  unfold exceptionalBudgetSlope
  have hlog16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  rw [hlog16]
  nlinarith [Real.log_two_gt_d9]

/-- Explicit large universal moment-threshold coefficient. -/
def concreteA0 : ℝ :=
  max 2
    ((13 * Real.log 2 + (1 / 2) * Real.log (2 / concreteB0) + 1) /
      exceptionalBudgetSlope)

lemma concreteA0_ge_two : 2 ≤ concreteA0 := le_max_left _ _

lemma concreteA0_exceptional_choice :
    13 * Real.log 2 + (1 / 2) * Real.log (2 / concreteB0) ≤
        concreteA0 * exceptionalBudgetSlope ∧
      1 ≤ concreteA0 * exceptionalBudgetSlope := by
  let base : ℝ := 13 * Real.log 2 + (1 / 2) * Real.log (2 / concreteB0)
  have hb0 := concreteB0_pos
  have hratio : 1 ≤ 2 / concreteB0 := by
    apply (le_div_iff₀ hb0).2
    nlinarith [concreteB0_le_half]
  have hbase : 0 ≤ base := by
    dsimp only [base]
    have hlog2 := log_two_pos.le
    have hlogratio := Real.log_nonneg hratio
    nlinarith
  have hdiv : (base + 1) / exceptionalBudgetSlope ≤ concreteA0 :=
    le_max_right _ _
  have hmain : base + 1 ≤ concreteA0 * exceptionalBudgetSlope :=
    (div_le_iff₀ exceptionalBudgetSlope_pos).mp hdiv
  exact ⟨by dsimp only [base] at hmain ⊢; linarith, by linarith⟩

variable {d : ℕ} (V : FirstOrderPotential d)

/-- Concrete arithmetic parameter record with all universal constants fixed. -/
def universalParameters (H : ℝ) (hH : 0 < H) : Parameters :=
  V.toParameters H concreteA0 concreteB0 concreteGapConstant hH
    concreteA0_ge_two concreteB0_pos concreteB0_le_half concreteGapConstant_pos

lemma universalParameters_match (H : ℝ) (hH : 0 < H) :
    PotentialParametersMatch V (V.universalParameters H hH) :=
  ⟨rfl, rfl, rfl⟩

lemma universalParameters_exceptionalChoice (H : ℝ) (hH : 0 < H) :
    ExceptionalBudgetParameterChoice (V.universalParameters H hH) := by
  change
    13 * Real.log 2 + (1 / 2) * Real.log (2 / concreteB0) ≤
        concreteA0 * (Real.log 16 - 1 / 2) ∧
      1 ≤ concreteA0 * (Real.log 16 - 1 / 2)
  simpa only [exceptionalBudgetSlope] using concreteA0_exceptional_choice

/-- Fully instantiated concrete master bound.  Bakry--Ledoux is the sole
remaining mathematical premise. -/
theorem universal_masterRHS_spectralGap_lower_of_bakryLedoux
    (H : ℝ) (hH : 0 < H)
    (hBL : BakryLedouxEnlargement
      (V.target : Measure (State d)) V.m
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure)) :
    let p := V.universalParameters H hH
    ENNReal.ofReal p.masterRHS ≤
      spectralGap (V.target : Measure (State d))
        (V.uniformMALA p.H p.hH) := by
  exact V.masterRHS_spectralGap_lower_of_bakryLedoux
    (V.universalParameters H hH) (V.universalParameters_match H hH)
    (by rfl) concreteB0_le_small concreteB0_large_control
    (V.universalParameters_exceptionalChoice H hH) hBL

end FirstOrderPotential
end Concrete
end
end UniformRandomMALA
