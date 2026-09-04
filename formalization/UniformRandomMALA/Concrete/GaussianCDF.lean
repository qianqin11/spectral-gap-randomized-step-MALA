import UniformRandomMALA.GaussianShiftArithmetic
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Concrete standard Gaussian CDF and tail

The paper's Gaussian-shift and isoperimetric arguments use `Φ`, its upper
tail, and their density.  This file fixes those objects as Mathlib's actual
standard Gaussian probability measure; no abstract CDF is used.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace Concrete

/-- The standard Gaussian probability measure on `ℝ`. -/
def standardGaussianMeasure : Measure ℝ :=
  gaussianReal 0 1

instance standardGaussianMeasure_isProbabilityMeasure :
    IsProbabilityMeasure standardGaussianMeasure := by
  unfold standardGaussianMeasure
  infer_instance

instance standardGaussianMeasure_nullSingletonClass :
    NullSingletonClass standardGaussianMeasure := by
  unfold standardGaussianMeasure
  exact nullSingletonClass_gaussianReal (by norm_num)

/-- The standard normal density `φ`. -/
def normalDensity (x : ℝ) : ℝ :=
  gaussianPDFReal 0 1 x

/-- Extended-valued standard normal distribution function. -/
def normalCDF (x : ℝ) : ℝ≥0∞ :=
  standardGaussianMeasure (Set.Iic x)

/-- Extended-valued upper standard normal tail. -/
def normalTail (x : ℝ) : ℝ≥0∞ :=
  standardGaussianMeasure (Set.Ioi x)

/-- Real-valued CDF used in the paper. -/
def normalCDFReal (x : ℝ) : ℝ :=
  (normalCDF x).toReal

/-- Real-valued upper tail. -/
def normalTailReal (x : ℝ) : ℝ :=
  (normalTail x).toReal

lemma normalDensity_def (x : ℝ) :
    normalDensity x =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) := by
  simp [normalDensity, gaussianPDFReal]

lemma normalDensity_pos (x : ℝ) : 0 < normalDensity x := by
  exact gaussianPDFReal_pos 0 1 x (by norm_num)

lemma normalDensity_nonneg (x : ℝ) : 0 ≤ normalDensity x :=
  (normalDensity_pos x).le

lemma measurable_normalDensity : Measurable normalDensity := by
  exact measurable_gaussianPDFReal 0 1

lemma integrable_normalDensity : Integrable normalDensity := by
  exact integrable_gaussianPDFReal 0 1

lemma integral_normalDensity : ∫ x, normalDensity x = 1 := by
  exact integral_gaussianPDFReal_eq_one 0 (by norm_num)

lemma normalCDF_eq_integral (x : ℝ) :
    normalCDF x = ENNReal.ofReal (∫ y in Set.Iic x, normalDensity y) := by
  exact gaussianReal_apply_eq_integral 0 (by norm_num) (Set.Iic x)

lemma normalTail_eq_integral (x : ℝ) :
    normalTail x = ENNReal.ofReal (∫ y in Set.Ioi x, normalDensity y) := by
  exact gaussianReal_apply_eq_integral 0 (by norm_num) (Set.Ioi x)

lemma normalCDF_mono : Monotone normalCDF := by
  intro x y hxy
  exact measure_mono (Set.Iic_subset_Iic.mpr hxy)

lemma normalTail_anti : Antitone normalTail := by
  intro x y hxy
  exact measure_mono (Set.Ioi_subset_Ioi hxy)

lemma normalCDF_le_one (x : ℝ) : normalCDF x ≤ 1 := prob_le_one

lemma normalTail_le_one (x : ℝ) : normalTail x ≤ 1 := prob_le_one

/-- `Φ(x) + Φ̄(x) = 1`, with the endpoint assigned to the CDF. -/
theorem normalCDF_add_tail (x : ℝ) :
    normalCDF x + normalTail x = 1 := by
  unfold normalCDF normalTail
  rw [← measure_union (μ := standardGaussianMeasure)
    (Set.disjoint_left.2 (by
      intro y hyic hyoi
      exact (not_lt_of_ge (show y ≤ x from hyic)) (show x < y from hyoi)))
    measurableSet_Ioi]
  rw [Set.Iic_union_Ioi, measure_univ]

lemma standardGaussianMeasure_map_neg :
    standardGaussianMeasure.map (fun x : ℝ => -x) = standardGaussianMeasure := by
  unfold standardGaussianMeasure
  simpa using (gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : NNReal)))

/-- Symmetry of the standard Gaussian, including the null endpoint. -/
theorem normalCDF_neg (x : ℝ) :
    normalCDF (-x) = normalTail x := by
  have hIciIoi :
      standardGaussianMeasure (Set.Ici x) =
        standardGaussianMeasure (Set.Ioi x) := by
    exact (measure_eq_measure_of_null_sdiff Set.Ioi_subset_Ici_self (by simp)).symm
  calc
    normalCDF (-x) =
        (standardGaussianMeasure.map (fun y : ℝ => -y)) (Set.Iic (-x)) := by
      rw [standardGaussianMeasure_map_neg]
      rfl
    _ = standardGaussianMeasure ((fun y : ℝ => -y) ⁻¹' Set.Iic (-x)) := by
      rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
    _ = standardGaussianMeasure (Set.Ici x) := by
      congr 1
      ext y
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_Ici]
      constructor <;> intro h <;> linarith
    _ = standardGaussianMeasure (Set.Ioi x) := hIciIoi
    _ = normalTail x := rfl

theorem normalCDF_zero : normalCDF 0 = 2⁻¹ := by
  have hsym := normalCDF_neg 0
  have hsum := normalCDF_add_tail 0
  simp only [neg_zero] at hsym
  rw [← hsym] at hsum
  have htwo : (2 : ℝ≥0∞) * normalCDF 0 = 1 := by
    simpa [two_mul] using hsum
  calc
    normalCDF 0 = 1 * normalCDF 0 := by simp
    _ = ((2 : ℝ≥0∞)⁻¹ * 2) * normalCDF 0 := by
      rw [ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
    _ = (2 : ℝ≥0∞)⁻¹ * (2 * normalCDF 0) := by rw [mul_assoc]
    _ = 2⁻¹ := by rw [htwo, mul_one]

theorem normalTail_zero : normalTail 0 = 2⁻¹ := by
  rw [← normalCDF_neg, neg_zero, normalCDF_zero]

end Concrete

end

end UniformRandomMALA
