import UniformRandomMALA.AggregationArithmetic
import UniformRandomMALA.Concrete.Median
import UniformRandomMALA.Concrete.Variance
import UniformRandomMALA.Concrete.LayerCake

/-!
# Measurable positive/negative median decomposition

This file lifts the scalar identities in `AggregationArithmetic` to the
concrete measure/kernel layer.  It supplies exactly the routine facts used by
the component-aggregation proof:

* measurability and support descriptions of the two median parts;
* squared-moment splitting;
* contraction of the sum of their Dirichlet energies; and
* the half-mass bound for every nonnegative squared superlevel.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace Concrete

variable {α : Type*} [MeasurableSpace α]

theorem measurable_positivePartAt
    {f : α → ℝ} (hf : Measurable f) (b : ℝ) :
    Measurable (fun x => positivePartAt b (f x)) := by
  unfold positivePartAt
  exact (hf.sub measurable_const).max measurable_const

theorem measurable_negativePartAt
    {f : α → ℝ} (hf : Measurable f) (b : ℝ) :
    Measurable (fun x => negativePartAt b (f x)) := by
  unfold negativePartAt
  exact (measurable_const.sub hf).max measurable_const

@[simp]
theorem positivePartAt_pos_iff (b x : ℝ) :
    0 < positivePartAt b x ↔ b < x := by
  simp [positivePartAt, sub_pos]

@[simp]
theorem negativePartAt_pos_iff (b x : ℝ) :
    0 < negativePartAt b x ↔ x < b := by
  simp [negativePartAt, sub_pos]

/-- The extended squared moment around `b` splits exactly into the moments
of the positive and negative parts. -/
theorem lintegral_sq_sub_eq_add_medianParts
    (π : Measure α) (f : α → ℝ) (hf : Measurable f) (b : ℝ) :
    (∫⁻ x, ENNReal.ofReal ((f x - b) ^ 2) ∂π) =
      (∫⁻ x, ENNReal.ofReal (positivePartAt b (f x) ^ 2) ∂π) +
        ∫⁻ x, ENNReal.ofReal (negativePartAt b (f x) ^ 2) ∂π := by
  have hp : Measurable (fun x =>
      ENNReal.ofReal (positivePartAt b (f x) ^ 2)) :=
    ENNReal.measurable_ofReal.comp
      ((measurable_positivePartAt hf b).pow_const 2)
  calc
    (∫⁻ x, ENNReal.ofReal ((f x - b) ^ 2) ∂π) =
        ∫⁻ x, ENNReal.ofReal (positivePartAt b (f x) ^ 2) +
          ENNReal.ofReal (negativePartAt b (f x) ^ 2) ∂π := by
      apply lintegral_congr
      intro x
      rw [centered_square_split,
        ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
    _ = (∫⁻ x, ENNReal.ofReal (positivePartAt b (f x) ^ 2) ∂π) +
        ∫⁻ x, ENNReal.ofReal (negativePartAt b (f x) ^ 2) ∂π := by
      rw [lintegral_add_left hp]

/-- Positive and negative parts do not increase total Dirichlet energy. -/
theorem energy_medianParts_le
    (π : Measure α) [SFinite π]
    (K : Kernel α α) [IsSFiniteKernel K]
    (f : α → ℝ) (hf : Measurable f) (b : ℝ) :
    Dirichlet.energy π K (fun x => positivePartAt b (f x)) +
        Dirichlet.energy π K (fun x => negativePartAt b (f x)) ≤
      Dirichlet.energy π K f := by
  let fp : α → ℝ := fun x => positivePartAt b (f x)
  let fn : α → ℝ := fun x => negativePartAt b (f x)
  have hfp : Measurable fp := measurable_positivePartAt hf b
  have hfn : Measurable fn := measurable_negativePartAt hf b
  have hep : Measurable (fun z : α × α =>
      ENNReal.ofReal ((fp z.1 - fp z.2) ^ 2)) :=
    Dirichlet.measurable_sqDiff hfp
  rw [energy_eq_edgeMeasure_lintegral π K fp hfp,
    energy_eq_edgeMeasure_lintegral π K fn hfn,
    energy_eq_edgeMeasure_lintegral π K f hf, ← mul_add]
  gcongr
  rw [← lintegral_add_left hep]
  apply lintegral_mono
  intro z
  calc
    ENNReal.ofReal ((fp z.1 - fp z.2) ^ 2) +
        ENNReal.ofReal ((fn z.1 - fn z.2) ^ 2) =
        ENNReal.ofReal
          ((fp z.1 - fp z.2) ^ 2 + (fn z.1 - fn z.2) ^ 2) := by
      rw [ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
    _ ≤ ENNReal.ofReal ((f z.1 - f z.2) ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      exact median_parts_edge_energy b (f z.1) (f z.2)

/-- If a nonnegative function has support of mass at most one half, every
positive squared superlevel also has mass at most one half. -/
theorem measure_sqSuperlevel_le_half_of_support
    (π : Measure α) (g : α → ℝ)
    (hg0 : ∀ x, 0 ≤ g x)
    (hsupport : π {x | 0 < g x} ≤ (2 : ℝ≥0∞)⁻¹)
    {r : ℝ} (hr : 0 ≤ r) :
    π (sqSuperlevel g r) ≤ (2 : ℝ≥0∞)⁻¹ := by
  refine (measure_mono ?_).trans hsupport
  intro x hx
  have hsq : 0 < g x ^ 2 := lt_of_le_of_lt hr hx
  have hne : g x ≠ 0 := by
    intro h
    simp [h] at hsq
  exact lt_of_le_of_ne (hg0 x) (Ne.symm hne)

/-- Positive-part superlevels inherit the upper strict-tail median bound. -/
theorem measure_sqSuperlevel_positivePart_le_half
    (π : Measure α) (f : α → ℝ) {b r : ℝ}
    (hb : IsMedian π f b) (hr : 0 ≤ r) :
    π (sqSuperlevel (fun x => positivePartAt b (f x)) r) ≤
      (2 : ℝ≥0∞)⁻¹ := by
  apply measure_sqSuperlevel_le_half_of_support π
    (fun x => positivePartAt b (f x))
    (fun x => positivePartAt_nonneg b (f x))
  · simpa only [positivePartAt_pos_iff] using hb.measure_gt
  · exact hr

/-- Negative-part superlevels inherit the lower strict-tail median bound. -/
theorem measure_sqSuperlevel_negativePart_le_half
    (π : Measure α) (f : α → ℝ) {b r : ℝ}
    (hb : IsMedian π f b) (hr : 0 ≤ r) :
    π (sqSuperlevel (fun x => negativePartAt b (f x)) r) ≤
      (2 : ℝ≥0∞)⁻¹ := by
  apply measure_sqSuperlevel_le_half_of_support π
    (fun x => negativePartAt b (f x))
    (fun x => negativePartAt_nonneg b (f x))
  · simpa only [negativePartAt_pos_iff] using hb.measure_lt
  · exact hr

end Concrete

end

end UniformRandomMALA
