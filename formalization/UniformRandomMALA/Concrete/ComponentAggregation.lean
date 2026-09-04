import UniformRandomMALA.Concrete.CoareaCauchySchwarz
import UniformRandomMALA.Concrete.ComponentFlow
import UniformRandomMALA.Concrete.MedianDecomposition
import Mathlib.Analysis.MeanInequalities

/-!
# Concrete component aggregation

This file begins the unconditional replacement for the abstract
`ComponentAggregation` field in `AnalyticInterfaces`.  It works directly
with Mathlib probability measures and kernels and keeps all quantities in
`ℝ≥0∞`.

The key proof rewrite is already implemented here: no component is selected
measurably as the superlevel changes.  Instead, the successful-component
bound is relaxed to the sum of every normalized flow, then coarea and
Cauchy--Schwarz are applied component by component.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

namespace Concrete

variable {α : Type*} [MeasurableSpace α]

/-- The finite harmonic cost that appears in the component aggregation
constant. -/
def harmonicCost {N : ℕ} (γ φ : Fin N → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ j, (γ j * (φ j) ^ 2)⁻¹

/-- Layer cake, finite component-flow relaxation, coarea, and edge
Cauchy--Schwarz assembled for one nonnegative function whose squared
superlevels all have mass at most one half. -/
theorem lintegral_sq_le_sum_component_coareaBounds
    {N : ℕ} (π : Measure α) [IsFiniteMeasure π]
    (K : Fin N → Kernel α α) [∀ j, IsMarkovKernel (K j)]
    (hrev : ∀ j, Kernel.IsReversible (K j) π)
    (φ : Fin N → ℝ≥0∞)
    (hφ0 : ∀ j, φ j ≠ 0) (hφtop : ∀ j, φ j ≠ ∞)
    (g : α → ℝ) (hg : Measurable g)
    (hsmall : ∀ r : ℝ, 0 ≤ r →
      π (sqSuperlevel g r) ≤ (2 : ℝ≥0∞)⁻¹)
    (hflow : ∀ A : Set α, MeasurableSet A →
      0 < π A → π A ≤ (2 : ℝ≥0∞)⁻¹ →
      ∃ j : Fin N, φ j * π A ≤ boundaryFlow π (K j) A) :
    (∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂π) ≤
      ∑ j, (φ j)⁻¹ * ((2 : ℝ≥0∞)⁻¹ *
        (((2 : ℝ≥0∞) * Dirichlet.energy π (K j) g) ^ (1 / 2 : ℝ) *
          ((4 : ℝ≥0∞) *
            ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂π) ^ (1 / 2 : ℝ))) := by
  calc
    (∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂π) =
        ∫⁻ r in Set.Ici (0 : ℝ), π (sqSuperlevel g r) ∂volume :=
      lintegral_sq_eq_lintegral_measure_sqSuperlevel π g hg
    _ ≤ ∑ j, (φ j)⁻¹ *
        ∫⁻ r in Set.Ici (0 : ℝ),
          boundaryFlow π (K j) (sqSuperlevel g r) ∂volume :=
      lintegral_measure_sqSuperlevel_le_sum_normalizedFlow
        π K φ hφ0 hφtop g hg hsmall hflow
    _ ≤ ∑ j, (φ j)⁻¹ * ((2 : ℝ≥0∞)⁻¹ *
        (((2 : ℝ≥0∞) * Dirichlet.energy π (K j) g) ^ (1 / 2 : ℝ) *
          ((4 : ℝ≥0∞) *
            ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂π) ^ (1 / 2 : ℝ))) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left
        (coarea_sqSuperlevel_le_energy_secondMoment
          π (K j) (hrev j) g hg) (by positivity)

/-- The preceding one-sided estimate applied to both parts of an actual
median.  This is the exact measurable reduction needed before the final
finite-dimensional harmonic Cauchy--Schwarz arithmetic. -/
theorem medianParts_lintegral_le_sum_component_coareaBounds
    {N : ℕ} (π : Measure α) [IsProbabilityMeasure π]
    (K : Fin N → Kernel α α) [∀ j, IsMarkovKernel (K j)]
    (hrev : ∀ j, Kernel.IsReversible (K j) π)
    (φ : Fin N → ℝ≥0∞)
    (hφ0 : ∀ j, φ j ≠ 0) (hφtop : ∀ j, φ j ≠ ∞)
    (f : α → ℝ) (hf : Measurable f)
    (b : ℝ) (hb : IsMedian π f b)
    (hflow : ∀ A : Set α, MeasurableSet A →
      0 < π A → π A ≤ (2 : ℝ≥0∞)⁻¹ →
      ∃ j : Fin N, φ j * π A ≤ boundaryFlow π (K j) A) :
    let fp : α → ℝ := fun x => positivePartAt b (f x)
    let fn : α → ℝ := fun x => negativePartAt b (f x)
    (∫⁻ x, ENNReal.ofReal (fp x ^ 2) ∂π) ≤
        ∑ j, (φ j)⁻¹ * ((2 : ℝ≥0∞)⁻¹ *
          (((2 : ℝ≥0∞) * Dirichlet.energy π (K j) fp) ^ (1 / 2 : ℝ) *
            ((4 : ℝ≥0∞) *
              ∫⁻ x, ENNReal.ofReal (fp x ^ 2) ∂π) ^ (1 / 2 : ℝ))) ∧
      (∫⁻ x, ENNReal.ofReal (fn x ^ 2) ∂π) ≤
        ∑ j, (φ j)⁻¹ * ((2 : ℝ≥0∞)⁻¹ *
          (((2 : ℝ≥0∞) * Dirichlet.energy π (K j) fn) ^ (1 / 2 : ℝ) *
            ((4 : ℝ≥0∞) *
              ∫⁻ x, ENNReal.ofReal (fn x ^ 2) ∂π) ^ (1 / 2 : ℝ))) := by
  dsimp only
  constructor
  · exact lintegral_sq_le_sum_component_coareaBounds π K hrev φ hφ0 hφtop
      (fun x => positivePartAt b (f x))
      (measurable_positivePartAt hf b)
      (fun r hr => measure_sqSuperlevel_positivePart_le_half π f hb hr)
      hflow
  · exact lintegral_sq_le_sum_component_coareaBounds π K hrev φ hφ0 hφtop
      (fun x => negativePartAt b (f x))
      (measurable_negativePartAt hf b)
      (fun r hr => measure_sqSuperlevel_negativePart_le_half π f hb hr)
      hflow

end Concrete

end

end UniformRandomMALA
