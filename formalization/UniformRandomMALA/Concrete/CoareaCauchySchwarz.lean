import UniformRandomMALA.Concrete.Conductance
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# The Cauchy--Schwarz block after coarea

This module isolates the analytic estimate used by component aggregation.
For a reversible kernel, the coarea integral of the squared superlevel cuts
is controlled by the Dirichlet energy and the stationary second moment.

The proof is deliberately factored into literal algebraic steps:

1. `|a²-b²| = |a-b| |a+b|`;
2. Hölder with exponents `(2,2)` on the stationary edge measure;
3. the first factor is twice the Dirichlet energy;
4. `(a+b)² ≤ 2(a²+b²)` and the two edge marginals are stationary.

No spectral theorem, Hilbert-space operator API, or signed-measure argument
is used.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace Concrete

variable {α : Type*} [MeasurableSpace α]

/-- Removing the factor `1/2` in the definition of Dirichlet energy. -/
theorem lintegral_edgeMeasure_sqDiff_eq_two_mul_energy
    (π : Measure α) [IsFiniteMeasure π]
    (K : Kernel α α) [IsMarkovKernel K]
    (g : α → ℝ) (hg : Measurable g) :
    (∫⁻ z, ENNReal.ofReal ((g z.1 - g z.2) ^ 2) ∂edgeMeasure π K) =
      (2 : ℝ≥0∞) * Dirichlet.energy π K g := by
  rw [energy_eq_edgeMeasure_lintegral π K g hg, ← mul_assoc,
    ENNReal.mul_inv_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞), one_mul]

/-- Cauchy--Schwarz for the factored difference of squares on the edge
measure. -/
theorem lintegral_edgeMeasure_abs_sqDiff_le
    (π : Measure α) [IsFiniteMeasure π]
    (K : Kernel α α) [IsMarkovKernel K]
    (g : α → ℝ) (hg : Measurable g) :
    (∫⁻ z, ENNReal.ofReal |g z.1 ^ 2 - g z.2 ^ 2| ∂edgeMeasure π K) ≤
      ((∫⁻ z, ENNReal.ofReal ((g z.1 - g z.2) ^ 2) ∂edgeMeasure π K) ^
          (1 / 2 : ℝ)) *
        ((∫⁻ z, ENNReal.ofReal ((g z.1 + g z.2) ^ 2) ∂edgeMeasure π K) ^
          (1 / 2 : ℝ)) := by
  let u : α × α → ℝ≥0∞ := fun z =>
    ENNReal.ofReal |g z.1 - g z.2|
  let v : α × α → ℝ≥0∞ := fun z =>
    ENNReal.ofReal |g z.1 + g z.2|
  have hu : Measurable u := by
    exact ENNReal.measurable_ofReal.comp (by
      simpa [Function.comp_apply, Real.norm_eq_abs] using
        ((hg.comp measurable_fst).sub (hg.comp measurable_snd)).norm)
  have hv : Measurable v := by
    exact ENNReal.measurable_ofReal.comp (by
      simpa [Function.comp_apply, Real.norm_eq_abs] using
        ((hg.comp measurable_fst).add (hg.comp measurable_snd)).norm)
  have hfactor (z : α × α) :
      ENNReal.ofReal |g z.1 ^ 2 - g z.2 ^ 2| = u z * v z := by
    dsimp [u, v]
    rw [← Real.enorm_eq_ofReal_abs, ← Real.enorm_eq_ofReal_abs,
      ← Real.enorm_eq_ofReal_abs, ← enorm_mul]
    congr 1
    ring
  have hu_sq (z : α × α) :
      u z ^ (2 : ℝ) = ENNReal.ofReal ((g z.1 - g z.2) ^ 2) := by
    dsimp [u]
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs]
  have hv_sq (z : α × α) :
      v z ^ (2 : ℝ) = ENNReal.ofReal ((g z.1 + g z.2) ^ 2) := by
    dsimp [v]
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs]
  calc
    (∫⁻ z, ENNReal.ofReal |g z.1 ^ 2 - g z.2 ^ 2| ∂edgeMeasure π K) =
        ∫⁻ z, u z * v z ∂edgeMeasure π K := by
      apply lintegral_congr
      exact hfactor
    _ ≤ ((∫⁻ z, u z ^ (2 : ℝ) ∂edgeMeasure π K) ^ (1 / 2 : ℝ)) *
        ((∫⁻ z, v z ^ (2 : ℝ) ∂edgeMeasure π K) ^ (1 / 2 : ℝ)) :=
      ENNReal.lintegral_mul_le_Lp_mul_Lq
        (edgeMeasure π K) Real.HolderConjugate.two_two
        hu.aemeasurable hv.aemeasurable
    _ = ((∫⁻ z, ENNReal.ofReal ((g z.1 - g z.2) ^ 2) ∂edgeMeasure π K) ^
          (1 / 2 : ℝ)) *
        ((∫⁻ z, ENNReal.ofReal ((g z.1 + g z.2) ^ 2) ∂edgeMeasure π K) ^
          (1 / 2 : ℝ)) := by
      simp_rw [hu_sq, hv_sq]

/-- Coarea plus Cauchy--Schwarz, in a form that is valid even when an
integral is infinite. -/
theorem coarea_sqSuperlevel_le_energy_secondMoment
    (π : Measure α) [IsFiniteMeasure π]
    (K : Kernel α α) [IsMarkovKernel K]
    (hrev : Kernel.IsReversible K π)
    (g : α → ℝ) (hg : Measurable g) :
    (∫⁻ r in Set.Ici (0 : ℝ),
        boundaryFlow π K (sqSuperlevel g r) ∂volume) ≤
      (2 : ℝ≥0∞)⁻¹ *
        (((2 : ℝ≥0∞) * Dirichlet.energy π K g) ^ (1 / 2 : ℝ) *
          ((4 : ℝ≥0∞) *
            ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂π) ^ (1 / 2 : ℝ)) := by
  rw [coarea_sqSuperlevel π K hrev g hg]
  gcongr
  calc
    (∫⁻ z, ENNReal.ofReal |g z.1 ^ 2 - g z.2 ^ 2| ∂edgeMeasure π K) ≤
        ((∫⁻ z, ENNReal.ofReal ((g z.1 - g z.2) ^ 2) ∂edgeMeasure π K) ^
            (1 / 2 : ℝ)) *
          ((∫⁻ z, ENNReal.ofReal ((g z.1 + g z.2) ^ 2) ∂edgeMeasure π K) ^
            (1 / 2 : ℝ)) :=
      lintegral_edgeMeasure_abs_sqDiff_le π K g hg
    _ ≤ (((2 : ℝ≥0∞) * Dirichlet.energy π K g) ^ (1 / 2 : ℝ)) *
        (((4 : ℝ≥0∞) *
          ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂π) ^ (1 / 2 : ℝ)) := by
      rw [lintegral_edgeMeasure_sqDiff_eq_two_mul_energy π K g hg]
      gcongr
      exact lintegral_edgeMeasure_sq_add_le_four π K hrev g hg

end Concrete

end

end UniformRandomMALA
