import UniformRandomMALA.Concrete.VarianceSeparationHilbert
import UniformRandomMALA.Concrete.StationaryVarianceGeneral

/-!
# Reciprocal-energy lower bound for actual stationary variance

Under a positive right gap, the Poisson lower bound applies to the proved
limit of the actual stationary path variance.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory KernelLp
open scoped ENNReal ProbabilityTheory RealInnerProductSpace

noncomputable section
variable {α : Type*} [MeasurableSpace α]

theorem centeredOperator_isSymmetric (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hrev : Kernel.IsReversible K π) :
    (centeredOperator K π hrev.invariant).toLinearMap.IsSymmetric := by
  intro f u
  change ⟪operator K π hrev.invariant 2 (by norm_num) (f : Lp ℝ 2 π),
      (u : Lp ℝ 2 π)⟫ =
    ⟪(f : Lp ℝ 2 π), operator K π hrev.invariant 2 (by norm_num) (u : Lp ℝ 2 π)⟫
  exact operator_isSymmetric K π hrev _ _

/-- The actual asymptotic variance of a unit centered observable is bounded
below by the reciprocal of its actual Dirichlet energy. -/
theorem stationaryAsymptoticVariance_centered_lower
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hrev : Kernel.IsReversible K π)
    (f : centeredL2 π) (hf : ‖f‖ = 1) {g : ℝ} (hg : 0 < g) (hg2 : g ≤ 2)
    (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π K) :
    0 < ⟪f, f - centeredOperator K π hrev.invariant f⟫ ∧
      2 / ⟪f, f - centeredOperator K π hrev.invariant f⟫ - 1 ≤
        stationaryAsymptoticVariance π K (f : Lp ℝ 2 π) := by
  rw [stationaryAsymptoticVariance_centered_eq π K hrev.invariant f hg hg2 hgap]
  exact poissonResolvent_variance_lower (centeredOperator K π hrev.invariant)
    (norm_centeredOperator_le K π hrev.invariant) (centeredOperator_isSymmetric π K hrev)
    f hf hg hg2 (centeredOperator_rightGap K π hrev.invariant hg.le hgap)

end
end UniformRandomMALA.Concrete
