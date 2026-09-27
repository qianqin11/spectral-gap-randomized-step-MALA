import UniformRandomMALA.Concrete.VarianceSeparationFixedStep
import UniformRandomMALA.Concrete.PaperAsymptoticVariance

/-!
# Both sides of the variance comparison

Assertion (i) of Corollary 2.7 (`cor:variance-separation`) is the tuned
randomized bound below. Assertion (ii) is
`exists_universal_fixedStep_variance_separation`, imported from the actual
fixed-step witness construction. Both use the same genuine extended
stationary asymptotic-variance quantity.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace C1Potential

variable {d : ℕ}

theorem varianceSeparation_randomized_upper (V : C1Potential d)
    {f : State d → ℝ} (hf : MemLp f 2 (V.toFirstOrderPotential.target : Measure (State d))) :
    let W := V.toFirstOrderPotential
    let π := (W.target : Measure (State d))
    let K := W.uniformMALA (V.normalizedTunedStep 1) (V.normalizedTunedStep_pos 1 zero_lt_one)
    asymptoticVarianceExtended π K f ≤
      ENNReal.ofReal (normalizedMixingUniversalConstant * V.normalizedMixingScale * variance f π) := by
  dsimp only
  have h := V.stationaryAsymptoticVariance_nonlazy_bounds 1 zero_lt_one hf
  have hid := (ENNReal.tendsto_ofReal h.2.2.2).limsup_eq
  change asymptoticVarianceExtended _ _ _ = _ at hid
  rw [hid]
  apply ENNReal.ofReal_le_ofReal
  simpa only [normalizedMixingConstant, div_one, max_self, mul_one] using h.2.2.1

end C1Potential

/-- Assertion (i) of Corollary 2.7 (`cor:variance-separation`) with a
universal constant chosen before every dimension, potential and observable. -/
theorem exists_universal_varianceSeparation_randomized_upper :
    ∃ C : ℝ, 0 < C ∧
      ∀ {d : ℕ} (V : C1Potential d) (f : State d → ℝ),
        MemLp f 2 (V.toFirstOrderPotential.target : Measure (State d)) →
        asymptoticVarianceExtended
          (V.toFirstOrderPotential.target : Measure (State d))
          (V.toFirstOrderPotential.uniformMALA (V.normalizedTunedStep 1)
            (V.normalizedTunedStep_pos 1 zero_lt_one)) f ≤
          ENNReal.ofReal (C * (V.L / V.m) *
            Real.sqrt ((d : ℝ) * (1 + Real.log (d : ℝ) + Real.log (V.L / V.m))) *
              variance f (V.toFirstOrderPotential.target : Measure (State d))) := by
  refine ⟨normalizedMixingUniversalConstant, normalizedMixingUniversalConstant_pos, ?_⟩
  intro d V f hf
  simpa only [C1Potential.normalizedMixingScale, C1Potential.normalizedMomentThreshold,
    mul_assoc] using V.varianceSeparation_randomized_upper hf

end
end UniformRandomMALA.Concrete
