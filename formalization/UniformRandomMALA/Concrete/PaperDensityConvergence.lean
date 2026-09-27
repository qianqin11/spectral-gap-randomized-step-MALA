import UniformRandomMALA.Concrete.L2DensityEvolution
import UniformRandomMALA.Concrete.C1MainTheorem

/-!
# The density and total-variation convergence bounds for randomized MALA

Equation `eq:TVbound` is instantiated for the actual half-lazy randomized
MALA transition law, using the actual Rayleigh gap. The intermediate
quantity is the RN density of that law, rather than a dual-test surrogate.
-/

namespace UniformRandomMALA.Concrete.C1Potential

open MeasureTheory ProbabilityTheory DiscreteTime
open scoped ENNReal ProbabilityTheory

noncomputable section

variable {d : ℕ}

/-- Both inequalities in `eq:TVbound`, with the actual evolved RN density
and the actual lazy gap, for every positive step range. -/
theorem densityTVConvergence
    (V : C1Potential d) (H : ℝ) (hH : 0 < H)
    (μ : Measure (State d)) [IsProbabilityMeasure μ]
    (hμ : μ ≪ (V.toFirstOrderPotential.target : Measure (State d)))
    (hDensity : MemLp
      (fun x => (μ.rnDeriv (V.toFirstOrderPotential.target : Measure (State d)) x).toReal)
      2 (V.toFirstOrderPotential.target : Measure (State d))) (n : ℕ) :
    let W := V.toFirstOrderPotential
    let π := (W.target : Measure (State d))
    let P := W.lazyUniformMALA H hH
    let ν := finiteKernelIterate P n ∘ₘ μ
    let gap := (rayleighSpectralGap π P).toReal
    (ν ≪ π) ∧ MemLp (fun x => (ν.rnDeriv π x).toReal) 2 π ∧
      setwiseTV ν π ≤ centeredDensityL2Norm ν π / 2 ∧
      centeredDensityL2Norm ν π / 2 ≤
        centeredDensityL2Norm μ π / 2 * (1 - gap) ^ n := by
  let W := V.toFirstOrderPotential
  let π := (W.target : Measure (State d))
  let K := W.uniformMALA H hH
  let : IsMarkovKernel K := W.uniformMALA_isMarkovKernel H hH
  have hrev : Kernel.IsReversible K π := W.uniformMALA_isReversible H hH
  exact densityTV_iterate_halfLazy_actualGap μ π hμ hDensity K hrev n

end
end UniformRandomMALA.Concrete.C1Potential
