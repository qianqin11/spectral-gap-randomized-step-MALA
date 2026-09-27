import UniformRandomMALA.Concrete.MarkovCLTVariance
import UniformRandomMALA.Concrete.MarkovErgodicL1Limit

/-! # The actual conditional variance satisfies the ergodic hypothesis -/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal ProbabilityTheory

noncomputable section
variable {α : Type*} [MeasurableSpace α]

theorem poissonIncrement_stronglyMeasurable
    (K : Kernel α α) [IsSFiniteKernel K] {u : α → ℝ} (hu : StronglyMeasurable u) :
    StronglyMeasurable (fun z : α × α => poissonIncrement K u z.1 z.2) := by
  exact (hu.comp_measurable measurable_snd).sub
    (hu.integral_kernel.comp_measurable measurable_fst)

theorem poissonConditionalVariance_measurable
    (K : Kernel α α) [IsSFiniteKernel K] {u : α → ℝ} (hu : StronglyMeasurable u) :
    Measurable (poissonConditionalVariance K u) := by
  exact ((poissonIncrement_stronglyMeasurable K hu).pow 2).integral_kernel_prod_right'.measurable

/-- This is the conditional-variance LLN required by the martingale
CLT, proved for the actual Markov trajectory law and the actual Poisson
increment. No separate ergodicity certificate is assumed. -/
theorem poissonConditionalVariance_meanAbsoluteError_tendsto_zero
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    (u : Lp ℝ 2 π) {g : ℝ} (hg : 0 < g) (hg2 : g ≤ 2)
    (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π K) :
    Tendsto (stationaryMeanAbsoluteError π K (poissonConditionalVariance K u))
      atTop (𝓝 0) :=
  stationaryMeanAbsoluteError_tendsto_zero_L1 π K hπ
    (poissonConditionalVariance_measurable K (Lp.stronglyMeasurable u))
    (poissonConditionalVariance_integrable π K hπ (Lp.memLp u)) hg hg2 hgap

end
end UniformRandomMALA.Concrete
