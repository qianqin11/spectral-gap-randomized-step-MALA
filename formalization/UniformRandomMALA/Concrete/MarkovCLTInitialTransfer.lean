import UniformRandomMALA.Concrete.MarkovCLTApproximation
import UniformRandomMALA.Concrete.MarkovInitialDensityApproximation

/-!
# Passing bounded tests from bounded densities to all absolutely continuous starts

The approximation is uniform in the transition kernel and test function.
In particular, the path length and the characteristic-function argument
may vary with the sequence index.
-/

namespace UniformRandomMALA.Concrete
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
noncomputable section
variable {α : Type*} [MeasurableSpace α]
variable {β : ℕ → Type*} [∀ n, MeasurableSpace (β n)]

theorem integral_kernel_tendsto_of_bounded_initial_density
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : μ ≪ π) (P : (n : ℕ) → Kernel α (β n)) [∀ n, IsMarkovKernel (P n)]
    (F : (n : ℕ) → β n → ℂ) (hF : ∀ n, Measurable (F n))
    (hbound : ∀ n x, ‖F n x‖ ≤ 1) (z : ℂ)
    (hlimit : ∀ (ν : Measure α), IsProbabilityMeasure ν →
      ∀ B : ℝ≥0∞, B ≠ ∞ → ν ≤ B • π →
      Tendsto (fun n => ∫ x, F n x ∂(P n ∘ₘ ν)) atTop (𝓝 z)) :
    Tendsto (fun n => ∫ x, F n x ∂(P n ∘ₘ μ)) atTop (𝓝 z) := by
  apply tendsto_of_arbitrarily_close_convergent_sequences
  intro ε hε
  obtain ⟨ν, ρ, a, B, hν, _, hB, hνB, _, ha, hρ, heq, hsmall⟩ :=
    exists_bounded_initial_density_approximation μ π hμ
      (ENNReal.ofReal_pos.mpr (show 0 < ε / 2 by positivity))
  let := hν
  let := hρ
  refine ⟨fun n => ∫ x, F n x ∂(P n ∘ₘ ν), hlimit ν hν B hB hνB, fun n => ?_⟩
  have h := norm_integral_kernel_sub_le_of_initial_decomposition
    (P n) μ ν ρ a ha heq (F n) (hF n) (hbound n)
  have hr : ρ.real Set.univ < ε / 2 := by
    have ht := (ENNReal.toReal_lt_toReal (measure_ne_top ρ Set.univ) ENNReal.ofReal_ne_top).mpr hsmall
    simpa only [ENNReal.toReal_ofReal (show 0 ≤ ε / 2 by positivity), measureReal_def] using ht
  linarith

end
end UniformRandomMALA.Concrete
