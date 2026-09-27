import UniformRandomMALA.Concrete.MarkovCLTInitialTransfer
import UniformRandomMALA.Concrete.MarkovCLTBoundary
import UniformRandomMALA.Concrete.MarkovInfiniteInitial

/-!
# Characteristic limits for every absolutely continuous initial law

Bounded initial densities suffice: truncation of the actual Radon–Nikodym
derivative and uniform path-kernel comparison remove the boundedness
assumption without imposing an initial moment condition.
-/

namespace UniformRandomMALA.Concrete
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
noncomputable section
variable {α : Type*} [MeasurableSpace α]

theorem markov_characteristic_tendsto_of_bounded_initial
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : μ ≪ π) (K : Kernel α α) [IsMarkovKernel K]
    {f : α → ℝ} (hf : Measurable f) (z : ℝ → ℂ)
    (hlimit : ∀ (ν : Measure α), IsProbabilityMeasure ν →
      ∀ B : ℝ≥0∞, B ≠ ∞ → ν ≤ B • π → ∀ t : ℝ,
      Tendsto (fun n => ∫ path, Complex.exp (Complex.I * (t * normalizedMarkovSum f n path))
        ∂infiniteMarkovPathLaw ν K) atTop (𝓝 (z t))) :
    ∀ t : ℝ, Tendsto
      (fun n => ∫ path, Complex.exp (Complex.I * (t * normalizedMarkovSum f n path))
        ∂infiniteMarkovPathLaw μ K) atTop (𝓝 (z t)) := by
  intro t
  have hm (n : ℕ) : Measurable (normalizedMarkovSum f n) :=
    measurable_const.mul (Finset.measurable_sum _ fun k _ => hf.comp (measurable_pi_apply k))
  have h := integral_kernel_tendsto_of_bounded_initial_density μ π hμ
    (fun _ => infiniteMarkovPathKernel K)
    (fun n path => Complex.exp (Complex.I * (t * normalizedMarkovSum f n path)))
    (fun n => by fun_prop)
    (fun n path => by rw [Complex.norm_exp]; simp) (z t) ?_
  · simpa only [← infiniteMarkovPathLaw_eq_comp] using h
  · intro ν hν B hB hνB
    simpa only [← infiniteMarkovPathLaw_eq_comp] using hlimit ν hν B hB hνB t

end
end UniformRandomMALA.Concrete
