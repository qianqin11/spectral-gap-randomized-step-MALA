import UniformRandomMALA.Concrete.MarkovAcceptanceApproximation
import UniformRandomMALA.Concrete.MarkovCLTDistribution
import UniformRandomMALA.Concrete.MarkovCLTPerturbation
import UniformRandomMALA.Concrete.MarkovCLTBurnInNormalization

/-!
# The CLT from every initial probability distribution

A positive chance of an absolutely continuous acceptance eventually
removes the singular part of the initial law. Its small remainder changes
bounded characteristic functions uniformly by a small amount. The finite
initial block vanishes pointwise under square-root normalization, so this
argument requires no moment condition on the initial distribution.
-/

namespace UniformRandomMALA.Concrete
open MeasureTheory ProbabilityTheory Filter DiscreteTime
open scoped ENNReal Topology ProbabilityTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type*} [MeasurableSpace α]

theorem markov_CLT_of_acceptance_approximation
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (K A : Kernel α α) [IsMarkovKernel K]
    (r : α → ℝ≥0∞) (hr : Measurable r) (hr1 : ∀ x, r x < 1)
    (hπ : Kernel.Invariant K π) (hA : ∀ x, A x ≪ π)
    (hdecomp : ∀ x, K x = A x + r x • Measure.dirac x)
    {f : α → ℝ} (hf : Measurable f) {v : ℝ} (hv : 0 ≤ v)
    (hCLT : ∀ (ν : Measure α) [IsProbabilityMeasure ν], ν ≪ π →
      TendstoInDistribution (normalizedMarkovSum f) atTop (id : ℝ → ℝ)
        (fun _ => infiniteMarkovPathLaw ν K) (gaussianReal 0 ⟨v, hv⟩)) :
    TendstoInDistribution (normalizedMarkovSum f) atTop (id : ℝ → ℝ)
      (fun _ => infiniteMarkovPathLaw μ K) (gaussianReal 0 ⟨v, hv⟩) := by
  have hm (n : ℕ) : Measurable (normalizedMarkovSum f n) :=
    measurable_const.mul (Finset.measurable_sum _ fun j _ => hf.comp (measurable_pi_apply j))
  apply tendstoInDistribution_gaussian_of_characteristic
    (fun _ => infiniteMarkovPathLaw μ K) (normalizedMarkovSum f) (fun n => (hm n).aemeasurable) hv
  intro t
  apply tendsto_of_arbitrarily_close_shifted_sequences
  intro ε hε
  obtain ⟨k, ν, a, hν, hνAC, _, ha, hsplit, hsmall⟩ :=
    exists_normalized_accepted_transition_approximation K A μ π r hr hr1 hπ hA hdecomp
      (ENNReal.ofReal_pos.mpr (show 0 < ε / 2 by positivity))
  let := hν
  let μk := finiteKernelIterate K k ∘ₘ μ
  let ρ := rejectionRemainder μ r k
  have hρle : ρ ≤ μk := by
    change rejectionRemainder μ r k ≤ finiteKernelIterate K k ∘ₘ μ
    rw [hsplit]
    intro s
    simp only [Measure.add_apply]
    exact le_add_left le_rfl
  let : IsFiniteMeasure ρ := isFiniteMeasure_of_le μk hρle
  let F (n : ℕ) (path : ℕ → α) : ℂ :=
    Complex.exp (Complex.I * (t * delayedNormalizedMarkovSum f k n path))
  have hF (n : ℕ) : Measurable (F n) := by
    have h := measurable_delayedNormalizedMarkovSum hf k n
    dsimp only [F]
    fun_prop
  have hFbound (n : ℕ) (path : ℕ → α) : ‖F n path‖ ≤ 1 := by
    dsimp only [F]
    rw [Complex.norm_exp]
    simp
  have hνCLT := tendstoInDistribution_delayedNormalizedMarkovSum
    (infiniteMarkovPathLaw ν K) (gaussianReal 0 ⟨v, hv⟩) f k (hCLT ν hνAC)
  have hlimit := characteristic_tendsto_of_tendstoInDistribution_gaussian
    (fun _ => infiniteMarkovPathLaw ν K) (delayedNormalizedMarkovSum f k) hv hνCLT t
  have hprefix := characteristic_expectation_sub_tendsto_zero_of_ae_sub_tendsto
    (infiniteMarkovPathLaw μ K)
    (fun n => normalizedMarkovSum f (n + k))
    (fun n path => delayedNormalizedMarkovSum f k n (markovPathShift k path))
    (fun n => hm (n + k))
    (fun n => (measurable_delayedNormalizedMarkovSum hf k n).comp (measurable_markovPathShift k))
    (ae_of_all _ fun path => normalizedMarkovSum_sub_delayed_tendsto_zero f k path) t
  have hshift (n : ℕ) : (∫ path, F n (markovPathShift k path) ∂infiniteMarkovPathLaw μ K) =
      ∫ path, F n path ∂infiniteMarkovPathLaw μk K := by
    have h := integral_map (measurable_markovPathShift k).aemeasurable (hF n).aestronglyMeasurable
      (μ := infiniteMarkovPathLaw μ K)
    rw [infiniteMarkovPathLaw_shift] at h
    exact h.symm
  have herror : Tendsto (fun n =>
      ‖(∫ path, Complex.exp (Complex.I * (t * normalizedMarkovSum f (n + k) path))
          ∂infiniteMarkovPathLaw μ K) -
        ∫ path, F n path ∂infiniteMarkovPathLaw μk K‖) atTop (𝓝 0) := by
    have h := hprefix.norm
    simpa only [Complex.ofReal_mul, norm_zero, ← hshift, F] using h
  refine ⟨k, (fun n => ∫ path, F n path ∂infiniteMarkovPathLaw ν K),
    (fun n => ‖(∫ path, Complex.exp (Complex.I * (t * normalizedMarkovSum f (n + k) path))
          ∂infiniteMarkovPathLaw μ K) -
        ∫ path, F n path ∂infiniteMarkovPathLaw μk K‖), hlimit, herror, fun n => ?_⟩
  have hb := norm_integral_kernel_sub_le_of_initial_decomposition
    (infiniteMarkovPathKernel K) μk ν ρ a ha hsplit (F n) (hF n) (hFbound n)
  simp only [← infiniteMarkovPathLaw_eq_comp] at hb
  have hρsmall : ρ.real Set.univ < ε / 2 := by
    have ht := (ENNReal.toReal_lt_toReal (measure_ne_top ρ Set.univ) ENNReal.ofReal_ne_top).mpr hsmall
    simpa only [ENNReal.toReal_ofReal (show 0 ≤ ε / 2 by positivity), measureReal_def] using ht
  have htri := dist_triangle
    (∫ path, Complex.exp (Complex.I * (t * normalizedMarkovSum f (n + k) path))
      ∂infiniteMarkovPathLaw μ K)
    (∫ path, F n path ∂infiniteMarkovPathLaw μk K)
    (∫ path, F n path ∂infiniteMarkovPathLaw ν K)
  simp only [dist_eq_norm] at htri
  linarith

end
end UniformRandomMALA.Concrete
