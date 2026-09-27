import UniformRandomMALA.Concrete.NonstationaryMSEPath
import UniformRandomMALA.Concrete.MartingaleCLTLimitAux
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Uniform comparison of characteristic functions across initial laws

An exact probability-mixture decomposition controls every bounded test
function, uniformly over the number of Markov transitions. This lets a
limit theorem pass through approximations of the initial distribution.
-/

namespace UniformRandomMALA.Concrete
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
noncomputable section

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem norm_integral_sub_le_of_probability_decomposition
    (μ ν ρ : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsFiniteMeasure ρ] (a : ℝ≥0∞) (ha : a ≤ 1) (hdecomp : μ = a • ν + ρ)
    (f : α → ℂ) (hf : Measurable f) (hbound : ∀ x, ‖f x‖ ≤ 1) :
    ‖(∫ x, f x ∂μ) - ∫ x, f x ∂ν‖ ≤ 2 * ρ.real Set.univ := by
  have hatop : a ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top ha
  have haReal : a.toReal ≤ 1 := by simpa using ENNReal.toReal_mono ENNReal.one_ne_top ha
  have hiν : Integrable f ν := (integrable_const (1 : ℝ)).mono'
    hf.aestronglyMeasurable (ae_of_all _ hbound)
  have hiρ : Integrable f ρ := (integrable_const (1 : ℝ)).mono'
    hf.aestronglyMeasurable (ae_of_all _ hbound)
  have hmass : a.toReal + ρ.real Set.univ = 1 := by
    have h := congrArg (fun m : Measure α => m Set.univ) hdecomp
    simp only [measure_univ, Measure.add_apply, Measure.smul_apply, smul_eq_mul, mul_one] at h
    have ht := congrArg ENNReal.toReal h
    simpa only [ENNReal.toReal_one, ENNReal.toReal_add hatop (measure_ne_top ρ Set.univ),
      measureReal_def] using ht.symm
  have hnν : ‖∫ x, f x ∂ν‖ ≤ 1 := by
    simpa using norm_integral_le_of_norm_le_const (μ := ν) (ae_of_all _ hbound)
  have hnρ : ‖∫ x, f x ∂ρ‖ ≤ ρ.real Set.univ := by
    simpa using norm_integral_le_of_norm_le_const (μ := ρ) (ae_of_all _ hbound)
  rw [hdecomp, integral_add_measure (hiν.smul_measure hatop) hiρ, integral_smul_measure]
  have heq : a.toReal • (∫ x, f x ∂ν) + (∫ x, f x ∂ρ) - (∫ x, f x ∂ν) =
      (a.toReal - 1) • (∫ x, f x ∂ν) + (∫ x, f x ∂ρ) := by
    rw [sub_smul, one_smul]
    abel
  rw [heq]
  calc
    _ ≤ ‖(a.toReal - 1) • (∫ x, f x ∂ν)‖ + ‖∫ x, f x ∂ρ‖ := norm_add_le _ _
    _ = (1 - a.toReal) * ‖∫ x, f x ∂ν‖ + ‖∫ x, f x ∂ρ‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr haReal)]
      ring
    _ ≤ (1 - a.toReal) * 1 + ρ.real Set.univ :=
      add_le_add (mul_le_mul_of_nonneg_left hnν (sub_nonneg.mpr haReal)) hnρ
    _ = 2 * ρ.real Set.univ := by linarith

theorem norm_integral_kernel_sub_le_of_initial_decomposition
    (K : Kernel α β) [IsMarkovKernel K]
    (μ ν ρ : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsFiniteMeasure ρ] (a : ℝ≥0∞) (ha : a ≤ 1) (hdecomp : μ = a • ν + ρ)
    (f : β → ℂ) (hf : Measurable f) (hbound : ∀ x, ‖f x‖ ≤ 1) :
    ‖(∫ x, f x ∂(K ∘ₘ μ)) - ∫ x, f x ∂(K ∘ₘ ν)‖ ≤ 2 * ρ.real Set.univ := by
  have hdecomp' : K ∘ₘ μ = a • (K ∘ₘ ν) + K ∘ₘ ρ := by
    rw [hdecomp, Measure.comp_add, Measure.comp_smul]
  have h := norm_integral_sub_le_of_probability_decomposition
    (K ∘ₘ μ) (K ∘ₘ ν) (K ∘ₘ ρ) a ha hdecomp' f hf hbound
  simpa only [measureReal_def, Measure.comp_apply_univ] using h

/-- A common limit persists under arbitrarily accurate uniform approximations.
The approximating sequence can depend on the requested accuracy. -/
theorem tendsto_of_arbitrarily_close_convergent_sequences
    {z : ℕ → ℂ} {w : ℂ}
    (happrox : ∀ ε > 0, ∃ v : ℕ → ℂ,
      Tendsto v atTop (𝓝 w) ∧ ∀ n, ‖z n - v n‖ ≤ ε) :
    Tendsto z atTop (𝓝 w) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨v, hv, hvbound⟩ := happrox (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hv (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have htri := dist_triangle (z n) (v n) w
  have hbound : dist (z n) (v n) ≤ ε / 2 := by simpa only [dist_eq_norm] using hvbound n
  linarith [hN n hn]

/-- Finite shifts may depend on the approximation accuracy. The vanishing
error also covers the contribution of the observations before the shift. -/
theorem tendsto_of_arbitrarily_close_shifted_sequences
    {z : ℕ → ℂ} {w : ℂ}
    (happrox : ∀ ε > 0, ∃ (k : ℕ) (v : ℕ → ℂ) (e : ℕ → ℝ),
      Tendsto v atTop (𝓝 w) ∧ Tendsto e atTop (𝓝 0) ∧
      ∀ n, ‖z (n + k) - v n‖ ≤ ε + e n) :
    Tendsto z atTop (𝓝 w) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, v, e, hv, he, hbound⟩ := happrox (ε / 3) (by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hv (ε / 3) (by positivity)
  obtain ⟨M, hM⟩ := eventually_atTop.mp (he.eventually (eventually_lt_nhds (show 0 < ε / 3 by positivity)))
  refine ⟨max N M + k, fun n hn => ?_⟩
  have hNk : N ≤ n - k := by omega
  have hMk : M ≤ n - k := by omega
  have hnk : n - k + k = n := by omega
  have hb := hbound (n - k)
  rw [hnk] at hb
  have htri := dist_triangle (z n) (v (n - k)) w
  simp only [dist_eq_norm] at htri ⊢
  have hv' := hN (n - k) hNk
  rw [dist_eq_norm] at hv'
  linarith [hM (n - k) hMk]

end
end UniformRandomMALA.Concrete
