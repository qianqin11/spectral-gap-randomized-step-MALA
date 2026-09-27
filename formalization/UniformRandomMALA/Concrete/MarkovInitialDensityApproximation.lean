import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Approximating arbitrary absolutely continuous initial laws

Truncate the actual Radon--Nikodym derivative and normalize the retained
mass. This gives a probability law with bounded density and an exact
positive-measure remainder of arbitrarily small mass. No square-integrability
or boundedness assumption is imposed on the original density.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory Filter Set
open scoped ENNReal Topology

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- The initial law with its actual density capped at the integer `n`. -/
def boundedInitialPart (μ π : Measure α) (n : ℕ) : Measure α :=
  π.withDensity (fun x => min (μ.rnDeriv π x) n)

/-- The nonnegative density discarded by the cap. -/
def initialDensityRemainder (μ π : Measure α) (n : ℕ) : Measure α :=
  π.withDensity (fun x => μ.rnDeriv π x - min (μ.rnDeriv π x) n)

theorem boundedInitialPart_add_remainder
    (μ π : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure π]
    (hμ : μ ≪ π) (n : ℕ) :
    μ = boundedInitialPart μ π n + initialDensityRemainder μ π n := by
  calc
    μ = π.withDensity (μ.rnDeriv π) := (μ.withDensity_rnDeriv_eq π hμ).symm
    _ = _ := ?_
  unfold boundedInitialPart initialDensityRemainder
  rw [← withDensity_add_left ((μ.measurable_rnDeriv π).min measurable_const)]
  apply withDensity_congr_ae
  exact ae_of_all _ fun x => (add_tsub_cancel_of_le (min_le_left (μ.rnDeriv π x) n)).symm

theorem boundedInitialPart_le_nat_smul (μ π : Measure α) (n : ℕ) :
    boundedInitialPart μ π n ≤ (n : ℝ≥0∞) • π := by
  unfold boundedInitialPart
  calc
    _ ≤ π.withDensity (fun _ => (n : ℝ≥0∞)) :=
      withDensity_mono (ae_of_all _ fun x => min_le_right _ _)
    _ = _ := withDensity_const _

theorem initialDensityRemainder_le
    (μ π : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure π]
    (hμ : μ ≪ π) (n : ℕ) : initialDensityRemainder μ π n ≤ μ := by
  calc
    _ ≤ π.withDensity (μ.rnDeriv π) :=
      withDensity_mono (ae_of_all _ fun _ => tsub_le_self)
    _ = _ := μ.withDensity_rnDeriv_eq π hμ

/-- The discarded mass tends to zero for every finite absolutely continuous law. -/
theorem initialDensityRemainder_mass_tendsto_zero
    (μ π : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure π]
    (hμ : μ ≪ π) :
    Tendsto (fun n => initialDensityRemainder μ π n Set.univ) atTop (𝓝 0) := by
  have h := tendsto_lintegral_of_dominated_convergence (μ := π)
    (F := fun n x => μ.rnDeriv π x - min (μ.rnDeriv π x) n)
    (f := fun _ => 0) (μ.rnDeriv π)
    (fun n => (μ.measurable_rnDeriv π).sub
      ((μ.measurable_rnDeriv π).min measurable_const))
    (fun n => ae_of_all _ fun _ => tsub_le_self)
    (by rw [μ.lintegral_rnDeriv hμ]; exact measure_ne_top μ _)
    (by
      filter_upwards [μ.rnDeriv_ne_top π] with x hx
      obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hx
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop N] with n hn
      have hle : μ.rnDeriv π x ≤ (n : ℝ≥0∞) := hN.le.trans (by exact_mod_cast hn)
      simp only [min_eq_left hle, tsub_self])
  simpa only [initialDensityRemainder, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, lintegral_zero] using h

theorem boundedInitialPart_mass_le_one
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsFiniteMeasure π]
    (hμ : μ ≪ π) (n : ℕ) : boundedInitialPart μ π n Set.univ ≤ 1 := by
  have h := congrArg (fun ν : Measure α => ν Set.univ)
    (boundedInitialPart_add_remainder μ π hμ n)
  simp only [measure_univ, Measure.add_apply] at h
  exact (le_add_right le_rfl).trans_eq h.symm

theorem boundedInitialPart_mass_tendsto_one
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsFiniteMeasure π]
    (hμ : μ ≪ π) :
    Tendsto (fun n => boundedInitialPart μ π n Set.univ) atTop (𝓝 1) := by
  have heq (n : ℕ) : boundedInitialPart μ π n Set.univ =
      1 - initialDensityRemainder μ π n Set.univ := by
    apply ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top
    have h := congrArg (fun ν : Measure α => ν Set.univ)
      (boundedInitialPart_add_remainder μ π hμ n)
    simpa only [measure_univ, Measure.add_apply] using h.symm
  simp_rw [heq]
  simpa only [tsub_zero] using
    ENNReal.Tendsto.sub tendsto_const_nhds (initialDensityRemainder_mass_tendsto_zero μ π hμ)
      (Or.inl ENNReal.one_ne_top)

/-- Every absolutely continuous initial probability law is an arbitrarily
accurate mixture of a bounded-density probability law and a finite remainder. -/
theorem exists_bounded_initial_density_approximation
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : μ ≪ π) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (ν ρ : Measure α) (a B : ℝ≥0∞),
      IsProbabilityMeasure ν ∧ ν ≪ π ∧ B ≠ ∞ ∧ ν ≤ B • π ∧
      0 < a ∧ a ≤ 1 ∧ IsFiniteMeasure ρ ∧ μ = a • ν + ρ ∧ ρ Set.univ < ε := by
  have hpos : ∀ᶠ n in atTop, 0 < boundedInitialPart μ π n Set.univ :=
    (boundedInitialPart_mass_tendsto_one μ π hμ).eventually (eventually_gt_nhds zero_lt_one)
  have hsmall : ∀ᶠ n in atTop, initialDensityRemainder μ π n Set.univ < ε :=
    (initialDensityRemainder_mass_tendsto_zero μ π hμ).eventually (eventually_lt_nhds hε)
  obtain ⟨n, hnpos, hnsmall⟩ := (hpos.and hsmall).exists
  let a : ℝ≥0∞ := boundedInitialPart μ π n Set.univ
  let ν : Measure α := a⁻¹ • boundedInitialPart μ π n
  let B : ℝ≥0∞ := a⁻¹ * n
  have ha1 : a ≤ 1 := boundedInitialPart_mass_le_one μ π hμ n
  have hatop : a ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top ha1
  have hν : IsProbabilityMeasure ν := by
    apply isProbabilityMeasure_iff.mpr
    exact ENNReal.inv_mul_cancel hnpos.ne' hatop
  refine ⟨ν, initialDensityRemainder μ π n, a, B, hν,
    (withDensity_absolutelyContinuous π _).smul_left _,
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hnpos.ne') (by simp), ?_, hnpos, ha1,
    isFiniteMeasure_of_le μ (initialDensityRemainder_le μ π hμ n), ?_, hnsmall⟩
  · intro s
    have hbound := boundedInitialPart_le_nat_smul μ π n s
    change a⁻¹ * boundedInitialPart μ π n s ≤ (a⁻¹ * n) * π s
    simpa only [Measure.smul_apply, smul_eq_mul, mul_assoc] using
      mul_le_mul' (le_refl a⁻¹) hbound
  · dsimp only [ν]
    rw [smul_smul, ENNReal.mul_inv_cancel hnpos.ne' hatop, one_smul]
    exact boundedInitialPart_add_remainder μ π hμ n

end
end UniformRandomMALA.Concrete
