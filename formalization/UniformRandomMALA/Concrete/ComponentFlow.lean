import UniformRandomMALA.Concrete.LayerCake

/-!
# Finite component-flow aggregation

The paper says that, for every cut, at least one component kernel supplies a
flow lower bound.  Choosing such a component as a function of the level would
create an avoidable measurable-selection obligation.  For finitely many
components we instead use the pointwise relaxation

`π(S) ≤ ∑ j φ_j⁻¹ Q_j(S,Sᶜ)`.

This loses nothing in the eventual harmonic Cauchy--Schwarz estimate and
requires only finite sums of measurable nonnegative functions.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

namespace Concrete

variable {α : Type*} [MeasurableSpace α]

/-- A single successful component implies the normalized finite-sum flow
bound. -/
theorem measure_le_sum_inv_mul_boundaryFlow
    {N : ℕ} (π : Measure α) (K : Fin N → Kernel α α)
    (φ : Fin N → ℝ≥0∞)
    (hφ0 : ∀ j, φ j ≠ 0) (hφtop : ∀ j, φ j ≠ ∞)
    (A : Set α)
    (hflow : ∃ j : Fin N,
      φ j * π A ≤ boundaryFlow π (K j) A) :
    π A ≤ ∑ j, (φ j)⁻¹ * boundaryFlow π (K j) A := by
  obtain ⟨j, hj⟩ := hflow
  calc
    π A = (φ j)⁻¹ * (φ j * π A) := by
      rw [← mul_assoc,
        ENNReal.inv_mul_cancel (hφ0 j) (hφtop j), one_mul]
    _ ≤ (φ j)⁻¹ * boundaryFlow π (K j) A :=
      mul_le_mul_of_nonneg_left hj (by positivity)
    _ ≤ ∑ i, (φ i)⁻¹ * boundaryFlow π (K i) A :=
      Finset.single_le_sum
        (f := fun i : Fin N => (φ i)⁻¹ * boundaryFlow π (K i) A)
        (fun _ _ => bot_le) (Finset.mem_univ j)

/-- Integrating the pointwise finite-sum relaxation over squared
superlevels.  The hypotheses are stated only for positive-mass cuts, since
the zero-mass case is automatic. -/
theorem lintegral_measure_sqSuperlevel_le_sum_normalizedFlow
    {N : ℕ} (π : Measure α) [IsFiniteMeasure π]
    (K : Fin N → Kernel α α) [∀ j, IsMarkovKernel (K j)]
    (φ : Fin N → ℝ≥0∞)
    (hφ0 : ∀ j, φ j ≠ 0) (hφtop : ∀ j, φ j ≠ ∞)
    (g : α → ℝ) (hg : Measurable g)
    (hsmall : ∀ r : ℝ, 0 ≤ r →
      π (sqSuperlevel g r) ≤ (2 : ℝ≥0∞)⁻¹)
    (hflow : ∀ A : Set α, MeasurableSet A →
      0 < π A → π A ≤ (2 : ℝ≥0∞)⁻¹ →
      ∃ j : Fin N, φ j * π A ≤ boundaryFlow π (K j) A) :
    (∫⁻ r in Set.Ici (0 : ℝ), π (sqSuperlevel g r) ∂volume) ≤
      ∑ j, (φ j)⁻¹ *
        ∫⁻ r in Set.Ici (0 : ℝ),
          boundaryFlow π (K j) (sqSuperlevel g r) ∂volume := by
  have hmeas (j : Fin N) : Measurable (fun r : ℝ =>
      (φ j)⁻¹ * boundaryFlow π (K j) (sqSuperlevel g r)) :=
    measurable_const.mul (measurable_boundaryFlow_sqSuperlevel π (K j) g hg)
  calc
    (∫⁻ r in Set.Ici (0 : ℝ), π (sqSuperlevel g r) ∂volume) ≤
        ∫⁻ r in Set.Ici (0 : ℝ),
          ∑ j, (φ j)⁻¹ * boundaryFlow π (K j) (sqSuperlevel g r) ∂volume := by
      apply setLIntegral_mono' measurableSet_Ici
      intro r hr
      by_cases hz : π (sqSuperlevel g r) = 0
      · simp [hz]
      · exact measure_le_sum_inv_mul_boundaryFlow π K φ hφ0 hφtop
          (sqSuperlevel g r)
          (hflow (sqSuperlevel g r) (measurableSet_sqSuperlevel hg r)
            (pos_iff_ne_zero.mpr hz) (hsmall r hr))
    _ = ∑ j, ∫⁻ r in Set.Ici (0 : ℝ),
          (φ j)⁻¹ * boundaryFlow π (K j) (sqSuperlevel g r) ∂volume := by
      rw [lintegral_finsetSum Finset.univ]
      intro j hj
      exact hmeas j
    _ = ∑ j, (φ j)⁻¹ *
        ∫⁻ r in Set.Ici (0 : ℝ),
          boundaryFlow π (K j) (sqSuperlevel g r) ∂volume := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (hφ0 j))]

end Concrete

end

end UniformRandomMALA
