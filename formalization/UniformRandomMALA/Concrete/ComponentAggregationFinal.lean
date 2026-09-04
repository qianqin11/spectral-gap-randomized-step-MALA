import UniformRandomMALA.Concrete.ComponentArithmetic
import UniformRandomMALA.Concrete.Truncation
import UniformRandomMALA.Concrete.SpectralGap

/-!
# Concrete finite-component aggregation

This module closes the concrete replacement for the paper's abstract
`ComponentAggregation` field.  The proof is unconditional at the level of
Mathlib measures and kernels.

The important order of operations is:

1. split a measurable test function at a genuine median;
2. cap each nonnegative median part at a natural level;
3. apply layer cake, finite flow relaxation, coarea, and weighted Hölder;
4. cancel only the finite capped second moment;
5. take the supremum over caps; and
6. recombine the median parts and pass to extended variance.

Thus no `L²` hypothesis, measurable component selection, or cancellation at
`∞` is hidden in the theorem.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

namespace Concrete

variable {α : Type*} [MeasurableSpace α]

/-- The harmonic cost is finite when every component weight and flow
constant is finite and nonzero. -/
theorem harmonicCost_ne_top
    {N : ℕ} (γ φ : Fin N → ℝ≥0∞)
    (hγ0 : ∀ j, γ j ≠ 0) (hφ0 : ∀ j, φ j ≠ 0) :
    harmonicCost γ φ ≠ ∞ := by
  change (∑ j, (γ j * (φ j) ^ 2)⁻¹) ≠ ∞
  rw [ENNReal.sum_ne_top]
  intro j hj
  exact ENNReal.inv_ne_top.mpr
    (mul_ne_zero (hγ0 j) (pow_ne_zero 2 (hφ0 j)))

/-- A nonempty family with finite component parameters has strictly positive
harmonic cost. -/
theorem harmonicCost_ne_zero
    {N : ℕ} (hN : 0 < N) (γ φ : Fin N → ℝ≥0∞)
    (hγtop : ∀ j, γ j ≠ ∞) (hφtop : ∀ j, φ j ≠ ∞) :
    harmonicCost γ φ ≠ 0 := by
  let j : Fin N := ⟨0, hN⟩
  have hbaseTop : γ j * (φ j) ^ 2 ≠ ∞ :=
    ENNReal.mul_ne_top (hγtop j) (ENNReal.pow_ne_top (hφtop j))
  have hterm : 0 < (γ j * (φ j) ^ 2)⁻¹ :=
    pos_iff_ne_zero.mpr (ENNReal.inv_ne_zero.mpr hbaseTop)
  have hle : (γ j * (φ j) ^ 2)⁻¹ ≤
      ∑ i, (γ i * (φ i) ^ 2)⁻¹ :=
    Finset.single_le_sum
      (f := fun i : Fin N => (γ i * (φ i) ^ 2)⁻¹)
      (fun _ _ => bot_le) (Finset.mem_univ j)
  exact ne_of_gt (hterm.trans_le hle)

/-- The one-sided aggregation estimate for a nonnegative function supported
on a set of mass at most one half.  Natural caps make every cancellation
finite, and monotone convergence removes the cap. -/
theorem lintegral_sq_le_two_harmonic_mul_energy
    {N : ℕ} (π : Measure α) [IsProbabilityMeasure π]
    (P : Kernel α α) [IsMarkovKernel P]
    (K : Fin N → Kernel α α) [hK : ∀ j, IsMarkovKernel (K j)]
    (hrev : ∀ j, Kernel.IsReversible (K j) π)
    (γ φ : Fin N → ℝ≥0∞)
    (hγ0 : ∀ j, γ j ≠ 0) (hγtop : ∀ j, γ j ≠ ∞)
    (hφ0 : ∀ j, φ j ≠ 0) (hφtop : ∀ j, φ j ≠ ∞)
    (hdom : ∀ u : α → ℝ, Measurable u →
      (∑ j, γ j * Dirichlet.energy π (K j) u) ≤
        Dirichlet.energy π P u)
    (hflow : ∀ A : Set α, MeasurableSet A →
      0 < π A → π A ≤ (2 : ℝ≥0∞)⁻¹ →
      ∃ j : Fin N, φ j * π A ≤ boundaryFlow π (K j) A)
    (g : α → ℝ) (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (hsupport : π {x | 0 < g x} ≤ (2 : ℝ≥0∞)⁻¹) :
    (∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂π) ≤
      (2 : ℝ≥0∞) * harmonicCost γ φ * Dirichlet.energy π P g := by
  rw [lintegral_sq_eq_iSup_lintegral_sq_capAt_nat π g hg hg0]
  apply iSup_le
  intro n
  let gn : α → ℝ := capAt (n : ℝ) g
  have hgn : Measurable gn := measurable_capAt hg (n : ℝ)
  have hgn0 : ∀ x, 0 ≤ gn x := fun x =>
    capAt_nonneg hg0 (Nat.cast_nonneg n) x
  have hsupportCap : π {x | 0 < gn x} ≤ (2 : ℝ≥0∞)⁻¹ :=
    (measure_pos_capAt_nat_le π g n).trans hsupport
  have hsmall : ∀ r : ℝ, 0 ≤ r →
      π (sqSuperlevel gn r) ≤ (2 : ℝ≥0∞)⁻¹ := fun r hr =>
    measure_sqSuperlevel_le_half_of_support π gn hgn0 hsupportCap hr
  have hraw := lintegral_sq_le_sum_component_coareaBounds
    π K hrev φ hφ0 hφtop gn hgn hsmall hflow
  have henergy :
      (∑ j, γ j * Dirichlet.energy π (K j) gn) ≤
        Dirichlet.energy π P g := by
    exact (hdom gn hgn).trans (energy_capAt_le π P g hg (n : ℝ))
  exact coarea_component_sum_cancel γ φ
    (fun j => Dirichlet.energy π (K j) gn)
    hγ0 hγtop hφ0 hφtop
    (lintegral_sq_capAt_nat_ne_top π g hg0 n) hraw henergy

/-- Median splitting turns the one-sided estimate into an extended-variance
bound for every measurable real function. -/
theorem evariance_le_two_harmonic_mul_energy
    {N : ℕ} (π : Measure α) [IsProbabilityMeasure π]
    (P : Kernel α α) [IsMarkovKernel P]
    (K : Fin N → Kernel α α) [hK : ∀ j, IsMarkovKernel (K j)]
    (hrev : ∀ j, Kernel.IsReversible (K j) π)
    (γ φ : Fin N → ℝ≥0∞)
    (hγ0 : ∀ j, γ j ≠ 0) (hγtop : ∀ j, γ j ≠ ∞)
    (hφ0 : ∀ j, φ j ≠ 0) (hφtop : ∀ j, φ j ≠ ∞)
    (hdom : ∀ u : α → ℝ, Measurable u →
      (∑ j, γ j * Dirichlet.energy π (K j) u) ≤
        Dirichlet.energy π P u)
    (hflow : ∀ A : Set α, MeasurableSet A →
      0 < π A → π A ≤ (2 : ℝ≥0∞)⁻¹ →
      ∃ j : Fin N, φ j * π A ≤ boundaryFlow π (K j) A)
    (f : α → ℝ) (hf : Measurable f) :
    evariance f π ≤
      (2 : ℝ≥0∞) * harmonicCost γ φ * Dirichlet.energy π P f := by
  obtain ⟨b, hb⟩ := exists_isMedian π f hf
  let fp : α → ℝ := fun x => positivePartAt b (f x)
  let fn : α → ℝ := fun x => negativePartAt b (f x)
  have hfp : Measurable fp := measurable_positivePartAt hf b
  have hfn : Measurable fn := measurable_negativePartAt hf b
  have hfp0 : ∀ x, 0 ≤ fp x := fun x => positivePartAt_nonneg b (f x)
  have hfn0 : ∀ x, 0 ≤ fn x := fun x => negativePartAt_nonneg b (f x)
  have hfpSupport : π {x | 0 < fp x} ≤ (2 : ℝ≥0∞)⁻¹ := by
    simpa only [fp, positivePartAt_pos_iff] using hb.measure_gt
  have hfnSupport : π {x | 0 < fn x} ≤ (2 : ℝ≥0∞)⁻¹ := by
    simpa only [fn, negativePartAt_pos_iff] using hb.measure_lt
  have hfpBound := lintegral_sq_le_two_harmonic_mul_energy
    π P K hrev γ φ hγ0 hγtop hφ0 hφtop hdom hflow
    fp hfp hfp0 hfpSupport
  have hfnBound := lintegral_sq_le_two_harmonic_mul_energy
    π P K hrev γ φ hγ0 hγtop hφ0 hφtop hdom hflow
    fn hfn hfn0 hfnSupport
  calc
    evariance f π ≤
        ∫⁻ x, ENNReal.ofReal ((f x - b) ^ 2) ∂π :=
      evariance_le_lintegral_sq_sub π f hf b
    _ = (∫⁻ x, ENNReal.ofReal (fp x ^ 2) ∂π) +
        ∫⁻ x, ENNReal.ofReal (fn x ^ 2) ∂π := by
      simpa only [fp, fn] using
        lintegral_sq_sub_eq_add_medianParts π f hf b
    _ ≤ ((2 : ℝ≥0∞) * harmonicCost γ φ *
          Dirichlet.energy π P fp) +
        ((2 : ℝ≥0∞) * harmonicCost γ φ *
          Dirichlet.energy π P fn) := add_le_add hfpBound hfnBound
    _ = (2 : ℝ≥0∞) * harmonicCost γ φ *
        (Dirichlet.energy π P fp + Dirichlet.energy π P fn) := by
      rw [mul_add]
    _ ≤ (2 : ℝ≥0∞) * harmonicCost γ φ *
        Dirichlet.energy π P f :=
      mul_le_mul_of_nonneg_left
        (energy_medianParts_le π P f hf b) (by positivity)

/-- The reciprocal harmonic constant as an explicit concrete Poincaré lower
bound.  Naming this intermediate proposition keeps the final use of the
variational spectral-gap definition trivial. -/
theorem componentAggregation_poincareLower
    {N : ℕ} (hN : 0 < N)
    (π : Measure α) [IsProbabilityMeasure π]
    (P : Kernel α α) [IsMarkovKernel P]
    (K : Fin N → Kernel α α) [hK : ∀ j, IsMarkovKernel (K j)]
    (hrev : ∀ j, Kernel.IsReversible (K j) π)
    (γ φ : Fin N → ℝ≥0∞)
    (hγ0 : ∀ j, γ j ≠ 0) (hγtop : ∀ j, γ j ≠ ∞)
    (hφ0 : ∀ j, φ j ≠ 0) (hφtop : ∀ j, φ j ≠ ∞)
    (hdom : ∀ u : α → ℝ, Measurable u →
      (∑ j, γ j * Dirichlet.energy π (K j) u) ≤
        Dirichlet.energy π P u)
    (hflow : ∀ A : Set α, MeasurableSet A →
      0 < π A → π A ≤ (2 : ℝ≥0∞)⁻¹ →
      ∃ j : Fin N, φ j * π A ≤ boundaryFlow π (K j) A) :
    PoincareLower π P (((2 : ℝ≥0∞) * harmonicCost γ φ)⁻¹) := by
  intro f hf
  let C : ℝ≥0∞ := (2 : ℝ≥0∞) * harmonicCost γ φ
  have hH0 : harmonicCost γ φ ≠ 0 :=
    harmonicCost_ne_zero hN γ φ hγtop hφtop
  have hHtop : harmonicCost γ φ ≠ ∞ :=
    harmonicCost_ne_top γ φ hγ0 hφ0
  have hC0 : C ≠ 0 :=
    mul_ne_zero (by norm_num) hH0
  have hCtop : C ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) hHtop
  have hvar := evariance_le_two_harmonic_mul_energy
    π P K hrev γ φ hγ0 hγtop hφ0 hφtop hdom hflow f hf
  change C⁻¹ * evariance f π ≤ Dirichlet.energy π P f
  calc
    C⁻¹ * evariance f π ≤
        C⁻¹ * (C * Dirichlet.energy π P f) :=
      mul_le_mul_of_nonneg_left hvar (by positivity)
    _ = Dirichlet.energy π P f :=
      ENNReal.inv_mul_cancel_left hC0 hCtop

/-- Concrete finite-component aggregation: the reciprocal harmonic constant
lies below the concrete spectral gap. -/
theorem componentAggregation_le_spectralGap
    {N : ℕ} (hN : 0 < N)
    (π : Measure α) [IsProbabilityMeasure π]
    (P : Kernel α α) [IsMarkovKernel P]
    (K : Fin N → Kernel α α) [hK : ∀ j, IsMarkovKernel (K j)]
    (hrev : ∀ j, Kernel.IsReversible (K j) π)
    (γ φ : Fin N → ℝ≥0∞)
    (hγ0 : ∀ j, γ j ≠ 0) (hγtop : ∀ j, γ j ≠ ∞)
    (hφ0 : ∀ j, φ j ≠ 0) (hφtop : ∀ j, φ j ≠ ∞)
    (hdom : ∀ u : α → ℝ, Measurable u →
      (∑ j, γ j * Dirichlet.energy π (K j) u) ≤
        Dirichlet.energy π P u)
    (hflow : ∀ A : Set α, MeasurableSet A →
      0 < π A → π A ≤ (2 : ℝ≥0∞)⁻¹ →
      ∃ j : Fin N, φ j * π A ≤ boundaryFlow π (K j) A) :
    ((2 : ℝ≥0∞) * harmonicCost γ φ)⁻¹ ≤ spectralGap π P := by
  exact le_spectralGap π P
    (componentAggregation_poincareLower hN π P K hrev γ φ
      hγ0 hγtop hφ0 hφtop hdom hflow)

end Concrete

end

end UniformRandomMALA
