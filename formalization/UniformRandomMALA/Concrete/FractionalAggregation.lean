import UniformRandomMALA.Concrete.ComponentAggregationFinal
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Fractional finite-component aggregation

This module proves the fractional aggregation lemma used in the paper.  In
contrast to the hard-assignment theorem in `ComponentAggregationFinal`, a cut
may receive simultaneous flow contributions from every component, with
nonnegative coefficients `β j` that are allowed to vanish.  The energy
domination hypothesis has exactly `L²` scope.  The proof applies it only to
bounded truncations and then removes the truncation by monotone convergence.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

namespace Concrete

variable {α : Type*} [MeasurableSpace α]

/-- The fractional aggregation cost `∑ j, β_j² / γ_j`. -/
def fractionalCost {N : ℕ} (γ β : Fin N → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ j, (β j) ^ 2 / γ j

/-- Weighted Cauchy--Schwarz in the fractional form.  The coefficients `β`
may vanish; only the energy weights `γ` must be finite and strictly positive.
-/
theorem fractional_weighted_sqrt_sum_le
    {N : ℕ} (γ β E : Fin N → ℝ≥0∞)
    (hγ0 : ∀ j, γ j ≠ 0) (hγtop : ∀ j, γ j ≠ ∞) :
    (∑ j, β j * (E j) ^ (1 / 2 : ℝ)) ≤
      (∑ j, γ j * E j) ^ (1 / 2 : ℝ) *
        (fractionalCost γ β) ^ (1 / 2 : ℝ) := by
  let F : Fin N → ℝ≥0∞ := fun j => (γ j * E j) ^ (1 / 2 : ℝ)
  let G : Fin N → ℝ≥0∞ := fun j => ((β j) ^ 2 / γ j) ^ (1 / 2 : ℝ)
  have hFtwo (j : Fin N) : F j ^ (2 : ℝ) = γ j * E j := by
    dsimp [F]
    rw [← ENNReal.rpow_mul]
    norm_num
  have hGtwo (j : Fin N) : G j ^ (2 : ℝ) = (β j) ^ 2 / γ j := by
    dsimp [G]
    rw [← ENNReal.rpow_mul]
    norm_num
  have hFG (j : Fin N) : F j * G j = β j * (E j) ^ (1 / 2 : ℝ) := by
    dsimp [F, G]
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [div_eq_mul_inv]
    have hcancel : γ j * (γ j)⁻¹ = 1 :=
      ENNReal.mul_inv_cancel (hγ0 j) (hγtop j)
    rw [show (γ j * E j) * ((β j) ^ 2 * (γ j)⁻¹) =
        (β j) ^ 2 * E j by
      calc
        (γ j * E j) * ((β j) ^ 2 * (γ j)⁻¹) =
            (γ j * (γ j)⁻¹) * ((β j) ^ 2 * E j) := by ac_rfl
        _ = (β j) ^ 2 * E j := by rw [hcancel, one_mul]]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have hrootSquare : ((β j) ^ 2) ^ (1 / 2 : ℝ) = β j := by
      simpa [one_div] using
        (ENNReal.pow_rpow_inv_natCast (by norm_num : (2 : ℕ) ≠ 0) (β j))
    rw [hrootSquare]
  calc
    (∑ j, β j * (E j) ^ (1 / 2 : ℝ)) = ∑ j, F j * G j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (hFG j).symm
    _ ≤ (∑ j, F j ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        (∑ j, G j ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
      ENNReal.inner_le_Lp_mul_Lq Finset.univ F G Real.HolderConjugate.two_two
    _ = (∑ j, γ j * E j) ^ (1 / 2 : ℝ) *
        (fractionalCost γ β) ^ (1 / 2 : ℝ) := by
      simp_rw [hFtwo, hGtwo]
      rfl

/-- Integrate the fractional boundary inequality over the squared
superlevels of a measurable function.  The zero-mass superlevels are handled
separately, so the boundary premise needs only positive-mass cuts. -/
theorem lintegral_measure_sqSuperlevel_le_sum_fractionalFlow
    {N : ℕ} (π : Measure α) [IsFiniteMeasure π]
    (K : Fin N → Kernel α α) [∀ j, IsMarkovKernel (K j)]
    (β : Fin N → ℝ≥0∞) (hβtop : ∀ j, β j ≠ ∞)
    (g : α → ℝ) (hg : Measurable g)
    (hsmall : ∀ r : ℝ, 0 ≤ r →
      π (sqSuperlevel g r) ≤ (2 : ℝ≥0∞)⁻¹)
    (hflow : ∀ A : Set α, MeasurableSet A →
      0 < π A → π A ≤ (2 : ℝ≥0∞)⁻¹ →
      π A ≤ ∑ j, β j * boundaryFlow π (K j) A) :
    (∫⁻ r in Set.Ici (0 : ℝ), π (sqSuperlevel g r) ∂volume) ≤
      ∑ j, β j *
        ∫⁻ r in Set.Ici (0 : ℝ),
          boundaryFlow π (K j) (sqSuperlevel g r) ∂volume := by
  have hmeas (j : Fin N) : Measurable (fun r : ℝ =>
      β j * boundaryFlow π (K j) (sqSuperlevel g r)) :=
    measurable_const.mul (measurable_boundaryFlow_sqSuperlevel π (K j) g hg)
  calc
    (∫⁻ r in Set.Ici (0 : ℝ), π (sqSuperlevel g r) ∂volume) ≤
        ∫⁻ r in Set.Ici (0 : ℝ),
          ∑ j, β j * boundaryFlow π (K j) (sqSuperlevel g r) ∂volume := by
      apply setLIntegral_mono' measurableSet_Ici
      intro r hr
      by_cases hz : π (sqSuperlevel g r) = 0
      · simp [hz]
      · exact hflow (sqSuperlevel g r) (measurableSet_sqSuperlevel hg r)
          (pos_iff_ne_zero.mpr hz) (hsmall r hr)
    _ = ∑ j, ∫⁻ r in Set.Ici (0 : ℝ),
          β j * boundaryFlow π (K j) (sqSuperlevel g r) ∂volume := by
      rw [lintegral_finsetSum Finset.univ]
      intro j hj
      exact hmeas j
    _ = ∑ j, β j *
        ∫⁻ r in Set.Ici (0 : ℝ),
          boundaryFlow π (K j) (sqSuperlevel g r) ∂volume := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [lintegral_const_mul' _ _ (hβtop j)]

/-- Layer cake, the fractional cut inequality, and componentwise coarea
assembled before the finite-dimensional weighted Cauchy--Schwarz step. -/
theorem lintegral_sq_le_sum_fractional_coareaBounds
    {N : ℕ} (π : Measure α) [IsFiniteMeasure π]
    (K : Fin N → Kernel α α) [∀ j, IsMarkovKernel (K j)]
    (hrev : ∀ j, Kernel.IsReversible (K j) π)
    (β : Fin N → ℝ≥0∞) (hβtop : ∀ j, β j ≠ ∞)
    (g : α → ℝ) (hg : Measurable g)
    (hsmall : ∀ r : ℝ, 0 ≤ r →
      π (sqSuperlevel g r) ≤ (2 : ℝ≥0∞)⁻¹)
    (hflow : ∀ A : Set α, MeasurableSet A →
      0 < π A → π A ≤ (2 : ℝ≥0∞)⁻¹ →
      π A ≤ ∑ j, β j * boundaryFlow π (K j) A) :
    (∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂π) ≤
      ∑ j, β j * ((2 : ℝ≥0∞)⁻¹ *
        (((2 : ℝ≥0∞) * Dirichlet.energy π (K j) g) ^ (1 / 2 : ℝ) *
          ((4 : ℝ≥0∞) *
            ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂π) ^ (1 / 2 : ℝ))) := by
  calc
    (∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂π) =
        ∫⁻ r in Set.Ici (0 : ℝ), π (sqSuperlevel g r) ∂volume :=
      lintegral_sq_eq_lintegral_measure_sqSuperlevel π g hg
    _ ≤ ∑ j, β j *
        ∫⁻ r in Set.Ici (0 : ℝ),
          boundaryFlow π (K j) (sqSuperlevel g r) ∂volume :=
      lintegral_measure_sqSuperlevel_le_sum_fractionalFlow
        π K β hβtop g hg hsmall hflow
    _ ≤ ∑ j, β j * ((2 : ℝ≥0∞)⁻¹ *
        (((2 : ℝ≥0∞) * Dirichlet.energy π (K j) g) ^ (1 / 2 : ℝ) *
          ((4 : ℝ≥0∞) *
            ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂π) ^ (1 / 2 : ℝ))) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left
        (coarea_sqSuperlevel_le_energy_secondMoment
          π (K j) (hrev j) g hg) (by positivity)

/-- Cancel the finite truncated second moment after fractional weighted
Cauchy--Schwarz. -/
theorem coarea_fractional_sum_cancel
    {N : ℕ} (γ β E : Fin N → ℝ≥0∞)
    (hγ0 : ∀ j, γ j ≠ 0) (hγtop : ∀ j, γ j ≠ ∞)
    {I Etotal : ℝ≥0∞} (hItop : I ≠ ∞)
    (hraw : I ≤
      ∑ j, β j * ((2 : ℝ≥0∞)⁻¹ *
        (((2 : ℝ≥0∞) * E j) ^ (1 / 2 : ℝ) *
          ((4 : ℝ≥0∞) * I) ^ (1 / 2 : ℝ))))
    (henergy : (∑ j, γ j * E j) ≤ Etotal) :
    I ≤ (2 : ℝ≥0∞) * fractionalCost γ β * Etotal := by
  let E2 : Fin N → ℝ≥0∞ := fun j => (2 : ℝ≥0∞) * E j
  have hraw' : I ≤ I ^ (1 / 2 : ℝ) *
      ∑ j, β j * (E2 j) ^ (1 / 2 : ℝ) := by
    calc
      I ≤ ∑ j, β j * ((2 : ℝ≥0∞)⁻¹ *
          (((2 : ℝ≥0∞) * E j) ^ (1 / 2 : ℝ) *
            ((4 : ℝ≥0∞) * I) ^ (1 / 2 : ℝ))) := hraw
      _ = ∑ j, I ^ (1 / 2 : ℝ) *
          (β j * (E2 j) ^ (1 / 2 : ℝ)) := by
        apply Finset.sum_congr rfl
        intro j hj
        calc
          β j * ((2 : ℝ≥0∞)⁻¹ *
              (((2 : ℝ≥0∞) * E j) ^ (1 / 2 : ℝ) *
                ((4 : ℝ≥0∞) * I) ^ (1 / 2 : ℝ))) =
              ((2 : ℝ≥0∞)⁻¹ *
                ((4 : ℝ≥0∞) * I) ^ (1 / 2 : ℝ)) *
                (β j * (E2 j) ^ (1 / 2 : ℝ)) := by
            dsimp [E2]
            ac_rfl
          _ = I ^ (1 / 2 : ℝ) *
                (β j * (E2 j) ^ (1 / 2 : ℝ)) := by
            rw [inv_two_mul_four_mul_rpow_half]
      _ = I ^ (1 / 2 : ℝ) *
          ∑ j, β j * (E2 j) ^ (1 / 2 : ℝ) := by
        rw [Finset.mul_sum]
  have hweighted := fractional_weighted_sqrt_sum_le γ β E2 hγ0 hγtop
  have hE2sum : (∑ j, γ j * E2 j) =
      (2 : ℝ≥0∞) * ∑ j, γ j * E j := by
    calc
      (∑ j, γ j * E2 j) = ∑ j, (2 : ℝ≥0∞) * (γ j * E j) := by
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [E2]
        ac_rfl
      _ = (2 : ℝ≥0∞) * ∑ j, γ j * E j := by
        rw [Finset.mul_sum]
  have hrootEnergy :
      (∑ j, γ j * E2 j) ^ (1 / 2 : ℝ) ≤
        ((2 : ℝ≥0∞) * Etotal) ^ (1 / 2 : ℝ) := by
    apply ENNReal.rpow_le_rpow
    · rw [hE2sum]
      exact mul_le_mul_of_nonneg_left henergy (by positivity)
    · norm_num
  have hroot : I ≤
      (I * ((2 : ℝ≥0∞) * fractionalCost γ β * Etotal)) ^
        (1 / 2 : ℝ) := by
    calc
      I ≤ I ^ (1 / 2 : ℝ) *
          ∑ j, β j * (E2 j) ^ (1 / 2 : ℝ) := hraw'
      _ ≤ I ^ (1 / 2 : ℝ) *
          ((∑ j, γ j * E2 j) ^ (1 / 2 : ℝ) *
            (fractionalCost γ β) ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hweighted (by positivity)
      _ ≤ I ^ (1 / 2 : ℝ) *
          (((2 : ℝ≥0∞) * Etotal) ^ (1 / 2 : ℝ) *
            (fractionalCost γ β) ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hrootEnergy (by positivity))
          (by positivity)
      _ = (I * ((2 : ℝ≥0∞) * fractionalCost γ β * Etotal)) ^
          (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        ac_rfl
  exact le_of_le_rpow_half_self_mul hItop hroot

/-- The one-sided fractional estimate.  The energy domination premise is
invoked only for the bounded truncations `capAt n g`, which are in `L²` on a
probability space. -/
theorem lintegral_sq_le_two_fractionalCost_mul_energy
    {N : ℕ} (π : Measure α) [IsProbabilityMeasure π]
    (P : Kernel α α) [IsMarkovKernel P]
    (K : Fin N → Kernel α α) [hK : ∀ j, IsMarkovKernel (K j)]
    (hrev : ∀ j, Kernel.IsReversible (K j) π)
    (γ β : Fin N → ℝ≥0∞)
    (hγ0 : ∀ j, γ j ≠ 0) (hγtop : ∀ j, γ j ≠ ∞)
    (hβtop : ∀ j, β j ≠ ∞)
    (hdom : ∀ u : α → ℝ, Measurable u →
      MemLp u (2 : ℝ≥0∞) π →
      (∑ j, γ j * Dirichlet.energy π (K j) u) ≤
        Dirichlet.energy π P u)
    (hflow : ∀ A : Set α, MeasurableSet A →
      0 < π A → π A ≤ (2 : ℝ≥0∞)⁻¹ →
      π A ≤ ∑ j, β j * boundaryFlow π (K j) A)
    (g : α → ℝ) (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (hsupport : π {x | 0 < g x} ≤ (2 : ℝ≥0∞)⁻¹) :
    (∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂π) ≤
      (2 : ℝ≥0∞) * fractionalCost γ β * Dirichlet.energy π P g := by
  rw [lintegral_sq_eq_iSup_lintegral_sq_capAt_nat π g hg hg0]
  apply iSup_le
  intro n
  let gn : α → ℝ := capAt (n : ℝ) g
  have hgn : Measurable gn := measurable_capAt hg (n : ℝ)
  have hgn0 : ∀ x, 0 ≤ gn x := fun x =>
    capAt_nonneg hg0 (Nat.cast_nonneg n) x
  have hgn_le : ∀ x, gn x ≤ (n : ℝ) := fun x => by
    dsimp [gn, capAt]
    exact min_le_right _ _
  have hgnL2 : MemLp gn (2 : ℝ≥0∞) π :=
    memLp_of_bounded
      (Filter.Eventually.of_forall fun x => ⟨hgn0 x, hgn_le x⟩)
      hgn.aestronglyMeasurable (2 : ℝ≥0∞)
  have hsupportCap : π {x | 0 < gn x} ≤ (2 : ℝ≥0∞)⁻¹ :=
    (measure_pos_capAt_nat_le π g n).trans hsupport
  have hsmall : ∀ r : ℝ, 0 ≤ r →
      π (sqSuperlevel gn r) ≤ (2 : ℝ≥0∞)⁻¹ := fun r hr =>
    measure_sqSuperlevel_le_half_of_support π gn hgn0 hsupportCap hr
  have hraw := lintegral_sq_le_sum_fractional_coareaBounds
    π K hrev β hβtop gn hgn hsmall hflow
  have henergy :
      (∑ j, γ j * Dirichlet.energy π (K j) gn) ≤
        Dirichlet.energy π P g := by
    exact (hdom gn hgn hgnL2).trans
      (energy_capAt_le π P g hg (n : ℝ))
  exact coarea_fractional_sum_cancel γ β
    (fun j => Dirichlet.energy π (K j) gn)
    hγ0 hγtop
    (lintegral_sq_capAt_nat_ne_top π g hg0 n) hraw henergy

/-- Median splitting turns the one-sided fractional estimate into the exact
extended-variance inequality. -/
theorem fractionalAggregation_evariance_le
    {N : ℕ} (π : Measure α) [IsProbabilityMeasure π]
    (P : Kernel α α) [IsMarkovKernel P]
    (K : Fin N → Kernel α α) [hK : ∀ j, IsMarkovKernel (K j)]
    (hrev : ∀ j, Kernel.IsReversible (K j) π)
    (γ β : Fin N → ℝ≥0∞)
    (hγ0 : ∀ j, γ j ≠ 0) (hγtop : ∀ j, γ j ≠ ∞)
    (hβtop : ∀ j, β j ≠ ∞)
    (hdom : ∀ u : α → ℝ, Measurable u →
      MemLp u (2 : ℝ≥0∞) π →
      (∑ j, γ j * Dirichlet.energy π (K j) u) ≤
        Dirichlet.energy π P u)
    (hflow : ∀ A : Set α, MeasurableSet A →
      0 < π A → π A ≤ (2 : ℝ≥0∞)⁻¹ →
      π A ≤ ∑ j, β j * boundaryFlow π (K j) A)
    (f : α → ℝ) (hf : Measurable f) :
    evariance f π ≤
      (2 : ℝ≥0∞) * fractionalCost γ β * Dirichlet.energy π P f := by
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
  have hfpBound := lintegral_sq_le_two_fractionalCost_mul_energy
    π P K hrev γ β hγ0 hγtop hβtop hdom hflow
    fp hfp hfp0 hfpSupport
  have hfnBound := lintegral_sq_le_two_fractionalCost_mul_energy
    π P K hrev γ β hγ0 hγtop hβtop hdom hflow
    fn hfn hfn0 hfnSupport
  calc
    evariance f π ≤
        ∫⁻ x, ENNReal.ofReal ((f x - b) ^ 2) ∂π :=
      evariance_le_lintegral_sq_sub π f hf b
    _ = (∫⁻ x, ENNReal.ofReal (fp x ^ 2) ∂π) +
        ∫⁻ x, ENNReal.ofReal (fn x ^ 2) ∂π := by
      simpa only [fp, fn] using
        lintegral_sq_sub_eq_add_medianParts π f hf b
    _ ≤ ((2 : ℝ≥0∞) * fractionalCost γ β *
          Dirichlet.energy π P fp) +
        ((2 : ℝ≥0∞) * fractionalCost γ β *
          Dirichlet.energy π P fn) := add_le_add hfpBound hfnBound
    _ = (2 : ℝ≥0∞) * fractionalCost γ β *
        (Dirichlet.energy π P fp + Dirichlet.energy π P fn) := by
      rw [mul_add]
    _ ≤ (2 : ℝ≥0∞) * fractionalCost γ β *
        Dirichlet.energy π P f :=
      mul_le_mul_of_nonneg_left
        (energy_medianParts_le π P f hf b) (by positivity)

/-- Finiteness of the fractional cost under the manuscript's finite
coefficients and positive component energy weights. -/
theorem fractionalCost_ne_top
    {N : ℕ} (γ β : Fin N → ℝ≥0∞)
    (hγ0 : ∀ j, γ j ≠ 0) (hβtop : ∀ j, β j ≠ ∞) :
    fractionalCost γ β ≠ ∞ := by
  unfold fractionalCost
  rw [ENNReal.sum_ne_top]
  intro j hj
  exact ENNReal.div_ne_top (ENNReal.pow_ne_top (hβtop j)) (hγ0 j)

/-- The exact fractional Poincaré lower bound from Lemma 3.5.  The strict
positivity premise is the paper's assumption `∑ β_j² / γ_j > 0`. -/
theorem fractionalAggregation_poincareLower
    {N : ℕ} (π : Measure α) [IsProbabilityMeasure π]
    (P : Kernel α α) [IsMarkovKernel P]
    (K : Fin N → Kernel α α) [hK : ∀ j, IsMarkovKernel (K j)]
    (hrev : ∀ j, Kernel.IsReversible (K j) π)
    (γ β : Fin N → ℝ≥0∞)
    (hγ0 : ∀ j, γ j ≠ 0) (hγtop : ∀ j, γ j ≠ ∞)
    (hβtop : ∀ j, β j ≠ ∞)
    (hcost : 0 < fractionalCost γ β)
    (hdom : ∀ u : α → ℝ, Measurable u →
      MemLp u (2 : ℝ≥0∞) π →
      (∑ j, γ j * Dirichlet.energy π (K j) u) ≤
        Dirichlet.energy π P u)
    (hflow : ∀ A : Set α, MeasurableSet A →
      0 < π A → π A ≤ (2 : ℝ≥0∞)⁻¹ →
      π A ≤ ∑ j, β j * boundaryFlow π (K j) A) :
    PoincareLower π P
      (((2 : ℝ≥0∞) * fractionalCost γ β)⁻¹) := by
  intro f hf
  let C : ℝ≥0∞ := (2 : ℝ≥0∞) * fractionalCost γ β
  have hcost0 : fractionalCost γ β ≠ 0 := ne_of_gt hcost
  have hcosttop : fractionalCost γ β ≠ ∞ :=
    fractionalCost_ne_top γ β hγ0 hβtop
  have hC0 : C ≠ 0 := mul_ne_zero (by norm_num) hcost0
  have hCtop : C ≠ ∞ := ENNReal.mul_ne_top (by norm_num) hcosttop
  have hvar := fractionalAggregation_evariance_le
    π P K hrev γ β hγ0 hγtop hβtop hdom hflow f hf
  change C⁻¹ * evariance f π ≤ Dirichlet.energy π P f
  calc
    C⁻¹ * evariance f π ≤
        C⁻¹ * (C * Dirichlet.energy π P f) :=
      mul_le_mul_of_nonneg_left hvar (by positivity)
    _ = Dirichlet.energy π P f :=
      ENNReal.inv_mul_cancel_left hC0 hCtop

/-- Spectral-gap form of the fractional finite-component aggregation lemma.
It is valid when some `β j` vanish and its domination premise ranges exactly
over measurable `L²` functions. -/
theorem fractionalAggregation_le_spectralGap
    {N : ℕ} (π : Measure α) [IsProbabilityMeasure π]
    (P : Kernel α α) [IsMarkovKernel P]
    (K : Fin N → Kernel α α) [hK : ∀ j, IsMarkovKernel (K j)]
    (hrev : ∀ j, Kernel.IsReversible (K j) π)
    (γ β : Fin N → ℝ≥0∞)
    (hγ0 : ∀ j, γ j ≠ 0) (hγtop : ∀ j, γ j ≠ ∞)
    (hβtop : ∀ j, β j ≠ ∞)
    (hcost : 0 < fractionalCost γ β)
    (hdom : ∀ u : α → ℝ, Measurable u →
      MemLp u (2 : ℝ≥0∞) π →
      (∑ j, γ j * Dirichlet.energy π (K j) u) ≤
        Dirichlet.energy π P u)
    (hflow : ∀ A : Set α, MeasurableSet A →
      0 < π A → π A ≤ (2 : ℝ≥0∞)⁻¹ →
      π A ≤ ∑ j, β j * boundaryFlow π (K j) A) :
    ((2 : ℝ≥0∞) * fractionalCost γ β)⁻¹ ≤ spectralGap π P := by
  exact le_spectralGap π P
    (fractionalAggregation_poincareLower
      π P K hrev γ β hγ0 hγtop hβtop hcost hdom hflow)

/-- Substituting `β j = (φ j)⁻¹` identifies the fractional cost with the
harmonic cost in the hard-assignment aggregation theorem. -/
theorem fractionalCost_inv_eq_harmonicCost
    {N : ℕ} (γ φ : Fin N → ℝ≥0∞)
    (hγ0 : ∀ j, γ j ≠ 0) (hγtop : ∀ j, γ j ≠ ∞)
    (hφ0 : ∀ j, φ j ≠ 0) (hφtop : ∀ j, φ j ≠ ∞) :
    fractionalCost γ (fun j => (φ j)⁻¹) = harmonicCost γ φ := by
  unfold fractionalCost harmonicCost
  apply Finset.sum_congr rfl
  intro j hj
  change (φ j)⁻¹ ^ 2 / γ j = (γ j * φ j ^ 2)⁻¹
  rw [div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inl (hγ0 j))
    (Or.inl (hγtop j))]
  rw [show φ j ^ 2 = φ j * φ j by ring]
  rw [ENNReal.mul_inv (Or.inl (hφ0 j)) (Or.inl (hφtop j))]
  simp only [pow_two]
  simp only [mul_comm]

/-- The paper's hard-assignment aggregation theorem, now with its exact
`L²`-scoped energy-domination premise, obtained from the fractional lemma by
setting `β j = (φ j)⁻¹`. -/
theorem hardAssignmentAggregation_poincareLower
    {N : ℕ} (hN : 0 < N)
    (π : Measure α) [IsProbabilityMeasure π]
    (P : Kernel α α) [IsMarkovKernel P]
    (K : Fin N → Kernel α α) [hK : ∀ j, IsMarkovKernel (K j)]
    (hrev : ∀ j, Kernel.IsReversible (K j) π)
    (γ φ : Fin N → ℝ≥0∞)
    (hγ0 : ∀ j, γ j ≠ 0) (hγtop : ∀ j, γ j ≠ ∞)
    (hφ0 : ∀ j, φ j ≠ 0) (hφtop : ∀ j, φ j ≠ ∞)
    (hdom : ∀ u : α → ℝ, Measurable u →
      MemLp u (2 : ℝ≥0∞) π →
      (∑ j, γ j * Dirichlet.energy π (K j) u) ≤
        Dirichlet.energy π P u)
    (hflow : ∀ A : Set α, MeasurableSet A →
      0 < π A → π A ≤ (2 : ℝ≥0∞)⁻¹ →
      ∃ j : Fin N, φ j * π A ≤ boundaryFlow π (K j) A) :
    PoincareLower π P (((2 : ℝ≥0∞) * harmonicCost γ φ)⁻¹) := by
  let β : Fin N → ℝ≥0∞ := fun j => (φ j)⁻¹
  have hβtop : ∀ j, β j ≠ ∞ := fun j =>
    ENNReal.inv_ne_top.mpr (hφ0 j)
  have hcostEq : fractionalCost γ β = harmonicCost γ φ := by
    simpa only [β] using
      fractionalCost_inv_eq_harmonicCost γ φ hγ0 hγtop hφ0 hφtop
  have hcost : 0 < fractionalCost γ β := by
    rw [hcostEq]
    exact pos_iff_ne_zero.mpr
      (harmonicCost_ne_zero hN γ φ hγtop hφtop)
  have hflow' : ∀ A : Set α, MeasurableSet A →
      0 < π A → π A ≤ (2 : ℝ≥0∞)⁻¹ →
      π A ≤ ∑ j, β j * boundaryFlow π (K j) A := by
    intro A hA hApos hAhalf
    exact measure_le_sum_inv_mul_boundaryFlow π K φ hφ0 hφtop A
      (hflow A hA hApos hAhalf)
  rw [← hcostEq]
  exact fractionalAggregation_poincareLower
    π P K hrev γ β hγ0 hγtop hβtop hcost hdom hflow'

/-- Spectral-gap form of the exact `L²` hard-assignment aggregation theorem.
-/
theorem hardAssignmentAggregation_le_spectralGap
    {N : ℕ} (hN : 0 < N)
    (π : Measure α) [IsProbabilityMeasure π]
    (P : Kernel α α) [IsMarkovKernel P]
    (K : Fin N → Kernel α α) [hK : ∀ j, IsMarkovKernel (K j)]
    (hrev : ∀ j, Kernel.IsReversible (K j) π)
    (γ φ : Fin N → ℝ≥0∞)
    (hγ0 : ∀ j, γ j ≠ 0) (hγtop : ∀ j, γ j ≠ ∞)
    (hφ0 : ∀ j, φ j ≠ 0) (hφtop : ∀ j, φ j ≠ ∞)
    (hdom : ∀ u : α → ℝ, Measurable u →
      MemLp u (2 : ℝ≥0∞) π →
      (∑ j, γ j * Dirichlet.energy π (K j) u) ≤
        Dirichlet.energy π P u)
    (hflow : ∀ A : Set α, MeasurableSet A →
      0 < π A → π A ≤ (2 : ℝ≥0∞)⁻¹ →
      ∃ j : Fin N, φ j * π A ≤ boundaryFlow π (K j) A) :
    ((2 : ℝ≥0∞) * harmonicCost γ φ)⁻¹ ≤ spectralGap π P := by
  exact le_spectralGap π P
    (hardAssignmentAggregation_poincareLower hN
      π P K hrev γ φ hγ0 hγtop hφ0 hφtop hdom hflow)

end Concrete

end

end UniformRandomMALA
