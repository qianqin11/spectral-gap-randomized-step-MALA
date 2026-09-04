import UniformRandomMALA.Concrete.ComponentAggregation
import Mathlib.Analysis.MeanInequalities

/-!
# Extended-nonnegative arithmetic for component aggregation

This file contains no measures or kernels.  It isolates the two pieces of
finite-dimensional arithmetic needed after coarea:

* weighted Cauchy--Schwarz with the harmonic weights
  `(γ_j φ_j²)⁻¹`; and
* cancellation of a *finite* quantity from a square-root inequality.

The finiteness requirement in the cancellation lemma is intentional.  The
measure-theoretic proof supplies it by applying coarea to bounded caps before
using monotone convergence.
-/

namespace UniformRandomMALA

open scoped BigOperators ENNReal

noncomputable section

namespace Concrete

/-- A finite positive denominator can be cancelled from one copy of its
square.  This coefficient identity is the elementary core of the weighted
Hölder substitution. -/
private theorem inv_mul_mul_sq_cancel
    {a b : ℝ≥0∞}
    (ha0 : a ≠ 0) (hatop : a ≠ ∞)
    (hb0 : b ≠ 0) (hbtop : b ≠ ∞) :
    (a * b ^ 2)⁻¹ * (a * b) = b⁻¹ := by
  let A : ℝ≥0∞ := a * b
  have hA0 : A ≠ 0 := mul_ne_zero ha0 hb0
  have hAtop : A ≠ ∞ := ENNReal.mul_ne_top hatop hbtop
  have hinv : (A * b)⁻¹ = A⁻¹ * b⁻¹ :=
    ENNReal.mul_inv (Or.inl hA0) (Or.inl hAtop)
  calc
    (a * b ^ 2)⁻¹ * (a * b) = (A * b)⁻¹ * A := by
      dsimp [A]
      congr 2
      ring
    _ = (A⁻¹ * b⁻¹) * A := by rw [hinv]
    _ = (A⁻¹ * A) * b⁻¹ := by ac_rfl
    _ = b⁻¹ := by rw [ENNReal.inv_mul_cancel hA0 hAtop, one_mul]

/-- The same cancellation with two numerator copies. -/
private theorem inv_mul_sq_mul_cancel
    {a b x : ℝ≥0∞}
    (ha0 : a ≠ 0) (hatop : a ≠ ∞)
    (hb0 : b ≠ 0) (hbtop : b ≠ ∞) :
    (a * b ^ 2)⁻¹ * (a * b * x) ^ 2 = a * x ^ 2 := by
  let A : ℝ≥0∞ := a * b
  have hA0 : A ≠ 0 := mul_ne_zero ha0 hb0
  have hAtop : A ≠ ∞ := ENNReal.mul_ne_top hatop hbtop
  have hinv : (A * b)⁻¹ = A⁻¹ * b⁻¹ :=
    ENNReal.mul_inv (Or.inl hA0) (Or.inl hAtop)
  calc
    (a * b ^ 2)⁻¹ * (a * b * x) ^ 2 =
        (A⁻¹ * b⁻¹) * (A * x) ^ 2 := by
      rw [show a * b ^ 2 = A * b by dsimp [A]; ring, hinv]
    _ = (A⁻¹ * A) * (b⁻¹ * A) * x ^ 2 := by
      simp only [pow_two]
      ac_rfl
    _ = (b⁻¹ * (a * b)) * x ^ 2 := by
      rw [ENNReal.inv_mul_cancel hA0 hAtop, one_mul]
    _ = a * x ^ 2 := by
      rw [show b⁻¹ * (a * b) = a * (b⁻¹ * b) by ac_rfl,
        ENNReal.inv_mul_cancel hb0 hbtop, mul_one]

/-- Weighted Cauchy--Schwarz in exactly the harmonic form used by the paper.
All entries may be extended-valued, but the weights `γ_j` and `φ_j` are
required to be finite and strictly positive. -/
theorem weighted_sqrt_sum_le
    {N : ℕ} (γ φ E : Fin N → ℝ≥0∞)
    (hγ0 : ∀ j, γ j ≠ 0) (hγtop : ∀ j, γ j ≠ ∞)
    (hφ0 : ∀ j, φ j ≠ 0) (hφtop : ∀ j, φ j ≠ ∞) :
    (∑ j, (φ j)⁻¹ * (E j) ^ (1 / 2 : ℝ)) ≤
      (∑ j, γ j * E j) ^ (1 / 2 : ℝ) *
        (harmonicCost γ φ) ^ (1 / 2 : ℝ) := by
  let w : Fin N → ℝ≥0∞ := fun j => (γ j * (φ j) ^ 2)⁻¹
  let F : Fin N → ℝ≥0∞ := fun j =>
    γ j * φ j * (E j) ^ (1 / 2 : ℝ)
  have hwF (j : Fin N) :
      w j * F j = (φ j)⁻¹ * (E j) ^ (1 / 2 : ℝ) := by
    dsimp [w, F]
    rw [← mul_assoc, inv_mul_mul_sq_cancel
      (hγ0 j) (hγtop j) (hφ0 j) (hφtop j)]
  have hwFtwo (j : Fin N) :
      w j * (F j) ^ (2 : ℝ) = γ j * E j := by
    dsimp [w, F]
    rw [ENNReal.rpow_two,
      inv_mul_sq_mul_cancel (hγ0 j) (hγtop j) (hφ0 j) (hφtop j),
      ← ENNReal.rpow_two,
      ← ENNReal.rpow_mul]
    norm_num
  calc
    (∑ j, (φ j)⁻¹ * (E j) ^ (1 / 2 : ℝ)) =
        ∑ j, w j * F j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (hwF j).symm
    _ ≤ (∑ j, w j) ^
          (1 - (2 : ℝ)⁻¹) *
        (∑ j, w j * F j ^ (2 : ℝ)) ^
          (2 : ℝ)⁻¹ :=
      ENNReal.inner_le_weight_mul_Lp_of_nonneg
        Finset.univ (by norm_num : (1 : ℝ) ≤ 2) w F
    _ = (∑ j, γ j * E j) ^ (1 / 2 : ℝ) *
        (harmonicCost γ φ) ^ (1 / 2 : ℝ) := by
      simp_rw [hwFtwo]
      change (harmonicCost γ φ) ^ (1 - (2 : ℝ)⁻¹) *
          (∑ j, γ j * E j) ^ (2 : ℝ)⁻¹ = _
      have hhalfSub : 1 - (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
      have hhalfInv : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
      rw [hhalfSub, hhalfInv, mul_comm]

/-- The factor produced by the second coarea moment is exactly the square
root of the truncated second moment. -/
theorem inv_two_mul_four_mul_rpow_half (I : ℝ≥0∞) :
    (2 : ℝ≥0∞)⁻¹ * ((4 : ℝ≥0∞) * I) ^ (1 / 2 : ℝ) =
      I ^ (1 / 2 : ℝ) := by
  have hfour : (4 : ℝ≥0∞) ^ (1 / 2 : ℝ) = 2 := by
    calc
      (4 : ℝ≥0∞) ^ (1 / 2 : ℝ) =
          ((2 : ℝ≥0∞) ^ 2) ^ ((2 : ℝ)⁻¹) := by norm_num
      _ = 2 := ENNReal.pow_rpow_inv_natCast (by norm_num) 2
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    hfour, ← mul_assoc,
    ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞), one_mul]

/-- Squaring and cancelling a finite nonzero left factor.  This is the safe
replacement for the informal instruction “cancel `sqrt I`”. -/
theorem le_of_le_rpow_half_self_mul
    {I C : ℝ≥0∞} (hItop : I ≠ ∞)
    (h : I ≤ (I * C) ^ (1 / 2 : ℝ)) :
    I ≤ C := by
  by_cases hI0 : I = 0
  · simp [hI0]
  have hsq : I * I ≤ I * C := by
    have h' : I ^ (2 : ℝ) ≤ I * C :=
      (ENNReal.le_rpow_inv_iff (by norm_num : (0 : ℝ) < 2)).1
        (by simpa [one_div] using h)
    simpa [ENNReal.rpow_two, pow_two] using h'
  calc
    I = I⁻¹ * (I * I) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hI0 hItop, one_mul]
    _ ≤ I⁻¹ * (I * C) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = C := ENNReal.inv_mul_cancel_left hI0 hItop

/-- The raw componentwise coarea bound implies the harmonic one-sided
second-moment estimate, provided the second moment being cancelled is
finite. -/
theorem coarea_component_sum_cancel
    {N : ℕ} (γ φ E : Fin N → ℝ≥0∞)
    (hγ0 : ∀ j, γ j ≠ 0) (hγtop : ∀ j, γ j ≠ ∞)
    (hφ0 : ∀ j, φ j ≠ 0) (hφtop : ∀ j, φ j ≠ ∞)
    {I Etotal : ℝ≥0∞} (hItop : I ≠ ∞)
    (hraw : I ≤
      ∑ j, (φ j)⁻¹ * ((2 : ℝ≥0∞)⁻¹ *
        (((2 : ℝ≥0∞) * E j) ^ (1 / 2 : ℝ) *
          ((4 : ℝ≥0∞) * I) ^ (1 / 2 : ℝ))))
    (henergy : (∑ j, γ j * E j) ≤ Etotal) :
    I ≤ (2 : ℝ≥0∞) * harmonicCost γ φ * Etotal := by
  let E2 : Fin N → ℝ≥0∞ := fun j => (2 : ℝ≥0∞) * E j
  have hraw' : I ≤ I ^ (1 / 2 : ℝ) *
      ∑ j, (φ j)⁻¹ * (E2 j) ^ (1 / 2 : ℝ) := by
    calc
      I ≤ ∑ j, (φ j)⁻¹ * ((2 : ℝ≥0∞)⁻¹ *
          (((2 : ℝ≥0∞) * E j) ^ (1 / 2 : ℝ) *
            ((4 : ℝ≥0∞) * I) ^ (1 / 2 : ℝ))) := hraw
      _ = ∑ j, I ^ (1 / 2 : ℝ) *
          ((φ j)⁻¹ * (E2 j) ^ (1 / 2 : ℝ)) := by
        apply Finset.sum_congr rfl
        intro j hj
        calc
          (φ j)⁻¹ * ((2 : ℝ≥0∞)⁻¹ *
              (((2 : ℝ≥0∞) * E j) ^ (1 / 2 : ℝ) *
                ((4 : ℝ≥0∞) * I) ^ (1 / 2 : ℝ))) =
              ((2 : ℝ≥0∞)⁻¹ *
                ((4 : ℝ≥0∞) * I) ^ (1 / 2 : ℝ)) *
                ((φ j)⁻¹ * (E2 j) ^ (1 / 2 : ℝ)) := by
            dsimp [E2]
            ac_rfl
          _ = I ^ (1 / 2 : ℝ) *
                ((φ j)⁻¹ * (E2 j) ^ (1 / 2 : ℝ)) := by
            rw [inv_two_mul_four_mul_rpow_half]
      _ = I ^ (1 / 2 : ℝ) *
          ∑ j, (φ j)⁻¹ * (E2 j) ^ (1 / 2 : ℝ) := by
        rw [Finset.mul_sum]
  have hweighted := weighted_sqrt_sum_le γ φ E2
    hγ0 hγtop hφ0 hφtop
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
      (I * ((2 : ℝ≥0∞) * harmonicCost γ φ * Etotal)) ^
        (1 / 2 : ℝ) := by
    calc
      I ≤ I ^ (1 / 2 : ℝ) *
          ∑ j, (φ j)⁻¹ * (E2 j) ^ (1 / 2 : ℝ) := hraw'
      _ ≤ I ^ (1 / 2 : ℝ) *
          ((∑ j, γ j * E2 j) ^ (1 / 2 : ℝ) *
            (harmonicCost γ φ) ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hweighted (by positivity)
      _ ≤ I ^ (1 / 2 : ℝ) *
          (((2 : ℝ≥0∞) * Etotal) ^ (1 / 2 : ℝ) *
            (harmonicCost γ φ) ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hrootEnergy (by positivity))
          (by positivity)
      _ = (I * ((2 : ℝ≥0∞) * harmonicCost γ φ * Etotal)) ^
          (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        ac_rfl
  exact le_of_le_rpow_half_self_mul hItop hroot

end Concrete

end

end UniformRandomMALA
