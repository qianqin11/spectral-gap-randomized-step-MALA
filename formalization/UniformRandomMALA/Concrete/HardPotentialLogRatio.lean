import UniformRandomMALA.Concrete.FixedStepHardPotential
import UniformRandomMALA.Concrete.SafeAcceptance

/-!
# Exact Hastings ratio for the fixed-step hard potential

This module isolates the deterministic algebra behind the sticky-region
branch.  It computes the log Hastings ratio at the origin coordinate by
coordinate and identifies the sole potentially positive term with

`cos v - 1 + v sin v / 2`.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory Gradient

noncomputable section

/-- The oscillatory scalar appearing in the appendix's log-ratio formula. -/
def hardAcceptanceShape (v : ℝ) : ℝ :=
  Real.cos v - 1 + v * Real.sin v / 2

/-- One coordinate's contribution to the symmetric MALA log ratio from the
origin to a point with coordinate `u`. -/
def hardCoordinateLogRatio (m L h : ℝ) (i : Fin d) (u : ℝ) : ℝ :=
  hardCoordinate m L h i 0 - hardCoordinate m L h i u +
    (1 / 2) * u *
      (hardCoordinateGradient m L h i 0 +
        hardCoordinateGradient m L h i u) +
    (h / 4) *
      ((hardCoordinateGradient m L h i 0) ^ 2 -
        (hardCoordinateGradient m L h i u) ^ 2)

/-- Exact coordinate formula.  On non-Gaussian coordinates, the only term
that is not visibly nonpositive is `((L-m)/2) h A(u/sqrt h)`. -/
theorem hardCoordinateLogRatio_eq
    {h : ℝ} (hh : 0 < h) (m L : ℝ) (i : Fin d) (u : ℝ) :
    hardCoordinateLogRatio m L h i u =
      if (i : ℕ) = 0 then -(h / 4) * (m * u) ^ 2
      else ((L - m) / 2) * h *
          hardAcceptanceShape (u / Real.sqrt h) -
        (h / 4) * (hardCoordinateGradient m L h i u) ^ 2 := by
  have hs : Real.sqrt h ≠ 0 := (Real.sqrt_pos.2 hh).ne'
  unfold hardCoordinateLogRatio hardCoordinate hardCoordinateGradient
  split_ifs
  · simp [hardGaussianCoordinate]
    ring
  · simp [hardOscillatoryCoordinate, hardAcceptanceShape]
    rw [← Real.sq_sqrt hh.le]
    field_simp [hs]
    ring

/-- The explicit hard witness has zero gradient at the origin. -/
@[simp] theorem fixedStepHardFirstOrderPotential_gradU_zero
    {d : ℕ} (hd : 2 ≤ d) {m L h : ℝ}
    (hm : 0 < m) (hmL : m < L) (hh : 0 < h) :
    (fixedStepHardFirstOrderPotential hd hm hmL hh).gradU 0 = 0 := by
  rw [fixedStepHardFirstOrderPotential_gradU]
  exact fixedStepHardGradient_zero d m L h

/-- The full MALA log ratio at the origin is the finite sum of the coordinate
contributions above. -/
theorem hard_malaLogRatio_zero_eq_sum
    {d : ℕ} (hd : 2 ≤ d) {m L h : ℝ}
    (hm : 0 < m) (hmL : m < L) (hh : 0 < h)
    (y : State d) :
    let W := fixedStepHardFirstOrderPotential hd hm hmL hh
    W.malaLogRatio h 0 y =
      ∑ i : Fin d, hardCoordinateLogRatio m L h i (y i) := by
  let W := fixedStepHardFirstOrderPotential hd hm hmL hh
  dsimp only
  rw [W.malaLogRatio_eq_symmetric hh]
  rw [fixedStepHardFirstOrderPotential_U,
    fixedStepHardFirstOrderPotential_gradU]
  simp only [fixedStepHardGradient_zero, zero_add, sub_zero, norm_zero]
  unfold fixedStepHardPotential hardCoordinateLogRatio
  rw [EuclideanSpace.real_norm_sq_eq]
  have hgradApply : ∀ i : Fin d,
      (fixedStepHardGradient d m L h y).ofLp i =
        hardCoordinateGradient m L h i (y i) := by
    intro i
    exact fixedStepHardGradient_apply d m L h y i
  simp_rw [hgradApply]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  simp_rw [hgradApply]
  have hgrad0 : ∀ i : Fin d,
      hardCoordinateGradient m L h i 0 = 0 := by
    intro i
    simp [hardCoordinateGradient]
  simp_rw [hgrad0]
  simp only [PiLp.zero_apply, zero_add]
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [Finset.mul_sum]
  ring_nf
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hsumComm :
      (∑ i : Fin d,
          hardCoordinateGradient m L h i (y i) * y i) =
        ∑ i : Fin d,
          y i * hardCoordinateGradient m L h i (y i) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsumComm]

/-- Combining the coordinate computation gives a pointwise upper bound by
the oscillatory `A`-sum alone. -/
theorem hard_malaLogRatio_zero_le_shape_sum
    {d : ℕ} (hd : 2 ≤ d) {m L h : ℝ}
    (hm : 0 < m) (hmL : m < L) (hh : 0 < h)
    (y : State d) :
    let W := fixedStepHardFirstOrderPotential hd hm hmL hh
    W.malaLogRatio h 0 y ≤
      ∑ i : Fin d, if (i : ℕ) = 0 then 0
        else ((L - m) / 2) * h *
          hardAcceptanceShape (y i / Real.sqrt h) := by
  dsimp only
  rw [hard_malaLogRatio_zero_eq_sum hd hm hmL hh y]
  apply Finset.sum_le_sum
  intro i hi
  rw [hardCoordinateLogRatio_eq hh]
  split_ifs with hzero
  · have hnonneg : 0 ≤ (h / 4) * (m * y i) ^ 2 :=
      mul_nonneg (by positivity) (sq_nonneg _)
    linarith
  · have hh4 : 0 ≤ h / 4 := by positivity
    nlinarith [sq_nonneg (hardCoordinateGradient m L h i (y i))]

end

end UniformRandomMALA.Concrete
