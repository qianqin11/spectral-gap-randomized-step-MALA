import UniformRandomMALA.Concrete.MedianDecomposition
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Bounded nonnegative truncations

Cancellation in `ℝ≥0∞` is not valid at `∞`.  The conductance proof therefore
has to be applied first to bounded truncations and only then passed to the
limit.  This file records that routine step independently of component
aggregation.

For a real function `g`, `capAt R g = min g R`.  When `g` is nonnegative,
the natural-number caps increase pointwise to `g`; their squared moments
increase to the squared moment of `g`; and capping does not increase any
Dirichlet energy because `x ↦ min x R` is one-Lipschitz.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace Concrete

variable {α : Type*} [MeasurableSpace α]

/-- Pointwise upper truncation at a real level. -/
def capAt (R : ℝ) (g : α → ℝ) (x : α) : ℝ :=
  min (g x) R

theorem measurable_capAt
    {g : α → ℝ} (hg : Measurable g) (R : ℝ) :
    Measurable (capAt R g) := by
  unfold capAt
  exact hg.min measurable_const

theorem capAt_nonneg
    {g : α → ℝ} (hg0 : ∀ x, 0 ≤ g x) {R : ℝ} (hR : 0 ≤ R) (x : α) :
    0 ≤ capAt R g x := by
  exact le_min (hg0 x) hR

theorem capAt_le (R : ℝ) (g : α → ℝ) (x : α) :
    capAt R g x ≤ g x :=
  min_le_left _ _

/-- Capping is a contraction for squared scalar differences. -/
theorem capAt_sqDiff_le (R a b : ℝ) :
    (min a R - min b R) ^ 2 ≤ (a - b) ^ 2 := by
  rw [sq_le_sq]
  simpa using abs_min_sub_min_le_max a R b R

/-- Capping does not increase the concrete Dirichlet energy. -/
theorem energy_capAt_le
    (π : Measure α) [SFinite π]
    (K : Kernel α α) [IsSFiniteKernel K]
    (g : α → ℝ) (hg : Measurable g) (R : ℝ) :
    Dirichlet.energy π K (capAt R g) ≤ Dirichlet.energy π K g := by
  rw [energy_eq_edgeMeasure_lintegral π K (capAt R g)
      (measurable_capAt hg R),
    energy_eq_edgeMeasure_lintegral π K g hg]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  apply lintegral_mono
  intro z
  exact ENNReal.ofReal_le_ofReal (capAt_sqDiff_le R (g z.1) (g z.2))

/-- The natural caps are pointwise monotone. -/
theorem monotone_capAt_nat (g : α → ℝ) :
    Monotone (fun n : ℕ => capAt (n : ℝ) g) := by
  intro n m hnm x
  exact min_le_min_left (g x) (Nat.cast_le.mpr hnm)

/-- A nonnegative scalar is the supremum of its natural-number caps after
squaring and embedding in `ℝ≥0∞`. -/
theorem iSup_ofReal_sq_capAt_nat (a : ℝ) (ha : 0 ≤ a) :
    (⨆ n : ℕ, ENNReal.ofReal ((min a (n : ℝ)) ^ 2)) =
      ENNReal.ofReal (a ^ 2) := by
  apply le_antisymm
  · refine iSup_le fun n => ENNReal.ofReal_le_ofReal ?_
    have hcap0 : 0 ≤ min a (n : ℝ) :=
      le_min ha (Nat.cast_nonneg n)
    exact (sq_le_sq₀ hcap0 ha).2 (min_le_left _ _)
  · obtain ⟨n, hn⟩ := exists_nat_ge a
    refine le_iSup_of_le n ?_
    rw [min_eq_left hn]

/-- Monotone convergence for squared natural caps, stated as an exact
supremum identity so no topology is needed in later aggregation proofs. -/
theorem lintegral_sq_eq_iSup_lintegral_sq_capAt_nat
    (π : Measure α) (g : α → ℝ) (hg : Measurable g)
    (hg0 : ∀ x, 0 ≤ g x) :
    (∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂π) =
      ⨆ n : ℕ, ∫⁻ x,
        ENNReal.ofReal (capAt (n : ℝ) g x ^ 2) ∂π := by
  let F : ℕ → α → ℝ≥0∞ := fun n x =>
    ENNReal.ofReal (capAt (n : ℝ) g x ^ 2)
  have hFmeas (n : ℕ) : Measurable (F n) :=
    ENNReal.measurable_ofReal.comp
      ((measurable_capAt hg (n : ℝ)).pow_const 2)
  have hFmono : Monotone F := by
    intro n m hnm x
    apply ENNReal.ofReal_le_ofReal
    have hn0 : 0 ≤ capAt (n : ℝ) g x :=
      capAt_nonneg hg0 (Nat.cast_nonneg n) x
    have hm0 : 0 ≤ capAt (m : ℝ) g x :=
      capAt_nonneg hg0 (Nat.cast_nonneg m) x
    exact (sq_le_sq₀ hn0 hm0).2 (monotone_capAt_nat g hnm x)
  calc
    (∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂π) =
        ∫⁻ x, ⨆ n : ℕ, F n x ∂π := by
      apply lintegral_congr
      intro x
      exact (iSup_ofReal_sq_capAt_nat (g x) (hg0 x)).symm
    _ = ⨆ n : ℕ, ∫⁻ x, F n x ∂π :=
      lintegral_iSup hFmeas hFmono

/-- Every natural cap has a finite squared moment on a probability space. -/
theorem lintegral_sq_capAt_nat_ne_top
    (π : Measure α) [IsProbabilityMeasure π]
    (g : α → ℝ) (hg0 : ∀ x, 0 ≤ g x) (n : ℕ) :
    (∫⁻ x, ENNReal.ofReal (capAt (n : ℝ) g x ^ 2) ∂π) ≠ ∞ := by
  refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (lintegral_le_const (μ := π)
      (c := ENNReal.ofReal ((n : ℝ) ^ 2)) ?_)
  filter_upwards [] with x
  apply ENNReal.ofReal_le_ofReal
  have hcap0 : 0 ≤ capAt (n : ℝ) g x :=
    capAt_nonneg hg0 (Nat.cast_nonneg n) x
  exact (sq_le_sq₀ hcap0 (Nat.cast_nonneg n)).2 (min_le_right _ _)

/-- Natural capping can only shrink the positive support. -/
theorem measure_pos_capAt_nat_le
    (π : Measure α) (g : α → ℝ) (n : ℕ) :
    π {x | 0 < capAt (n : ℝ) g x} ≤ π {x | 0 < g x} := by
  apply measure_mono
  intro x hx
  exact hx.trans_le (capAt_le (n : ℝ) g x)

end Concrete

end

end UniformRandomMALA
