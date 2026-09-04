import Mathlib.MeasureTheory.Measure.Real

/-!
# A lightweight probability-measure total-variation convention

Mathlib currently provides total variation for signed measures, but no
canonical probability-measure distance with the convention
`sup_A |μ(A) - ν(A)|`.  Constructing a signed-measure difference merely to
package the setwise estimates would add a large, irrelevant dependency.

This file therefore defines exactly the supremum used in probability theory.
It is intentionally small: the main bridge says that a uniform bound on every
measurable set bounds the supremum.
-/

namespace UniformRandomMALA

open MeasureTheory

noncomputable section

/-- Probability-theory convention for total variation: supremum of the
absolute difference over measurable sets. -/
def setwiseTV {α : Type*} [MeasurableSpace α] (μ ν : Measure α) : ℝ :=
  sSup {r : ℝ | ∃ s : Set α, MeasurableSet s ∧ r = |μ.real s - ν.real s|}

theorem setwiseTV_le_of_forall {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) {c : ℝ}
    (h : ∀ s : Set α, MeasurableSet s → |μ.real s - ν.real s| ≤ c) :
    setwiseTV μ ν ≤ c := by
  apply csSup_le
  · refine ⟨0, (∅ : Set α), MeasurableSet.empty, ?_⟩
    simp
  rintro r ⟨s, hs, rfl⟩
  exact h s hs

/-- Every measurable event discrepancy is bounded by `setwiseTV`.  The
finiteness assumptions are automatic for the transition measures of a
Markov kernel. -/
theorem abs_measureReal_sub_le_setwiseTV
    {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {s : Set α} (hs : MeasurableSet s) :
    |μ.real s - ν.real s| ≤ setwiseTV μ ν := by
  apply le_csSup
  · refine ⟨μ.real Set.univ + ν.real Set.univ, ?_⟩
    rintro r ⟨t, ht, rfl⟩
    have hμ : μ.real t ≤ μ.real Set.univ := by
      exact ENNReal.toReal_mono (measure_ne_top μ Set.univ)
        (measure_mono (Set.subset_univ t))
    have hν : ν.real t ≤ ν.real Set.univ := by
      exact ENNReal.toReal_mono (measure_ne_top ν Set.univ)
        (measure_mono (Set.subset_univ t))
    have hμ0 : 0 ≤ μ.real t := ENNReal.toReal_nonneg
    have hν0 : 0 ≤ ν.real t := ENNReal.toReal_nonneg
    rw [abs_le]
    constructor <;> linarith
  · exact ⟨s, hs, rfl⟩

end
end UniformRandomMALA
