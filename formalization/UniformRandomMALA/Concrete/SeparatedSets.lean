import UniformRandomMALA.Concrete.DefectiveConductance
import Mathlib.Topology.MetricSpace.Thickening

/-!
# From Bakry--Ledoux enlargement to separated sets

This module makes the geometric step after Bakry--Ledoux completely
explicit.  The only analytic inputs are the enlargement inequality itself
and the one-dimensional Gaussian shift bound.  Set separation and all
measure subtraction are handled elementarily.
-/

namespace UniformRandomMALA

open MeasureTheory Metric

noncomputable section

namespace Concrete

variable {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]

/-- Bakry--Ledoux metric enlargement in real-valued probability notation.
For measurable sets of mass strictly between zero and one and every positive
radius, the open thickening has mass at least
`Phi (PhiInv (pi.real A) + sqrt m * r)`. Interior masses avoid the singular
quantile endpoints; `r > 0` matches `Metric.thickening`, whose zero-radius
value is empty in mathlib. -/
def BakryLedouxEnlargement
    (π : Measure α) (m : ℝ) (Phi PhiInv : ℝ → ℝ) : Prop :=
  ∀ A : Set α, MeasurableSet A →
    0 < π.real A → π.real A < 1 → ∀ r : ℝ, 0 < r →
    Phi (PhiInv (π.real A) + Real.sqrt m * r) ≤
      π.real (thickening r A)

/-- The elementary one-dimensional normal-CDF input. -/
def GaussianShift (Phi PhiInv : ℝ → ℝ) : Prop :=
  ∀ q s : ℝ, 0 < q → q ≤ 1 / 2 → 0 ≤ s →
    q / 4 * min 1 (s * Real.sqrt (Real.log (1 / q))) ≤
      Phi (PhiInv q + s) - q

private theorem thickening_subset_union_compl_of_separated
    {A B : Set α} {r : ℝ} (hr : 0 < r)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, r ≤ dist x y) :
    thickening r A ⊆ A ∪ (A ∪ B)ᶜ := by
  intro x hx
  by_cases hxA : x ∈ A
  · exact Or.inl hxA
  · apply Or.inr
    simp only [Set.mem_compl_iff, Set.mem_union, not_or]
    refine ⟨hxA, ?_⟩
    intro hxB
    obtain ⟨a, ha, hax⟩ := (mem_thickening_iff.mp hx)
    exact (not_lt_of_ge (hsep a ha x hxB))
      (by simpa only [dist_comm] using hax)

private theorem thickening_subset_union_compl_of_separated_symm
    {A B : Set α} {r : ℝ} (hr : 0 < r)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, r ≤ dist x y) :
    thickening r B ⊆ B ∪ (A ∪ B)ᶜ := by
  intro y hy
  by_cases hyB : y ∈ B
  · exact Or.inl hyB
  · apply Or.inr
    simp only [Set.mem_compl_iff, Set.mem_union, not_or]
    refine ⟨?_, hyB⟩
    intro hyA
    obtain ⟨b, hb, hby⟩ := (mem_thickening_iff.mp hy)
    exact (not_lt_of_ge (by simpa [dist_comm] using hsep y hyA b hb)) hby

/-- Proposition 3.3 from Bakry--Ledoux and the Gaussian shift. -/
theorem separatedSets_of_bakryLedoux_of_gaussianShift
    (π : Measure α) [IsProbabilityMeasure π]
    (m : ℝ) (hm : 0 ≤ m) (Phi PhiInv : ℝ → ℝ)
    (hBL : BakryLedouxEnlargement π m Phi PhiInv)
    (hshift : GaussianShift Phi PhiInv) :
    SeparatedSets π m := by
  intro A B hA hB hAB r hr hsep
  dsimp only
  set q : ℝ := min (π.real A) (π.real B) with hqDef
  intro hqPos hqHalf
  by_cases hr0 : r = 0
  · subst r
    simpa using (measureReal_nonneg : 0 ≤ π.real (A ∪ B)ᶜ)
  have hrPos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  have hsNonneg : 0 ≤ Real.sqrt m * r := mul_nonneg (Real.sqrt_nonneg _) hr
  rcases min_choice (π.real A) (π.real B) with hqA | hqB
  · have hqEq : q = π.real A := by simpa only [q, hqA]
    have hthickSub :=
      thickening_subset_union_compl_of_separated hrPos hsep
    have hthickUpper :
        π.real (thickening r A) ≤
          π.real A + π.real (A ∪ B)ᶜ := by
      exact (measureReal_mono hthickSub).trans (measureReal_union_le _ _)
    have hgauss := hshift q (Real.sqrt m * r) hqPos hqHalf hsNonneg
    have hscale : Real.sqrt m * r * Real.sqrt (Real.log (1 / q)) =
        r * Real.sqrt (m * Real.log (1 / q)) := by
      rw [Real.sqrt_mul hm]
      ring
    rw [hscale] at hgauss
    have hApos : 0 < π.real A := by rwa [← hqEq]
    have hAlt : π.real A < 1 := by
      rw [← hqEq]
      exact hqHalf.trans_lt (by norm_num)
    have hbl := hBL A hA hApos hAlt r hrPos
    rw [← hqEq] at hbl hthickUpper
    exact le_trans hgauss (by linarith)
  · have hqEq : q = π.real B := by simpa only [q, hqB]
    have hthickSub :=
      thickening_subset_union_compl_of_separated_symm hrPos hsep
    have hthickUpper :
        π.real (thickening r B) ≤
          π.real B + π.real (A ∪ B)ᶜ := by
      exact (measureReal_mono hthickSub).trans (measureReal_union_le _ _)
    have hgauss := hshift q (Real.sqrt m * r) hqPos hqHalf hsNonneg
    have hscale : Real.sqrt m * r * Real.sqrt (Real.log (1 / q)) =
        r * Real.sqrt (m * Real.log (1 / q)) := by
      rw [Real.sqrt_mul hm]
      ring
    rw [hscale] at hgauss
    have hBpos : 0 < π.real B := by rwa [← hqEq]
    have hBlt : π.real B < 1 := by
      rw [← hqEq]
      exact hqHalf.trans_lt (by norm_num)
    have hbl := hBL B hB hBpos hBlt r hrPos
    rw [← hqEq] at hbl hthickUpper
    exact le_trans hgauss (by linarith)

end Concrete

end

end UniformRandomMALA
