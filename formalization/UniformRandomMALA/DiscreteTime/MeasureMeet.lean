import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Elementary invariance of pointwise-density meets

The measure with density `min f g` does not depend on the chosen common
dominating reference measure.  The proof below avoids the lattice theory of
measures: on a measurable set it splits the integral over `{f ≤ g}` and its
complement, then compares against the corresponding split for the other
reference measure.
-/

namespace UniformRandomMALA

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace DiscreteTime

variable {X : Type*} [MeasurableSpace X]

private lemma setLIntegral_min_split
    {mu : Measure X} {f g : X → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    {s B : Set X} (hs : MeasurableSet s) (hB : MeasurableSet B) :
    (∫⁻ x in s, min (f x) (g x) ∂mu) =
      (∫⁻ x in s ∩ B, min (f x) (g x) ∂mu) +
        ∫⁻ x in s ∩ Bᶜ, min (f x) (g x) ∂mu := by
  have hdisj : Disjoint (s ∩ B) (s ∩ Bᶜ) := by
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    exact hx₂.2 hx₁.2
  rw [← lintegral_union (hs.inter hB.compl) hdisj]
  congr 2
  ext x
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
  tauto

private lemma withDensity_min_apply_le_split
    {mu : Measure X} {f g : X → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    {s B : Set X} (hs : MeasurableSet s) (hB : MeasurableSet B) :
    mu.withDensity (fun x => min (f x) (g x)) s ≤
      mu.withDensity f (s ∩ B) + mu.withDensity g (s ∩ Bᶜ) := by
  rw [withDensity_apply _ hs, withDensity_apply _ (hs.inter hB),
    withDensity_apply _ (hs.inter hB.compl),
    setLIntegral_min_split hf hg hs hB]
  exact add_le_add
    (setLIntegral_mono hf fun x _ => min_le_left _ _)
    (setLIntegral_mono hg fun x _ => min_le_right _ _)

private lemma withDensity_min_apply_eq_canonicalSplit
    {mu : Measure X} {f g : X → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    {s : Set X} (hs : MeasurableSet s) :
    mu.withDensity (fun x => min (f x) (g x)) s =
      mu.withDensity f (s ∩ {x | f x ≤ g x}) +
        mu.withDensity g (s ∩ {x | f x ≤ g x}ᶜ) := by
  let B : Set X := {x | f x ≤ g x}
  have hB : MeasurableSet B := measurableSet_le hf hg
  rw [withDensity_apply _ hs, withDensity_apply _ (hs.inter hB),
    withDensity_apply _ (hs.inter hB.compl),
    setLIntegral_min_split hf hg hs hB]
  congr 1
  · exact setLIntegral_congr_fun (hs.inter hB) fun x hx => min_eq_left hx.2
  · exact setLIntegral_congr_fun (hs.inter hB.compl) fun x hx =>
      min_eq_right (le_of_not_ge hx.2)

/-- Pointwise minimum of two densities is invariant under a change of their
common dominating reference measure. -/
theorem withDensity_min_invariant
    {sigma tau : Measure X} {f g u v : X → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hu : Measurable u) (hv : Measurable v)
    (hfu : sigma.withDensity f = tau.withDensity u)
    (hgv : sigma.withDensity g = tau.withDensity v) :
    sigma.withDensity (fun x => min (f x) (g x)) =
      tau.withDensity (fun x => min (u x) (v x)) := by
  ext s hs
  apply le_antisymm
  · let B : Set X := {x | u x ≤ v x}
    have hB : MeasurableSet B := measurableSet_le hu hv
    calc
      sigma.withDensity (fun x => min (f x) (g x)) s ≤
          sigma.withDensity f (s ∩ B) +
            sigma.withDensity g (s ∩ Bᶜ) :=
        withDensity_min_apply_le_split hf hg hs hB
      _ = tau.withDensity u (s ∩ B) +
            tau.withDensity v (s ∩ Bᶜ) := by rw [hfu, hgv]
      _ = tau.withDensity (fun x => min (u x) (v x)) s :=
        (withDensity_min_apply_eq_canonicalSplit hu hv hs).symm
  · let B : Set X := {x | f x ≤ g x}
    have hB : MeasurableSet B := measurableSet_le hf hg
    calc
      tau.withDensity (fun x => min (u x) (v x)) s ≤
          tau.withDensity u (s ∩ B) +
            tau.withDensity v (s ∩ Bᶜ) :=
        withDensity_min_apply_le_split hu hv hs hB
      _ = sigma.withDensity f (s ∩ B) +
            sigma.withDensity g (s ∩ Bᶜ) := by rw [hfu, hgv]
      _ = sigma.withDensity (fun x => min (f x) (g x)) s :=
        (withDensity_min_apply_eq_canonicalSplit hf hg hs).symm

/-- Under a swap-invariant reference measure, swapping a with-density measure
composes its density with the swap map. -/
theorem map_swap_withDensity_of_swapInvariant
    {sigma : Measure (X × X)} {f : X × X → ℝ≥0∞}
    (hf : Measurable f) (hsymm : Measure.map Prod.swap sigma = sigma) :
    Measure.map Prod.swap (sigma.withDensity f) =
      sigma.withDensity (fun z => f (Prod.swap z)) := by
  have hmp : MeasurePreserving Prod.swap sigma sigma :=
    ⟨measurable_swap, hsymm⟩
  ext s hs
  rw [Measure.map_apply measurable_swap hs,
    withDensity_apply _ (hs.preimage measurable_swap), withDensity_apply _ hs]
  rw [← lintegral_indicator (hs.preimage measurable_swap),
    ← lintegral_indicator hs]
  have h := hmp.lintegral_comp ((hf.comp measurable_swap).indicator hs)
  convert h using 1 <;> apply lintegral_congr <;> intro z <;> rfl

end DiscreteTime

end
end UniformRandomMALA
