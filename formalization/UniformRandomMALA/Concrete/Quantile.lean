import Mathlib.Probability.CDF

/-!
# A concrete real quantile

The component-aggregation proof needs a median of a measurable real-valued
function.  Mathlib provides the CDF and its limiting/right-continuity facts,
but not the generalized inverse in the form needed here.  This file isolates
that routine one-dimensional order-theoretic construction.

The endpoint is the Galois equivalence

`lowerQuantile μ u ≤ x ↔ u ≤ cdf μ x`

for `0 < u < 1`.  Keeping this result independent of kernels makes the later
median argument reusable and keeps all uses of completeness of `ℝ` in one
small module.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter

noncomputable section

namespace Concrete

/-- The lower generalized inverse of the CDF:
`Qμ(u) = inf {x | u ≤ Fμ(x)}`. -/
def lowerQuantile (μ : Measure ℝ) [IsProbabilityMeasure μ] (u : ℝ) : ℝ :=
  sInf {x : ℝ | u ≤ cdf μ x}

private lemma quantileLevelSet_nonempty
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {u : ℝ} (hu : u < 1) :
    Set.Nonempty {x : ℝ | u ≤ cdf μ x} := by
  have hev : ∀ᶠ x in atTop, u ≤ cdf μ x := by
    have h1 := (tendsto_order.mp (tendsto_cdf_atTop μ)).1 u hu
    exact h1.mono fun x hx => le_of_lt hx
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  exact ⟨N, hN N (le_refl _)⟩

private lemma quantileLevelSet_bddBelow
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {u : ℝ} (hu : 0 < u) :
    BddBelow {x : ℝ | u ≤ cdf μ x} := by
  have hev : ∀ᶠ x in atBot, cdf μ x < u :=
    (tendsto_order.mp (tendsto_cdf_atBot μ)).2 u hu
  rw [Filter.eventually_atBot] at hev
  obtain ⟨N, hN⟩ := hev
  exact ⟨N, fun x hx => by
    by_contra hlt
    push_neg at hlt
    exact absurd hx (not_le.mpr (hN x (le_of_lt hlt)))⟩

/-- Monotonicity of the lower quantile on the open unit interval. -/
theorem lowerQuantile_mono
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {u v : ℝ} (huv : u ≤ v) (hv : v < 1) (hu : 0 < u) :
    lowerQuantile μ u ≤ lowerQuantile μ v :=
  csInf_le_csInf
    (quantileLevelSet_bddBelow μ hu)
    (quantileLevelSet_nonempty μ hv)
    (fun _ hx => le_trans huv hx)

/-- The easy half of the quantile--CDF Galois connection. -/
lemma lowerQuantile_le_of_le_cdf
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {u x : ℝ} (hu : 0 < u) (h : u ≤ cdf μ x) :
    lowerQuantile μ u ≤ x :=
  csInf_le (quantileLevelSet_bddBelow μ hu) h

/-- Right-continuity of the CDF supplies the converse Galois implication. -/
lemma le_cdf_of_lowerQuantile_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {u x : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (h : lowerQuantile μ u ≤ x) :
    u ≤ cdf μ x := by
  suffices hq : u ≤ cdf μ (lowerQuantile μ u) from
    le_trans hq (monotone_cdf μ h)
  set S : Set ℝ := {y : ℝ | u ≤ cdf μ y}
  set q : ℝ := sInf S
  change u ≤ cdf μ q
  have hne : S.Nonempty := quantileLevelSet_nonempty μ hu1
  have hbd : BddBelow S := quantileLevelSet_bddBelow μ hu0
  have habove : ∀ y, q < y → u ≤ cdf μ y := by
    intro y hy
    obtain ⟨z, hzS, hzy⟩ := exists_lt_of_csInf_lt hne hy
    exact le_trans hzS (monotone_cdf μ (le_of_lt hzy))
  have hrc := (cdf μ).right_continuous q
  by_contra hlt
  push_neg at hlt
  rw [Metric.continuousWithinAt_iff] at hrc
  obtain ⟨δ, hδ, hrc'⟩ := hrc (u - cdf μ q) (sub_pos.mpr hlt)
  obtain ⟨z, hzS, hzlt⟩ := exists_lt_of_csInf_lt hne
    (show q < q + δ by linarith)
  have hzge : q ≤ z := csInf_le hbd hzS
  have hdist : dist (cdf μ z) (cdf μ q) < u - cdf μ q := by
    apply hrc' (Set.mem_Ici.mpr hzge)
    rw [Real.dist_eq, abs_of_nonneg (by linarith)]
    linarith
  rw [Real.dist_eq] at hdist
  have hzltu : cdf μ z < u := by
    have habs := abs_lt.mp hdist
    linarith
  exact absurd hzS (not_le.mpr hzltu)

/-- The generalized inverse/CDF Galois connection on `0 < u < 1`. -/
theorem lowerQuantile_le_iff
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {u x : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    lowerQuantile μ u ≤ x ↔ u ≤ cdf μ x :=
  ⟨le_cdf_of_lowerQuantile_le μ hu0 hu1,
    lowerQuantile_le_of_le_cdf μ hu0⟩

/-- For a continuous distribution function, the generalized inverse attains
every level in the open unit interval.  This is the exact inverse identity
needed for the standard Gaussian; isolating it here avoids introducing a
separate inverse-function package. -/
theorem cdf_lowerQuantile_eq
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hcont : Continuous (cdf μ))
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    cdf μ (lowerQuantile μ u) = u := by
  apply le_antisymm
  · by_contra hnot
    have hstrict : u < cdf μ (lowerQuantile μ u) :=
      lt_of_not_ge hnot
    have hc := Metric.continuousAt_iff.mp
      (hcont.continuousAt : ContinuousAt (cdf μ) (lowerQuantile μ u))
      (cdf μ (lowerQuantile μ u) - u) (sub_pos.mpr hstrict)
    obtain ⟨δ, hδ0, hδ⟩ := hc
    let x := lowerQuantile μ u - δ / 2
    have hxlt : x < lowerQuantile μ u := by
      dsimp [x]
      linarith
    have hdist : dist x (lowerQuantile μ u) < δ := by
      rw [Real.dist_eq]
      dsimp [x]
      rw [abs_of_nonpos (by linarith)]
      linarith
    have hclose := hδ hdist
    rw [Real.dist_eq] at hclose
    have hux : u < cdf μ x := by
      have habs := abs_lt.mp hclose
      linarith
    have hqx := lowerQuantile_le_of_le_cdf μ hu0 hux.le
    exact (not_le_of_gt hxlt) hqx
  · exact le_cdf_of_lowerQuantile_le μ hu0 hu1 le_rfl

end Concrete

end

end UniformRandomMALA
