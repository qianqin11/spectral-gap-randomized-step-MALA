import UniformRandomMALA.Concrete.Conductance
import UniformRandomMALA.Concrete.SetwiseTV
import UniformRandomMALA.DefectiveArithmetic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# The generic defective-conductance argument

This file formalizes Appendix D.1 directly for a Mathlib probability
measure and Markov kernel.  The construction uses only measurable sets,
Markov's inequality, reversibility, and the event definition of total
variation.  In particular, it introduces no diffusion or continuous-time
objects.

The Gaussian input is isolated as a separated-set lower bound.  A later
module can obtain that bound from Bakry--Ledoux; everything in this file is
elementary measure theory.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace Concrete

variable {α : Type*} [MeasurableSpace α]

/-- Concrete real-valued formulation of Proposition 3.3.  It is deliberately
stated with pointwise separation, avoiding an additional extended-real
`infDist` API. -/
def SeparatedSets
    [PseudoMetricSpace α] (π : Measure α) (m : ℝ) : Prop :=
  ∀ A B : Set α, MeasurableSet A → MeasurableSet B → Disjoint A B →
    ∀ r : ℝ, 0 ≤ r →
      (∀ x ∈ A, ∀ y ∈ B, r ≤ dist x y) →
      let q := min (π.real A) (π.real B)
      0 < q → q ≤ 1 / 2 →
        q / 4 * min 1 (r * Real.sqrt (m * Real.log (1 / q))) ≤
          π.real (A ∪ B)ᶜ

/-- Points on the source side whose probability of crossing the cut is at
least `1/16`. -/
def badEscapeSet (K : Kernel α α) (S : Set α) : Set α :=
  S ∩ {x | (16 : ℝ≥0∞)⁻¹ ≤ K x Sᶜ}

/-- The retained part of `S`: good points with crossing probability below
`1/16`. -/
def retainedLeft (K : Kernel α α) (G S : Set α) : Set α :=
  S ∩ G ∩ {x | K x Sᶜ < (16 : ℝ≥0∞)⁻¹}

/-- The retained part of the complementary side. -/
def retainedRight (K : Kernel α α) (G S : Set α) : Set α :=
  Sᶜ ∩ G ∩ {x | K x S < (16 : ℝ≥0∞)⁻¹}

theorem measurableSet_badEscapeSet
    (K : Kernel α α) {S : Set α} (hS : MeasurableSet S) :
    MeasurableSet (badEscapeSet K S) := by
  exact hS.inter (measurableSet_le measurable_const
    (K.measurable_coe hS.compl))

theorem measurableSet_retainedLeft
    (K : Kernel α α) {G S : Set α}
    (hG : MeasurableSet G) (hS : MeasurableSet S) :
    MeasurableSet (retainedLeft K G S) := by
  exact (hS.inter hG).inter
    (measurableSet_lt (K.measurable_coe hS.compl) measurable_const)

theorem measurableSet_retainedRight
    (K : Kernel α α) {G S : Set α}
    (hG : MeasurableSet G) (hS : MeasurableSet S) :
    MeasurableSet (retainedRight K G S) := by
  exact (hS.compl.inter hG).inter
    (measurableSet_lt (K.measurable_coe hS) measurable_const)

/-- Markov's inequality in exactly the form used in Appendix D.1. -/
theorem measure_badEscapeSet_le
    (π : Measure α) (K : Kernel α α)
    {S : Set α} (hS : MeasurableSet S) :
    π (badEscapeSet K S) ≤
      (16 : ℝ≥0∞) * flow π K S Sᶜ := by
  let ε : ℝ≥0∞ := (16 : ℝ≥0∞)⁻¹
  have hmarkov := meas_ge_le_lintegral_div
    (μ := π.restrict S) (ε := ε)
    (K.measurable_coe hS.compl).aemeasurable
    (by simp [ε]) (by simp [ε])
  have hrewrite :
      (π.restrict S) {x | ε ≤ K x Sᶜ} = π (badEscapeSet K S) := by
    rw [Measure.restrict_apply
      (measurableSet_le measurable_const (K.measurable_coe hS.compl))]
    simp only [badEscapeSet, ε]
    rw [Set.inter_comm]
  rw [hrewrite] at hmarkov
  calc
    π (badEscapeSet K S) ≤
        (∫⁻ x in S, K x Sᶜ ∂π) / ε := hmarkov
    _ = (16 : ℝ≥0∞) * flow π K S Sᶜ := by
      simp [flow, ε, div_eq_mul_inv, mul_comm]

/-- The left retained set is obtained from `S` by deleting only exceptional
points and high-escape points. -/
theorem source_subset_retainedLeft_union
    (K : Kernel α α) (G S : Set α) :
    S ⊆ retainedLeft K G S ∪ Gᶜ ∪ badEscapeSet K S := by
  intro x hx
  by_cases hxG : x ∈ G
  · by_cases hcross : K x Sᶜ < (16 : ℝ≥0∞)⁻¹
    · exact Or.inl (Or.inl ⟨⟨hx, hxG⟩, hcross⟩)
    · exact Or.inr ⟨hx, le_of_not_gt hcross⟩
  · exact Or.inl (Or.inr hxG)

/-- The same deletion statement on the complementary side. -/
theorem complement_subset_retainedRight_union
    (K : Kernel α α) (G S : Set α) :
    Sᶜ ⊆ retainedRight K G S ∪ Gᶜ ∪ badEscapeSet K Sᶜ := by
  intro x hx
  by_cases hxG : x ∈ G
  · by_cases hcross : K x S < (16 : ℝ≥0∞)⁻¹
    · exact Or.inl (Or.inl ⟨⟨hx, hxG⟩, hcross⟩)
    · have : x ∈ badEscapeSet K Sᶜ := by
        simpa only [badEscapeSet, compl_compl] using
          (show x ∈ Sᶜ ∩ {y | (16 : ℝ≥0∞)⁻¹ ≤ K y S} from
            ⟨hx, le_of_not_gt hcross⟩)
      exact Or.inr this
  · exact Or.inl (Or.inr hxG)

/-- A retained left/right pair has event discrepancy strictly above `7/8`.
This is the only place where the threshold `1/16` is used. -/
theorem retained_event_discrepancy
    (K : Kernel α α) [IsMarkovKernel K]
    {G S : Set α} (hS : MeasurableSet S)
    {x y : α} (hx : x ∈ retainedLeft K G S)
    (hy : y ∈ retainedRight K G S) :
    (7 / 8 : ℝ) < (K x).real S - (K y).real S := by
  have hxCross : K x Sᶜ < (16 : ℝ≥0∞)⁻¹ := hx.2
  have hyCross : K y S < (16 : ℝ≥0∞)⁻¹ := hy.2
  have hprobx : K x S + K x Sᶜ = 1 := by
    rw [← measure_union disjoint_compl_right hS.compl,
      Set.union_compl_self, measure_univ]
  have hxReal : (15 / 16 : ℝ) < (K x).real S := by
    have htopS : K x S ≠ ∞ := measure_ne_top (K x) S
    have htopSc : K x Sᶜ ≠ ∞ := measure_ne_top (K x) Sᶜ
    have hxCrossReal : (K x).real Sᶜ < (1 / 16 : ℝ) := by
      have h := ENNReal.toReal_strict_mono
        (by norm_num : (16 : ℝ≥0∞)⁻¹ ≠ ∞) hxCross
      simpa only [Measure.real, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
        one_div] using h
    have hsumReal : (K x).real S + (K x).real Sᶜ = 1 := by
      change (K x S).toReal + (K x Sᶜ).toReal = 1
      rw [← ENNReal.toReal_add htopS htopSc, hprobx]
      norm_num
    linarith
  have hyReal : (K y).real S < (1 / 16 : ℝ) := by
    have h := ENNReal.toReal_strict_mono
      (by norm_num : (16 : ℝ≥0∞)⁻¹ ≠ ∞) hyCross
    simpa only [Measure.real, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
      one_div] using h
  linarith

/-- Real-valued form of the Markov deletion bound. -/
theorem measureReal_badEscapeSet_le
    (π : Measure α) [IsFiniteMeasure π]
    (K : Kernel α α) [IsMarkovKernel K]
    {S : Set α} (hS : MeasurableSet S) :
    π.real (badEscapeSet K S) ≤
      16 * (flow π K S Sᶜ).toReal := by
  have h := measure_badEscapeSet_le π K hS
  have hright : (16 : ℝ≥0∞) * flow π K S Sᶜ ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) (flow_ne_top π K S Sᶜ hS)
  have hreal := ENNReal.toReal_mono hright h
  simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_ofNat] using hreal

/-- Quantitative retained mass on the source side, before inserting any
particular exceptional-set estimate. -/
theorem measureReal_source_le_retainedLeft_add
    (π : Measure α) [IsFiniteMeasure π]
    (K : Kernel α α) [IsMarkovKernel K]
    {G S : Set α} (hG : MeasurableSet G) (hS : MeasurableSet S) :
    π.real S ≤ π.real (retainedLeft K G S) + π.real Gᶜ +
      16 * (flow π K S Sᶜ).toReal := by
  calc
    π.real S ≤
        π.real (retainedLeft K G S ∪ Gᶜ ∪ badEscapeSet K S) :=
      measureReal_mono (source_subset_retainedLeft_union K G S)
    _ ≤ (π.real (retainedLeft K G S) + π.real Gᶜ) +
        π.real (badEscapeSet K S) := by
      have houter := measureReal_union_le (μ := π)
        (retainedLeft K G S ∪ Gᶜ) (badEscapeSet K S)
      have hinner := measureReal_union_le (μ := π)
        (retainedLeft K G S) Gᶜ
      linarith
    _ ≤ π.real (retainedLeft K G S) + π.real Gᶜ +
        16 * (flow π K S Sᶜ).toReal := by
      have hbad := measureReal_badEscapeSet_le π K hS
      linarith

/-- Quantitative retained mass on the complementary side.  Reversibility
identifies its bad-escape flow with the original cut flow. -/
theorem measureReal_complement_le_retainedRight_add
    (π : Measure α) [IsFiniteMeasure π]
    (K : Kernel α α) [IsMarkovKernel K]
    (hrev : Kernel.IsReversible K π)
    {G S : Set α} (hG : MeasurableSet G) (hS : MeasurableSet S) :
    π.real Sᶜ ≤ π.real (retainedRight K G S) + π.real Gᶜ +
      16 * (flow π K S Sᶜ).toReal := by
  have hbad := measureReal_badEscapeSet_le π K hS.compl
  rw [compl_compl, flow_symm π K hrev hS.compl hS] at hbad
  calc
    π.real Sᶜ ≤
        π.real (retainedRight K G S ∪ Gᶜ ∪ badEscapeSet K Sᶜ) :=
      measureReal_mono (complement_subset_retainedRight_union K G S)
    _ ≤ (π.real (retainedRight K G S) + π.real Gᶜ) +
        π.real (badEscapeSet K Sᶜ) := by
      have houter := measureReal_union_le (μ := π)
        (retainedRight K G S ∪ Gᶜ) (badEscapeSet K Sᶜ)
      have hinner := measureReal_union_le (μ := π)
        (retainedRight K G S) Gᶜ
      linarith
    _ ≤ π.real (retainedRight K G S) + π.real Gᶜ +
        16 * (flow π K S Sᶜ).toReal := by
      linarith

theorem retainedLeft_subset (K : Kernel α α) (G S : Set α) :
    retainedLeft K G S ⊆ S := fun _ hx => hx.1.1

theorem retainedRight_subset (K : Kernel α α) (G S : Set α) :
    retainedRight K G S ⊆ Sᶜ := fun _ hx => hx.1.1

theorem disjoint_retainedLeft_retainedRight
    (K : Kernel α α) (G S : Set α) :
    Disjoint (retainedLeft K G S) (retainedRight K G S) :=
  disjoint_compl_right.mono
    (retainedLeft_subset K G S) (retainedRight_subset K G S)

/-- The complement of the two retained sets consists only of the exceptional
set and the two high-escape sets. -/
theorem retained_union_compl_subset_removed
    (K : Kernel α α) (G S : Set α) :
    (retainedLeft K G S ∪ retainedRight K G S)ᶜ ⊆
      Gᶜ ∪ badEscapeSet K S ∪ badEscapeSet K Sᶜ := by
  intro x hx
  have hxL : x ∉ retainedLeft K G S := fun h => hx (Or.inl h)
  have hxR : x ∉ retainedRight K G S := fun h => hx (Or.inr h)
  by_cases hxG : x ∈ G
  · by_cases hxS : x ∈ S
    · have hcross : (16 : ℝ≥0∞)⁻¹ ≤ K x Sᶜ := by
        by_contra hnot
        exact hxL ⟨⟨hxS, hxG⟩, lt_of_not_ge hnot⟩
      exact Or.inl (Or.inr ⟨hxS, hcross⟩)
    · have hxSc : x ∈ Sᶜ := hxS
      have hcross : (16 : ℝ≥0∞)⁻¹ ≤ K x S := by
        by_contra hnot
        exact hxR ⟨⟨hxSc, hxG⟩, lt_of_not_ge hnot⟩
      have hbad : x ∈ badEscapeSet K Sᶜ := by
        simpa only [badEscapeSet, compl_compl] using
          (show x ∈ Sᶜ ∩ {y | (16 : ℝ≥0∞)⁻¹ ≤ K y S} from
            ⟨hxSc, hcross⟩)
      exact Or.inr hbad
  · exact Or.inl (Or.inl hxG)

/-- The sharp union bound used in the contradiction: each high-escape set
costs `16` times the same reversible cut flow. -/
theorem measureReal_retained_union_compl_le
    (π : Measure α) [IsFiniteMeasure π]
    (K : Kernel α α) [IsMarkovKernel K]
    (hrev : Kernel.IsReversible K π)
    {G S : Set α} (hG : MeasurableSet G) (hS : MeasurableSet S) :
    π.real (retainedLeft K G S ∪ retainedRight K G S)ᶜ ≤
      π.real Gᶜ + 32 * (flow π K S Sᶜ).toReal := by
  have hbadL := measureReal_badEscapeSet_le π K hS
  have hbadR := measureReal_badEscapeSet_le π K hS.compl
  rw [compl_compl, flow_symm π K hrev hS.compl hS] at hbadR
  calc
    π.real (retainedLeft K G S ∪ retainedRight K G S)ᶜ ≤
        π.real (Gᶜ ∪ badEscapeSet K S ∪ badEscapeSet K Sᶜ) :=
      measureReal_mono (retained_union_compl_subset_removed K G S)
    _ ≤ (π.real Gᶜ + π.real (badEscapeSet K S)) +
        π.real (badEscapeSet K Sᶜ) := by
      have houter := measureReal_union_le (μ := π)
        (Gᶜ ∪ badEscapeSet K S) (badEscapeSet K Sᶜ)
      have hinner := measureReal_union_le (μ := π)
        Gᶜ (badEscapeSet K S)
      linarith
    _ ≤ π.real Gᶜ + 32 * (flow π K S Sᶜ).toReal := by
      nlinarith

/-- Monotonicity and square-root arithmetic which compare the separated-set
scale at retained mass `q` with the original defective-conductance scale at
mass `s`. -/
theorem defective_scale_comparison
    (m t s q : ℝ) (hm : 0 < m) (ht : 0 < t)
    (hs : 0 < s) (hsHalf : s ≤ 1 / 2)
    (hq : 0 < q) (hqs : q ≤ s) :
    min 1 (Real.sqrt (m * t * Real.log (1 / s))) / 16 ≤
      min 1 ((Real.sqrt t / 16) *
        Real.sqrt (m * Real.log (1 / q))) := by
  have hsOne : s ≤ 1 := hsHalf.trans (by norm_num)
  have hqOne : q ≤ 1 := hqs.trans hsOne
  have hinv : 1 / s ≤ 1 / q :=
    one_div_le_one_div_of_le hq hqs
  have hinvSOne : 1 ≤ 1 / s := by
    exact one_le_one_div hs hsOne
  have hlogS : 0 ≤ Real.log (1 / s) :=
    Real.log_nonneg hinvSOne
  have hlogQ : 0 ≤ Real.log (1 / q) := by
    exact Real.log_nonneg (one_le_one_div hq hqOne)
  have hlog : Real.log (1 / s) ≤ Real.log (1 / q) :=
    Real.log_le_log (by positivity) hinv
  have hinner :
      m * Real.log (1 / s) ≤ m * Real.log (1 / q) :=
    mul_le_mul_of_nonneg_left hlog hm.le
  have hsqrtInner :
      Real.sqrt (m * Real.log (1 / s)) ≤
        Real.sqrt (m * Real.log (1 / q)) :=
    Real.sqrt_le_sqrt hinner
  have hsqrtFactor :
      Real.sqrt (m * t * Real.log (1 / s)) =
        Real.sqrt t * Real.sqrt (m * Real.log (1 / s)) := by
    rw [show m * t * Real.log (1 / s) =
        t * (m * Real.log (1 / s)) by ring,
      Real.sqrt_mul ht.le]
  have hargScale :
      Real.sqrt (m * t * Real.log (1 / s)) / 16 ≤
        (Real.sqrt t / 16) *
          Real.sqrt (m * Real.log (1 / q)) := by
    rw [hsqrtFactor]
    have := mul_le_mul_of_nonneg_left hsqrtInner (Real.sqrt_nonneg t)
    nlinarith
  have hbetaOne :
      min 1 (Real.sqrt (m * t * Real.log (1 / s))) / 16 ≤ 1 := by
    have := min_le_left (1 : ℝ) (Real.sqrt (m * t * Real.log (1 / s)))
    nlinarith
  have hbetaArg :
      min 1 (Real.sqrt (m * t * Real.log (1 / s))) / 16 ≤
        (Real.sqrt t / 16) *
          Real.sqrt (m * Real.log (1 / q)) := by
    have hmin := min_le_right (1 : ℝ)
      (Real.sqrt (m * t * Real.log (1 / s)))
    exact (div_le_div_of_nonneg_right hmin (by norm_num)).trans hargScale
  exact le_min hbetaOne hbetaArg

/-- Consequently retained points cannot be close whenever the kernel has
the local `3/4` total-variation overlap property. -/
theorem retained_points_far
    [PseudoMetricSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    {G S : Set α} (hS : MeasurableSet S) {r : ℝ}
    (hclose : ∀ x ∈ G, ∀ y ∈ G,
      dist x y ≤ r → setwiseTV (K x) (K y) ≤ 3 / 4)
    {x y : α} (hx : x ∈ retainedLeft K G S)
    (hy : y ∈ retainedRight K G S) :
    r < dist x y := by
  by_contra hnot
  have htv := hclose x hx.1.2 y hy.1.2 (le_of_not_gt hnot)
  have hevent := abs_measureReal_sub_le_setwiseTV (K x) (K y) hS
  have hdiff := retained_event_discrepancy K hS hx hy
  have habs : (K x).real S - (K y).real S ≤
      |(K x).real S - (K y).real S| := le_abs_self _
  linarith

/-- Appendix D.1, with its sole geometric input exposed as
`SeparatedSets π m`.  All other assumptions are literal measure/kernel
properties. -/
theorem defectiveConductance_of_separatedSets
    [PseudoMetricSpace α] [BorelSpace α]
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K]
    (m t : ℝ) (hm : 0 < m) (ht : 0 < t)
    (hrev : Kernel.IsReversible K π)
    (hseparated : SeparatedSets π m)
    {G S : Set α} (hG : MeasurableSet G) (hS : MeasurableSet S)
    (hoverlap : ∀ x ∈ G, ∀ y ∈ G,
      dist x y ≤ Real.sqrt t / 16 →
        setwiseTV (K x) (K y) ≤ 3 / 4)
    (hSpos : 0 < π.real S) (hShalf : π.real S ≤ 1 / 2)
    (hexceptional : π.real Gᶜ ≤
      π.real S * min 1
        (Real.sqrt (m * t * Real.log (1 / π.real S))) /
          (2 : ℝ) ^ 13) :
    π.real S * min 1
        (Real.sqrt (m * t * Real.log (1 / π.real S))) /
          (2 : ℝ) ^ 13 ≤
      (boundaryFlow π K S).toReal := by
  let s : ℝ := π.real S
  let beta : ℝ := min 1 (Real.sqrt (m * t * Real.log (1 / s)))
  let F : ℝ := (boundaryFlow π K S).toReal
  have hs : 0 < s := hSpos
  have hsHalf : s ≤ 1 / 2 := hShalf
  have hsOne : s ≤ 1 := hsHalf.trans (by norm_num)
  have hinvTwo : (2 : ℝ) ≤ 1 / s := by
    apply (le_div_iff₀ hs).2
    nlinarith
  have hlog : 0 < Real.log (1 / s) := by
    exact Real.log_pos (lt_of_lt_of_le (by norm_num) hinvTwo)
  have hroot : 0 < Real.sqrt (m * t * Real.log (1 / s)) := by
    apply Real.sqrt_pos.2
    positivity
  have hbetaPos : 0 < beta := by
    exact lt_min (by norm_num) hroot
  have hbeta0 : 0 ≤ beta := hbetaPos.le
  have hbetaOne : beta ≤ 1 := min_le_left _ _
  have hexceptional' : π.real Gᶜ ≤ s * beta / (2 : ℝ) ^ 13 := by
    simpa only [s, beta] using hexceptional
  change s * beta / (2 : ℝ) ^ 13 ≤ F
  by_contra hnot
  have hF : F < s * beta / (2 : ℝ) ^ 13 := lt_of_not_ge hnot
  let S1 : Set α := retainedLeft K G S
  let S2 : Set α := retainedRight K G S
  have hS1m : MeasurableSet S1 := measurableSet_retainedLeft K hG hS
  have hS2m : MeasurableSet S2 := measurableSet_retainedRight K hG hS
  have hleftRaw := measureReal_source_le_retainedLeft_add π K hG hS
  have hrightRaw := measureReal_complement_le_retainedRight_add
    π K hrev hG hS
  have hretainedArithmetic := retained_mass_at_least_half
    s beta (π.real Gᶜ) F hs hbeta0 hbetaOne hexceptional' hF
  have hS1mass : s / 2 < π.real S1 := by
    change s ≤ π.real S1 + π.real Gᶜ + 16 * F at hleftRaw
    linarith
  have hprobCompl : π.real Sᶜ = 1 - s := by
    rw [measureReal_compl hS, probReal_univ]
  have hS2mass : s / 2 < π.real S2 := by
    change π.real Sᶜ ≤ π.real S2 + π.real Gᶜ + 16 * F at hrightRaw
    rw [hprobCompl] at hrightRaw
    have hside : s ≤ 1 - s := by linarith
    linarith
  let q : ℝ := min (π.real S1) (π.real S2)
  have hqLower : s / 2 ≤ q := by
    exact le_min hS1mass.le hS2mass.le
  have hqPos : 0 < q := lt_of_lt_of_le (half_pos hs) hqLower
  have hS1sub : S1 ⊆ S := retainedLeft_subset K G S
  have hqS1 : q ≤ π.real S1 := min_le_left _ _
  have hS1le : π.real S1 ≤ s := by
    exact measureReal_mono hS1sub
  have hqs : q ≤ s := hqS1.trans hS1le
  have hqHalf : q ≤ 1 / 2 := hqs.trans hsHalf
  have hdisjoint : Disjoint S1 S2 :=
    disjoint_retainedLeft_retainedRight K G S
  have hfar : ∀ x ∈ S1, ∀ y ∈ S2,
      Real.sqrt t / 16 ≤ dist x y := by
    intro x hx y hy
    exact (retained_points_far K hS hoverlap hx hy).le
  have hsep :
      q / 4 * min 1 ((Real.sqrt t / 16) *
          Real.sqrt (m * Real.log (1 / q))) ≤
        π.real (S1 ∪ S2)ᶜ := by
    exact hseparated S1 S2 hS1m hS2m hdisjoint
      (Real.sqrt t / 16) (by positivity) hfar hqPos hqHalf
  have hscale : beta / 16 ≤
      min 1 ((Real.sqrt t / 16) *
        Real.sqrt (m * Real.log (1 / q))) := by
    exact defective_scale_comparison m t s q hm ht hs hsHalf hqPos hqs
  have hlower : s * beta / 128 ≤ π.real (S1 ∪ S2)ᶜ :=
    retained_separation_constant s q beta
      (min 1 ((Real.sqrt t / 16) *
        Real.sqrt (m * Real.log (1 / q))))
      (π.real (S1 ∪ S2)ᶜ) hs hbeta0 hqLower hscale hsep
  have hupper : π.real (S1 ∪ S2)ᶜ ≤ π.real Gᶜ + 32 * F := by
    simpa only [S1, S2, F, boundaryFlow] using
      measureReal_retained_union_compl_le π K hrev hG hS
  exact defective_conductance_constant_contradiction
    s beta (π.real (S1 ∪ S2)ᶜ) (π.real Gᶜ) F
    hs hbetaPos hlower hupper hexceptional' hF

end Concrete

end

end UniformRandomMALA
