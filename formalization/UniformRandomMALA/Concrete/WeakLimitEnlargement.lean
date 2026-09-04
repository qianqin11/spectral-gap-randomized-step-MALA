import UniformRandomMALA.DiscreteTime.ProkhorovBridge
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Stability of enlargement inequalities under weak convergence

This file isolates the Portmanteau argument used in the Bakry--Ledoux
construction.  The output thickening is never treated as a closed set.
Instead, an open input thickening is enlarged once more and placed inside a
closed thickening.  The liminf inequality is used on the input and the limsup
inequality on that closed output.

The profile is kept abstract.  `LowerContinuousProfile` is the exact
one-sided approximation property needed at the final step; it is satisfied by
the endpoint-corrected Gaussian shift profile developed in the normal-profile
module.
-/

namespace UniformRandomMALA

open Filter MeasureTheory Metric Set Topology
open scoped ENNReal Topology

noncomputable section

namespace Concrete

/-- A two-variable enlargement profile is closed from below if its value at a
probability mass `q` and a positive shift `t` is controlled by all values at
strictly smaller masses and strictly smaller nonnegative shifts.  This
formulation includes the endpoint convention at `q = 0`. -/
def LowerContinuousProfile (J : ℝ≥0∞ → ℝ → ℝ≥0∞) : Prop :=
  ∀ q t b, q ≤ 1 → 0 < t →
    (∀ q' u, q' < q → 0 ≤ u → u < t → J q' u ≤ b) →
      J q t ≤ b

/-- The fixed-profile Portmanteau sandwich.  A continuous monotone function
of the mass of an open set may be compared with the mass of a closed set in
the weak limit. -/
theorem profile_measure_open_le_closed_of_tendsto
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {mu : ℕ → ProbabilityMeasure X} {muLimit : ProbabilityMeasure X}
    (hmu : Tendsto mu atTop (nhds muLimit))
    {G F : Set X} (hG : IsOpen G) (hF : IsClosed F)
    (j : ℝ≥0∞ → ℝ≥0∞) (hjMono : Monotone j) (hjCont : Continuous j)
    (hbound : ∀ᶠ n in atTop,
      j ((mu n : Measure X) G) ≤ (mu n : Measure X) F) :
    j ((muLimit : Measure X) G) ≤ (muLimit : Measure X) F := by
  have hopen : (muLimit : Measure X) G ≤
      atTop.liminf (fun n => (mu n : Measure X) G) :=
    ProbabilityMeasure.le_liminf_measure_open_of_tendsto hmu hG
  calc
    j ((muLimit : Measure X) G) ≤
        j (atTop.liminf (fun n => (mu n : Measure X) G)) :=
      hjMono hopen
    _ = atTop.liminf (fun n => j ((mu n : Measure X) G)) := by
      simpa only [Function.comp_def] using
        hjMono.map_liminf_of_continuousAt
          (fun n => (mu n : Measure X) G) hjCont.continuousAt
    _ ≤ atTop.limsup (fun n => (mu n : Measure X) F) :=
      Filter.liminf_le_limsup_of_frequently_le
        hbound.frequently
    _ ≤ (muLimit : Measure X) F :=
      ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hmu hF

/-- Compact-input form of the weak-limit argument.  The varying scale
constants are handled before Portmanteau: if `c_n -> c` and `u*c < s`, then
eventually `u ≤ s/c_n`. -/
theorem profile_compact_le_closedThickening_of_weakLimit
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {mu : ℕ → ProbabilityMeasure X} {muLimit : ProbabilityMeasure X}
    {cSeq : ℕ → ℝ} {c : ℝ}
    (hmu : Tendsto mu atTop (nhds muLimit))
    (hc : Tendsto cSeq atTop (nhds c))
    (hcSeq : ∀ n, 0 < cSeq n)
    (J : ℝ≥0∞ → ℝ → ℝ≥0∞)
    (hJmass : ∀ u, Monotone (fun q => J q u))
    (hJmassCont : ∀ u, Continuous (fun q => J q u))
    (hJshift : ∀ q, Monotone (J q))
    (hfinite : ∀ n (A : Set X), MeasurableSet A →
      ∀ r : ℝ, 0 < r →
        J ((mu n : Measure X) A) (r / cSeq n) ≤
          (mu n : Measure X) (thickening r A))
    {K : Set X}
    {u s epsilon : ℝ} (hs : 0 < s)
    (hus : u * c < s) (hepsilon : 0 < epsilon) :
    J ((muLimit : Measure X) K) u ≤
      (muLimit : Measure X) (cthickening (s + epsilon) K) := by
  let G : Set X := thickening epsilon K
  let F : Set X := cthickening (s + epsilon) K
  have heventually : ∀ᶠ n in atTop, u * cSeq n < s := by
    have htendsto : Tendsto (fun n => u * cSeq n) atTop (nhds (u * c)) :=
      tendsto_const_nhds.mul hc
    exact (tendsto_order.1 htendsto).2 s hus
  have hbound : ∀ᶠ n in atTop,
      J ((mu n : Measure X) G) u ≤ (mu n : Measure X) F := by
    filter_upwards [heventually] with n hn
    have huc : u ≤ s / cSeq n := by
      rw [le_div_iff₀ (hcSeq n)]
      exact hn.le
    calc
      J ((mu n : Measure X) G) u ≤
          J ((mu n : Measure X) G) (s / cSeq n) :=
        hJshift _ huc
      _ ≤ (mu n : Measure X) (thickening s G) :=
        hfinite n G isOpen_thickening.measurableSet s hs
      _ ≤ (mu n : Measure X) F := by
        apply measure_mono
        exact (thickening_thickening_subset s epsilon K).trans
          (by simpa only [add_comm] using
            thickening_subset_cthickening (s + epsilon) K)
  have htransfer : J ((muLimit : Measure X) G) u ≤
      (muLimit : Measure X) F :=
    profile_measure_open_le_closed_of_tendsto hmu isOpen_thickening
      isClosed_cthickening (fun q => J q u) (hJmass u) (hJmassCont u) hbound
  refine (hJmass u ?_).trans htransfer
  apply measure_mono
  exact self_subset_thickening hepsilon K

/-- The usable interior form of W1--W3.  Every mass and shift strictly below
the desired endpoint survives the weak limit. -/
theorem profile_lt_enlargement_of_weakLimit
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {mu : ℕ → ProbabilityMeasure X} {muLimit : ProbabilityMeasure X}
    [Measure.Regular (muLimit : Measure X)]
    {cSeq : ℕ → ℝ} {c : ℝ}
    (hmu : Tendsto mu atTop (nhds muLimit))
    (hc : Tendsto cSeq atTop (nhds c)) (hcPos : 0 < c)
    (hcSeq : ∀ n, 0 < cSeq n)
    (J : ℝ≥0∞ → ℝ → ℝ≥0∞)
    (hJmass : ∀ u, Monotone (fun q => J q u))
    (hJmassCont : ∀ u, Continuous (fun q => J q u))
    (hJshift : ∀ q, Monotone (J q))
    (hfinite : ∀ n (A : Set X), MeasurableSet A →
      ∀ r : ℝ, 0 < r →
        J ((mu n : Measure X) A) (r / cSeq n) ≤
          (mu n : Measure X) (thickening r A))
    {A : Set X} (hA : MeasurableSet A) {r : ℝ} (hr : 0 < r)
    {q : ℝ≥0∞} (hq : q < (muLimit : Measure X) A)
    {u : ℝ} (hu : 0 ≤ u) (hur : u < r / c) :
    J q u ≤ (muLimit : Measure X) (thickening r A) := by
  obtain ⟨K, hKA, _hKcompact, hqK⟩ :=
    hA.exists_lt_isCompact_of_ne_top (measure_ne_top (muLimit : Measure X) A) hq
  let s : ℝ := (u * c + r) / 2
  let epsilon : ℝ := (r - s) / 2
  have huc : u * c < r := by
    rw [lt_div_iff₀ hcPos] at hur
    simpa only [mul_comm] using hur
  have hs : 0 < s := by
    dsimp only [s]
    have huc0 : 0 ≤ u * c := mul_nonneg hu hcPos.le
    linarith
  have hucs : u * c < s := by
    dsimp only [s]
    linarith
  have hsr : s < r := by
    dsimp only [s]
    linarith
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    linarith
  have hesr : s + epsilon < r := by
    dsimp only [epsilon]
    linarith
  have hcompact := profile_compact_le_closedThickening_of_weakLimit
    (K := K) (u := u) (s := s) (epsilon := epsilon)
    hmu hc hcSeq J hJmass hJmassCont hJshift hfinite
    hs hucs hepsilon
  calc
    J q u ≤ J ((muLimit : Measure X) K) u := hJmass u hqK.le
    _ ≤ (muLimit : Measure X) (cthickening (s + epsilon) K) := hcompact
    _ ≤ (muLimit : Measure X) (thickening r A) := by
      apply measure_mono
      exact (cthickening_subset_thickening' hr hesr K).trans
        (thickening_subset_of_subset r hKA)

/-- W1--W3: an enlargement inequality with positive constants `c_n`
survives weak convergence when `c_n -> c > 0`.  The proof uses compact inner
approximation and the open/closed Portmanteau sandwich. -/
theorem enlargement_profile_of_weakLimit
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {mu : ℕ → ProbabilityMeasure X} {muLimit : ProbabilityMeasure X}
    [Measure.Regular (muLimit : Measure X)]
    {cSeq : ℕ → ℝ} {c : ℝ}
    (hmu : Tendsto mu atTop (nhds muLimit))
    (hc : Tendsto cSeq atTop (nhds c)) (hcPos : 0 < c)
    (hcSeq : ∀ n, 0 < cSeq n)
    (J : ℝ≥0∞ → ℝ → ℝ≥0∞)
    (hJmass : ∀ u, Monotone (fun q => J q u))
    (hJmassCont : ∀ u, Continuous (fun q => J q u))
    (hJshift : ∀ q, Monotone (J q))
    (hJclosed : LowerContinuousProfile J)
    (hfinite : ∀ n (A : Set X), MeasurableSet A →
      ∀ r : ℝ, 0 < r →
        J ((mu n : Measure X) A) (r / cSeq n) ≤
          (mu n : Measure X) (thickening r A)) :
    ∀ A : Set X, MeasurableSet A → ∀ r : ℝ, 0 < r →
      J ((muLimit : Measure X) A) (r / c) ≤
        (muLimit : Measure X) (thickening r A) := by
  intro A hA r hr
  apply hJclosed ((muLimit : Measure X) A) (r / c)
      ((muLimit : Measure X) (thickening r A))
  · exact prob_le_one
  · exact div_pos hr hcPos
  · intro q u hq hu hur
    exact profile_lt_enlargement_of_weakLimit hmu hc hcPos hcSeq J
      hJmass hJmassCont hJshift hfinite hA hr hq hu hur

end Concrete

end

end UniformRandomMALA
