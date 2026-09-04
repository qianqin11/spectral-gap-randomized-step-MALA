import UniformRandomMALA.Concrete.GaussianOUGenerator
import UniformRandomMALA.Concrete.SeparatedSets
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.MetricSpace.ThickenedIndicator

/-!
# Gaussian ramps, perimeter slopes, and enlargement

This module implements the geometric G5 stage of the Gaussian
Bakry--Ledoux argument.  It provides:

* the canonical closed-set ramps, with their exact support, range,
  Lipschitz, pointwise-convergence, and integral-convergence properties;
* a lower-right-slope formulation of Gaussian perimeter;
* propagation of that slope through metric thickenings;
* the one-variable Gaussian-quantile chain rule and Dini comparison;
* sharp closed-set Gaussian enlargement; and
* the Radon inner-approximation step from closed to measurable sets.

The geometric stage itself is unconditional once a closed-strip functional
estimate is available.  Closed-enlargement mass is monotone and
right-continuous by finite-measure continuity; the monotone Dini comparison
below therefore removes the former two-sided continuity premise.  The
locally-Lipschitz Bobkov interface remains as a compatibility entry point,
while `GaussianRampMollification` supplies a narrower smooth route whose
only remaining Gaussian input is the canonical G3 OU interpolation.
-/

namespace UniformRandomMALA

open Filter Set Metric MeasureTheory ProbabilityTheory
open scoped Topology ENNReal ProbabilityTheory NNReal

noncomputable section

namespace Concrete

/-! ## Canonical Lipschitz ramps -/

variable {X : Type*} [PseudoMetricSpace X]

/-- The standard ramp `max (0, 1 - dist(x,A)/h)`, implemented through
Mathlib's extended-distance-safe thickened indicator. -/
def gaussianRamp {h : ℝ} (hh : 0 < h) (A : Set X) :
    BoundedContinuousFunction X ℝ :=
  BoundedContinuousFunction.comp ((↑) : ℝ≥0 → ℝ)
    NNReal.isometry_coe.lipschitz (thickenedIndicator hh A)

@[simp] theorem gaussianRamp_apply {h : ℝ} (hh : 0 < h)
    (A : Set X) (x : X) :
    gaussianRamp hh A x = (thickenedIndicator hh A x : ℝ) := rfl

theorem gaussianRamp_mem_Icc {h : ℝ} (hh : 0 < h)
    (A : Set X) (x : X) : gaussianRamp hh A x ∈ Icc (0 : ℝ) 1 := by
  constructor
  · change 0 ≤ ((thickenedIndicator hh A x : ℝ≥0) : ℝ)
    exact_mod_cast
      (show (0 : ℝ≥0) ≤ thickenedIndicator hh A x from bot_le)
  · exact_mod_cast thickenedIndicator_le_one hh A x

theorem gaussianRamp_one {h : ℝ} (hh : 0 < h)
    (A : Set X) {x : X} (hx : x ∈ A) : gaussianRamp hh A x = 1 := by
  change ((thickenedIndicator hh A x : ℝ≥0) : ℝ) = 1
  rw [thickenedIndicator_one hh A hx]
  rfl

theorem gaussianRamp_zero {h : ℝ} (hh : 0 < h)
    (A : Set X) {x : X} (hx : x ∉ thickening h A) :
    gaussianRamp hh A x = 0 := by
  change ((thickenedIndicator hh A x : ℝ≥0) : ℝ) = 0
  rw [thickenedIndicator_zero hh A hx]
  rfl

/-- The closed-set ramp has the exact global Lipschitz constant `1/h`. -/
theorem lipschitzWith_gaussianRamp {h : ℝ} (hh : 0 < h)
    (A : Set X) :
    LipschitzWith h.toNNReal⁻¹ (gaussianRamp hh A) := by
  change LipschitzWith h.toNNReal⁻¹
    (((↑) : ℝ≥0 → ℝ) ∘ thickenedIndicator hh A)
  simpa only [one_mul] using NNReal.isometry_coe.lipschitz.comp
    (lipschitzWith_thickenedIndicator hh A)

/-- Ramps with radii tending to zero converge pointwise to the indicator of
a closed set. -/
theorem tendsto_gaussianRamp_indicator
    {h : ℕ → ℝ} (hh : ∀ n, 0 < h n)
    (hh0 : Tendsto h atTop (nhds 0)) {A : Set X} (hA : IsClosed A) :
    Tendsto (fun n : ℕ => ⇑(gaussianRamp (hh n) A)) atTop
      (nhds (A.indicator fun _ => (1 : ℝ))) := by
  rw [tendsto_pi_nhds]
  intro x
  have hx := (tendsto_pi_nhds.mp
    (thickenedIndicator_tendsto_indicator_closure hh hh0 A)) x
  have hcoe := NNReal.continuous_coe.continuousAt.tendsto.comp hx
  simpa [gaussianRamp_apply, hA.closure_eq, Function.comp_def,
    NNReal.coe_indicator, NNReal.coe_one, NNReal.coe_zero] using hcoe

/-- Dominated convergence turns the pointwise ramp limit into convergence
of means. -/
theorem tendsto_integral_gaussianRamp
    [MeasurableSpace X] [BorelSpace X]
    (pi : Measure X) [IsFiniteMeasure pi]
    {h : ℕ → ℝ} (hh : ∀ n, 0 < h n)
    (hh0 : Tendsto h atTop (nhds 0)) {A : Set X} (hA : IsClosed A) :
    Tendsto (fun n : ℕ => ∫ x, gaussianRamp (hh n) A x ∂pi) atTop
      (nhds (pi.real A)) := by
  have hpoint := tendsto_gaussianRamp_indicator hh hh0 hA
  have hint : ∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂pi = pi.real A :=
    integral_indicator_one hA.measurableSet
  rw [← hint]
  apply tendsto_integral_filter_of_norm_le_const
  · exact Filter.Eventually.of_forall fun n =>
      (gaussianRamp (hh n) A).continuous.aestronglyMeasurable
  · refine ⟨1, Filter.Eventually.of_forall fun n =>
      Filter.Eventually.of_forall fun x => ?_⟩
    rw [Real.norm_eq_abs,
      abs_of_nonneg (gaussianRamp_mem_Icc (hh n) A x).1]
    exact (gaussianRamp_mem_Icc (hh n) A x).2
  · exact Filter.Eventually.of_forall fun x =>
      (tendsto_pi_nhds.mp hpoint) x

/-! ## Locally-Lipschitz functional Bobkov and the ramp strip -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [SecondCountableTopology E]

/-- The exact locally-Lipschitz extension of the functional Bobkov
inequality needed by G5.  Rademacher's theorem makes the Fréchet derivative
an almost-everywhere gradient; at nondifferentiability points `fderiv` is
zero by definition. -/
def GaussianBobkovLocallyLipschitz : Prop :=
  ∀ f : BoundedContinuousFunction E ℝ,
    (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) → LocallyLipschitz f →
    normalProfileClosed (∫ x, f x ∂stdGaussian E) ≤
      ∫ x, Real.sqrt
        (normalProfileClosed (f x) ^ 2 +
          ‖fderiv ℝ (⇑f) x‖ ^ 2) ∂stdGaussian E

/-- Only the values of functional Bobkov on the canonical distance ramps are
needed by G5.  This is a strictly narrower interface than the full
locally-Lipschitz inequality and records the actual trust boundary of the
geometric argument. -/
def GaussianBobkovDistanceRamps : Prop :=
  ∀ {h : ℝ} (hh : 0 < h) {A : Set E}, IsClosed A →
    normalProfileClosed (∫ x, gaussianRamp hh A x ∂stdGaussian E) ≤
      ∫ x, Real.sqrt
        (normalProfileClosed (gaussianRamp hh A x) ^ 2 +
          ‖fderiv ℝ (⇑(gaussianRamp hh A)) x‖ ^ 2)
        ∂stdGaussian E

/-- The still weaker ramp estimate sufficient for Gaussian perimeter.  A
smooth approximation may use a slightly larger closed transition strip;
right-continuity lets that strip shrink to the radius `h`. -/
def GaussianRampClosedStripBound : Prop :=
  ∀ {h : ℝ} (hh : 0 < h) {A : Set E}, IsClosed A →
    normalProfileClosed (∫ x, gaussianRamp hh A x ∂stdGaussian E) ≤
      ((Real.sqrt (2 * Real.pi))⁻¹ + h⁻¹) *
        (stdGaussian E).real (cthickening h A \ A)

theorem gaussianBobkovDistanceRamps_of_locallyLipschitz
    (hBobkov : GaussianBobkovLocallyLipschitz (E := E)) :
    GaussianBobkovDistanceRamps (E := E) := by
  intro h hh A _hA
  exact hBobkov (gaussianRamp hh A)
    (gaussianRamp_mem_Icc hh A)
    (lipschitzWith_gaussianRamp hh A).locallyLipschitz

theorem fderiv_gaussianRamp_eq_zero_of_mem
    {h : ℝ} (hh : 0 < h) (A : Set E) {x : E} (hx : x ∈ A) :
    fderiv ℝ (⇑(gaussianRamp hh A)) x = 0 := by
  apply IsLocalMax.fderiv_eq_zero
  exact Filter.Eventually.of_forall fun y => by
    rw [gaussianRamp_one hh A hx]
    exact (gaussianRamp_mem_Icc hh A y).2

theorem fderiv_gaussianRamp_eq_zero_of_not_mem_thickening
    {h : ℝ} (hh : 0 < h) (A : Set E) {x : E}
    (hx : x ∉ thickening h A) :
    fderiv ℝ (⇑(gaussianRamp hh A)) x = 0 := by
  apply IsLocalMin.fderiv_eq_zero
  exact Filter.Eventually.of_forall fun y => by
    rw [gaussianRamp_zero hh A hx]
    exact (gaussianRamp_mem_Icc hh A y).1

theorem norm_fderiv_gaussianRamp_le
    {h : ℝ} (hh : 0 < h) (A : Set E) (x : E) :
    ‖fderiv ℝ (⇑(gaussianRamp hh A)) x‖ ≤ h⁻¹ := by
  have hlip := lipschitzWith_gaussianRamp hh A
  have hbound := norm_fderiv_le_of_lipschitz ℝ hlip (x₀ := x)
  simpa [NNReal.coe_inv, Real.toNNReal_of_nonneg hh.le] using hbound

/-- The Bobkov integrand of a ramp is supported on its transition strip and
is bounded there by `1/sqrt(2π) + 1/h`. -/
theorem gaussianRamp_bobkovIntegrand_le_strip
    {h : ℝ} (hh : 0 < h) (A : Set E) (x : E) :
    Real.sqrt
        (normalProfileClosed (gaussianRamp hh A x) ^ 2 +
          ‖fderiv ℝ (⇑(gaussianRamp hh A)) x‖ ^ 2) ≤
      (thickening h A \ A).indicator
        (fun _ => (Real.sqrt (2 * Real.pi))⁻¹ + h⁻¹) x := by
  by_cases hxA : x ∈ A
  · rw [indicator_of_notMem (by simp [hxA])]
    rw [gaussianRamp_one hh A hxA, normalProfileClosed_one,
      fderiv_gaussianRamp_eq_zero_of_mem hh A hxA]
    simp
  by_cases hxT : x ∈ thickening h A
  · rw [indicator_of_mem (by exact ⟨hxT, hxA⟩)]
    have hp0 := normalProfileClosed_nonneg (gaussianRamp hh A x)
    have hp := normalProfileClosed_le_inv_sqrt_two_pi
      (gaussianRamp hh A x)
    have hD0 : 0 ≤ ‖fderiv ℝ (⇑(gaussianRamp hh A)) x‖ :=
      norm_nonneg _
    have hD := norm_fderiv_gaussianRamp_le hh A x
    have hsqrt : Real.sqrt
        (normalProfileClosed (gaussianRamp hh A x) ^ 2 +
          ‖fderiv ℝ (⇑(gaussianRamp hh A)) x‖ ^ 2) ≤
        normalProfileClosed (gaussianRamp hh A x) +
          ‖fderiv ℝ (⇑(gaussianRamp hh A)) x‖ := by
      rw [Real.sqrt_le_iff]
      constructor
      · linarith
      · nlinarith [sq_nonneg
          (normalProfileClosed (gaussianRamp hh A x) +
            ‖fderiv ℝ (⇑(gaussianRamp hh A)) x‖)]
    exact hsqrt.trans (add_le_add hp hD)
  · rw [indicator_of_notMem (by simp [hxT])]
    rw [gaussianRamp_zero hh A hxT, normalProfileClosed_zero,
      fderiv_gaussianRamp_eq_zero_of_not_mem_thickening hh A hxT]
    simp

/-- Applying the ramp-only Bobkov interface bounds a ramp profile by the
Gaussian mass of its transition strip. -/
theorem gaussianRamp_functional_le_strip_of_distanceRamps
    (hBobkov : GaussianBobkovDistanceRamps (E := E))
    {h : ℝ} (hh : 0 < h) {A : Set E} (hA : IsClosed A) :
    normalProfileClosed
        (∫ x, gaussianRamp hh A x ∂stdGaussian E) ≤
      ((Real.sqrt (2 * Real.pi))⁻¹ + h⁻¹) *
        (stdGaussian E).real (thickening h A \ A) := by
  let lhs : E → ℝ := fun x => Real.sqrt
    (normalProfileClosed (gaussianRamp hh A x) ^ 2 +
      ‖fderiv ℝ (⇑(gaussianRamp hh A)) x‖ ^ 2)
  let rhs : E → ℝ := (thickening h A \ A).indicator
    (fun _ => (Real.sqrt (2 * Real.pi))⁻¹ + h⁻¹)
  have hstrip : MeasurableSet (thickening h A \ A) :=
    isOpen_thickening.measurableSet.diff hA.measurableSet
  have hconst0 : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ + h⁻¹ :=
    add_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
      (inv_nonneg.mpr hh.le)
  have hrhs : Integrable rhs (stdGaussian E) := by
    exact (integrable_const
      ((Real.sqrt (2 * Real.pi))⁻¹ + h⁻¹)).indicator hstrip
  have hlhsMeas : AEStronglyMeasurable lhs (stdGaussian E) := by
    dsimp only [lhs]
    have hp : Measurable (fun x : E =>
        normalProfileClosed (gaussianRamp hh A x)) :=
      continuous_normalProfileClosed.measurable.comp
        (gaussianRamp hh A).continuous.measurable
    have hD : Measurable (fun x : E =>
        ‖fderiv ℝ (⇑(gaussianRamp hh A)) x‖) :=
      (measurable_fderiv ℝ (⇑(gaussianRamp hh A))).norm
    exact (Real.continuous_sqrt.measurable.comp
      ((hp.pow_const 2).add (hD.pow_const 2))).aestronglyMeasurable
  have hpoint : ∀ x, lhs x ≤ rhs x := fun x => by
    exact gaussianRamp_bobkovIntegrand_le_strip hh A x
  have hlhs : Integrable lhs (stdGaussian E) := by
    apply hrhs.mono' hlhsMeas
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      have hrhs0 : 0 ≤ rhs x := by
        change 0 ≤ (thickening h A \ A).indicator
          (fun _ => (Real.sqrt (2 * Real.pi))⁻¹ + h⁻¹) x
        by_cases hx : x ∈ thickening h A \ A
        · rw [indicator_of_mem hx]
          exact hconst0
        · rw [indicator_of_notMem hx]
      exact hpoint x
  calc
    normalProfileClosed
        (∫ x, gaussianRamp hh A x ∂stdGaussian E) ≤
        ∫ x, lhs x ∂stdGaussian E := by
      exact hBobkov hh hA
    _ ≤ ∫ x, rhs x ∂stdGaussian E :=
      integral_mono_ae hlhs hrhs (Filter.Eventually.of_forall hpoint)
    _ = ((Real.sqrt (2 * Real.pi))⁻¹ + h⁻¹) *
        (stdGaussian E).real (thickening h A \ A) := by
      dsimp only [rhs]
      rw [integral_indicator_const _ hstrip]
      simp only [smul_eq_mul]
      ring

/-- The locally-Lipschitz formulation implies the ramp strip bound.  Kept as
a compatibility wrapper around the narrower G5 interface. -/
theorem gaussianRamp_functional_le_strip
    (hBobkov : GaussianBobkovLocallyLipschitz (E := E))
    {h : ℝ} (hh : 0 < h) {A : Set E} (hA : IsClosed A) :
    normalProfileClosed
        (∫ x, gaussianRamp hh A x ∂stdGaussian E) ≤
      ((Real.sqrt (2 * Real.pi))⁻¹ + h⁻¹) *
        (stdGaussian E).real (thickening h A \ A) := by
  exact gaussianRamp_functional_le_strip_of_distanceRamps
    (gaussianBobkovDistanceRamps_of_locallyLipschitz hBobkov) hh hA

theorem gaussianRampClosedStripBound_of_distanceRamps
    (hBobkov : GaussianBobkovDistanceRamps (E := E)) :
    GaussianRampClosedStripBound (E := E) := by
  intro h hh A hA
  have hopen := gaussianRamp_functional_le_strip_of_distanceRamps
    hBobkov hh hA
  have hsubset : thickening h A \ A ⊆ cthickening h A \ A :=
    sdiff_subset_sdiff_left (thickening_subset_cthickening h A)
  exact hopen.trans (mul_le_mul_of_nonneg_left
    (measureReal_mono hsubset)
    (add_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
      (inv_nonneg.mpr hh.le)))

/-! ## Lower Dini slopes and scalar Gaussian comparison -/

/-- `LowerRightSlopeAtLeast f c x` says that the lower right Dini slope of
`f` at `x` is at least `c`. -/
def LowerRightSlopeAtLeast (f : ℝ → ℝ) (c x : ℝ) : Prop :=
  ∀ r, r < c → ∃ᶠ z in 𝓝[>] x, r < slope f x z

/-- A lower right slope bound by one integrates across a compact interval. -/
theorem lowerRightSlope_endpoint
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hslope : ∀ x ∈ Ico a b, LowerRightSlopeAtLeast f 1 x) :
    f a + (b - a) ≤ f b := by
  have h := image_le_of_liminf_slope_right_le_deriv_boundary
    (f := -f) (a := a) (b := b)
    hf.neg
    (B := fun x => -(f a + (x - a)))
    (B' := fun _ => -1)
    (by simp)
    (by fun_prop)
    (fun x _ => by
      change HasDerivWithinAt (-(fun y : ℝ => f a + (y - a))) (-1)
        (Ici x) x
      simpa using (((hasDerivAt_id x).sub_const a).const_add
        (f a)).neg.hasDerivWithinAt)
    (by
      intro x hx r hr
      have hfreq := hslope x hx (-r) (by linarith)
      exact hfreq.mono fun z hz => by
        change slope (fun t => -f t) x z < r
        rw [slope_neg]
        linarith)
    (show b ∈ Icc a b from ⟨hab, le_rfl⟩)
  change -f b ≤ -(f a + (b - a)) at h
  linarith

/-- A monotone function does not need two-sided continuity for a lower-right
slope bound to integrate.  Any upward jumps only improve the endpoint
estimate. -/
theorem lowerRightSlope_endpoint_of_monotone
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : MonotoneOn f (Icc a b))
    (hslope : ∀ x ∈ Ico a b, LowerRightSlopeAtLeast f 1 x) :
    f a + (b - a) ≤ f b := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  have hd : 0 < b - a := sub_pos.mpr hab
  have hfixed : ∀ c : ℝ, c < 1 → f a + c * (b - a) ≤ f b := by
    intro c hc
    let S : Set ℝ := {x | x ∈ Icc a b ∧ f a + c * (x - a) ≤ f x}
    have haS : a ∈ S := by
      exact ⟨⟨le_rfl, hab.le⟩, by simp⟩
    have hSne : S.Nonempty := ⟨a, haS⟩
    have hSbdd : BddAbove S := by
      exact ⟨b, fun x hx => hx.1.2⟩
    let z := sSup S
    have haz : a ≤ z := le_csSup hSbdd haS
    have hzb : z ≤ b := csSup_le hSne fun x hx => hx.1.2
    have hzgood : f a + c * (z - a) ≤ f z := by
      by_cases hc0 : c ≤ 0
      · have hfaz : f a ≤ f z := hf ⟨le_rfl, hab.le⟩ ⟨haz, hzb⟩ haz
        exact (add_le_of_nonpos_right (mul_nonpos_of_nonpos_of_nonneg hc0
          (sub_nonneg.mpr haz))).trans hfaz
      · have hcpos : 0 < c := lt_of_not_ge hc0
        apply le_of_forall_pos_le_add
        intro eps heps
        have hnear : z - eps / c < z := by
          have : 0 < eps / c := div_pos heps hcpos
          linarith
        obtain ⟨x, hxS, hxnear⟩ := exists_lt_of_lt_csSup hSne hnear
        have hxgood : f a + c * (x - a) ≤ f x := hxS.2
        have hxz : x ≤ z := le_csSup hSbdd hxS
        have hfxz : f x ≤ f z :=
          hf hxS.1 ⟨haz, hzb⟩ hxz
        have hczx : c * (z - x) < eps := by
          have : z - x < eps / c := by linarith
          calc
            c * (z - x) < c * (eps / c) :=
              mul_lt_mul_of_pos_left this hcpos
            _ = eps := by field_simp
        calc
          f a + c * (z - a) =
              (f a + c * (x - a)) + c * (z - x) := by ring
          _ ≤ f x + c * (z - x) := by linarith
          _ ≤ f z + c * (z - x) := by linarith
          _ ≤ f z + eps := by linarith
    have hzS : z ∈ S := ⟨⟨haz, hzb⟩, hzgood⟩
    have hzeq : z = b := by
      apply le_antisymm hzb
      by_contra hznot
      have hzb' : z < b := lt_of_not_ge hznot
      have hfreq := hslope z ⟨haz, hzb'⟩ c hc
      obtain ⟨y, hyslope, hyIoc⟩ :=
        (hfreq.and_eventually (Ioc_mem_nhdsGT hzb')).exists
      have hzy : 0 < y - z := sub_pos.mpr hyIoc.1
      have hyinc : c * (y - z) < f y - f z := by
        rw [slope_def_field, lt_div_iff₀ hzy] at hyslope
        exact hyslope
      have hyS : y ∈ S := by
        constructor
        · exact ⟨haz.trans hyIoc.1.le, hyIoc.2⟩
        · calc
            f a + c * (y - a) =
                (f a + c * (z - a)) + c * (y - z) := by ring
            _ ≤ f z + c * (y - z) := by linarith
            _ ≤ f y := by linarith
      exact (not_lt_of_ge (le_csSup hSbdd hyS)) hyIoc.1
    simpa [hzeq] using hzgood
  by_contra hgoal
  have hstrict : f b < f a + (b - a) := lt_of_not_ge hgoal
  have hratio : (f b - f a) / (b - a) < 1 := by
    rw [div_lt_one hd]
    linarith
  let c : ℝ := ((f b - f a) / (b - a) + 1) / 2
  have hc1 : c < 1 := by
    dsimp only [c]
    linarith
  have hrc : (f b - f a) / (b - a) < c := by
    dsimp only [c]
    linarith
  have hcendpoint := hfixed c hc1
  have hcontra : f b - f a < c * (b - a) := by
    exact (div_lt_iff₀ hd).mp hrc
  linarith

lemma slope_comp_eq_mul {f g : ℝ → ℝ} {x z : ℝ}
    (hxz : x ≠ z) (hfg : f x ≠ f z) :
    slope (g ∘ f) x z = slope g (f x) (f z) * slope f x z := by
  simp only [slope, Function.comp_apply, smul_eq_mul, vsub_eq_sub]
  field_simp

/-- The inverse Gaussian CDF turns the nonlinear slope `I(a)` into the
constant slope one. -/
theorem lowerRightSlopeAtLeast_quantile
    {a : ℝ → ℝ} {x : ℝ}
    (ha : ContinuousAt a x)
    (hax : a x ∈ Ioo (0 : ℝ) 1)
    (hslope : LowerRightSlopeAtLeast a (normalProfile (a x)) x) :
    LowerRightSlopeAtLeast
      (lowerQuantile standardGaussianMeasure ∘ a) 1 x := by
  intro r hr
  let c : ℝ := (max r 0 + 1) / 2
  have hc0 : 0 < c := by
    dsimp only [c]
    have : 0 ≤ max r 0 := le_max_right _ _
    linarith
  have hc1 : c < 1 := by
    dsimp only [c]
    have := max_lt (show r < 1 from hr) zero_lt_one
    linarith
  have hrcsq : r < c ^ 2 := by
    dsimp only [c]
    by_cases hr0 : r ≤ 0
    · have hc : max r 0 = 0 := max_eq_right hr0
      rw [hc]
      nlinarith
    · have hc : max r 0 = r := max_eq_left (le_of_not_ge hr0)
      rw [hc]
      nlinarith [sq_pos_of_pos (sub_pos.mpr hr)]
  have hI : 0 < normalProfile (a x) := normalProfile_pos hax
  have hq := hasDerivAt_lowerQuantile_standardGaussian hax
  have hderivLower : c / normalProfile (a x) <
      (normalDensity
        (lowerQuantile standardGaussianMeasure (a x)))⁻¹ := by
    change c / normalProfile (a x) < (normalProfile (a x))⁻¹
    rw [div_eq_mul_inv]
    simpa using mul_lt_mul_of_pos_right hc1 (inv_pos.mpr hI)
  have hqevent : ∀ᶠ y in 𝓝[≠] (a x),
      c / normalProfile (a x) <
        slope (lowerQuantile standardGaussianMeasure) (a x) y :=
    hq.tendsto_slope (Ioi_mem_nhds hderivLower)
  change {y | c / normalProfile (a x) <
      slope (lowerQuantile standardGaussianMeasure) (a x) y} ∈
        nhdsWithin (a x) ({a x}ᶜ) at hqevent
  obtain ⟨U, hU, hUsub⟩ :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hqevent
  have haU : ∀ᶠ z in 𝓝 x, a z ∈ U := ha hU
  have haUGT : ∀ᶠ z in 𝓝[>] x, a z ∈ U :=
    haU.filter_mono inf_le_left
  have hzxGT : ∀ᶠ z in 𝓝[>] x, x < z := self_mem_nhdsWithin
  have hfreq := hslope (c * normalProfile (a x))
    (by nlinarith [hI, hc1])
  refine (hfreq.and_eventually (haUGT.and hzxGT)).mono ?_
  rintro z ⟨hza, hzU, hzx⟩
  have haz : a x ≠ a z := by
    intro heq
    have hslopeZero : slope a x z = 0 := by simp [slope, heq]
    rw [hslopeZero] at hza
    nlinarith [hI, hc0]
  have hqz : c / normalProfile (a x) <
      slope (lowerQuantile standardGaussianMeasure) (a x) (a z) :=
    hUsub ⟨hzU, haz.symm⟩
  rw [slope_comp_eq_mul (ne_of_lt hzx) haz]
  have hqz0 : 0 <
      slope (lowerQuantile standardGaussianMeasure) (a x) (a z) :=
    (div_pos hc0 hI).trans hqz
  calc
    r < c ^ 2 := hrcsq
    _ = (c / normalProfile (a x)) *
        (c * normalProfile (a x)) := by field_simp
    _ < slope (lowerQuantile standardGaussianMeasure) (a x) (a z) *
        slope a x z := mul_lt_mul hqz hza.le (mul_pos hc0 hI)
      hqz0.le

/-- Right continuity is enough for the quantile slope chain rule, since the
lower Dini slope only probes points to the right. -/
theorem lowerRightSlopeAtLeast_quantile_of_rightContinuous
    {a : ℝ → ℝ} {x : ℝ}
    (ha : ContinuousWithinAt a (Ici x) x)
    (hax : a x ∈ Ioo (0 : ℝ) 1)
    (hslope : LowerRightSlopeAtLeast a (normalProfile (a x)) x) :
    LowerRightSlopeAtLeast
      (lowerQuantile standardGaussianMeasure ∘ a) 1 x := by
  intro r hr
  let c : ℝ := (max r 0 + 1) / 2
  have hc0 : 0 < c := by
    dsimp only [c]
    have : 0 ≤ max r 0 := le_max_right _ _
    linarith
  have hc1 : c < 1 := by
    dsimp only [c]
    have := max_lt (show r < 1 from hr) zero_lt_one
    linarith
  have hrcsq : r < c ^ 2 := by
    dsimp only [c]
    by_cases hr0 : r ≤ 0
    · have hc : max r 0 = 0 := max_eq_right hr0
      rw [hc]
      nlinarith
    · have hc : max r 0 = r := max_eq_left (le_of_not_ge hr0)
      rw [hc]
      nlinarith [sq_pos_of_pos (sub_pos.mpr hr)]
  have hI : 0 < normalProfile (a x) := normalProfile_pos hax
  have hq := hasDerivAt_lowerQuantile_standardGaussian hax
  have hderivLower : c / normalProfile (a x) <
      (normalDensity
        (lowerQuantile standardGaussianMeasure (a x)))⁻¹ := by
    change c / normalProfile (a x) < (normalProfile (a x))⁻¹
    rw [div_eq_mul_inv]
    simpa using mul_lt_mul_of_pos_right hc1 (inv_pos.mpr hI)
  have hqevent : ∀ᶠ y in 𝓝[≠] (a x),
      c / normalProfile (a x) <
        slope (lowerQuantile standardGaussianMeasure) (a x) y :=
    hq.tendsto_slope (Ioi_mem_nhds hderivLower)
  change {y | c / normalProfile (a x) <
      slope (lowerQuantile standardGaussianMeasure) (a x) y} ∈
        nhdsWithin (a x) ({a x}ᶜ) at hqevent
  obtain ⟨U, hU, hUsub⟩ :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hqevent
  have haU : ∀ᶠ z in 𝓝[≥] x, a z ∈ U := ha hU
  have haUGT : ∀ᶠ z in 𝓝[>] x, a z ∈ U :=
    haU.filter_mono (nhdsWithin_mono x Ioi_subset_Ici_self)
  have hzxGT : ∀ᶠ z in 𝓝[>] x, x < z := self_mem_nhdsWithin
  have hfreq := hslope (c * normalProfile (a x))
    (by nlinarith [hI, hc1])
  refine (hfreq.and_eventually (haUGT.and hzxGT)).mono ?_
  rintro z ⟨hza, hzU, hzx⟩
  have haz : a x ≠ a z := by
    intro heq
    have hslopeZero : slope a x z = 0 := by simp [slope, heq]
    rw [hslopeZero] at hza
    nlinarith [hI, hc0]
  have hqz : c / normalProfile (a x) <
      slope (lowerQuantile standardGaussianMeasure) (a x) (a z) :=
    hUsub ⟨hzU, haz.symm⟩
  rw [slope_comp_eq_mul (ne_of_lt hzx) haz]
  have hqz0 : 0 <
      slope (lowerQuantile standardGaussianMeasure) (a x) (a z) :=
    (div_pos hc0 hI).trans hqz
  calc
    r < c ^ 2 := hrcsq
    _ = (c / normalProfile (a x)) *
        (c * normalProfile (a x)) := by field_simp
    _ < slope (lowerQuantile standardGaussianMeasure) (a x) (a z) *
        slope a x z := mul_lt_mul hqz hza.le (mul_pos hc0 hI)
      hqz0.le

/-- Scalar G5 comparison: `D⁺a ≥ I(a)` integrates to the sharp shifted
Gaussian profile. -/
theorem normalCDF_shift_le_of_lowerRightSlope
    {a : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (ha : Continuous a)
    (hrange : ∀ s ∈ Icc (0 : ℝ) t, a s ∈ Ioo (0 : ℝ) 1)
    (hslope : ∀ s ∈ Ico (0 : ℝ) t,
      LowerRightSlopeAtLeast a (normalProfile (a s)) s) :
    normalCDFReal
        (lowerQuantile standardGaussianMeasure (a 0) + t) ≤ a t := by
  let b : ℝ → ℝ := lowerQuantile standardGaussianMeasure ∘ a
  have hbcont : ContinuousOn b (Icc (0 : ℝ) t) := by
    intro s hs
    exact ((continuousAt_lowerQuantile_standardGaussian
      (hrange s hs)).comp ha.continuousAt).continuousWithinAt
  have hbslope : ∀ s ∈ Ico (0 : ℝ) t,
      LowerRightSlopeAtLeast b 1 s := by
    intro s hs
    exact lowerRightSlopeAtLeast_quantile ha.continuousAt
      (hrange s ⟨hs.1, hs.2.le⟩) (hslope s hs)
  have hb := lowerRightSlope_endpoint ht hbcont hbslope
  have hcdf := strictMono_normalCDFReal.monotone hb
  have hat : normalCDFReal
      (lowerQuantile standardGaussianMeasure (a t)) = a t := by
    rw [← cdf_standardGaussian_eq_normalCDFReal]
    exact cdf_lowerQuantile_eq standardGaussianMeasure
      continuous_standardGaussianCDF
        (hrange t ⟨ht, le_rfl⟩).1 (hrange t ⟨ht, le_rfl⟩).2
  simpa only [b, Function.comp_apply, sub_zero, hat] using hcdf

/-- Monotonicity and right continuity suffice for the scalar G5 comparison;
two-sided continuity is unnecessary. -/
theorem normalCDF_shift_le_of_lowerRightSlope_monotone
    {a : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (ha : MonotoneOn a (Icc (0 : ℝ) t))
    (haright : ∀ s ∈ Ico (0 : ℝ) t,
      ContinuousWithinAt a (Ici s) s)
    (hrange : ∀ s ∈ Icc (0 : ℝ) t, a s ∈ Ioo (0 : ℝ) 1)
    (hslope : ∀ s ∈ Ico (0 : ℝ) t,
      LowerRightSlopeAtLeast a (normalProfile (a s)) s) :
    normalCDFReal
        (lowerQuantile standardGaussianMeasure (a 0) + t) ≤ a t := by
  let b : ℝ → ℝ := lowerQuantile standardGaussianMeasure ∘ a
  have hbmono : MonotoneOn b (Icc (0 : ℝ) t) := by
    intro x hx y hy hxy
    exact lowerQuantile_mono standardGaussianMeasure
      (ha hx hy hxy) (hrange y hy).2 (hrange x hx).1
  have hbslope : ∀ s ∈ Ico (0 : ℝ) t,
      LowerRightSlopeAtLeast b 1 s := by
    intro s hs
    exact lowerRightSlopeAtLeast_quantile_of_rightContinuous
      (haright s hs) (hrange s ⟨hs.1, hs.2.le⟩) (hslope s hs)
  have hb := lowerRightSlope_endpoint_of_monotone ht hbmono hbslope
  have hcdf := strictMono_normalCDFReal.monotone hb
  have hat : normalCDFReal
      (lowerQuantile standardGaussianMeasure (a t)) = a t := by
    rw [← cdf_standardGaussian_eq_normalCDFReal]
    exact cdf_lowerQuantile_eq standardGaussianMeasure
      continuous_standardGaussianCDF
        (hrange t ⟨ht, le_rfl⟩).1 (hrange t ⟨ht, le_rfl⟩).2
  simpa only [b, Function.comp_apply, sub_zero, hat] using hcdf

/-! ## Perimeter propagation and closed-set enlargement -/

/-- Mass of a closed metric enlargement. -/
def closedEnlargementMass {Y : Type*} [PseudoMetricSpace Y]
    [MeasurableSpace Y] (pi : Measure Y) (K : Set Y) (r : ℝ) : ℝ :=
  pi.real (cthickening r K)

/-- Closed-enlargement mass is intrinsically right-continuous for every
finite Borel measure.  This follows directly from continuity of measure along
the decreasing closed thickenings above a fixed radius. -/
theorem continuousWithinAt_closedEnlargementMass_right
    {Y : Type*} [PseudoMetricSpace Y] [MeasurableSpace Y]
    [BorelSpace Y]
    (pi : Measure Y) [IsFiniteMeasure pi]
    (K : Set Y) (r : ℝ) :
    ContinuousWithinAt (closedEnlargementMass pi K) (Ici r) r := by
  rw [← continuousWithinAt_Ioi_iff_Ici]
  unfold ContinuousWithinAt closedEnlargementMass Measure.real
  apply (ENNReal.tendsto_toReal (measure_ne_top pi (cthickening r K))).comp
  rw [cthickening_eq_iInter_cthickening]
  exact tendsto_measure_biInter_gt
    (fun s _ => isClosed_cthickening.nullMeasurableSet)
    (fun i j _ hij => cthickening_mono hij K)
    ⟨r + 1, by linarith, measure_ne_top pi _⟩

/-- The Gaussian perimeter conclusion obtained by applying the functional
Bobkov inequality to the canonical ramps and sending their width to zero. -/
def ClosedGaussianPerimeter {Y : Type*} [PseudoMetricSpace Y]
    [MeasurableSpace Y] (pi : Measure Y) : Prop :=
  ∀ K : Set Y, IsClosed K → 0 < pi.real K → pi.real K < 1 →
    LowerRightSlopeAtLeast (closedEnlargementMass pi K)
      (normalProfile (pi.real K)) 0

/-- The stronger, legacy two-sided continuity interface.  G5 no longer needs
this hypothesis: monotonicity plus the intrinsic right-continuity theorem
above suffice. -/
def ContinuousClosedEnlargementMass {Y : Type*} [PseudoMetricSpace Y]
    [MeasurableSpace Y] (pi : Measure Y) : Prop :=
  ∀ K : Set Y, IsClosed K →
    ContinuousOn (closedEnlargementMass pi K) (Ici 0)

/-- The closed-strip ramp estimate yields the closed-set Gaussian perimeter
lower slope by sending the ramp width to zero. -/
theorem closedGaussianPerimeter_of_closedStrip
    (hBobkov : GaussianRampClosedStripBound (E := E)) :
    ClosedGaussianPerimeter (stdGaussian E) := by
  intro K hK hK0 hK1 q hq
  rw [(nhdsGT_basis (0 : ℝ)).frequently_iff]
  intro u hu
  by_cases hq0 : q < 0
  · refine ⟨u / 2, ⟨half_pos hu, half_lt_self hu⟩, ?_⟩
    have hmono : (stdGaussian E).real K ≤
        (stdGaussian E).real (cthickening (u / 2) K) := by
      apply measureReal_mono (h₂ := measure_ne_top (stdGaussian E) _)
      simpa only [hK.closure_eq] using
        closure_subset_cthickening (u / 2) K
    have hslope0 : 0 ≤ slope
        (closedEnlargementMass (stdGaussian E) K) 0 (u / 2) := by
      simp only [closedEnlargementMass, slope, smul_eq_mul,
        vsub_eq_sub, sub_zero, cthickening_zero, hK.closure_eq]
      exact mul_nonneg (inv_nonneg.mpr (half_pos hu).le)
        (sub_nonneg.mpr hmono)
    exact hq0.trans_le hslope0
  have hqnonneg : 0 ≤ q := le_of_not_gt hq0
  by_contra hnone
  push Not at hnone
  let d : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hdpos : ∀ n, 0 < d n := fun n => by
    dsimp only [d]
    positivity
  have hd0 : Tendsto d atTop (nhds 0) := by
    simpa only [d] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hdlt : ∀ᶠ n in atTop, d n < u :=
    (tendsto_order.1 hd0).2 u hu
  have hmean := tendsto_integral_gaussianRamp
    (stdGaussian E) hdpos hd0 hK
  have hleft : Tendsto (fun n => normalProfileClosed
      (∫ x, gaussianRamp (hdpos n) K x ∂stdGaussian E)) atTop
      (nhds (normalProfile ((stdGaussian E).real K))) := by
    have hcomp :=
      continuous_normalProfileClosed.continuousAt.tendsto.comp hmean
    rw [normalProfileClosed_eq_normalProfile ⟨hK0, hK1⟩] at hcomp
    exact hcomp
  let C : ℝ := (Real.sqrt (2 * Real.pi))⁻¹
  have hright : Tendsto (fun n => q * (1 + C * d n)) atTop
      (nhds q) := by
    convert tendsto_const_nhds.mul
      (tendsto_const_nhds.add (tendsto_const_nhds.mul hd0)) using 1
    ring
  have hevent : ∀ᶠ n in atTop,
      normalProfileClosed
          (∫ x, gaussianRamp (hdpos n) K x ∂stdGaussian E) ≤
        q * (1 + C * d n) := by
    filter_upwards [hdlt] with n hdu
    have hdn := hdpos n
    have hslopeUpper := hnone (d n) ⟨hdn, hdu⟩
    have hclosedDiff : (stdGaussian E).real
          (cthickening (d n) K) - (stdGaussian E).real K ≤
        q * d n := by
      simp only [closedEnlargementMass, slope, smul_eq_mul,
        vsub_eq_sub, sub_zero, cthickening_zero,
        hK.closure_eq] at hslopeUpper
      have := mul_le_mul_of_nonneg_right hslopeUpper hdn.le
      field_simp at this
      simpa [mul_comm] using this
    have hstrip : (stdGaussian E).real (cthickening (d n) K \ K) ≤
        q * d n := by
      calc
        (stdGaussian E).real (cthickening (d n) K \ K) =
            (stdGaussian E).real (cthickening (d n) K) -
            (stdGaussian E).real K := by
          rw [measureReal_sdiff]
          · exact self_subset_cthickening K
          · exact hK.measurableSet
        _ ≤ q * d n := hclosedDiff
    have hfunctional := hBobkov hdn hK
    calc
      normalProfileClosed
          (∫ x, gaussianRamp (hdpos n) K x ∂stdGaussian E) ≤
          (C + (d n)⁻¹) *
            (stdGaussian E).real (cthickening (d n) K \ K) := by
        simpa only [C] using hfunctional
      _ ≤ (C + (d n)⁻¹) * (q * d n) :=
        mul_le_mul_of_nonneg_left hstrip
          (add_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
            (inv_nonneg.mpr hdn.le))
      _ = q * (1 + C * d n) := by field_simp; ring
  have hlimit := le_of_tendsto_of_tendsto hleft hright hevent
  exact (not_le_of_gt hq) hlimit

/-- Bobkov's inequality on the canonical distance ramps implies the weaker
closed-strip estimate and hence Gaussian perimeter. -/
theorem closedGaussianPerimeter_of_distanceRamps
    (hBobkov : GaussianBobkovDistanceRamps (E := E)) :
    ClosedGaussianPerimeter (stdGaussian E) := by
  exact closedGaussianPerimeter_of_closedStrip
    (gaussianRampClosedStripBound_of_distanceRamps hBobkov)

/-- Compatibility wrapper deriving the ramp perimeter result from the full
locally-Lipschitz functional inequality. -/
theorem closedGaussianPerimeter_of_functionalLipschitz
    (hBobkov : GaussianBobkovLocallyLipschitz (E := E)) :
    ClosedGaussianPerimeter (stdGaussian E) := by
  exact closedGaussianPerimeter_of_distanceRamps
    (gaussianBobkovDistanceRamps_of_locallyLipschitz hBobkov)

/-- The perimeter lower bound for a closed set propagates to the mass flow
of all of its later closed thickenings. -/
theorem lowerRightSlope_closedEnlargementMass_of_perimeter
    {Y : Type*} [PseudoMetricSpace Y] [MeasurableSpace Y]
    (pi : Measure Y) [IsFiniteMeasure pi]
    (hper : ClosedGaussianPerimeter pi)
    {K : Set Y} {s : ℝ} (hs : 0 ≤ s)
    (hs0 : 0 < closedEnlargementMass pi K s)
    (hs1 : closedEnlargementMass pi K s < 1) :
    LowerRightSlopeAtLeast (closedEnlargementMass pi K)
      (normalProfile (closedEnlargementMass pi K s)) s := by
  let B : Set Y := cthickening s K
  have hBclosed : IsClosed B := isClosed_cthickening
  have hperB := hper B hBclosed hs0 hs1
  intro q hq
  rw [(nhdsGT_basis s).frequently_iff]
  intro u hsu
  have hperBq := hperB q
    (by simpa [B, closedEnlargementMass] using hq)
  rw [(nhdsGT_basis (0 : ℝ)).frequently_iff] at hperBq
  obtain ⟨h, hhmem, hhq⟩ := hperBq (u - s) (sub_pos.mpr hsu)
  refine ⟨s + h, ?_, ?_⟩
  · exact ⟨lt_add_of_pos_right s hhmem.1, by linarith [hhmem.2]⟩
  · have hsub : cthickening h B ⊆ cthickening (s + h) K := by
      have hraw := cthickening_cthickening_subset hhmem.1.le hs K
      simpa only [B, add_comm] using hraw
    have hmeasure : pi.real (cthickening h B) ≤
        pi.real (cthickening (s + h) K) := measureReal_mono hsub
    have hzero : pi.real (cthickening 0 B) =
        pi.real (cthickening s K) := by simp [B]
    simp only [closedEnlargementMass, slope, smul_eq_mul, vsub_eq_sub,
      sub_zero, add_sub_cancel_left, hzero] at hhq ⊢
    exact lt_of_lt_of_le hhq (mul_le_mul_of_nonneg_left
      (sub_le_sub_right hmeasure _) (inv_nonneg.mpr hhmem.1.le))

/-- Closed-set G5: Gaussian perimeter plus continuity of enlargement masses
integrates to the sharp finite-radius Gaussian enlargement bound. -/
theorem normalCDF_shift_le_thickening_of_closedPerimeter
    {Y : Type*} [MetricSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [OpensMeasurableSpace Y]
    (pi : Measure Y) [IsProbabilityMeasure pi]
    (hper : ClosedGaussianPerimeter pi)
    (hcont : ContinuousClosedEnlargementMass pi)
    {K : Set Y} (hK : IsClosed K)
    (hK0 : 0 < pi.real K) (_hK1 : pi.real K < 1)
    {r : ℝ} (hr : 0 < r) :
    normalCDFReal
        (lowerQuantile standardGaussianMeasure (pi.real K) + r) ≤
      pi.real (thickening r K) := by
  by_cases hfull : pi.real (thickening r K) = 1
  · rw [hfull]
    exact (normalCDFReal_lt_one _).le
  have hthick1 : pi.real (thickening r K) < 1 :=
    measureReal_le_one.lt_of_ne hfull
  let G : ℝ → ℝ := fun t => normalCDFReal
    (lowerQuantile standardGaussianMeasure (pi.real K) + t)
  by_contra hgoal
  have hstrict : pi.real (thickening r K) < G r :=
    lt_of_not_ge hgoal
  have hGcont : ContinuousAt G r := by
    exact (hasDerivAt_normalCDFReal _).continuousAt.comp
      (continuousAt_const.add continuousAt_id)
  have hevent : ∀ᶠ t in 𝓝 r, pi.real (thickening r K) < G t :=
    hGcont (Ioi_mem_nhds hstrict)
  obtain ⟨t, htr, htprofile, ht0⟩ :=
    (hevent.and (Ioi_mem_nhds hr)).exists_lt
  let a : ℝ → ℝ := fun s =>
    closedEnlargementMass pi K (max s 0)
  have ha : Continuous a := by
    change Continuous (closedEnlargementMass pi K ∘
      fun s : ℝ => max s 0)
    apply (hcont K hK).comp_continuous
      (continuous_id.max continuous_const)
    intro s
    exact le_max_right s 0
  have hamass {s : ℝ} (hs : 0 ≤ s) :
      a s = closedEnlargementMass pi K s := by
    simp [a, max_eq_left hs]
  have hKsubset (s : ℝ) (hs : 0 ≤ s) :
      K ⊆ cthickening s K := by
    simpa only [hK.closure_eq, cthickening_zero] using
      cthickening_mono hs K
  have hrange : ∀ s ∈ Icc (0 : ℝ) t, a s ∈ Ioo (0 : ℝ) 1 := by
    intro s hs
    rw [hamass hs.1]
    constructor
    · exact hK0.trans_le (measureReal_mono (hKsubset s hs.1))
    · have hsr : s < r := hs.2.trans_lt htr
      exact (measureReal_mono
        (cthickening_subset_thickening' hr hsr K)).trans_lt hthick1
  have hslope : ∀ s ∈ Ico (0 : ℝ) t,
      LowerRightSlopeAtLeast a (normalProfile (a s)) s := by
    intro s hs
    have hraw := lowerRightSlope_closedEnlargementMass_of_perimeter
      pi hper hs.1
      (by simpa [hamass hs.1] using
        (hrange s ⟨hs.1, hs.2.le⟩).1)
      (by simpa [hamass hs.1] using
        (hrange s ⟨hs.1, hs.2.le⟩).2)
    rw [hamass hs.1]
    intro q hq
    have hright : ∀ᶠ z in 𝓝[>] s, s < z := self_mem_nhdsWithin
    refine ((hraw q hq).and_eventually hright).mono ?_
    rintro z ⟨hz, hsz'⟩
    have hsz : 0 ≤ z := le_trans hs.1 hsz'.le
    simpa only [a, slope, smul_eq_mul, vsub_eq_sub,
      max_eq_left hs.1, max_eq_left hsz] using hz
  have htbound := normalCDF_shift_le_of_lowerRightSlope
    ht0.le ha hrange hslope
  have ha0 : a 0 = pi.real K := by
    simp [a, closedEnlargementMass]
  have hat : a t = closedEnlargementMass pi K t := hamass ht0.le
  have hclosedOpen : closedEnlargementMass pi K t ≤
      pi.real (thickening r K) :=
    measureReal_mono (cthickening_subset_thickening' hr htr K)
  rw [ha0, hat] at htbound
  exact (not_lt_of_ge (htbound.trans hclosedOpen)) htprofile

/-- Closed-set G5 with no external continuity premise.  Closed-enlargement
mass is monotone, and its required right continuity follows from finite
measure continuity along decreasing closed thickenings. -/
theorem normalCDF_shift_le_thickening_of_closedPerimeter_monotone
    {Y : Type*} [MetricSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [OpensMeasurableSpace Y]
    (pi : Measure Y) [IsProbabilityMeasure pi]
    (hper : ClosedGaussianPerimeter pi)
    {K : Set Y} (hK : IsClosed K)
    (hK0 : 0 < pi.real K) (_hK1 : pi.real K < 1)
    {r : ℝ} (hr : 0 < r) :
    normalCDFReal
        (lowerQuantile standardGaussianMeasure (pi.real K) + r) ≤
      pi.real (thickening r K) := by
  by_cases hfull : pi.real (thickening r K) = 1
  · rw [hfull]
    exact (normalCDFReal_lt_one _).le
  have hthick1 : pi.real (thickening r K) < 1 :=
    measureReal_le_one.lt_of_ne hfull
  let G : ℝ → ℝ := fun t => normalCDFReal
    (lowerQuantile standardGaussianMeasure (pi.real K) + t)
  by_contra hgoal
  have hstrict : pi.real (thickening r K) < G r :=
    lt_of_not_ge hgoal
  have hGcont : ContinuousAt G r := by
    exact (hasDerivAt_normalCDFReal _).continuousAt.comp
      (continuousAt_const.add continuousAt_id)
  have hevent : ∀ᶠ t in 𝓝 r, pi.real (thickening r K) < G t :=
    hGcont (Ioi_mem_nhds hstrict)
  obtain ⟨t, htr, htprofile, ht0⟩ :=
    (hevent.and (Ioi_mem_nhds hr)).exists_lt
  let a : ℝ → ℝ := fun s => closedEnlargementMass pi K s
  have hamono : MonotoneOn a (Icc (0 : ℝ) t) := by
    intro s hs u hu hsu
    exact measureReal_mono (cthickening_mono hsu K)
  have haright : ∀ s ∈ Ico (0 : ℝ) t,
      ContinuousWithinAt a (Ici s) s := by
    intro s _
    exact continuousWithinAt_closedEnlargementMass_right pi K s
  have hKsubset (s : ℝ) (hs : 0 ≤ s) :
      K ⊆ cthickening s K := by
    simpa only [hK.closure_eq, cthickening_zero] using
      cthickening_mono hs K
  have hrange : ∀ s ∈ Icc (0 : ℝ) t, a s ∈ Ioo (0 : ℝ) 1 := by
    intro s hs
    constructor
    · exact hK0.trans_le (measureReal_mono (hKsubset s hs.1))
    · have hsr : s < r := hs.2.trans_lt htr
      exact (measureReal_mono
        (cthickening_subset_thickening' hr hsr K)).trans_lt hthick1
  have hslope : ∀ s ∈ Ico (0 : ℝ) t,
      LowerRightSlopeAtLeast a (normalProfile (a s)) s := by
    intro s hs
    exact lowerRightSlope_closedEnlargementMass_of_perimeter
      pi hper hs.1
      (hrange s ⟨hs.1, hs.2.le⟩).1
      (hrange s ⟨hs.1, hs.2.le⟩).2
  have htbound := normalCDF_shift_le_of_lowerRightSlope_monotone
    ht0.le hamono haright hrange hslope
  have ha0 : a 0 = pi.real K := by
    simp [a, closedEnlargementMass]
  have hclosedOpen : a t ≤ pi.real (thickening r K) :=
    measureReal_mono (cthickening_subset_thickening' hr htr K)
  rw [ha0] at htbound
  exact (not_lt_of_ge (htbound.trans hclosedOpen)) htprofile

/-! ## Radon approximation and measurable-set enlargement -/

/-- Compact/closed inner approximation upgrades a closed-set Gaussian
enlargement theorem to every measurable set of interior mass. -/
theorem bakryLedouxEnlargement_of_closed
    {Y : Type*} [MetricSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [OpensMeasurableSpace Y]
    (pi : Measure Y) [IsProbabilityMeasure pi] [Measure.Regular pi]
    (m : ℝ)
    (hclosed : ∀ K : Set Y, IsClosed K →
      0 < pi.real K → pi.real K < 1 → ∀ r : ℝ, 0 < r →
        normalCDFReal
            (lowerQuantile standardGaussianMeasure (pi.real K) +
              Real.sqrt m * r) ≤ pi.real (thickening r K)) :
    BakryLedouxEnlargement pi m
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure) := by
  intro A hA hA0 hA1 r hr
  rw [cdf_standardGaussian_eq_normalCDFReal]
  by_contra hgoal
  have hstrict : pi.real (thickening r A) <
      normalCDFReal
        (lowerQuantile standardGaussianMeasure (pi.real A) +
          Real.sqrt m * r) := lt_of_not_ge hgoal
  let G : ℝ → ℝ := fun q => normalCDFReal
    (lowerQuantile standardGaussianMeasure q + Real.sqrt m * r)
  have hGcont : ContinuousAt G (pi.real A) := by
    exact (hasDerivAt_normalCDFReal _).continuousAt.comp
      ((continuousAt_lowerQuantile_standardGaussian ⟨hA0, hA1⟩).add
        continuousAt_const)
  have hevent : ∀ᶠ q in 𝓝 (pi.real A),
      pi.real (thickening r A) < G q :=
    hGcont (Ioi_mem_nhds hstrict)
  obtain ⟨q, hqA, hqprofile, hq0⟩ :=
    (hevent.and (Ioi_mem_nhds hA0)).exists_lt
  have hAfin : pi A ≠ ∞ := measure_ne_top pi A
  have hqENN : ENNReal.ofReal q < pi A := by
    rw [ENNReal.ofReal_lt_iff_lt_toReal hq0.le hAfin]
    simpa only [Measure.real_def] using hqA
  obtain ⟨K, hKA, hKcompact, hqK⟩ :=
    hA.exists_lt_isCompact_of_ne_top hAfin hqENN
  have hqKreal : q < pi.real K := by
    have h := (ENNReal.toReal_lt_toReal (by finiteness)
      (measure_ne_top pi K)).2 hqK
    simpa [Measure.real_def, ENNReal.toReal_ofReal hq0.le] using h
  have hK0 : 0 < pi.real K := hq0.trans hqKreal
  have hK1 : pi.real K < 1 :=
    (measureReal_mono hKA).trans_lt hA1
  have hKbound := hclosed K hKcompact.isClosed hK0 hK1 r hr
  have hthick : pi.real (thickening r K) ≤
      pi.real (thickening r A) :=
    measureReal_mono (thickening_subset_of_subset r hKA)
  have hquantileMono : lowerQuantile standardGaussianMeasure q ≤
      lowerQuantile standardGaussianMeasure (pi.real K) := by
    rw [← normalCDFOrderIso_symm_apply
      (⟨q, hq0, hqA.trans hA1⟩ : Ioo (0 : ℝ) 1)]
    rw [← normalCDFOrderIso_symm_apply
      (⟨pi.real K, hK0, hK1⟩ : Ioo (0 : ℝ) 1)]
    exact normalCDFOrderIso.symm.monotone hqKreal.le
  have hprofileMono : G q ≤ G (pi.real K) := by
    apply strictMono_normalCDFReal.monotone
    gcongr
  have : G q ≤ pi.real (thickening r A) :=
    hprofileMono.trans (hKbound.trans hthick)
  exact (not_lt_of_ge this) hqprofile

/-- Complete G5 assembly at unit Gaussian curvature. -/
theorem bakryLedouxEnlargement_of_closedPerimeter
    {Y : Type*} [MetricSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [OpensMeasurableSpace Y]
    (pi : Measure Y) [IsProbabilityMeasure pi] [Measure.Regular pi]
    (hper : ClosedGaussianPerimeter pi)
    (hcont : ContinuousClosedEnlargementMass pi) :
    BakryLedouxEnlargement pi 1
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure) := by
  apply bakryLedouxEnlargement_of_closed pi 1
  intro K hK hK0 hK1 r hr
  simpa using normalCDF_shift_le_thickening_of_closedPerimeter
    pi hper hcont hK hK0 hK1 hr

/-- Complete G5 assembly from perimeter alone.  The former two-sided
enlargement-mass continuity premise is replaced by intrinsic right
continuity and the monotone scalar comparison. -/
theorem bakryLedouxEnlargement_of_closedPerimeter_monotone
    {Y : Type*} [MetricSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [OpensMeasurableSpace Y]
    (pi : Measure Y) [IsProbabilityMeasure pi] [Measure.Regular pi]
    (hper : ClosedGaussianPerimeter pi) :
    BakryLedouxEnlargement pi 1
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure) := by
  apply bakryLedouxEnlargement_of_closed pi 1
  intro K hK hK0 hK1 r hr
  simpa using
    normalCDF_shift_le_thickening_of_closedPerimeter_monotone
      pi hper hK hK0 hK1 hr

/-- Weakest G4-to-G5 entry point: a Bobkov bound by the closed transition
strip of each canonical ramp suffices. -/
theorem bakryLedouxEnlargement_of_closedStrip
    (hBobkov : GaussianRampClosedStripBound (E := E)) :
    BakryLedouxEnlargement (stdGaussian E) 1
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure) := by
  exact bakryLedouxEnlargement_of_closedPerimeter_monotone
    (stdGaussian E) (closedGaussianPerimeter_of_closedStrip hBobkov)

/-- Exact G4-to-G5 entry point: it suffices to prove functional Bobkov only
for the canonical distance ramps. -/
theorem bakryLedouxEnlargement_of_distanceRamps
    (hBobkov : GaussianBobkovDistanceRamps (E := E)) :
    BakryLedouxEnlargement (stdGaussian E) 1
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure) := by
  exact bakryLedouxEnlargement_of_closedPerimeter_monotone
    (stdGaussian E) (closedGaussianPerimeter_of_distanceRamps hBobkov)

/-- G4-to-G5 entry point for the standard Gaussian: the locally-Lipschitz
functional Bobkov inequality alone implies the sharp measurable-set
enlargement inequality.  Monotonicity and intrinsic right continuity of
closed-enlargement mass discharge the former continuity premise. -/
theorem bakryLedouxEnlargement_of_functionalLipschitz
    (hBobkov : GaussianBobkovLocallyLipschitz (E := E)) :
    BakryLedouxEnlargement (stdGaussian E) 1
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure) := by
  exact bakryLedouxEnlargement_of_distanceRamps
    (gaussianBobkovDistanceRamps_of_locallyLipschitz hBobkov)

end Concrete

end

end UniformRandomMALA
