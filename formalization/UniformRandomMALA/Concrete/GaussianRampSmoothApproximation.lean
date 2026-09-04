import UniformRandomMALA.Concrete.GaussianEnlargement

/-!
# Smooth approximation of Gaussian distance ramps

This module isolates the exact mollification statement needed between the
smooth G3--G4 Bobkov argument and G5.  In particular, no convergence of
mollified gradients to a Rademacher derivative is required: uniform gradient
control and localization to a shrinking closed transition strip suffice.
-/

namespace UniformRandomMALA

open Filter Set Metric MeasureTheory ProbabilityTheory
open scoped Topology ENNReal ProbabilityTheory NNReal

noncomputable section

namespace Concrete

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [SecondCountableTopology E]

/-- A sequence of smooth functions witnessing that a distance ramp can be
used in the smooth Bobkov inequality.  The approximants equal one on the
closed set, vanish outside a shrinking outer closed thickening, and retain
the ramp's `1/h` gradient bound. -/
structure GaussianRampSmoothApproximation
    {h : ℝ} (hh : 0 < h) (A : Set E) where
  delta : ℕ → ℝ
  approx : ℕ → BoundedContinuousFunction E ℝ
  Dapprox : ℕ → BoundedContinuousFunction E (E →L[ℝ] ℝ)
  delta_pos : ∀ n, 0 < delta n
  delta_tendsto_zero : Tendsto delta atTop (nhds 0)
  range : ∀ n x, approx n x ∈ Icc (0 : ℝ) 1
  smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (⇑(approx n))
  fderiv_eq : ∀ n x, fderiv ℝ (⇑(approx n)) x = Dapprox n x
  mean_tendsto : Tendsto
    (fun n => ∫ x, approx n x ∂stdGaussian E) atTop
    (nhds (∫ x, gaussianRamp hh A x ∂stdGaussian E))
  one_on : ∀ n, ∀ x ∈ A, approx n x = 1
  zero_off : ∀ n, ∀ x ∉ cthickening (h + delta n) A, approx n x = 0
  norm_Dapprox_le : ∀ n x, ‖Dapprox n x‖ ≤ h⁻¹

/-- Every closed-set distance ramp admits the smooth approximation certificate
used by `gaussianRampClosedStripBound_of_smooth`. -/
def GaussianRampSmoothApproximationProperty : Prop :=
  ∀ {h : ℝ} (hh : 0 < h) {A : Set E}, IsClosed A →
    Nonempty (GaussianRampSmoothApproximation hh A)

theorem gaussianRampSmooth_bobkovIntegrand_le_closedStrip
    {h : ℝ} (hh : 0 < h) {A : Set E}
    (a : GaussianRampSmoothApproximation hh A) (n : ℕ) (x : E) :
    Real.sqrt
        (normalProfileClosed (a.approx n x) ^ 2 + ‖a.Dapprox n x‖ ^ 2) ≤
      (cthickening (h + a.delta n) A \ A).indicator
        (fun _ => (Real.sqrt (2 * Real.pi))⁻¹ + h⁻¹) x := by
  by_cases hxA : x ∈ A
  · rw [indicator_of_notMem (by simp [hxA]), a.one_on n x hxA,
      normalProfileClosed_one]
    have hDzero : a.Dapprox n x = 0 := by
      rw [← a.fderiv_eq n x]
      apply IsLocalMax.fderiv_eq_zero
      exact Filter.Eventually.of_forall fun y => by
        rw [a.one_on n x hxA]
        exact (a.range n y).2
    rw [hDzero]
    simp
  by_cases hxT : x ∈ cthickening (h + a.delta n) A
  · rw [indicator_of_mem
      (show x ∈ cthickening (h + a.delta n) A \ A from ⟨hxT, hxA⟩)]
    have hp0 := normalProfileClosed_nonneg (a.approx n x)
    have hp := normalProfileClosed_le_inv_sqrt_two_pi (a.approx n x)
    have hD0 : 0 ≤ ‖a.Dapprox n x‖ := norm_nonneg _
    have hD := a.norm_Dapprox_le n x
    have hsqrt : Real.sqrt
        (normalProfileClosed (a.approx n x) ^ 2 + ‖a.Dapprox n x‖ ^ 2) ≤
        normalProfileClosed (a.approx n x) + ‖a.Dapprox n x‖ := by
      rw [Real.sqrt_le_iff]
      constructor
      · linarith
      · nlinarith [sq_nonneg
          (normalProfileClosed (a.approx n x) + ‖a.Dapprox n x‖)]
    exact hsqrt.trans (add_le_add hp hD)
  · rw [indicator_of_notMem (by simp [hxT]), a.zero_off n x hxT,
      normalProfileClosed_zero]
    have hDzero : a.Dapprox n x = 0 := by
      rw [← a.fderiv_eq n x]
      apply IsLocalMin.fderiv_eq_zero
      exact Filter.Eventually.of_forall fun y => by
        rw [a.zero_off n x hxT]
        exact (a.range n y).1
    rw [hDzero]
    simp

/-- A single localized ramp approximation satisfying the Bobkov inequality
at every approximation level yields the required closed-strip estimate. -/
theorem gaussianRampClosedStripBound_of_approximation
    {h : ℝ} (hh : 0 < h) {A : Set E} (hA : IsClosed A)
    (a : GaussianRampSmoothApproximation hh A)
    (hBobkov : ∀ n,
      normalProfileClosed (∫ x, a.approx n x ∂stdGaussian E) ≤
        ∫ x, Real.sqrt
          (normalProfileClosed (a.approx n x) ^ 2 +
            ‖a.Dapprox n x‖ ^ 2) ∂stdGaussian E) :
    normalProfileClosed
        (∫ x, gaussianRamp hh A x ∂stdGaussian E) ≤
      ((Real.sqrt (2 * Real.pi))⁻¹ + h⁻¹) *
        (stdGaussian E).real (cthickening h A \ A) := by
  let C : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ + h⁻¹
  have hC0 : 0 ≤ C := add_nonneg
    (inv_nonneg.mpr (Real.sqrt_nonneg _)) (inv_nonneg.mpr hh.le)
  have hleft : Tendsto (fun n => normalProfileClosed
      (∫ x, a.approx n x ∂stdGaussian E)) atTop
      (nhds (normalProfileClosed
        (∫ x, gaussianRamp hh A x ∂stdGaussian E))) :=
    continuous_normalProfileClosed.continuousAt.tendsto.comp a.mean_tendsto
  have hradius : Tendsto (fun n => h + a.delta n) atTop (nhds h) := by
    simpa using tendsto_const_nhds.add a.delta_tendsto_zero
  have hradiusWithin : Tendsto (fun n => h + a.delta n) atTop
      (nhdsWithin h (Ici h)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hradius, Filter.Eventually.of_forall fun n => ?_⟩
    exact le_add_of_nonneg_right (a.delta_pos n).le
  have hmass : Tendsto
      (fun n => (stdGaussian E).real (cthickening (h + a.delta n) A))
      atTop (nhds ((stdGaussian E).real (cthickening h A))) := by
    exact (continuousWithinAt_closedEnlargementMass_right
      (stdGaussian E) A h).tendsto.comp hradiusWithin
  have hstripEq (r : ℝ) (hr : 0 ≤ r) :
      (stdGaussian E).real (cthickening r A \ A) =
        (stdGaussian E).real (cthickening r A) -
          (stdGaussian E).real A := by
    rw [measureReal_sdiff]
    · simpa only [hA.closure_eq, cthickening_zero] using
        cthickening_mono hr A
    · exact hA.measurableSet
  have hright : Tendsto (fun n => C *
      (stdGaussian E).real (cthickening (h + a.delta n) A \ A)) atTop
      (nhds (C * (stdGaussian E).real (cthickening h A \ A))) := by
    have hsub := hmass.sub_const ((stdGaussian E).real A)
    have hmul : Tendsto (fun n : ℕ => C *
        ((stdGaussian E).real (cthickening (h + a.delta n) A) -
          (stdGaussian E).real A)) atTop
        (nhds (C * ((stdGaussian E).real (cthickening h A) -
          (stdGaussian E).real A))) :=
      (tendsto_const_nhds.mul hsub)
    convert hmul using 1
    · funext n
      rw [hstripEq (h + a.delta n) (by linarith [a.delta_pos n])]
    · rw [hstripEq h hh.le]
  have hevent : ∀ n,
      normalProfileClosed (∫ x, a.approx n x ∂stdGaussian E) ≤
        C * (stdGaussian E).real
          (cthickening (h + a.delta n) A \ A) := by
    intro n
    let lhs : E → ℝ := fun x => Real.sqrt
      (normalProfileClosed (a.approx n x) ^ 2 + ‖a.Dapprox n x‖ ^ 2)
    let rhs : E → ℝ := (cthickening (h + a.delta n) A \ A).indicator
      (fun _ => C)
    have hstrip : MeasurableSet (cthickening (h + a.delta n) A \ A) :=
      isClosed_cthickening.measurableSet.diff hA.measurableSet
    have hrhs : Integrable rhs (stdGaussian E) :=
      (integrable_const C).indicator hstrip
    have hlhsMeas : AEStronglyMeasurable lhs (stdGaussian E) := by
      dsimp only [lhs]
      have hp : Measurable (fun x : E =>
          normalProfileClosed (a.approx n x)) :=
        continuous_normalProfileClosed.measurable.comp
          (a.approx n).continuous.measurable
      have hD : Measurable (fun x : E => ‖a.Dapprox n x‖) :=
        (a.Dapprox n).continuous.measurable.norm
      exact (Real.continuous_sqrt.measurable.comp
        ((hp.pow_const 2).add (hD.pow_const 2))).aestronglyMeasurable
    have hpoint : ∀ x, lhs x ≤ rhs x := fun x => by
      exact gaussianRampSmooth_bobkovIntegrand_le_closedStrip hh a n x
    have hlhs : Integrable lhs (stdGaussian E) := by
      apply hrhs.mono' hlhsMeas
      exact Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
        have hrhs0 : 0 ≤ rhs x := by
          change 0 ≤ (cthickening (h + a.delta n) A \ A).indicator
            (fun _ => C) x
          by_cases hx : x ∈ cthickening (h + a.delta n) A \ A
          · rw [indicator_of_mem hx]
            exact hC0
          · rw [indicator_of_notMem hx]
        exact hpoint x
    calc
      normalProfileClosed (∫ x, a.approx n x ∂stdGaussian E) ≤
          ∫ x, lhs x ∂stdGaussian E := hBobkov n
      _ ≤ ∫ x, rhs x ∂stdGaussian E :=
        integral_mono_ae hlhs hrhs (Filter.Eventually.of_forall hpoint)
      _ = C * (stdGaussian E).real
          (cthickening (h + a.delta n) A \ A) := by
        dsimp only [rhs]
        rw [integral_indicator_const _ hstrip]
        simp only [smul_eq_mul]
        ring
  exact le_of_tendsto_of_tendsto hleft hright
    (Filter.Eventually.of_forall hevent)

/-- Smooth Bobkov plus the localized ramp mollification certificate implies
the closed-strip bound needed by G5.  The proof only uses convergence of
means and finite-measure right continuity of closed thickenings. -/
theorem gaussianRampClosedStripBound_of_smooth
    (hSmooth : GaussianBobkovSmooth (X := E))
    (hApprox : GaussianRampSmoothApproximationProperty (E := E)) :
    GaussianRampClosedStripBound (E := E) := by
  intro h hh A hA
  let a := Classical.choice (hApprox hh hA)
  exact gaussianRampClosedStripBound_of_approximation hh hA a fun n =>
    hSmooth (a.approx n) (a.Dapprox n) (a.range n)
      (a.smooth n) (a.fderiv_eq n)

/-- Smooth G3--G4 Bobkov and localized smooth ramp approximation together
imply the full measurable-set Bakry--Ledoux enlargement theorem. -/
theorem bakryLedouxEnlargement_of_smoothBobkovAndRampApproximation
    (hSmooth : GaussianBobkovSmooth (X := E))
    (hApprox : GaussianRampSmoothApproximationProperty (E := E)) :
    BakryLedouxEnlargement (stdGaussian E) 1
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure) := by
  exact bakryLedouxEnlargement_of_closedStrip
    (gaussianRampClosedStripBound_of_smooth hSmooth hApprox)

/-- End-to-end G3--G5 assembly with the two remaining concrete analytic
obligations exposed separately: construct the canonical smooth OU
interpolations, and construct localized smooth distance-ramp approximants. -/
theorem bakryLedouxEnlargement_of_smoothInterpolationsAndRampApproximation
    (hflow : GaussianBobkovSmoothInterpolationProperty (X := E))
    (hApprox : GaussianRampSmoothApproximationProperty (E := E)) :
    BakryLedouxEnlargement (stdGaussian E) 1
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure) := by
  exact bakryLedouxEnlargement_of_smoothBobkovAndRampApproximation
    (gaussianBobkovSmooth_of_smoothInterpolations hflow) hApprox

end Concrete

end

end UniformRandomMALA
