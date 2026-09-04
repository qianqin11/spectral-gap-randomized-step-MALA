import UniformRandomMALA.Concrete.MALAFamily
import UniformRandomMALA.DiscreteTime.RejectionGoodSet

/-!
# A dyadic MALA rejection good set

This file specializes the abstract Jensen--Markov lemma to the concrete
jointly measurable MALA family.  Its only quantitative input is a fixed-step
`p`-moment bound, uniform over the dyadic interval `(t/2,t]`.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace Concrete
namespace FirstOrderPotential

variable {d : ℕ} (V : FirstOrderPotential d)

/-- Real rejection mass of the jointly measurable MALA family. -/
def malaRejectionMassReal (h : ℝ) (x : State d) : ℝ :=
  (1 - V.malaFamilyAcceptanceMass (h, x)).toReal

lemma measurable_uncurry_malaRejectionMassReal :
    Measurable (Function.uncurry V.malaRejectionMassReal) := by
  exact ENNReal.measurable_toReal.comp
    (measurable_const.sub V.measurable_malaFamilyAcceptanceMass)

lemma malaRejectionMassReal_nonneg (h : ℝ) (x : State d) :
    0 ≤ V.malaRejectionMassReal h x :=
  ENNReal.toReal_nonneg

lemma malaRejectionMassReal_le_one (h : ℝ) (x : State d) :
    V.malaRejectionMassReal h x ≤ 1 := by
  unfold malaRejectionMassReal
  have hle : 1 - V.malaFamilyAcceptanceMass (h, x) ≤ (1 : ℝ≥0∞) :=
    tsub_le_self
  have := ENNReal.toReal_mono ENNReal.one_ne_top hle
  simpa using this

lemma malaRejectionMassReal_eq_fixed
    {h : ℝ} (hh : 0 < h) (x : State d) :
    V.malaRejectionMassReal h x =
      (1 - MetropolisHastings.acceptanceMass
        (V.gaussianDensityProposal h) (V.malaAcceptance h) x).toReal := by
  unfold malaRejectionMassReal
  rw [V.malaFamilyAcceptanceMass_pair h x, effectiveStep_of_pos hh]

/-- Rejection mass averaged over the upper dyadic half interval. -/
def dyadicAverageRejection (t : ℝ) (x : State d) : ℝ :=
  DiscreteTime.averagedRejection (dyadicStepMeasure t)
    (fun z : State d × ℝ => V.malaRejectionMassReal z.2 z.1) x

lemma dyadicAverageRejection_eq_integral (t : ℝ) (x : State d) :
    V.dyadicAverageRejection t x =
      ∫ h, V.malaRejectionMassReal h x ∂dyadicStepMeasure t := by
  rfl

lemma measurable_dyadicAverageRejection {t : ℝ} (ht : 0 < t) :
    Measurable (V.dyadicAverageRejection t) := by
  let _ : IsProbabilityMeasure (dyadicStepMeasure t) :=
    dyadicStepMeasure_isProbabilityMeasure ht
  apply DiscreteTime.measurable_averagedRejection
  exact V.measurable_uncurry_malaRejectionMassReal.comp measurable_swap

/-- Concrete dyadic good-set estimate.  No continuity in the step size is
needed: joint measurability follows from `malaKernelFamily`, and boundedness
of rejection mass by one supplies all integrability hypotheses.

The sole quantitative hypothesis is the displayed fixed-step moment bound,
uniform for `h in (t/2,t]`. -/
theorem exists_dyadicAverageRejection_goodSet_one_third
    {t p B : ℝ} (ht : 0 < t) (hp : 1 ≤ p) (hB : 0 ≤ B)
    (hmoment : ∀ h ∈ Set.Ioc (t / 2) t,
      (∫ x : State d, (V.malaRejectionMassReal h x) ^ p
          ∂(V.target : Measure (State d))) ≤ B ^ p) :
    ∃ G : Set (State d),
      MeasurableSet G ∧
      (V.target : Measure (State d)) Gᶜ ≤
        ENNReal.ofReal ((3 * B) ^ p) ∧
      ∀ x ∈ G, V.dyadicAverageRejection t x ≤ 1 / 3 := by
  let nu : Measure ℝ := dyadicStepMeasure t
  let r : State d × ℝ → ℝ := fun z =>
    V.malaRejectionMassReal z.2 z.1
  let _ : IsProbabilityMeasure nu := dyadicStepMeasure_isProbabilityMeasure ht
  have hr : Measurable r := by
    exact V.measurable_uncurry_malaRejectionMassReal.comp measurable_swap
  have hr0 (z : State d × ℝ) : 0 ≤ r z :=
    V.malaRejectionMassReal_nonneg z.2 z.1
  have hr1 (z : State d × ℝ) : r z ≤ 1 :=
    V.malaRejectionMassReal_le_one z.2 z.1
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hrpMeas : Measurable (fun z => (r z) ^ p) := by
    exact (Real.continuous_rpow_const hp0).measurable.comp hr
  have hrpInt : Integrable (fun z => (r z) ^ p)
      ((V.target : Measure (State d)).prod nu) := by
    apply Integrable.of_bound hrpMeas.aestronglyMeasurable 1
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hr0 z) p)]
      exact Real.rpow_le_one (hr0 z) (hr1 z) hp0
  have hmem : ∀ᵐ h ∂nu, h ∈ Set.Ioc (t / 2) t := by
    change ∀ᵐ h ∂(volume : Measure ℝ)[|Set.Ioc (t / 2) t],
      h ∈ Set.Ioc (t / 2) t
    exact ProbabilityTheory.ae_cond_mem measurableSet_Ioc
  have hfiber : ∀ᵐ h ∂nu,
      (∫ x : State d, (r (x, h)) ^ p
          ∂(V.target : Measure (State d))) ≤ B ^ p := by
    filter_upwards [hmem] with h hh
    exact hmoment h hh
  have houterInt : Integrable
      (fun h => ∫ x : State d, (r (x, h)) ^ p
        ∂(V.target : Measure (State d))) nu :=
    hrpInt.integral_prod_right
  have hprodMoment :
      (∫ z, (r z) ^ p
          ∂((V.target : Measure (State d)).prod nu)) ≤ B ^ p := by
    calc
      (∫ z, (r z) ^ p
          ∂((V.target : Measure (State d)).prod nu)) =
          ∫ h, ∫ x : State d, (r (x, h)) ^ p
            ∂(V.target : Measure (State d)) ∂nu :=
        integral_prod_symm (fun z => (r z) ^ p) hrpInt
      _ ≤ ∫ _h, B ^ p ∂nu :=
        integral_mono_ae houterInt (integrable_const _) hfiber
      _ = B ^ p := by simp
  obtain ⟨G, hG, hmass, hgood⟩ :=
    DiscreteTime.exists_averagedRejection_goodSet_one_third
      (mu := (V.target : Measure (State d))) (rho := nu)
      hp hB hr hr0 hrpInt hprodMoment
  refine ⟨G, hG, hmass, ?_⟩
  simpa only [dyadicAverageRejection, nu, r] using hgood

/-- Version whose quantitative hypothesis is stated directly using the
fixed-step MALA rejection probability. -/
theorem exists_dyadicMALARejection_goodSet_one_third
    {t p B : ℝ} (ht : 0 < t) (hp : 1 ≤ p) (hB : 0 ≤ B)
    (hmoment : ∀ h ∈ Set.Ioc (t / 2) t,
      (∫ x : State d,
        ((1 - MetropolisHastings.acceptanceMass
          (V.gaussianDensityProposal h) (V.malaAcceptance h) x).toReal) ^ p
          ∂(V.target : Measure (State d))) ≤ B ^ p) :
    ∃ G : Set (State d),
      MeasurableSet G ∧
      (V.target : Measure (State d)) Gᶜ ≤
        ENNReal.ofReal ((3 * B) ^ p) ∧
      ∀ x ∈ G,
        (∫ h, V.malaRejectionMassReal h x ∂dyadicStepMeasure t) ≤ 1 / 3 := by
  have hmoment' : ∀ h ∈ Set.Ioc (t / 2) t,
      (∫ x : State d, (V.malaRejectionMassReal h x) ^ p
          ∂(V.target : Measure (State d))) ≤ B ^ p := by
    intro h hhmem
    have hh : 0 < h := lt_of_lt_of_le (by linarith [ht]) hhmem.1.le
    simpa only [V.malaRejectionMassReal_eq_fixed hh] using hmoment h hhmem
  obtain ⟨G, hG, hmass, hgood⟩ :=
    V.exists_dyadicAverageRejection_goodSet_one_third ht hp hB hmoment'
  refine ⟨G, hG, hmass, ?_⟩
  intro x hx
  rw [← V.dyadicAverageRejection_eq_integral t x]
  exact hgood x hx

end FirstOrderPotential
end Concrete

end
end UniformRandomMALA
