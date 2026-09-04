import UniformRandomMALA.DiscreteTime.ExplicitRWMBalance
import UniformRandomMALA.Concrete.RWMExpansion
import UniformRandomMALA.Concrete.PotentialCentering
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Mathlib.Probability.Kernel.Composition.CompMap

/-!
# A finite Gaussian--uniform coupling of Euler and explicit RWM

This file constructs the elementary one-step coupling used in the fully
discrete proof.  One standard Gaussian innovation drives both coordinates;
one unit-uniform coordinate makes the RWM accept--reject decision.  The RWM
marginal is identified directly with `explicitRWMKernel`.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory unitInterval RealInnerProductSpace

noncomputable section

namespace DiscreteTime

open Concrete

variable {d : ℕ}

/-- One Euler step driven by a standard Gaussian innovation. -/
def explicitEulerUpdate (V : FirstOrderPotential d) (δ : ℝ)
    (x z : State d) : State d :=
  x - δ • V.gradU x + Real.sqrt (2 * δ) • z

lemma continuous_uncurry_explicitEulerUpdate
    (V : FirstOrderPotential d) (δ : ℝ) :
    Continuous (Function.uncurry (explicitEulerUpdate V δ)) := by
  unfold Function.uncurry explicitEulerUpdate
  have hg : Continuous (fun p : State d × State d => δ • V.gradU p.1) :=
    (V.continuous_gradU.comp continuous_fst).const_smul δ
  have hz : Continuous (fun p : State d × State d =>
      Real.sqrt (2 * δ) • p.2) :=
    continuous_snd.const_smul (Real.sqrt (2 * δ))
  exact (continuous_fst.sub hg).add hz

lemma measurable_uncurry_explicitEulerUpdate
    (V : FirstOrderPotential d) (δ : ℝ) :
    Measurable (Function.uncurry (explicitEulerUpdate V δ)) :=
  (continuous_uncurry_explicitEulerUpdate V δ).measurable

/-- The real acceptance threshold used by the uniform coordinate. -/
def explicitRWMAcceptanceReal
    (V : FirstOrderPotential d) (δ : ℝ) (x z : State d) : ℝ :=
  min 1 (Real.exp (V.U x - V.U (explicitRWMEndpoint δ x z)))

lemma explicitRWMAcceptanceReal_eq_toReal
    (V : FirstOrderPotential d) (δ : ℝ) (x z : State d) :
    explicitRWMAcceptanceReal V δ x z =
      (explicitRWMAcceptance V δ x z).toReal := by
  rw [explicitRWMAcceptance_eq_boltzmann,
    ENNReal.toReal_inf (by simp) ENNReal.one_ne_top]
  simp [explicitRWMAcceptanceReal, (Real.exp_pos _).le, min_comm]

lemma explicitRWMAcceptanceReal_nonneg
    (V : FirstOrderPotential d) (δ : ℝ) (x z : State d) :
    0 ≤ explicitRWMAcceptanceReal V δ x z := by
  exact le_min (by norm_num) (Real.exp_pos _).le

lemma explicitRWMAcceptanceReal_le_one
    (V : FirstOrderPotential d) (δ : ℝ) (x z : State d) :
    explicitRWMAcceptanceReal V δ x z ≤ 1 :=
  min_le_left _ _

lemma measurable_uncurry_explicitRWMAcceptanceReal
    (V : FirstOrderPotential d) (δ : ℝ) :
    Measurable (Function.uncurry (explicitRWMAcceptanceReal V δ)) := by
  unfold Function.uncurry explicitRWMAcceptanceReal
  have hx : Measurable (fun p : State d × State d => V.U p.1) :=
    V.continuous_U.measurable.comp measurable_fst
  have hy : Measurable (fun p : State d × State d =>
      V.U (explicitRWMEndpoint δ p.1 p.2)) :=
    V.continuous_U.measurable.comp
      (measurable_uncurry_explicitRWMEndpoint δ)
  exact measurable_const.min (hx.sub hy).exp

/-- An explicit RWM step from a Gaussian proposal and a unit uniform. -/
def explicitRWMUniformUpdate
    (V : FirstOrderPotential d) (δ : ℝ) (x : State d)
    (zu : State d × Set.Icc (0 : ℝ) 1) : State d :=
  if (zu.2 : ℝ) ≤ explicitRWMAcceptanceReal V δ x zu.1 then
    explicitRWMEndpoint δ x zu.1
  else x

lemma measurable_explicitRWMUniformUpdate
    (V : FirstOrderPotential d) (δ : ℝ) (x : State d) :
    Measurable (explicitRWMUniformUpdate V δ x) := by
  unfold explicitRWMUniformUpdate
  apply Measurable.ite
  · exact measurableSet_le (measurable_subtype_coe.comp measurable_snd)
      ((Measurable.of_uncurry_left
        (measurable_uncurry_explicitRWMAcceptanceReal V δ)).comp measurable_fst)
  · exact (Measurable.of_uncurry_left
      (measurable_uncurry_explicitRWMEndpoint δ)).comp measurable_fst
  · exact measurable_const

lemma measurable_uncurry_explicitRWMUniformUpdate
    (V : FirstOrderPotential d) (δ : ℝ) :
    Measurable (Function.uncurry (explicitRWMUniformUpdate V δ)) := by
  unfold Function.uncurry explicitRWMUniformUpdate
  let xz : State d × (State d × Set.Icc (0 : ℝ) 1) →
      State d × State d := fun p => (p.1, p.2.1)
  have hxz : Measurable xz :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hu : Measurable (fun p : State d ×
      (State d × Set.Icc (0 : ℝ) 1) => (p.2.2 : ℝ)) :=
    measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)
  have ha : Measurable (fun p : State d ×
      (State d × Set.Icc (0 : ℝ) 1) =>
        explicitRWMAcceptanceReal V δ p.1 p.2.1) := by
    exact (measurable_uncurry_explicitRWMAcceptanceReal V δ).comp hxz
  have hy : Measurable (fun p : State d ×
      (State d × Set.Icc (0 : ℝ) 1) =>
        explicitRWMEndpoint δ p.1 p.2.1) := by
    exact (measurable_uncurry_explicitRWMEndpoint δ).comp hxz
  exact Measurable.ite (measurableSet_le hu ha) hy measurable_fst

/-- RWM update written in rejection form, matching the expansion lemmas in
`Concrete.RWMExpansion`. -/
def explicitRWMRejectionUniformUpdate
    (V : FirstOrderPotential d) (δ : ℝ) (x : State d)
    (zu : State d × Set.Icc (0 : ℝ) 1) : State d :=
  if (zu.2 : ℝ) ≤ 1 - explicitRWMAcceptanceReal V δ x zu.1 then
    x
  else explicitRWMEndpoint δ x zu.1

lemma one_sub_explicitRWMAcceptanceReal_eq_rejectionProfile
    (V : FirstOrderPotential d) (δ : ℝ) (x z : State d) :
    1 - explicitRWMAcceptanceReal V δ x z =
      DiscreteTime.rejectionProfile
        (V.rwmEnergyIncrement x (Real.sqrt (2 * δ) • z)) := by
  unfold explicitRWMAcceptanceReal DiscreteTime.rejectionProfile
    Concrete.FirstOrderPotential.rwmEnergyIncrement explicitRWMEndpoint
  congr 2
  ring_nf

lemma measurable_explicitRWMRejectionUniformUpdate
    (V : FirstOrderPotential d) (δ : ℝ) (x : State d) :
    Measurable (explicitRWMRejectionUniformUpdate V δ x) := by
  unfold explicitRWMRejectionUniformUpdate
  apply Measurable.ite
  · exact measurableSet_le (measurable_subtype_coe.comp measurable_snd)
      (measurable_const.sub ((Measurable.of_uncurry_left
        (measurable_uncurry_explicitRWMAcceptanceReal V δ)).comp measurable_fst))
  · exact measurable_const
  · exact (Measurable.of_uncurry_left
      (measurable_uncurry_explicitRWMEndpoint δ)).comp measurable_fst

lemma measurable_uncurry_explicitRWMRejectionUniformUpdate
    (V : FirstOrderPotential d) (δ : ℝ) :
    Measurable
      (Function.uncurry (explicitRWMRejectionUniformUpdate V δ)) := by
  unfold Function.uncurry explicitRWMRejectionUniformUpdate
  let xz : State d × (State d × Set.Icc (0 : ℝ) 1) →
      State d × State d := fun p => (p.1, p.2.1)
  have hxz : Measurable xz :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hu : Measurable (fun p : State d ×
      (State d × Set.Icc (0 : ℝ) 1) => (p.2.2 : ℝ)) :=
    measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)
  have hr : Measurable (fun p : State d ×
      (State d × Set.Icc (0 : ℝ) 1) =>
        1 - explicitRWMAcceptanceReal V δ p.1 p.2.1) := by
    exact measurable_const.sub
      ((measurable_uncurry_explicitRWMAcceptanceReal V δ).comp hxz)
  have hy : Measurable (fun p : State d ×
      (State d × Set.Icc (0 : ℝ) 1) =>
        explicitRWMEndpoint δ p.1 p.2.1) := by
    exact (measurable_uncurry_explicitRWMEndpoint δ).comp hxz
  exact Measurable.ite (measurableSet_le hu hr) measurable_fst hy

/-- The rejection-form update is proposal minus the actual Bernoulli
rejected increment used by the one-step expansion. -/
lemma explicitRWMRejectionUniformUpdate_eq_endpoint_sub_rejectedIncrement
    (V : FirstOrderPotential d) (δ : ℝ) (x z : State d)
    (u : Set.Icc (0 : ℝ) 1) :
    explicitRWMRejectionUniformUpdate V δ x (z, u) =
      explicitRWMEndpoint δ x z -
        V.bernoulliRWMRejectedIncrement δ x z u := by
  rw [show explicitRWMRejectionUniformUpdate V δ x (z, u) =
      if (u : ℝ) ≤ DiscreteTime.rejectionProfile
          (V.rwmEnergyIncrement x (Real.sqrt (2 * δ) • z)) then x
      else explicitRWMEndpoint δ x z by
    unfold explicitRWMRejectionUniformUpdate
    rw [one_sub_explicitRWMAcceptanceReal_eq_rejectionProfile]]
  unfold Concrete.FirstOrderPotential.bernoulliRWMRejectedIncrement thresholdConst
  by_cases hu : (u : ℝ) ≤ DiscreteTime.rejectionProfile
      (V.rwmEnergyIncrement x (Real.sqrt (2 * δ) • z))
  · rw [if_pos hu, if_pos hu]
    simp only [explicitRWMEndpoint, add_sub_cancel_right]
  · rw [if_neg hu, if_neg hu]
    simp only [sub_zero]

/-- One coupled Euler/RWM update.  The two chains use the same Gaussian
innovation, while only the RWM coordinate reads the uniform coordinate. -/
def eulerRWMPairUpdate
    (V : FirstOrderPotential d) (δ : ℝ)
    (xy : State d × State d)
  (zu : State d × Set.Icc (0 : ℝ) 1) : State d × State d :=
  (explicitEulerUpdate V δ xy.1 zu.1,
    explicitRWMRejectionUniformUpdate V δ xy.2 zu)

lemma measurable_eulerRWMPairUpdate
    (V : FirstOrderPotential d) (δ : ℝ) (xy : State d × State d) :
    Measurable (eulerRWMPairUpdate V δ xy) := by
  exact ((Measurable.of_uncurry_left
      (measurable_uncurry_explicitEulerUpdate V δ)).comp measurable_fst).prodMk
    (measurable_explicitRWMRejectionUniformUpdate V δ xy.2)

lemma measurable_uncurry_eulerRWMPairUpdate
    (V : FirstOrderPotential d) (δ : ℝ) :
    Measurable (Function.uncurry (eulerRWMPairUpdate V δ)) := by
  let ez : (State d × State d) ×
      (State d × Set.Icc (0 : ℝ) 1) → State d × State d :=
    fun p => (p.1.1, p.2.1)
  let rzu : (State d × State d) ×
      (State d × Set.Icc (0 : ℝ) 1) →
        State d × (State d × Set.Icc (0 : ℝ) 1) :=
    fun p => (p.1.2, p.2)
  have hez : Measurable ez :=
    (measurable_fst.comp measurable_fst).prodMk
      (measurable_fst.comp measurable_snd)
  have hrzu : Measurable rzu :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  exact (measurable_uncurry_explicitEulerUpdate V δ |>.comp hez).prodMk
    (measurable_uncurry_explicitRWMRejectionUniformUpdate V δ |>.comp hrzu)

/-- The independent Gaussian--unit-uniform innovation law. -/
def gaussianUniformNoise (d : ℕ) :
    Measure (State d × Set.Icc (0 : ℝ) 1) :=
  (stdGaussian (State d)).prod volume

instance gaussianUniformNoise_isProbabilityMeasure (d : ℕ) :
    IsProbabilityMeasure (gaussianUniformNoise d) := by
  unfold gaussianUniformNoise
  infer_instance

/-- Integrating a unit-uniform threshold decision gives its two-point
mixture.  This is the elementary replacement for an abstract Bernoulli
kernel construction. -/
lemma lintegral_unitInterval_acceptReject
    {E : Type*} [MeasurableSpace E]
    (g : E → ℝ≥0∞) (_hg : Measurable g) (x y : E)
    (a : ℝ≥0∞) (ha : a ≤ 1) :
    (∫⁻ u : Set.Icc (0 : ℝ) 1,
        g (if (u : ℝ) ≤ a.toReal then y else x) ∂volume) =
      a * g y + (1 - a) * g x := by
  let aI : Set.Icc (0 : ℝ) 1 :=
    ⟨a.toReal, ENNReal.toReal_nonneg,
      by simpa using ENNReal.toReal_mono ENNReal.one_ne_top ha⟩
  have ha_top : a ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top ha
  have hsplit : (fun u : Set.Icc (0 : ℝ) 1 =>
      g (if (u : ℝ) ≤ a.toReal then y else x)) =
      (Set.Iic aI).indicator (fun _ => g y) +
        (Set.Ioi aI).indicator (fun _ => g x) := by
    funext u
    by_cases hu : (u : ℝ) ≤ a.toReal
    · have huI : u ≤ aI := hu
      simp [hu, huI]
    · have huI : aI < u := lt_of_not_ge hu
      simp [hu, huI]
  rw [hsplit]
  change (∫⁻ u : Set.Icc (0 : ℝ) 1,
      (Set.Iic aI).indicator (fun _ => g y) u +
        (Set.Ioi aI).indicator (fun _ => g x) u ∂volume) = _
  rw [lintegral_add_left
    (measurable_const.indicator measurableSet_Iic),
    lintegral_indicator measurableSet_Iic,
    lintegral_indicator measurableSet_Ioi,
    lintegral_const, lintegral_const]
  simp only [Measure.restrict_apply_univ]
  rw [
    unitInterval.volume_Iic, unitInterval.volume_Ioi]
  have hcomp : ENNReal.ofReal (1 - a.toReal) = 1 - a := by
    rw [ENNReal.ofReal_sub 1 ENNReal.toReal_nonneg]
    simp [ha_top]
  rw [show ENNReal.ofReal (aI : ℝ) = a by
      simpa [aI] using ENNReal.ofReal_toReal ha_top,
    show ENNReal.ofReal (1 - (aI : ℝ)) = 1 - a by
      simpa [aI] using hcomp]
  ac_rfl

/-! ## A common-uniform discrepancy lemma -/

/-- Generic accept--reject update from one unit uniform. -/
def unitAcceptRejectUpdate {E : Type*}
    (x y : E) (a : ℝ) (u : Set.Icc (0 : ℝ) 1) : E :=
  if (u : ℝ) ≤ a then y else x

/-- Unit uniforms on which two thresholds make different decisions. -/
def unitThresholdDisagreement (a b : ℝ) :
    Set (Set.Icc (0 : ℝ) 1) :=
  {u | (((u : ℝ) ≤ a) ∧ ¬((u : ℝ) ≤ b)) ∨
    (((u : ℝ) ≤ b) ∧ ¬((u : ℝ) ≤ a))}

lemma measurableSet_unitThresholdDisagreement (a b : ℝ) :
    MeasurableSet (unitThresholdDisagreement a b) := by
  unfold unitThresholdDisagreement
  let A : Set (Set.Icc (0 : ℝ) 1) := {u | (u : ℝ) ≤ a}
  let B : Set (Set.Icc (0 : ℝ) 1) := {u | (u : ℝ) ≤ b}
  have hA : MeasurableSet A :=
    measurableSet_le measurable_subtype_coe measurable_const
  have hB : MeasurableSet B :=
    measurableSet_le measurable_subtype_coe measurable_const
  exact (hA.inter hB.compl).union (hB.inter hA.compl)

/-- The probability that one unit uniform disagrees at thresholds `a,b` is
exactly `|a-b|`. -/
theorem volume_unitThresholdDisagreement
    (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    volume (unitThresholdDisagreement a b) = ENNReal.ofReal |a - b| := by
  let aI : Set.Icc (0 : ℝ) 1 := ⟨a, ha0, ha1⟩
  let bI : Set.Icc (0 : ℝ) 1 := ⟨b, hb0, hb1⟩
  rcases le_total a b with hab | hba
  · have hset : unitThresholdDisagreement a b = Set.Ioc aI bI := by
      ext u
      change ((((u : ℝ) ≤ a) ∧ ¬((u : ℝ) ≤ b)) ∨
          (((u : ℝ) ≤ b) ∧ ¬((u : ℝ) ≤ a))) ↔
        (a < (u : ℝ) ∧ (u : ℝ) ≤ b)
      constructor
      · rintro (⟨hua, hub⟩ | ⟨hub, hua⟩)
        · exact False.elim (hub (hua.trans hab))
        · exact ⟨lt_of_not_ge hua, hub⟩
      · rintro ⟨hua, hub⟩
        exact Or.inr ⟨hub, not_le_of_gt hua⟩
    rw [hset, unitInterval.volume_Ioc]
    simp [aI, bI, abs_of_nonpos (sub_nonpos.mpr hab)]
  · have hset : unitThresholdDisagreement a b = Set.Ioc bI aI := by
      ext u
      change ((((u : ℝ) ≤ a) ∧ ¬((u : ℝ) ≤ b)) ∨
          (((u : ℝ) ≤ b) ∧ ¬((u : ℝ) ≤ a))) ↔
        (b < (u : ℝ) ∧ (u : ℝ) ≤ a)
      constructor
      · rintro (⟨hua, hub⟩ | ⟨hub, hua⟩)
        · exact ⟨lt_of_not_ge hub, hua⟩
        · exact False.elim (hua (hub.trans hba))
      · rintro ⟨hub, hua⟩
        exact Or.inl ⟨hua, not_le_of_gt hub⟩
    rw [hset, unitInterval.volume_Ioc]
    simp [aI, bI, abs_of_nonneg (sub_nonneg.mpr hba)]

/-- Away from threshold disagreement, a shared uniform leaves only the
larger of the two baseline/proposal discrepancies. -/
lemma dist_unitAcceptRejectUpdate_le_max_of_not_disagreement
    {E : Type*} [PseudoMetricSpace E]
    (x₁ y₁ x₂ y₂ : E) (a b : ℝ) (u : Set.Icc (0 : ℝ) 1)
    (hu : u ∉ unitThresholdDisagreement a b) :
    dist (unitAcceptRejectUpdate x₁ y₁ a u)
        (unitAcceptRejectUpdate x₂ y₂ b u) ≤
      max (dist x₁ x₂) (dist y₁ y₂) := by
  have hsame : ((u : ℝ) ≤ a) ↔ ((u : ℝ) ≤ b) := by
    change ¬((((u : ℝ) ≤ a) ∧ ¬((u : ℝ) ≤ b)) ∨
      (((u : ℝ) ≤ b) ∧ ¬((u : ℝ) ≤ a))) at hu
    constructor
    · intro hua
      by_contra hub
      exact hu (Or.inl ⟨hua, hub⟩)
    · intro hub
      by_contra hua
      exact hu (Or.inr ⟨hub, hua⟩)
  by_cases hua : (u : ℝ) ≤ a
  · have hub : (u : ℝ) ≤ b := hsame.mp hua
    simp [unitAcceptRejectUpdate, hua, hub]
  · have hub : ¬(u : ℝ) ≤ b := fun h => hua (hsame.mpr h)
    simp [unitAcceptRejectUpdate, hua, hub]

/-- Coupling-tail form: after allowing the larger proposal/baseline
discrepancy, the only remaining mismatch probability is the absolute
difference of acceptance probabilities. -/
theorem volume_unitAcceptRejectUpdate_dist_gt_max_le
    {E : Type*} [PseudoMetricSpace E]
    (x₁ y₁ x₂ y₂ : E) (a b : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    volume {u : Set.Icc (0 : ℝ) 1 |
        max (dist x₁ x₂) (dist y₁ y₂) <
          dist (unitAcceptRejectUpdate x₁ y₁ a u)
            (unitAcceptRejectUpdate x₂ y₂ b u)} ≤
      ENNReal.ofReal |a - b| := by
  calc
    volume {u : Set.Icc (0 : ℝ) 1 |
        max (dist x₁ x₂) (dist y₁ y₂) <
          dist (unitAcceptRejectUpdate x₁ y₁ a u)
            (unitAcceptRejectUpdate x₂ y₂ b u)} ≤
        volume (unitThresholdDisagreement a b) := by
      apply measure_mono
      intro u hu
      by_contra hdis
      exact (not_lt_of_ge
        (dist_unitAcceptRejectUpdate_le_max_of_not_disagreement
          x₁ y₁ x₂ y₂ a b u hdis)) hu
    _ = ENNReal.ofReal |a - b| :=
      volume_unitThresholdDisagreement a b ha0 ha1 hb0 hb1

/-- Concrete shared-innovation RWM coupling bound.  Once the tolerance
allows the larger of the current-state and proposal discrepancies, the only
remaining bad uniforms have mass bounded by the difference of acceptance
probabilities. -/
theorem volume_explicitRWMRejectionUniformUpdate_dist_gt_max_le
    (V : FirstOrderPotential d) (δ : ℝ)
    (x₁ x₂ z : State d) :
    volume {u : Set.Icc (0 : ℝ) 1 |
        max (dist (explicitRWMEndpoint δ x₁ z)
              (explicitRWMEndpoint δ x₂ z)) (dist x₁ x₂) <
          dist (explicitRWMRejectionUniformUpdate V δ x₁ (z, u))
            (explicitRWMRejectionUniformUpdate V δ x₂ (z, u))} ≤
      ENNReal.ofReal
        |explicitRWMAcceptanceReal V δ x₁ z -
          explicitRWMAcceptanceReal V δ x₂ z| := by
  let a₁ := explicitRWMAcceptanceReal V δ x₁ z
  let a₂ := explicitRWMAcceptanceReal V δ x₂ z
  have ha₁0 : 0 ≤ 1 - a₁ := sub_nonneg.mpr
    (explicitRWMAcceptanceReal_le_one V δ x₁ z)
  have ha₁1 : 1 - a₁ ≤ 1 := by
    linarith [explicitRWMAcceptanceReal_nonneg V δ x₁ z]
  have ha₂0 : 0 ≤ 1 - a₂ := sub_nonneg.mpr
    (explicitRWMAcceptanceReal_le_one V δ x₂ z)
  have ha₂1 : 1 - a₂ ≤ 1 := by
    linarith [explicitRWMAcceptanceReal_nonneg V δ x₂ z]
  have h := volume_unitAcceptRejectUpdate_dist_gt_max_le
    (explicitRWMEndpoint δ x₁ z) x₁
    (explicitRWMEndpoint δ x₂ z) x₂
    (1 - a₁) (1 - a₂) ha₁0 ha₁1 ha₂0 ha₂1
  simpa only [unitAcceptRejectUpdate,
    explicitRWMRejectionUniformUpdate, a₁, a₂,
    show |(1 - a₁) - (1 - a₂)| = |a₁ - a₂| by
      rw [show (1 - a₁) - (1 - a₂) = -(a₁ - a₂) by ring,
        abs_neg]] using h

/-- With a common start and Gaussian proposal, Euler minus RWM is exactly
the centered rejected increment. -/
lemma explicitEulerUpdate_sub_explicitRWMRejectionUniformUpdate
    (V : FirstOrderPotential d) (δ : ℝ) (x z : State d)
    (u : Set.Icc (0 : ℝ) 1) :
    explicitEulerUpdate V δ x z -
        explicitRWMRejectionUniformUpdate V δ x (z, u) =
      V.bernoulliRWMRejectedIncrement δ x z u - δ • V.gradU x := by
  rw [explicitRWMRejectionUniformUpdate_eq_endpoint_sub_rejectedIncrement]
  unfold explicitEulerUpdate explicitRWMEndpoint
  abel

/-- Elementary pointwise second-moment majorant for the one-step
Euler--RWM discrepancy. -/
theorem norm_explicitEulerUpdate_sub_explicitRWMRejectionUniformUpdate_sq_le
    (V : FirstOrderPotential d) (δ : ℝ) (x z : State d)
    (u : Set.Icc (0 : ℝ) 1) :
    ‖explicitEulerUpdate V δ x z -
        explicitRWMRejectionUniformUpdate V δ x (z, u)‖ ^ 2 ≤
      2 * ‖V.bernoulliRWMRejectedIncrement δ x z u‖ ^ 2 +
        2 * δ ^ 2 * ‖V.gradU x‖ ^ 2 := by
  rw [explicitEulerUpdate_sub_explicitRWMRejectionUniformUpdate]
  let A := ‖V.bernoulliRWMRejectedIncrement δ x z u‖
  let B := ‖δ • V.gradU x‖
  have hnorm :
      ‖V.bernoulliRWMRejectedIncrement δ x z u - δ • V.gradU x‖ ≤
        A + B := by
    exact norm_sub_le _ _
  have hsq :
      ‖V.bernoulliRWMRejectedIncrement δ x z u - δ • V.gradU x‖ ^ 2 ≤
        (A + B) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 hnorm
  have hB : B ^ 2 = δ ^ 2 * ‖V.gradU x‖ ^ 2 := by
    dsimp [B]
    rw [norm_smul, Real.norm_eq_abs]
    nlinarith [sq_abs δ]
  calc
    ‖V.bernoulliRWMRejectedIncrement δ x z u - δ • V.gradU x‖ ^ 2 ≤
        (A + B) ^ 2 := hsq
    _ ≤ 2 * A ^ 2 + 2 * B ^ 2 := by
      nlinarith [sq_nonneg (A - B)]
    _ = 2 * ‖V.bernoulliRWMRejectedIncrement δ x z u‖ ^ 2 +
        2 * δ ^ 2 * ‖V.gradU x‖ ^ 2 := by
      rw [hB]
      dsimp [A]
      ring

/-- After integrating only the unit-uniform decision, the one-step squared
Euler--RWM discrepancy is controlled by the raw rejection second moment and
the deterministic Euler drift. -/
theorem integral_unitInterval_norm_explicitEuler_sub_rwm_sq_le
    (V : FirstOrderPotential d) (δ : ℝ) (x z : State d) :
    (∫ u : Set.Icc (0 : ℝ) 1,
        ‖explicitEulerUpdate V δ x z -
          explicitRWMRejectionUniformUpdate V δ x (z, u)‖ ^ 2
        ∂volume) ≤
      2 * V.scaledRWMRejectionSecondMomentIntegrand δ x z +
        2 * δ ^ 2 * ‖V.gradU x‖ ^ 2 := by
  let R : Set.Icc (0 : ℝ) 1 → State d := fun u =>
    V.bernoulliRWMRejectedIncrement δ x z u
  let s : State d := Real.sqrt (2 * δ) • z
  have hRmeas : Measurable R := by
    dsimp [R, Concrete.FirstOrderPotential.bernoulliRWMRejectedIncrement]
    exact measurable_thresholdConst _ _
  have hRnorm2 : Integrable (fun u => ‖R u‖ ^ 2) := by
    apply Integrable.of_bound (hRmeas.norm.pow_const 2).aestronglyMeasurable
      (‖s‖ ^ 2)
    exact ae_of_all _ fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      dsimp [R, Concrete.FirstOrderPotential.bernoulliRWMRejectedIncrement]
      change ‖thresholdConst
          (DiscreteTime.rejectionProfile (V.rwmEnergyIncrement x s)) s u‖ ^ 2 ≤
        ‖s‖ ^ 2
      by_cases hu : (u : ℝ) ≤ DiscreteTime.rejectionProfile
          (V.rwmEnergyIncrement x s) <;>
        simp [thresholdConst, hu]
  let f : Set.Icc (0 : ℝ) 1 → ℝ := fun u =>
    ‖explicitEulerUpdate V δ x z -
      explicitRWMRejectionUniformUpdate V δ x (z, u)‖ ^ 2
  let g : Set.Icc (0 : ℝ) 1 → ℝ := fun u =>
    2 * ‖R u‖ ^ 2 + 2 * δ ^ 2 * ‖V.gradU x‖ ^ 2
  have hfmeas : Measurable f := by
    have hRcenter : Measurable (fun u => R u - δ • V.gradU x) :=
      hRmeas.sub measurable_const
    rw [show f = fun u => ‖R u - δ • V.gradU x‖ ^ 2 by
      funext u
      dsimp [f, R]
      rw [explicitEulerUpdate_sub_explicitRWMRejectionUniformUpdate]]
    exact hRcenter.norm.pow_const 2
  have hgint : Integrable g (volume : Measure (Set.Icc (0 : ℝ) 1)) := by
    exact (hRnorm2.const_mul 2).add (integrable_const _)
  have hfint : Integrable f (volume : Measure (Set.Icc (0 : ℝ) 1)) := by
    apply hgint.mono hfmeas.aestronglyMeasurable
    exact ae_of_all _ fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
        Real.norm_eq_abs, abs_of_nonneg]
      · exact norm_explicitEulerUpdate_sub_explicitRWMRejectionUniformUpdate_sq_le
          V δ x z u
      · dsimp [g]
        positivity
  calc
    (∫ u : Set.Icc (0 : ℝ) 1,
        ‖explicitEulerUpdate V δ x z -
          explicitRWMRejectionUniformUpdate V δ x (z, u)‖ ^ 2
        ∂volume) = ∫ u, f u ∂volume := rfl
    _ ≤ ∫ u, g u ∂volume := by
      apply integral_mono hfint hgint
      intro u
      exact norm_explicitEulerUpdate_sub_explicitRWMRejectionUniformUpdate_sq_le
        V δ x z u
    _ = 2 * V.scaledRWMRejectionSecondMomentIntegrand δ x z +
        2 * δ ^ 2 * ‖V.gradU x‖ ^ 2 := by
      dsimp [g]
      rw [integral_add (hRnorm2.const_mul 2) (integrable_const _),
        integral_const_mul, integral_const]
      have hR : (∫ u : Set.Icc (0 : ℝ) 1, ‖R u‖ ^ 2 ∂volume) =
          V.scaledRWMRejectionSecondMomentIntegrand δ x z := by
        dsimp [R, Concrete.FirstOrderPotential.bernoulliRWMRejectedIncrement,
          Concrete.FirstOrderPotential.scaledRWMRejectionSecondMomentIntegrand]
        exact integral_norm_thresholdConst_sq _
          (DiscreteTime.rejectionProfile_nonneg _)
          (DiscreteTime.rejectionProfile_le_one _) _
      rw [hR]
      have hvol : (volume : Measure (Set.Icc (0 : ℝ) 1)).real Set.univ = 1 := by
        rw [MeasureTheory.measureReal_def]
        simp
      rw [hvol]
      ring

lemma integrable_scaledRWMRejectionSecondMomentIntegrand
    (V : FirstOrderPotential d) (δ : ℝ) (x : State d) :
    Integrable (V.scaledRWMRejectionSecondMomentIntegrand δ x)
      (stdGaussian (State d)) := by
  let a : ℝ := Real.sqrt (2 * δ)
  have hmajor : Integrable (fun z : State d => ‖a • z‖ ^ 2)
      (stdGaussian (State d)) := by
    exact ((IsGaussian.memLp_id (stdGaussian (State d)) 2
      (by norm_num)).const_smul a).integrable_norm_pow (by norm_num)
  have hcont : Continuous
      (V.scaledRWMRejectionSecondMomentIntegrand δ x) := by
    change Continuous (fun z : State d =>
      DiscreteTime.rejectionProfile
          (V.U (x + a • z) - V.U x) * ‖a • z‖ ^ 2)
    have hs : Continuous (fun z : State d => a • z) :=
      continuous_id.const_smul a
    have hu : Continuous (fun z : State d => V.U (x + a • z) - V.U x) :=
      (V.continuous_U.comp (continuous_const.add hs)).sub continuous_const
    exact (DiscreteTime.continuous_rejectionProfile.comp hu).mul
      ((continuous_norm.comp hs).pow 2)
  apply hmajor.mono hcont.aestronglyMeasurable
  exact ae_of_all _ fun z => by
    have hnonneg : 0 ≤ V.scaledRWMRejectionSecondMomentIntegrand δ x z := by
      unfold Concrete.FirstOrderPotential.scaledRWMRejectionSecondMomentIntegrand
      exact mul_nonneg (DiscreteTime.rejectionProfile_nonneg _) (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg,
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    unfold Concrete.FirstOrderPotential.scaledRWMRejectionSecondMomentIntegrand
    dsimp [a]
    exact mul_le_of_le_one_left (sq_nonneg _)
      (DiscreteTime.rejectionProfile_le_one _)

/-- Fully iterated coarse one-step bound.  Both random coordinates are now
ordinary finite-dimensional integrals; no conditional expectation is used. -/
theorem iteratedIntegral_norm_explicitEuler_sub_rwm_sq_le
    (V : FirstOrderPotential d) (δ : ℝ) (x : State d) :
    (∫ z : State d,
        (∫ u : Set.Icc (0 : ℝ) 1,
          ‖explicitEulerUpdate V δ x z -
            explicitRWMRejectionUniformUpdate V δ x (z, u)‖ ^ 2
          ∂volume)
      ∂stdGaussian (State d)) ≤
      2 * (∫ z : State d,
        V.scaledRWMRejectionSecondMomentIntegrand δ x z
        ∂stdGaussian (State d)) +
        2 * δ ^ 2 * ‖V.gradU x‖ ^ 2 := by
  let F : State d × Set.Icc (0 : ℝ) 1 → ℝ := fun zu =>
    ‖explicitEulerUpdate V δ x zu.1 -
      explicitRWMRejectionUniformUpdate V δ x zu‖ ^ 2
  let f : State d → ℝ := fun z => ∫ u, F (z, u) ∂volume
  let g : State d → ℝ := fun z =>
    2 * V.scaledRWMRejectionSecondMomentIntegrand δ x z +
      2 * δ ^ 2 * ‖V.gradU x‖ ^ 2
  have hFmeas : Measurable F := by
    have he : Measurable (fun zu : State d × Set.Icc (0 : ℝ) 1 =>
        explicitEulerUpdate V δ x zu.1) :=
      (Measurable.of_uncurry_left
        (measurable_uncurry_explicitEulerUpdate V δ)).comp measurable_fst
    exact (he.sub (measurable_explicitRWMRejectionUniformUpdate V δ x)).norm.pow_const 2
  have hfmeas : Measurable f :=
    hFmeas.stronglyMeasurable.integral_prod_right'.measurable
  have hsecond := integrable_scaledRWMRejectionSecondMomentIntegrand V δ x
  have hgint : Integrable g (stdGaussian (State d)) := by
    change Integrable (fun z : State d =>
      2 * V.scaledRWMRejectionSecondMomentIntegrand δ x z +
        2 * δ ^ 2 * ‖V.gradU x‖ ^ 2) (stdGaussian (State d))
    exact (hsecond.const_mul 2).add
      (integrable_const (μ := stdGaussian (State d))
        (2 * δ ^ 2 * ‖V.gradU x‖ ^ 2))
  have hfint : Integrable f (stdGaussian (State d)) := by
    apply hgint.mono hfmeas.aestronglyMeasurable
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg, Real.norm_eq_abs, abs_of_nonneg]
      · exact integral_unitInterval_norm_explicitEuler_sub_rwm_sq_le V δ x z
      · dsimp [g]
        exact add_nonneg
          (mul_nonneg (by norm_num) (by
            unfold Concrete.FirstOrderPotential.scaledRWMRejectionSecondMomentIntegrand
            exact mul_nonneg (DiscreteTime.rejectionProfile_nonneg _) (sq_nonneg _)))
          (by positivity)
      · dsimp [f]
        exact integral_nonneg fun _ => sq_nonneg _
  calc
    (∫ z : State d,
        (∫ u : Set.Icc (0 : ℝ) 1,
          ‖explicitEulerUpdate V δ x z -
            explicitRWMRejectionUniformUpdate V δ x (z, u)‖ ^ 2
          ∂volume)
      ∂stdGaussian (State d)) = ∫ z, f z ∂stdGaussian (State d) := rfl
    _ ≤ ∫ z, g z ∂stdGaussian (State d) := by
      apply integral_mono (μ := stdGaussian (State d)) hfint hgint
      intro z
      exact integral_unitInterval_norm_explicitEuler_sub_rwm_sq_le V δ x z
    _ = 2 * (∫ z : State d,
        V.scaledRWMRejectionSecondMomentIntegrand δ x z
        ∂stdGaussian (State d)) +
        2 * δ ^ 2 * ‖V.gradU x‖ ^ 2 := by
      dsimp [g]
      rw [integral_add (hsecond.const_mul 2) (integrable_const _),
        integral_const_mul, integral_const]
      have hgauss : (stdGaussian (State d)).real Set.univ = 1 := by
        rw [MeasureTheory.measureReal_def]
        simp
      rw [hgauss]
      ring

/-- Explicit Gaussian-moment version of the same-start one-step `L²`
Euler--RWM coupling bound. -/
theorem iteratedIntegral_norm_explicitEuler_sub_rwm_sq_explicit_le
    (V : FirstOrderPotential d) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (x : State d) :
    (∫ z : State d,
        (∫ u : Set.Icc (0 : ℝ) 1,
          ‖explicitEulerUpdate V δ x z -
            explicitRWMRejectionUniformUpdate V δ x (z, u)‖ ^ 2
          ∂volume)
      ∂stdGaussian (State d)) ≤
      2 * (Real.sqrt (2 * δ)) ^ 3 *
        (‖V.gradU x‖ *
            (∫ z : State d, ‖z‖ ^ 3 ∂stdGaussian (State d)) +
          (2 * (V.L / 2) + 4 * ‖V.gradU x‖ ^ 2) *
            (∫ z : State d, ‖z‖ ^ 4 ∂stdGaussian (State d)) +
          16 * (V.L / 2) ^ 2 *
            (∫ z : State d, ‖z‖ ^ 6 ∂stdGaussian (State d))) +
        2 * δ ^ 2 * ‖V.gradU x‖ ^ 2 := by
  have hcoarse := iteratedIntegral_norm_explicitEuler_sub_rwm_sq_le V δ x
  have hsecond :=
    V.integral_scaledRWMRejectionSecondMomentIntegrand_le δ hδ hδ1 x
  calc
    (∫ z : State d,
        (∫ u : Set.Icc (0 : ℝ) 1,
          ‖explicitEulerUpdate V δ x z -
            explicitRWMRejectionUniformUpdate V δ x (z, u)‖ ^ 2
          ∂volume)
      ∂stdGaussian (State d)) ≤
        2 * (∫ z : State d,
          V.scaledRWMRejectionSecondMomentIntegrand δ x z
          ∂stdGaussian (State d)) +
          2 * δ ^ 2 * ‖V.gradU x‖ ^ 2 := hcoarse
    _ ≤ 2 * ((Real.sqrt (2 * δ)) ^ 3 *
        (‖V.gradU x‖ *
            (∫ z : State d, ‖z‖ ^ 3 ∂stdGaussian (State d)) +
          (2 * (V.L / 2) + 4 * ‖V.gradU x‖ ^ 2) *
            (∫ z : State d, ‖z‖ ^ 4 ∂stdGaussian (State d)) +
          16 * (V.L / 2) ^ 2 *
            (∫ z : State d, ‖z‖ ^ 6 ∂stdGaussian (State d)))) +
          2 * δ ^ 2 * ‖V.gradU x‖ ^ 2 := by
      have hm := mul_le_mul_of_nonneg_left hsecond (show (0 : ℝ) ≤ 2 by norm_num)
      simpa only [add_comm] using
        add_le_add_right hm (2 * δ ^ 2 * ‖V.gradU x‖ ^ 2)
    _ = 2 * (Real.sqrt (2 * δ)) ^ 3 *
        (‖V.gradU x‖ *
            (∫ z : State d, ‖z‖ ^ 3 ∂stdGaussian (State d)) +
          (2 * (V.L / 2) + 4 * ‖V.gradU x‖ ^ 2) *
            (∫ z : State d, ‖z‖ ^ 4 ∂stdGaussian (State d)) +
          16 * (V.L / 2) ^ 2 *
            (∫ z : State d, ‖z‖ ^ 6 ∂stdGaussian (State d))) +
          2 * δ ^ 2 * ‖V.gradU x‖ ^ 2 := by ring

/-! ## Stationary same-start coupling bound -/

/-- The `p`-th norm moment of the standard Gaussian innovation.  Keeping
this as a named finite-dimensional integral avoids importing closed formulas
for Gaussian moments into the discrete coupling argument. -/
def gaussianNormMoment (d p : ℕ) : ℝ :=
  ∫ z : State d, ‖z‖ ^ p ∂stdGaussian (State d)

/-- The `p`-th norm moment of the target gradient. -/
def targetGradNormMoment (V : FirstOrderPotential d) (p : ℕ) : ℝ :=
  ∫ x : State d, ‖V.gradU x‖ ^ p ∂(V.target : Measure (State d))

/-- Integrability of the squared gradient norm under the target, obtained
elementarily from the fourth-moment estimate. -/
lemma integrable_target_gradU_norm_sq (V : FirstOrderPotential d) :
    Integrable (fun x : State d => ‖V.gradU x‖ ^ 2)
      (V.target : Measure (State d)) := by
  have hmajor : Integrable (fun x : State d =>
      1 + ‖V.gradU x‖ ^ 4) (V.target : Measure (State d)) :=
    (integrable_const (1 : ℝ)).add V.integrable_gradU_norm_fourth
  apply hmajor.mono
  · exact (V.continuous_gradU.norm.pow 2).aestronglyMeasurable
  · exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _),
        Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      let t : ℝ := ‖V.gradU x‖
      have ht : 0 ≤ t := by dsimp [t]; positivity
      have hs : 0 ≤ (t ^ 2 - (1 / 2 : ℝ)) ^ 2 := sq_nonneg _
      dsimp [t] at ht hs ⊢
      nlinarith

/-- Integrability of the gradient norm under the target, obtained from its
square by the elementary bound `t ≤ 1 + t²`. -/
lemma integrable_target_gradU_norm (V : FirstOrderPotential d) :
    Integrable (fun x : State d => ‖V.gradU x‖)
      (V.target : Measure (State d)) := by
  have h2 := integrable_target_gradU_norm_sq V
  have hmajor : Integrable (fun x : State d =>
      1 + ‖V.gradU x‖ ^ 2) (V.target : Measure (State d)) :=
    (integrable_const (1 : ℝ)).add h2
  apply hmajor.mono
  · exact V.continuous_gradU.norm.aestronglyMeasurable
  · exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
        Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hs : 0 ≤ (‖V.gradU x‖ - (1 / 2 : ℝ)) ^ 2 := sq_nonneg _
      nlinarith

/-- The coefficient of `(sqrt (2δ))³` in the same-start coupling estimate,
before averaging the common starting point over the target. -/
def pointwiseEulerRWMCouplingConstant
    (V : FirstOrderPotential d) (x : State d) : ℝ :=
  2 * (gaussianNormMoment d 3 * ‖V.gradU x‖ +
    V.L * gaussianNormMoment d 4 +
    4 * gaussianNormMoment d 4 * ‖V.gradU x‖ ^ 2 +
    4 * V.L ^ 2 * gaussianNormMoment d 6)

/-- The explicit stationary coefficient in the same-start Euler/RWM
coupling bound. -/
def stationaryEulerRWMCouplingConstant (V : FirstOrderPotential d) : ℝ :=
  2 * (gaussianNormMoment d 3 * targetGradNormMoment V 1 +
    V.L * gaussianNormMoment d 4 +
    4 * gaussianNormMoment d 4 * targetGradNormMoment V 2 +
    4 * V.L ^ 2 * gaussianNormMoment d 6)

/-- The explicit one-step estimate in a form whose target average is a
direct integral calculation. -/
theorem iteratedIntegral_norm_explicitEuler_sub_rwm_sq_pointwise_le
    (V : FirstOrderPotential d) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (x : State d) :
    (∫ z : State d,
        (∫ u : Set.Icc (0 : ℝ) 1,
          ‖explicitEulerUpdate V δ x z -
            explicitRWMRejectionUniformUpdate V δ x (z, u)‖ ^ 2
          ∂volume)
      ∂stdGaussian (State d)) ≤
      (Real.sqrt (2 * δ)) ^ 3 * pointwiseEulerRWMCouplingConstant V x +
        2 * δ ^ 2 * ‖V.gradU x‖ ^ 2 := by
  have h := iteratedIntegral_norm_explicitEuler_sub_rwm_sq_explicit_le
    V δ hδ hδ1 x
  dsimp [pointwiseEulerRWMCouplingConstant, gaussianNormMoment]
  convert h using 1
  ring

lemma integrable_pointwiseEulerRWMCouplingConstant
    (V : FirstOrderPotential d) :
    Integrable (pointwiseEulerRWMCouplingConstant V)
      (V.target : Measure (State d)) := by
  have h1 := integrable_target_gradU_norm V
  have h2 := integrable_target_gradU_norm_sq V
  exact ((((h1.const_mul (gaussianNormMoment d 3)).add
      (integrable_const
        (V.L * gaussianNormMoment d 4))).add
      (h2.const_mul (4 * gaussianNormMoment d 4))).add
      (integrable_const
        (4 * V.L ^ 2 * gaussianNormMoment d 6))).const_mul 2

/-- Averaging the pointwise coefficient over the target gives exactly the
named stationary coefficient. -/
lemma integral_pointwiseEulerRWMCouplingConstant
    (V : FirstOrderPotential d) :
    (∫ x : State d, pointwiseEulerRWMCouplingConstant V x
      ∂(V.target : Measure (State d))) =
      stationaryEulerRWMCouplingConstant V := by
  let M3 := gaussianNormMoment d 3
  let M4 := gaussianNormMoment d 4
  let M6 := gaussianNormMoment d 6
  have h1 := integrable_target_gradU_norm V
  have h2 := integrable_target_gradU_norm_sq V
  have hA : Integrable (fun x : State d => M3 * ‖V.gradU x‖)
      (V.target : Measure (State d)) := h1.const_mul M3
  have hB : Integrable (fun _x : State d => V.L * M4)
      (V.target : Measure (State d)) := integrable_const _
  have hC : Integrable (fun x : State d => 4 * M4 * ‖V.gradU x‖ ^ 2)
      (V.target : Measure (State d)) := h2.const_mul (4 * M4)
  have hD : Integrable (fun _x : State d => 4 * V.L ^ 2 * M6)
      (V.target : Measure (State d)) := integrable_const _
  have htarget : (V.target : Measure (State d)).real Set.univ = 1 := by
    rw [MeasureTheory.measureReal_def]
    simp
  simp only [pointwiseEulerRWMCouplingConstant,
    stationaryEulerRWMCouplingConstant, targetGradNormMoment]
  change (∫ x : State d,
      2 * (M3 * ‖V.gradU x‖ + V.L * M4 +
        4 * M4 * ‖V.gradU x‖ ^ 2 + 4 * V.L ^ 2 * M6)
        ∂(V.target : Measure (State d))) = _
  rw [integral_const_mul]
  have hsplit :
      (∫ x : State d,
        M3 * ‖V.gradU x‖ + V.L * M4 +
          4 * M4 * ‖V.gradU x‖ ^ 2 + 4 * V.L ^ 2 * M6
        ∂(V.target : Measure (State d))) =
        (∫ x : State d, M3 * ‖V.gradU x‖ ∂(V.target : Measure (State d))) +
        (∫ _x : State d, V.L * M4 ∂(V.target : Measure (State d))) +
        (∫ x : State d, 4 * M4 * ‖V.gradU x‖ ^ 2
          ∂(V.target : Measure (State d))) +
        (∫ _x : State d, 4 * V.L ^ 2 * M6
          ∂(V.target : Measure (State d))) := by
    calc
      _ = (∫ x : State d,
          M3 * ‖V.gradU x‖ + V.L * M4 + 4 * M4 * ‖V.gradU x‖ ^ 2
          ∂(V.target : Measure (State d))) +
          ∫ _x : State d, 4 * V.L ^ 2 * M6
            ∂(V.target : Measure (State d)) :=
        integral_add ((hA.add hB).add hC) hD
      _ = ((∫ x : State d, M3 * ‖V.gradU x‖ + V.L * M4
            ∂(V.target : Measure (State d))) +
          ∫ x : State d, 4 * M4 * ‖V.gradU x‖ ^ 2
            ∂(V.target : Measure (State d))) +
          ∫ _x : State d, 4 * V.L ^ 2 * M6
            ∂(V.target : Measure (State d)) := by
        exact congrArg
          (fun t : ℝ => t +
            ∫ _x : State d, 4 * V.L ^ 2 * M6
              ∂(V.target : Measure (State d)))
          (integral_add (hA.add hB) hC)
      _ = _ := by
        exact congrArg
          (fun t : ℝ => t +
              (∫ x : State d, 4 * M4 * ‖V.gradU x‖ ^ 2
                ∂(V.target : Measure (State d))) +
              ∫ _x : State d, 4 * V.L ^ 2 * M6
                ∂(V.target : Measure (State d)))
          (integral_add hA hB)
  rw [hsplit, integral_const_mul, integral_const,
    integral_const_mul, integral_const]
  rw [htarget]
  dsimp [M3, M4, M6]
  simp only [pow_one]
  ring

/-- The completely elementary target×Gaussian×uniform same-start bound.
It contains only iterated finite-dimensional integrals and explicit moments;
in particular it uses neither conditional expectation nor a path-space
construction. -/
theorem target_iteratedIntegral_norm_explicitEuler_sub_rwm_sq_le
    (V : FirstOrderPotential d) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (∫ x : State d,
      (∫ z : State d,
        (∫ u : Set.Icc (0 : ℝ) 1,
          ‖explicitEulerUpdate V δ x z -
            explicitRWMRejectionUniformUpdate V δ x (z, u)‖ ^ 2
          ∂volume)
        ∂stdGaussian (State d))
      ∂(V.target : Measure (State d))) ≤
      (Real.sqrt (2 * δ)) ^ 3 * stationaryEulerRWMCouplingConstant V +
        2 * δ ^ 2 * targetGradNormMoment V 2 := by
  let H : (State d × State d) × Set.Icc (0 : ℝ) 1 → ℝ := fun p =>
    ‖explicitEulerUpdate V δ p.1.1 p.1.2 -
      explicitRWMRejectionUniformUpdate V δ p.1.1 (p.1.2, p.2)‖ ^ 2
  let f : State d → ℝ := fun x =>
    ∫ z : State d, ∫ u : Set.Icc (0 : ℝ) 1, H ((x, z), u) ∂volume
      ∂stdGaussian (State d)
  let g : State d → ℝ := fun x =>
    (Real.sqrt (2 * δ)) ^ 3 * pointwiseEulerRWMCouplingConstant V x +
      2 * δ ^ 2 * ‖V.gradU x‖ ^ 2
  have hHmeas : Measurable H := by
    let ez : (State d × State d) × Set.Icc (0 : ℝ) 1 →
        State d × State d := fun p => (p.1.1, p.1.2)
    let xzu : (State d × State d) × Set.Icc (0 : ℝ) 1 →
        State d × (State d × Set.Icc (0 : ℝ) 1) :=
      fun p => (p.1.1, (p.1.2, p.2))
    have hez : Measurable ez :=
      (measurable_fst.comp measurable_fst).prodMk
        (measurable_snd.comp measurable_fst)
    have hxzu : Measurable xzu :=
      (measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    exact ((measurable_uncurry_explicitEulerUpdate V δ).comp hez |>.sub
      ((measurable_uncurry_explicitRWMRejectionUniformUpdate V δ).comp hxzu)).norm.pow_const 2
  have hfmeas : Measurable f := by
    have hinner : Measurable (fun xz : State d × State d =>
        ∫ u : Set.Icc (0 : ℝ) 1, H (xz, u) ∂volume) :=
      hHmeas.stronglyMeasurable.integral_prod_right'.measurable
    exact hinner.stronglyMeasurable.integral_prod_right'.measurable
  have hgint : Integrable g (V.target : Measure (State d)) := by
    exact (integrable_pointwiseEulerRWMCouplingConstant V |>.const_mul
      ((Real.sqrt (2 * δ)) ^ 3)).add
      (integrable_target_gradU_norm_sq V |>.const_mul (2 * δ ^ 2))
  have hfint : Integrable f (V.target : Measure (State d)) := by
    apply hgint.mono hfmeas.aestronglyMeasurable
    exact ae_of_all _ fun x => by
      have hle := iteratedIntegral_norm_explicitEuler_sub_rwm_sq_pointwise_le
        V δ hδ hδ1 x
      have hf0 : 0 ≤ f x := by
        dsimp [f, H]
        exact integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
      have hg0 : 0 ≤ g x := by
        exact hf0.trans (by simpa only [f, g, H] using hle)
      rw [Real.norm_eq_abs, abs_of_nonneg hf0,
        Real.norm_eq_abs, abs_of_nonneg hg0]
      simpa only [f, g, H] using hle
  calc
    (∫ x : State d,
      (∫ z : State d,
        (∫ u : Set.Icc (0 : ℝ) 1,
          ‖explicitEulerUpdate V δ x z -
            explicitRWMRejectionUniformUpdate V δ x (z, u)‖ ^ 2
          ∂volume)
        ∂stdGaussian (State d))
      ∂(V.target : Measure (State d))) =
        ∫ x, f x ∂(V.target : Measure (State d)) := rfl
    _ ≤ ∫ x, g x ∂(V.target : Measure (State d)) := by
      apply integral_mono hfint hgint
      intro x
      exact iteratedIntegral_norm_explicitEuler_sub_rwm_sq_pointwise_le
        V δ hδ hδ1 x
    _ = (Real.sqrt (2 * δ)) ^ 3 * stationaryEulerRWMCouplingConstant V +
        2 * δ ^ 2 * targetGradNormMoment V 2 := by
      dsimp [g]
      rw [integral_add
        (integrable_pointwiseEulerRWMCouplingConstant V |>.const_mul
          ((Real.sqrt (2 * δ)) ^ 3))
        (integrable_target_gradU_norm_sq V |>.const_mul (2 * δ ^ 2)),
        integral_const_mul, integral_const_mul,
        integral_pointwiseEulerRWMCouplingConstant]
      rfl

lemma lintegral_unitInterval_explicitRWMUniformUpdate
    (V : FirstOrderPotential d) (δ : ℝ) (x z : State d)
    {g : State d → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ u : Set.Icc (0 : ℝ) 1,
        g (explicitRWMUniformUpdate V δ x (z, u)) ∂volume) =
      explicitRWMAcceptance V δ x z *
          g (explicitRWMEndpoint δ x z) +
        (1 - explicitRWMAcceptance V δ x z) * g x := by
  unfold explicitRWMUniformUpdate
  change (∫⁻ u : Set.Icc (0 : ℝ) 1,
      g (if (u : ℝ) ≤ explicitRWMAcceptanceReal V δ x z then
        explicitRWMEndpoint δ x z else x) ∂volume) = _
  rw [explicitRWMAcceptanceReal_eq_toReal]
  exact lintegral_unitInterval_acceptReject g hg x
    (explicitRWMEndpoint δ x z) (explicitRWMAcceptance V δ x z)
    (explicitRWMAcceptance_le_one V δ x z)

/-- The acceptance mass of the explicit proposal is the Gaussian integral
of the innovation-wise acceptance threshold. -/
lemma explicitRWMAcceptanceMass_eq_lintegral
    (V : FirstOrderPotential d) (δ : ℝ) (x : State d) :
    MetropolisHastings.acceptanceMass (explicitRWMProposal δ)
        (explicitRWMAcceptanceAt V) x =
      ∫⁻ z, explicitRWMAcceptance V δ x z
        ∂stdGaussian (State d) := by
  unfold MetropolisHastings.acceptanceMass
  exact lintegral_explicitRWMProposal δ x
    (Measurable.of_uncurry_left
      (measurable_uncurry_explicitRWMAcceptanceAt V))

lemma lintegral_one_sub_explicitRWMAcceptance
    (V : FirstOrderPotential d) (δ : ℝ) (x : State d) :
    (∫⁻ z, 1 - explicitRWMAcceptance V δ x z
        ∂stdGaussian (State d)) =
      1 - ∫⁻ z, explicitRWMAcceptance V δ x z
        ∂stdGaussian (State d) := by
  have ha : Measurable (explicitRWMAcceptance V δ x) :=
    Measurable.of_uncurry_left (measurable_uncurry_explicitRWMAcceptance V δ)
  have hfin : (∫⁻ z, explicitRWMAcceptance V δ x z
      ∂stdGaussian (State d)) ≠ ∞ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    calc
      (∫⁻ z, explicitRWMAcceptance V δ x z
          ∂stdGaussian (State d)) ≤
          ∫⁻ _z : State d, (1 : ℝ≥0∞)
            ∂stdGaussian (State d) :=
        lintegral_mono (explicitRWMAcceptance_le_one V δ x)
      _ = 1 := by simp
  rw [lintegral_sub ha hfin
    (ae_of_all _ (explicitRWMAcceptance_le_one V δ x))]
  simp

/-- Setwise formula for the explicit RWM kernel in Gaussian--uniform
coordinates. -/
theorem explicitRWMKernel_apply_eq_gaussianUniform
    (V : FirstOrderPotential d) (δ : ℝ) (x : State d)
    (B : Set (State d)) (hB : MeasurableSet B) :
    explicitRWMKernel V δ x B =
      ∫⁻ z : State d,
        explicitRWMAcceptance V δ x z *
            B.indicator (fun _ => (1 : ℝ≥0∞))
              (explicitRWMEndpoint δ x z) +
          (1 - explicitRWMAcceptance V δ x z) *
            B.indicator (fun _ => (1 : ℝ≥0∞)) x
        ∂stdGaussian (State d) := by
  let a : State d → ℝ≥0∞ := explicitRWMAcceptance V δ x
  let p : State d → ℝ≥0∞ := fun z =>
    B.indicator (fun _ => (1 : ℝ≥0∞)) (explicitRWMEndpoint δ x z)
  let c : ℝ≥0∞ := B.indicator (fun _ => (1 : ℝ≥0∞)) x
  have ha : Measurable a :=
    Measurable.of_uncurry_left (measurable_uncurry_explicitRWMAcceptance V δ)
  have hp : Measurable p := by
    exact (measurable_const.indicator hB).comp
      (Measurable.of_uncurry_left
        (measurable_uncurry_explicitRWMEndpoint δ))
  have hac : Measurable (fun z => (1 - a z) * c) :=
    (measurable_const.sub ha).mul measurable_const
  have haccepted :
      explicitRWMAcceptedKernel V δ x B =
        ∫⁻ z, a z * p z ∂stdGaussian (State d) := by
    rw [explicitRWMAcceptedKernel_apply V δ x hB]
    apply lintegral_congr
    intro z
    by_cases hz : explicitRWMEndpoint δ x z ∈ B <;>
      simp [a, p, hz, explicitRWMAcceptanceAt_endpoint]
  have hreject :
      MetropolisHastings.rejected (explicitRWMProposal δ)
          (explicitRWMAcceptanceAt V) x B =
        (1 - ∫⁻ z, a z ∂stdGaussian (State d)) * c := by
    rw [MetropolisHastings.rejected_apply
      (explicitRWMProposal δ) (explicitRWMAcceptanceAt V)
      (measurable_uncurry_explicitRWMAcceptanceAt V) x B hB]
    rw [explicitRWMAcceptanceMass_eq_lintegral V δ x]
    by_cases hx : x ∈ B <;> simp [a, c, hx]
  rw [explicitRWMKernel, MetropolisHastings.kernel,
    add_apply, Measure.add_apply,
    show MetropolisHastings.accepted (explicitRWMProposal δ)
        (explicitRWMAcceptanceAt V) = explicitRWMAcceptedKernel V δ by rfl,
    haccepted, hreject]
  change (∫⁻ z, a z * p z ∂stdGaussian (State d)) +
      (1 - ∫⁻ z, a z ∂stdGaussian (State d)) * c =
    ∫⁻ z, a z * p z + (1 - a z) * c
      ∂stdGaussian (State d)
  symm
  calc
    (∫⁻ z, a z * p z + (1 - a z) * c
        ∂stdGaussian (State d)) =
        (∫⁻ z, a z * p z ∂stdGaussian (State d)) +
          ∫⁻ z, (1 - a z) * c ∂stdGaussian (State d) :=
      lintegral_add_left (ha.mul hp) (fun z => (1 - a z) * c)
    _ = (∫⁻ z, a z * p z ∂stdGaussian (State d)) +
        (1 - ∫⁻ z, a z ∂stdGaussian (State d)) * c := by
      have hmul : (∫⁻ z, (1 - a z) * c
          ∂stdGaussian (State d)) =
          (∫⁻ z, 1 - a z ∂stdGaussian (State d)) * c :=
        lintegral_mul_const c (measurable_const.sub ha)
      rw [hmul]
      have hsub : (∫⁻ z, 1 - a z ∂stdGaussian (State d)) =
          1 - ∫⁻ z, a z ∂stdGaussian (State d) := by
        exact lintegral_one_sub_explicitRWMAcceptance V δ x
      rw [hsub]

/-- The RWM update map pushes Gaussian--uniform noise exactly to the explicit
RWM transition measure. -/
theorem map_explicitRWMUniformUpdate_gaussianUniformNoise
    (V : FirstOrderPotential d) (δ : ℝ) (x : State d) :
    Measure.map (explicitRWMUniformUpdate V δ x)
        (gaussianUniformNoise d) =
      explicitRWMKernel V δ x := by
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply (measurable_explicitRWMUniformUpdate V δ x) hB]
  have hpre : MeasurableSet
      (explicitRWMUniformUpdate V δ x ⁻¹' B) :=
    hB.preimage (measurable_explicitRWMUniformUpdate V δ x)
  calc
    gaussianUniformNoise d (explicitRWMUniformUpdate V δ x ⁻¹' B) =
        ∫⁻ zu : State d × Set.Icc (0 : ℝ) 1,
          B.indicator (fun _ => (1 : ℝ≥0∞))
            (explicitRWMUniformUpdate V δ x zu)
          ∂gaussianUniformNoise d := by
      have hind : (fun zu : State d × Set.Icc (0 : ℝ) 1 =>
          B.indicator (fun _ => (1 : ℝ≥0∞))
            (explicitRWMUniformUpdate V δ x zu)) =
          (explicitRWMUniformUpdate V δ x ⁻¹' B).indicator
            (fun _ => (1 : ℝ≥0∞)) := by
        funext zu
        by_cases hzu : explicitRWMUniformUpdate V δ x zu ∈ B <;>
          simp [hzu]
      rw [hind, lintegral_indicator hpre]
      simp
    _ = explicitRWMKernel V δ x B := by
      rw [gaussianUniformNoise]
      calc
        (∫⁻ zu : State d × Set.Icc (0 : ℝ) 1,
            B.indicator (fun _ => (1 : ℝ≥0∞))
              (explicitRWMUniformUpdate V δ x zu)
            ∂(stdGaussian (State d)).prod volume) =
            ∫⁻ z : State d, ∫⁻ u : Set.Icc (0 : ℝ) 1,
              B.indicator (fun _ => (1 : ℝ≥0∞))
                (explicitRWMUniformUpdate V δ x (z, u))
              ∂volume ∂stdGaussian (State d) :=
          lintegral_prod _
            ((measurable_const.indicator hB).comp
              (measurable_explicitRWMUniformUpdate V δ x)).aemeasurable
        _ = ∫⁻ z : State d,
              explicitRWMAcceptance V δ x z *
                  B.indicator (fun _ => (1 : ℝ≥0∞))
                    (explicitRWMEndpoint δ x z) +
                (1 - explicitRWMAcceptance V δ x z) *
                  B.indicator (fun _ => (1 : ℝ≥0∞)) x
              ∂stdGaussian (State d) := by
          apply lintegral_congr
          intro z
          exact lintegral_unitInterval_explicitRWMUniformUpdate
            (V := V) (δ := δ) (x := x) z
            (measurable_const.indicator hB)
        _ = explicitRWMKernel V δ x B :=
          (explicitRWMKernel_apply_eq_gaussianUniform V δ x B hB).symm

lemma ofReal_explicitRWMAcceptanceReal
    (V : FirstOrderPotential d) (δ : ℝ) (x z : State d) :
    ENNReal.ofReal (explicitRWMAcceptanceReal V δ x z) =
      explicitRWMAcceptance V δ x z := by
  rw [explicitRWMAcceptanceReal_eq_toReal,
    ENNReal.ofReal_toReal]
  exact ne_top_of_le_ne_top ENNReal.one_ne_top
    (explicitRWMAcceptance_le_one V δ x z)

lemma ofReal_rejectionProfile_eq_one_sub_explicitRWMAcceptance
    (V : FirstOrderPotential d) (δ : ℝ) (x z : State d) :
    ENNReal.ofReal (DiscreteTime.rejectionProfile
        (V.rwmEnergyIncrement x (Real.sqrt (2 * δ) • z))) =
      1 - explicitRWMAcceptance V δ x z := by
  rw [← one_sub_explicitRWMAcceptanceReal_eq_rejectionProfile,
    ENNReal.ofReal_sub 1 (explicitRWMAcceptanceReal_nonneg V δ x z),
    ENNReal.ofReal_one, ofReal_explicitRWMAcceptanceReal]

lemma lintegral_unitInterval_explicitRWMRejectionUniformUpdate
    (V : FirstOrderPotential d) (δ : ℝ) (x z : State d)
    {g : State d → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ u : Set.Icc (0 : ℝ) 1,
        g (explicitRWMRejectionUniformUpdate V δ x (z, u)) ∂volume) =
      explicitRWMAcceptance V δ x z *
          g (explicitRWMEndpoint δ x z) +
        (1 - explicitRWMAcceptance V δ x z) * g x := by
  let r : ℝ := DiscreteTime.rejectionProfile
    (V.rwmEnergyIncrement x (Real.sqrt (2 * δ) • z))
  have hr0 : 0 ≤ r := DiscreteTime.rejectionProfile_nonneg _
  have hr1 : r ≤ 1 := DiscreteTime.rejectionProfile_le_one _
  have hmix := lintegral_unitInterval_acceptReject g hg
    (explicitRWMEndpoint δ x z) x (ENNReal.ofReal r)
    (ENNReal.ofReal_le_one.2 hr1)
  unfold explicitRWMRejectionUniformUpdate
  change (∫⁻ u : Set.Icc (0 : ℝ) 1,
      g (if (u : ℝ) ≤ 1 - explicitRWMAcceptanceReal V δ x z then
          x else explicitRWMEndpoint δ x z)
        ∂volume) = _
  rw [one_sub_explicitRWMAcceptanceReal_eq_rejectionProfile]
  change (∫⁻ u : Set.Icc (0 : ℝ) 1,
      g (if (u : ℝ) ≤ r then x else explicitRWMEndpoint δ x z)
        ∂volume) = _
  rw [show r = (ENNReal.ofReal r).toReal by
    symm
    exact ENNReal.toReal_ofReal hr0]
  rw [hmix]
  have hrej : ENNReal.ofReal r =
      1 - explicitRWMAcceptance V δ x z := by
    exact ofReal_rejectionProfile_eq_one_sub_explicitRWMAcceptance V δ x z
  rw [hrej,
    ENNReal.sub_sub_cancel ENNReal.one_ne_top
      (explicitRWMAcceptance_le_one V δ x z)]
  ac_rfl

/-- The rejection-form update has the same exact explicit RWM law. -/
theorem map_explicitRWMRejectionUniformUpdate_gaussianUniformNoise
    (V : FirstOrderPotential d) (δ : ℝ) (x : State d) :
    Measure.map (explicitRWMRejectionUniformUpdate V δ x)
        (gaussianUniformNoise d) =
      explicitRWMKernel V δ x := by
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply
    (measurable_explicitRWMRejectionUniformUpdate V δ x) hB]
  have hpre : MeasurableSet
      (explicitRWMRejectionUniformUpdate V δ x ⁻¹' B) :=
    hB.preimage (measurable_explicitRWMRejectionUniformUpdate V δ x)
  calc
    gaussianUniformNoise d
        (explicitRWMRejectionUniformUpdate V δ x ⁻¹' B) =
        ∫⁻ zu : State d × Set.Icc (0 : ℝ) 1,
          B.indicator (fun _ => (1 : ℝ≥0∞))
            (explicitRWMRejectionUniformUpdate V δ x zu)
          ∂gaussianUniformNoise d := by
      have hind : (fun zu : State d × Set.Icc (0 : ℝ) 1 =>
          B.indicator (fun _ => (1 : ℝ≥0∞))
            (explicitRWMRejectionUniformUpdate V δ x zu)) =
          (explicitRWMRejectionUniformUpdate V δ x ⁻¹' B).indicator
            (fun _ => (1 : ℝ≥0∞)) := by
        funext zu
        by_cases hzu : explicitRWMRejectionUniformUpdate V δ x zu ∈ B <;>
          simp [hzu]
      rw [hind, lintegral_indicator hpre]
      simp
    _ = explicitRWMKernel V δ x B := by
      rw [gaussianUniformNoise]
      calc
        (∫⁻ zu : State d × Set.Icc (0 : ℝ) 1,
            B.indicator (fun _ => (1 : ℝ≥0∞))
              (explicitRWMRejectionUniformUpdate V δ x zu)
            ∂(stdGaussian (State d)).prod volume) =
            ∫⁻ z : State d, ∫⁻ u : Set.Icc (0 : ℝ) 1,
              B.indicator (fun _ => (1 : ℝ≥0∞))
                (explicitRWMRejectionUniformUpdate V δ x (z, u))
              ∂volume ∂stdGaussian (State d) :=
          lintegral_prod _
            ((measurable_const.indicator hB).comp
              (measurable_explicitRWMRejectionUniformUpdate V δ x)).aemeasurable
        _ = ∫⁻ z : State d,
              explicitRWMAcceptance V δ x z *
                  B.indicator (fun _ => (1 : ℝ≥0∞))
                    (explicitRWMEndpoint δ x z) +
                (1 - explicitRWMAcceptance V δ x z) *
                  B.indicator (fun _ => (1 : ℝ≥0∞)) x
              ∂stdGaussian (State d) := by
          apply lintegral_congr
          intro z
          exact lintegral_unitInterval_explicitRWMRejectionUniformUpdate
            (V := V) (δ := δ) (x := x) z
            (measurable_const.indicator hB)
        _ = explicitRWMKernel V δ x B :=
          (explicitRWMKernel_apply_eq_gaussianUniform V δ x B hB).symm

/-! ## Pair transition and finite iteration -/

/-- One-step law of the coupled pair from a deterministic initial pair. -/
def eulerRWMPairLaw
    (V : FirstOrderPotential d) (δ : ℝ) (xy : State d × State d) :
    Measure (State d × State d) :=
  Measure.map (eulerRWMPairUpdate V δ xy) (gaussianUniformNoise d)

instance eulerRWMPairLaw_isProbabilityMeasure
    (V : FirstOrderPotential d) (δ : ℝ) (xy : State d × State d) :
    IsProbabilityMeasure (eulerRWMPairLaw V δ xy) := by
  constructor
  rw [eulerRWMPairLaw,
    Measure.map_apply (measurable_eulerRWMPairUpdate V δ xy)
      MeasurableSet.univ]
  simp

/-- The second marginal of the coupled one-step law is exactly one explicit
RWM transition. -/
theorem map_snd_eulerRWMPairLaw
    (V : FirstOrderPotential d) (δ : ℝ) (xy : State d × State d) :
    Measure.map Prod.snd (eulerRWMPairLaw V δ xy) =
      explicitRWMKernel V δ xy.2 := by
  rw [eulerRWMPairLaw,
    Measure.map_map measurable_snd (measurable_eulerRWMPairUpdate V δ xy)]
  change Measure.map (explicitRWMRejectionUniformUpdate V δ xy.2)
      (gaussianUniformNoise d) = explicitRWMKernel V δ xy.2
  exact map_explicitRWMRejectionUniformUpdate_gaussianUniformNoise V δ xy.2

/-- Markov kernel of the coupled Euler/RWM pair. -/
def eulerRWMPairKernel
    (V : FirstOrderPotential d) (δ : ℝ) :
    Kernel (State d × State d) (State d × State d) :=
  Kernel.map
    (Kernel.id ×ₖ Kernel.const (State d × State d)
      (gaussianUniformNoise d))
    (Function.uncurry (eulerRWMPairUpdate V δ))

instance eulerRWMPairKernel_isMarkovKernel
    (V : FirstOrderPotential d) (δ : ℝ) :
    IsMarkovKernel (eulerRWMPairKernel V δ) := by
  unfold eulerRWMPairKernel
  exact Kernel.IsMarkovKernel.map _
    (measurable_uncurry_eulerRWMPairUpdate V δ)

theorem lintegral_eulerRWMPairKernel
    (V : FirstOrderPotential d) (δ : ℝ) (xy : State d × State d)
    {g : State d × State d → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ xy', g xy' ∂eulerRWMPairKernel V δ xy) =
      ∫⁻ zu, g (eulerRWMPairUpdate V δ xy zu)
        ∂gaussianUniformNoise d := by
  rw [eulerRWMPairKernel,
    Kernel.lintegral_map _ (measurable_uncurry_eulerRWMPairUpdate V δ) xy hg]
  change (∫⁻ p : (State d × State d) ×
      (State d × Set.Icc (0 : ℝ) 1),
      g (eulerRWMPairUpdate V δ p.1 p.2)
        ∂(Kernel.id ×ₖ Kernel.const (State d × State d)
          (gaussianUniformNoise d)) xy) = _
  rw [Kernel.lintegral_id_prod
    (f := fun p => g (eulerRWMPairUpdate V δ p.1 p.2))
    (hg.comp (measurable_uncurry_eulerRWMPairUpdate V δ))
    (Kernel.const (State d × State d) (gaussianUniformNoise d)) xy]
  rfl

theorem eulerRWMPairKernel_apply_eq_pairLaw
    (V : FirstOrderPotential d) (δ : ℝ) (xy : State d × State d) :
    eulerRWMPairKernel V δ xy = eulerRWMPairLaw V δ xy := by
  rw [Measure.ext_iff_lintegral]
  intro g hg
  rw [lintegral_eulerRWMPairKernel V δ xy hg,
    eulerRWMPairLaw,
    lintegral_map hg (measurable_eulerRWMPairUpdate V δ xy)]

/-- The second marginal of the pair transition kernel is the explicit RWM
kernel. -/
theorem map_snd_eulerRWMPairKernel
    (V : FirstOrderPotential d) (δ : ℝ) (xy : State d × State d) :
    Measure.map Prod.snd (eulerRWMPairKernel V δ xy) =
      explicitRWMKernel V δ xy.2 := by
  rw [eulerRWMPairKernel_apply_eq_pairLaw]
  exact map_snd_eulerRWMPairLaw V δ xy

/-- Kernel-level form of the one-step RWM marginal identity. -/
theorem snd_eulerRWMPairKernel
    (V : FirstOrderPotential d) (δ : ℝ) :
    Kernel.snd (eulerRWMPairKernel V δ) =
      explicitRWMKernel V δ ∘ₖ
        Kernel.deterministic Prod.snd measurable_snd := by
  rw [Kernel.snd_eq]
  ext xy : 1
  rw [Kernel.map_apply _ measurable_snd]
  rw [Kernel.comp_deterministic_eq_comap,
    Kernel.comap_apply]
  exact map_snd_eulerRWMPairKernel V δ xy

/-- Elementary finite iterate of a time-homogeneous kernel. -/
def finiteKernelIterate {α : Type*} [MeasurableSpace α]
    (K : Kernel α α) : ℕ → Kernel α α
  | 0 => Kernel.id
  | n + 1 => K ∘ₖ finiteKernelIterate K n

instance finiteKernelIterate_isMarkovKernel
    {α : Type*} [MeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (finiteKernelIterate K n) := by
  induction n with
  | zero => simp only [finiteKernelIterate]; infer_instance
  | succ n ih => simp only [finiteKernelIterate]; infer_instance

/-- If one pair step has second marginal `P`, then every finite pair iterate
has second marginal the corresponding finite iterate of `P`. -/
lemma snd_finiteKernelIterate
    {E : Type*} [MeasurableSpace E]
    (C : Kernel (E × E) (E × E)) (P : Kernel E E)
    (hCP : Kernel.snd C =
      P ∘ₖ Kernel.deterministic Prod.snd measurable_snd) :
    ∀ n, Kernel.snd (finiteKernelIterate C n) =
      finiteKernelIterate P n ∘ₖ
        Kernel.deterministic Prod.snd measurable_snd := by
  intro n
  induction n with
  | zero =>
      simp only [finiteKernelIterate, Kernel.snd_eq]
      rw [← Kernel.deterministic_comp_eq_map measurable_snd,
        Kernel.comp_id, Kernel.id_comp]
  | succ n ih =>
      simp only [finiteKernelIterate]
      rw [Kernel.snd_comp, hCP, Kernel.comp_assoc,
        Kernel.deterministic_comp_eq_map measurable_snd,
        ← Kernel.snd_eq, ih, ← Kernel.comp_assoc]

lemma finiteKernelIterate_invariant
    {α : Type*} [MeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    (μ : Measure α) (hK : Kernel.Invariant K μ) :
    ∀ n, Kernel.Invariant (finiteKernelIterate K n) μ := by
  intro n
  induction n with
  | zero =>
      simp only [finiteKernelIterate, Kernel.Invariant]
      simp
  | succ n ih =>
      simp only [finiteKernelIterate]
      exact hK.comp ih

/-- The finite coupled chain. -/
def eulerRWMPairChainKernel
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ) :
    Kernel (State d × State d) (State d × State d) :=
  finiteKernelIterate (eulerRWMPairKernel V δ) n

instance eulerRWMPairChainKernel_isMarkovKernel
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ) :
    IsMarkovKernel (eulerRWMPairChainKernel V δ n) := by
  unfold eulerRWMPairChainKernel
  infer_instance

theorem snd_eulerRWMPairChainKernel
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ) :
    Kernel.snd (eulerRWMPairChainKernel V δ n) =
      finiteKernelIterate (explicitRWMKernel V δ) n ∘ₖ
        Kernel.deterministic Prod.snd measurable_snd := by
  unfold eulerRWMPairChainKernel
  exact snd_finiteKernelIterate (eulerRWMPairKernel V δ)
    (explicitRWMKernel V δ) (snd_eulerRWMPairKernel V δ) n

/-- The second marginal after `n` coupled steps is exactly the `n`-step RWM
law. -/
theorem map_snd_eulerRWMPairChainKernel
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ)
    (xy : State d × State d) :
    Measure.map Prod.snd (eulerRWMPairChainKernel V δ n xy) =
      finiteKernelIterate (explicitRWMKernel V δ) n xy.2 := by
  change Kernel.snd (eulerRWMPairChainKernel V δ n) xy = _
  rw [snd_eulerRWMPairChainKernel,
    Kernel.comp_deterministic_eq_comap, Kernel.comap_apply]

/-- Every finite iterate of the explicit RWM kernel preserves the target. -/
theorem explicitRWMKernel_finiteIterate_invariant
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ) :
    Kernel.Invariant (finiteKernelIterate (explicitRWMKernel V δ) n)
      (V.target : Measure (State d)) := by
  exact @finiteKernelIterate_invariant (State d) inferInstance
    (explicitRWMKernel V δ) (explicitRWMKernel_isMarkovKernel V δ)
    (V.target : Measure (State d)) (explicitRWMKernel_invariant V δ) n

end DiscreteTime

end

end UniformRandomMALA
