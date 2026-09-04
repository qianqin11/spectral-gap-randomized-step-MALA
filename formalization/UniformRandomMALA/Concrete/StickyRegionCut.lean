import UniformRandomMALA.Concrete.FixedStepHardPotential
import UniformRandomMALA.Concrete.SpectralGapUpperBounds
import UniformRandomMALA.Concrete.SafeAcceptance
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Regular

/-!
# Sticky-region cuts for fixed-step MALA

This file isolates the topological and measure-theoretic part of the sticky
set argument.  The proposal-averaged Metropolis acceptance is written as a
bounded real integral over a fixed standard Gaussian law.  Dominated
convergence makes this profile continuous.  Outer regularity and the strictly
positive target density then produce an arbitrarily small positive-mass open
cut around the origin.  Finally, the accepted/rejected kernel decomposition
turns a pointwise acceptance bound on that cut into a boundary-flow and
Rayleigh-gap upper bound.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace FirstOrderPotential

variable {d : ℕ} (V : FirstOrderPotential d)

/-- The real Metropolis acceptance at a proposal expressed through a standard
Gaussian innovation. -/
def malaAcceptanceIntegrand (h : ℝ) (x z : State d) : ℝ :=
  min (Real.exp (V.malaLogRatio h x
    (V.proposalMean h x + Real.sqrt (2 * h) • z))) 1

/-- Proposal-averaged MALA acceptance, represented as a real integral against
one fixed standard Gaussian law. -/
def malaAcceptanceProfile (h : ℝ) (x : State d) : ℝ :=
  ∫ z : State d, V.malaAcceptanceIntegrand h x z ∂stdGaussian (State d)

lemma continuous_malaLogRatio (h : ℝ) :
    Continuous (Function.uncurry (V.malaLogRatio h)) := by
  unfold malaLogRatio
  have hmean : Continuous (fun x : State d => V.proposalMean h x) :=
    V.continuous_proposalMean.comp (continuous_const.prodMk continuous_id)
  have hforward : Continuous (fun p : State d × State d =>
      p.2 - V.proposalMean h p.1) :=
    continuous_snd.sub (hmean.comp continuous_fst)
  have hreverse : Continuous (fun p : State d × State d =>
      p.1 - V.proposalMean h p.2) :=
    continuous_fst.sub (hmean.comp continuous_snd)
  exact ((V.continuous_U.comp continuous_fst).sub
    (V.continuous_U.comp continuous_snd)).add
      (((continuous_norm.comp hforward).pow 2 |>.sub
        ((continuous_norm.comp hreverse).pow 2)).div_const (4 * h))

lemma continuous_malaAcceptanceIntegrand (h : ℝ) :
    Continuous (Function.uncurry (V.malaAcceptanceIntegrand h)) := by
  unfold malaAcceptanceIntegrand
  have hmean : Continuous (fun x : State d => V.proposalMean h x) :=
    V.continuous_proposalMean.comp (continuous_const.prodMk continuous_id)
  have hproposal : Continuous (fun p : State d × State d =>
      V.proposalMean h p.1 + Real.sqrt (2 * h) • p.2) := by
    fun_prop
  have hratio : Continuous (fun p : State d × State d =>
      V.malaLogRatio h p.1
        (V.proposalMean h p.1 + Real.sqrt (2 * h) • p.2)) := by
    exact (V.continuous_malaLogRatio h).comp
      (continuous_fst.prodMk hproposal)
  exact (Real.continuous_exp.comp hratio).min continuous_const

lemma malaAcceptanceIntegrand_nonneg (h : ℝ) (x z : State d) :
    0 ≤ V.malaAcceptanceIntegrand h x z := by
  unfold malaAcceptanceIntegrand
  exact le_min (Real.exp_pos _).le zero_le_one

lemma malaAcceptanceIntegrand_le_one (h : ℝ) (x z : State d) :
    V.malaAcceptanceIntegrand h x z ≤ 1 := by
  unfold malaAcceptanceIntegrand
  exact min_le_right _ _

lemma integrable_malaAcceptanceIntegrand (h : ℝ) (x : State d) :
    Integrable (V.malaAcceptanceIntegrand h x) (stdGaussian (State d)) := by
  apply Integrable.of_bound
    ((V.continuous_malaAcceptanceIntegrand h).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable 1
  filter_upwards with z
  change |V.malaAcceptanceIntegrand h x z| ≤ 1
  rw [abs_of_nonneg (V.malaAcceptanceIntegrand_nonneg h x z)]
  exact V.malaAcceptanceIntegrand_le_one h x z

/-- Dominated convergence for the pointwise MALA acceptance profile.  Only
continuity of `U` and its recorded genuine gradient is used. -/
theorem continuous_malaAcceptanceProfile (h : ℝ) :
    Continuous (V.malaAcceptanceProfile h) := by
  rw [continuous_iff_continuousAt]
  intro x
  unfold malaAcceptanceProfile
  apply tendsto_integral_filter_of_dominated_convergence
    (bound := fun _z : State d => 1)
  · exact Filter.Eventually.of_forall fun x' =>
      ((V.continuous_malaAcceptanceIntegrand h).comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x' => ae_of_all _ fun z => by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (V.malaAcceptanceIntegrand_nonneg h x' z)]
      exact V.malaAcceptanceIntegrand_le_one h x' z
  · exact integrable_const 1
  · exact ae_of_all _ fun z =>
      ((V.continuous_malaAcceptanceIntegrand h).comp
        (continuous_id.prodMk continuous_const)).continuousAt

lemma malaAcceptanceProfile_nonneg (h : ℝ) (x : State d) :
    0 ≤ V.malaAcceptanceProfile h x := by
  exact integral_nonneg fun z => V.malaAcceptanceIntegrand_nonneg h x z

lemma malaAcceptanceProfile_le_one (h : ℝ) (x : State d) :
    V.malaAcceptanceProfile h x ≤ 1 := by
  calc
    V.malaAcceptanceProfile h x ≤ ∫ _z : State d, (1 : ℝ)
        ∂stdGaussian (State d) := by
      apply integral_mono (V.integrable_malaAcceptanceIntegrand h x)
        (integrable_const 1)
      exact fun z => V.malaAcceptanceIntegrand_le_one h x z
    _ = 1 := by simp

/-- The real profile is exactly the extended-valued acceptance mass used by
the concrete Metropolis kernel. -/
theorem ofReal_malaAcceptanceProfile_eq_acceptanceMass
    {h : ℝ} (hh : 0 < h) (x : State d) :
    ENNReal.ofReal (V.malaAcceptanceProfile h x) =
      MetropolisHastings.acceptanceMass
        (V.gaussianDensityProposal h) (V.malaAcceptance h) x := by
  unfold malaAcceptanceProfile MetropolisHastings.acceptanceMass
  rw [DiscreteTime.gaussianDensityProposal_eq_map_stdGaussian V hh x]
  rw [lintegral_map]
  · simp_rw [V.malaAcceptance_eq_ofReal_min_exp_logRatio hh]
    change ENNReal.ofReal (∫ z : State d,
        V.malaAcceptanceIntegrand h x z ∂stdGaussian (State d)) =
      ∫⁻ z : State d, ENNReal.ofReal
        (V.malaAcceptanceIntegrand h x z) ∂stdGaussian (State d)
    rw [← ofReal_integral_eq_lintegral_ofReal
      (V.integrable_malaAcceptanceIntegrand h x)]
    exact ae_of_all _ fun z => V.malaAcceptanceIntegrand_nonneg h x z
  · exact (V.measurable_uncurry_malaAcceptance h).of_uncurry_left
  · fun_prop

/-- The normalized target gives positive mass to every nonempty open set. -/
theorem target_isOpen_measure_pos {U : Set (State d)}
    (hU : IsOpen U) (hne : U.Nonempty) :
    0 < (V.target : Measure (State d)) U := by
  rw [V.target_toMeasure_eq_withDensity, withDensity_apply _ hU.measurableSet]
  rw [setLIntegral_pos_iff V.measurable_targetDensity]
  have hsupp : Function.support V.targetDensity = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (V.targetDensity_pos x).ne'
  rw [hsupp, Set.univ_inter]
  exact hU.measure_pos volume hne

/-- The target has no atom at any point; this follows from its Lebesgue
density and is stated explicitly for the outer-regular small-cut argument. -/
theorem target_singleton_zero (x : State d) :
    (V.target : Measure (State d)) {x} = 0 := by
  let _ : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp V.hd
  rw [V.target_toMeasure_eq_withDensity]
  exact measure_singleton x

/-- Any open neighborhood of the origin contains an open target cut with
positive mass and mass strictly below one half. -/
theorem exists_open_target_cut_inside
    {N : Set (State d)} (hN : IsOpen N) (h0N : (0 : State d) ∈ N) :
    ∃ A : Set (State d), IsOpen A ∧ (0 : State d) ∈ A ∧ A ⊆ N ∧
      0 < (V.target : Measure (State d)) A ∧
      (V.target : Measure (State d)) A < (2 : ℝ≥0∞)⁻¹ := by
  have hsingleton : (V.target : Measure (State d)) ({0} : Set (State d)) = 0 :=
    V.target_singleton_zero 0
  have hhalf : (V.target : Measure (State d)) ({0} : Set (State d)) <
      (2 : ℝ≥0∞)⁻¹ := by simp [hsingleton]
  rcases (({0} : Set (State d)).exists_isOpen_lt_of_lt
      ((2 : ℝ≥0∞)⁻¹) hhalf) with ⟨U, hsub, hU, hUhalf⟩
  let A : Set (State d) := U ∩ N
  have h0U : (0 : State d) ∈ U := hsub (Set.mem_singleton 0)
  have hAopen : IsOpen A := hU.inter hN
  have h0A : (0 : State d) ∈ A := ⟨h0U, h0N⟩
  refine ⟨A, hAopen, h0A, Set.inter_subset_right, ?_, ?_⟩
  · exact V.target_isOpen_measure_pos hAopen ⟨0, h0A⟩
  · exact (measure_mono Set.inter_subset_left).trans_lt hUhalf

/-- Metric-ball form of `exists_open_target_cut_inside`.  The ball is
centered at the origin, has positive radius and positive target mass, lies in
the prescribed neighborhood, and has mass below one half. -/
theorem exists_target_ball_inside
    {N : Set (State d)} (hN : IsOpen N) (h0N : (0 : State d) ∈ N) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : State d) r ⊆ N ∧
      0 < (V.target : Measure (State d)) (Metric.ball 0 r) ∧
      (V.target : Measure (State d)) (Metric.ball 0 r) <
        (2 : ℝ≥0∞)⁻¹ := by
  rcases V.exists_open_target_cut_inside hN h0N with
    ⟨A, hAopen, h0A, hAN, hApos, hAhalf⟩
  rcases Metric.isOpen_iff.mp hAopen 0 h0A with ⟨r, hr, hballA⟩
  have hballOpen : IsOpen (Metric.ball (0 : State d) r) := Metric.isOpen_ball
  have h0ball : (0 : State d) ∈ Metric.ball 0 r := Metric.mem_ball_self hr
  exact ⟨r, hr, hballA.trans hAN,
    V.target_isOpen_measure_pos hballOpen ⟨0, h0ball⟩,
    (measure_mono hballA).trans_lt hAhalf⟩

/-- An origin acceptance bound persists on a positive-mass open cut. -/
theorem exists_open_target_cut_acceptanceProfile_lt
    {h b : ℝ} (hb : V.malaAcceptanceProfile h 0 < b) :
    ∃ A : Set (State d), IsOpen A ∧ (0 : State d) ∈ A ∧
      0 < (V.target : Measure (State d)) A ∧
      (V.target : Measure (State d)) A < (2 : ℝ≥0∞)⁻¹ ∧
      ∀ x ∈ A, V.malaAcceptanceProfile h x < b := by
  let N : Set (State d) := (V.malaAcceptanceProfile h) ⁻¹' Set.Iio b
  have hN : IsOpen N := isOpen_Iio.preimage (V.continuous_malaAcceptanceProfile h)
  have h0N : (0 : State d) ∈ N := hb
  rcases V.exists_open_target_cut_inside hN h0N with
    ⟨A, hAopen, h0A, hAN, hApos, hAhalf⟩
  exact ⟨A, hAopen, h0A, hApos, hAhalf,
    fun x hx => hAN hx⟩

/-- Actual centered-ball version of the local acceptance-profile cut. -/
theorem exists_target_ball_acceptanceProfile_lt
    {h b : ℝ} (hb : V.malaAcceptanceProfile h 0 < b) :
    ∃ r : ℝ, 0 < r ∧
      0 < (V.target : Measure (State d)) (Metric.ball 0 r) ∧
      (V.target : Measure (State d)) (Metric.ball 0 r) <
        (2 : ℝ≥0∞)⁻¹ ∧
      ∀ x ∈ Metric.ball (0 : State d) r,
        V.malaAcceptanceProfile h x < b := by
  let N : Set (State d) := (V.malaAcceptanceProfile h) ⁻¹' Set.Iio b
  have hN : IsOpen N := isOpen_Iio.preimage (V.continuous_malaAcceptanceProfile h)
  have h0N : (0 : State d) ∈ N := hb
  rcases V.exists_target_ball_inside hN h0N with
    ⟨r, hr, hballN, hballpos, hballhalf⟩
  exact ⟨r, hr, hballpos, hballhalf, fun x hx => hballN hx⟩

/-- From a point inside a measurable set, the MALA probability of exiting is
at most the total accepted proposal mass: the rejection kernel stays put. -/
theorem malaKernel_apply_compl_le_acceptanceMass
    {h : ℝ} (hh : 0 < h) {A : Set (State d)} (hA : MeasurableSet A)
    {x : State d} (hx : x ∈ A) :
    V.malaKernel h hh x Aᶜ ≤
      MetropolisHastings.acceptanceMass
        (V.gaussianDensityProposal h) (V.malaAcceptance h) x := by
  let q := V.gaussianDensityProposal h
  let a := V.malaAcceptance h
  have ha : Measurable (Function.uncurry a) := V.measurable_uncurry_malaAcceptance h
  change MetropolisHastings.kernel q a x Aᶜ ≤
    MetropolisHastings.acceptanceMass q a x
  rw [MetropolisHastings.kernel, add_apply,
    Measure.add_apply, MetropolisHastings.rejected_apply q a ha x Aᶜ hA.compl]
  have hxc : x ∉ Aᶜ := by simpa
  simp only [Set.indicator_of_notMem hxc, add_zero]
  calc
    MetropolisHastings.accepted q a x Aᶜ ≤
        MetropolisHastings.accepted q a x Set.univ :=
      measure_mono (Set.subset_univ _)
    _ = MetropolisHastings.acceptanceMass q a x :=
      MetropolisHastings.accepted_apply_univ q a ha x

/-- A uniform profile bound on a measurable cut gives the corresponding
boundary-flow estimate. -/
theorem boundaryFlow_malaKernel_le_of_acceptanceProfile
    {h b : ℝ} (hh : 0 < h) {A : Set (State d)} (hA : MeasurableSet A)
    (hbound : ∀ x ∈ A, V.malaAcceptanceProfile h x ≤ b) :
    boundaryFlow (V.target : Measure (State d)) (V.malaKernel h hh) A ≤
      ENNReal.ofReal b * (V.target : Measure (State d)) A := by
  unfold boundaryFlow flow
  calc
    (∫⁻ x in A, V.malaKernel h hh x Aᶜ
        ∂(V.target : Measure (State d))) ≤
        ∫⁻ x in A,
          MetropolisHastings.acceptanceMass
            (V.gaussianDensityProposal h) (V.malaAcceptance h) x
          ∂(V.target : Measure (State d)) := by
      apply setLIntegral_mono' hA
      exact fun x hx => V.malaKernel_apply_compl_le_acceptanceMass hh hA hx
    _ ≤ ∫⁻ _x in A, ENNReal.ofReal b
          ∂(V.target : Measure (State d)) := by
      apply setLIntegral_mono' hA
      intro x hx
      rw [← V.ofReal_malaAcceptanceProfile_eq_acceptanceMass hh x]
      exact ENNReal.ofReal_le_ofReal (hbound x hx)
    _ = ENNReal.ofReal b * (V.target : Measure (State d)) A := by
      simp

/-- Cut-form Rayleigh upper bound obtained directly from a pointwise
acceptance-profile estimate. -/
theorem rayleighSpectralGap_malaKernel_le_of_acceptanceProfile
    {h b : ℝ} (hh : 0 < h) {A : Set (State d)} (hA : MeasurableSet A)
    (hvar : (V.target : Measure (State d)).real A *
      (1 - (V.target : Measure (State d)).real A) ≠ 0)
    (hbound : ∀ x ∈ A, V.malaAcceptanceProfile h x ≤ b) :
    rayleighSpectralGap (V.target : Measure (State d)) (V.malaKernel h hh) ≤
      (ENNReal.ofReal b * (V.target : Measure (State d)) A) /
        ENNReal.ofReal ((V.target : Measure (State d)).real A *
          (1 - (V.target : Measure (State d)).real A)) := by
  exact (rayleighSpectralGap_le_boundaryFlow_div_cutVariance
    (V.malaKernel h hh) (V.malaKernel_isReversible h hh) hA hvar).trans
      (ENNReal.div_le_div_right
        (V.boundaryFlow_malaKernel_le_of_acceptanceProfile hh hA hbound) _)

/-- When the cut has mass at most one half, cancellation of its positive mass
reduces the exact cut quotient to twice the pointwise acceptance bound. -/
theorem rayleighSpectralGap_malaKernel_le_two_mul_of_acceptanceProfile
    {h b : ℝ} (hh : 0 < h) {A : Set (State d)} (hA : MeasurableSet A)
    (hApos : 0 < (V.target : Measure (State d)) A)
    (hAhalf : (V.target : Measure (State d)) A < (2 : ℝ≥0∞)⁻¹)
    (hb : 0 ≤ b)
    (hbound : ∀ x ∈ A, V.malaAcceptanceProfile h x ≤ b) :
    rayleighSpectralGap (V.target : Measure (State d))
        (V.malaKernel h hh) ≤ ENNReal.ofReal (2 * b) := by
  let q : ℝ := (V.target : Measure (State d)).real A
  have hAtop : (V.target : Measure (State d)) A ≠ ∞ := measure_ne_top _ _
  have hqpos : 0 < q := by
    dsimp [q]
    rw [measureReal_def]
    exact ENNReal.toReal_pos hApos.ne' hAtop
  have hqhalf : q < 1 / 2 := by
    have hhalfTop : (2 : ℝ≥0∞)⁻¹ ≠ ∞ := by simp
    have hto := (ENNReal.toReal_lt_toReal hAtop hhalfTop).2 hAhalf
    simpa [q, measureReal_def] using hto
  have hqone : 0 < 1 - q := by linarith
  have hvar : (V.target : Measure (State d)).real A *
      (1 - (V.target : Measure (State d)).real A) ≠ 0 := by
    dsimp [q] at hqpos hqhalf hqone ⊢
    exact mul_ne_zero hqpos.ne' hqone.ne'
  have hgap := V.rayleighSpectralGap_malaKernel_le_of_acceptanceProfile
    hh hA hvar hbound
  apply hgap.trans
  rw [← ofReal_measureReal (μ := (V.target : Measure (State d)))
    (s := A) hAtop]
  change (ENNReal.ofReal b * ENNReal.ofReal q) /
      ENNReal.ofReal (q * (1 - q)) ≤ ENNReal.ofReal (2 * b)
  rw [← ENNReal.ofReal_mul hb,
    ← ENNReal.ofReal_div_of_pos (mul_pos hqpos hqone)]
  apply ENNReal.ofReal_le_ofReal
  calc
    b * q / (q * (1 - q)) = b / (1 - q) := by
      field_simp [hqpos.ne', hqone.ne']
    _ ≤ 2 * b := by
      apply (div_le_iff₀ hqone).2
      nlinarith

/-- Complete sticky-cut package.  A strict origin profile bound produces a
positive target cut of mass below one half and the familiar factor-two
Rayleigh upper bound.  This is the endpoint consumed by the exponential
hard-potential calculation. -/
theorem exists_open_target_cut_rayleighSpectralGap_le_two_mul
    {h b : ℝ} (hh : 0 < h) (hb : V.malaAcceptanceProfile h 0 < b) :
    ∃ A : Set (State d), IsOpen A ∧ (0 : State d) ∈ A ∧
      0 < (V.target : Measure (State d)) A ∧
      (V.target : Measure (State d)) A < (2 : ℝ≥0∞)⁻¹ ∧
      boundaryFlow (V.target : Measure (State d)) (V.malaKernel h hh) A ≤
        ENNReal.ofReal b * (V.target : Measure (State d)) A ∧
      rayleighSpectralGap (V.target : Measure (State d))
          (V.malaKernel h hh) ≤ ENNReal.ofReal (2 * b) := by
  rcases V.exists_open_target_cut_acceptanceProfile_lt hb with
    ⟨A, hAopen, h0A, hApos, hAhalf, hboundlt⟩
  have hbpos : 0 < b := (V.malaAcceptanceProfile_nonneg h 0).trans_lt hb
  have hA : MeasurableSet A := hAopen.measurableSet
  have hbound : ∀ x ∈ A, V.malaAcceptanceProfile h x ≤ b :=
    fun x hx => (hboundlt x hx).le
  have hflow := V.boundaryFlow_malaKernel_le_of_acceptanceProfile
    hh hA hbound
  have hgap := V.rayleighSpectralGap_malaKernel_le_two_mul_of_acceptanceProfile
    hh hA hApos hAhalf hbpos.le hbound
  exact ⟨A, hAopen, h0A, hApos, hAhalf, hflow, hgap⟩

/-- Centered metric-ball endpoint for the sticky-region argument. -/
theorem exists_target_ball_rayleighSpectralGap_le_two_mul
    {h b : ℝ} (hh : 0 < h) (hb : V.malaAcceptanceProfile h 0 < b) :
    ∃ r : ℝ, 0 < r ∧
      0 < (V.target : Measure (State d)) (Metric.ball 0 r) ∧
      (V.target : Measure (State d)) (Metric.ball 0 r) <
        (2 : ℝ≥0∞)⁻¹ ∧
      boundaryFlow (V.target : Measure (State d)) (V.malaKernel h hh)
          (Metric.ball 0 r) ≤
        ENNReal.ofReal b *
          (V.target : Measure (State d)) (Metric.ball 0 r) ∧
      rayleighSpectralGap (V.target : Measure (State d))
          (V.malaKernel h hh) ≤ ENNReal.ofReal (2 * b) := by
  rcases V.exists_target_ball_acceptanceProfile_lt hb with
    ⟨r, hr, hballpos, hballhalf, hboundlt⟩
  have hbpos : 0 < b := (V.malaAcceptanceProfile_nonneg h 0).trans_lt hb
  have hball : MeasurableSet (Metric.ball (0 : State d) r) :=
    Metric.isOpen_ball.measurableSet
  have hbound : ∀ x ∈ Metric.ball (0 : State d) r,
      V.malaAcceptanceProfile h x ≤ b :=
    fun x hx => (hboundlt x hx).le
  have hflow := V.boundaryFlow_malaKernel_le_of_acceptanceProfile
    hh hball hbound
  have hgap := V.rayleighSpectralGap_malaKernel_le_two_mul_of_acceptanceProfile
    hh hball hballpos hballhalf hbpos.le hbound
  exact ⟨r, hr, hballpos, hballhalf, hflow, hgap⟩

end FirstOrderPotential

end

end UniformRandomMALA.Concrete
