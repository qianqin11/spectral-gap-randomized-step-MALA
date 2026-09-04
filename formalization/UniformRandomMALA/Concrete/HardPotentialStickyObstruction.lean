import UniformRandomMALA.Concrete.HardPotentialShiftedConcentration
import UniformRandomMALA.Concrete.StickyRegionCut

/-!
# Sticky-region obstruction for the fixed-step hard potential

This module combines the exact hard-potential Hastings ratio, the direct
Gaussian product Chernoff estimate, and the general small-ball cut theorem.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory

noncomputable section

/-- Split a bounded nonnegative expectation over a measurable exceptional
event.  This elementary lemma records the exact estimate used for mean
Metropolis acceptance. -/
theorem integral_le_measureReal_add_of_le_on_compl
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {E : Set Ω} (hE : MeasurableSet E)
    {f : Ω → ℝ} (hf : StronglyMeasurable f)
    (hf0 : ∀ ω, 0 ≤ f ω) (hf1 : ∀ ω, f ω ≤ 1)
    {q : ℝ} (hq : 0 ≤ q) (hcompl : ∀ ω ∉ E, f ω ≤ q) :
    ∫ ω, f ω ∂μ ≤ μ.real E + q := by
  let g : Ω → ℝ :=
    E.indicator (fun _ => 1) + Eᶜ.indicator (fun _ => q)
  have hfint : Integrable f μ := by
    apply Integrable.of_bound hf.aestronglyMeasurable 1
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 ω)]
    exact hf1 ω
  have hgint : Integrable g μ :=
    (integrable_const 1).indicator hE |>.add
      ((integrable_const q).indicator hE.compl)
  have hgE : Integrable (E.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hE
  have hgEc : Integrable (Eᶜ.indicator (fun _ => q)) μ :=
    (integrable_const q).indicator hE.compl
  have hfg : ∀ ω, f ω ≤ g ω := by
    intro ω
    by_cases hω : ω ∈ E
    · simp [g, hω, hf1 ω]
    · simp [g, hω, hcompl ω hω]
  have hint := integral_mono hfint hgint hfg
  have hcompReal : μ.real Eᶜ ≤ 1 := by
    have hmono := measureReal_mono (μ := μ) (Set.subset_univ Eᶜ)
    simp at hmono ⊢
  calc
    ∫ ω, f ω ∂μ ≤ ∫ ω, g ω ∂μ := hint
    _ = μ.real E + μ.real Eᶜ * q := by
      unfold g
      change (∫ ω, E.indicator (fun _ => (1 : ℝ)) ω +
        Eᶜ.indicator (fun _ => q) ω ∂μ) = _
      rw [integral_add hgE hgEc,
        integral_indicator_const 1 hE,
        integral_indicator_const q hE.compl]
      simp [smul_eq_mul]
    _ ≤ μ.real E + q := by
      gcongr
      exact mul_le_of_le_one_left hq hcompReal

/-- The origin acceptance profile is bounded by a universal product
contraction plus the deterministic exponential penalty from the Hastings
ratio. -/
theorem fixedStepHard_malaAcceptanceProfile_zero_le
    (n : ℕ) (hn : 1 ≤ n) {m L h : ℝ}
    (hm : 0 < m) (hmL : m < L) (hh : 0 < h) :
    ∃ t ρ : ℝ, 0 < t ∧ 0 ≤ ρ ∧ ρ < 1 ∧
      (fixedStepHardFirstOrderPotential (d := n + 1) (by omega)
          hm hmL hh).malaAcceptanceProfile h 0 ≤
        ρ ^ n + Real.exp
          (-(((L - m) / 2) * h * hardAcceptanceDrift * n)) := by
  let μ : Measure (Fin (n + 1) → ℝ) :=
    Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 (1 : ℝ≥0))
  let W := fixedStepHardFirstOrderPotential (d := n + 1) (by omega)
    hm hmL hh
  let E : Set (Fin (n + 1) → ℝ) :=
    {ω | -hardAcceptanceDrift * n ≤
      ∑ j : Fin n, gaussianTrigonometricIncrement
        (Real.sqrt 2 * ω j.succ)}
  obtain ⟨t, ρ, ht, hρ0, hρ1, hprob⟩ :=
    exists_contraction_factor_for_pi_scaledGaussian_tail n
  refine ⟨t, ρ, ht, hρ0, hρ1, ?_⟩
  have hE : MeasurableSet E := by
    unfold E
    exact measurableSet_le measurable_const (Finset.measurable_sum _ fun j _ =>
      continuous_gaussianTrigonometricIncrement.measurable.comp
        (measurable_const.mul (measurable_pi_apply j.succ)))
  let f : (Fin (n + 1) → ℝ) → ℝ := fun ω =>
    W.malaAcceptanceIntegrand h 0 (WithLp.toLp 2 ω)
  have hf : StronglyMeasurable f := by
    exact ((W.continuous_malaAcceptanceIntegrand h).comp
      (continuous_const.prodMk (PiLp.continuous_toLp 2 _))).stronglyMeasurable
  have hf0 : ∀ ω, 0 ≤ f ω := fun ω =>
    W.malaAcceptanceIntegrand_nonneg h 0 (WithLp.toLp 2 ω)
  have hf1 : ∀ ω, f ω ≤ 1 := fun ω =>
    W.malaAcceptanceIntegrand_le_one h 0 (WithLp.toLp 2 ω)
  let q : ℝ := Real.exp
    (-(((L - m) / 2) * h * hardAcceptanceDrift * n))
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have hcompl : ∀ ω ∉ E, f ω ≤ q := by
    intro ω hω
    have hsum : (∑ j : Fin n, gaussianTrigonometricIncrement
        (Real.sqrt 2 * ω j.succ)) < -hardAcceptanceDrift * n := by
      simpa [E] using hω
    have hcoef : 0 < ((L - m) / 2) * h := by positivity
    have hratio := hard_malaLogRatio_zero_at_piInnovation_le
      n hn hm hmL hh ω
    have hstrict : W.malaLogRatio h 0
        (Real.sqrt (2 * h) • WithLp.toLp 2 ω) <
          -(((L - m) / 2) * h * hardAcceptanceDrift * n) := by
      apply hratio.trans_lt
      calc
        ((L - m) / 2) * h *
            (∑ j : Fin n, gaussianTrigonometricIncrement
              (Real.sqrt 2 * ω j.succ)) <
            ((L - m) / 2) * h * (-hardAcceptanceDrift * n) := by
          exact mul_lt_mul_of_pos_left hsum hcoef
        _ = -(((L - m) / 2) * h * hardAcceptanceDrift * n) := by ring
    unfold f FirstOrderPotential.malaAcceptanceIntegrand
    have hmean : W.proposalMean h 0 = 0 := by
      simp [FirstOrderPotential.proposalMean, W,
        fixedStepHardFirstOrderPotential_gradU_zero]
    rw [hmean, zero_add]
    exact (min_le_left _ _).trans
      (Real.exp_le_exp.mpr hstrict.le)
  have hsplit := integral_le_measureReal_add_of_le_on_compl
    (μ := μ) (E := E) (f := f) hE hf hf0 hf1 hq hcompl
  have hmap :
      ∫ ω, f ω ∂μ = W.malaAcceptanceProfile h 0 := by
    unfold FirstOrderPotential.malaAcceptanceProfile
    rw [← map_pi_eq_stdGaussian (ι := Fin (n + 1))]
    rw [integral_map]
    · exact (PiLp.continuous_toLp 2 _).measurable.aemeasurable
    · simpa only [map_pi_eq_stdGaussian] using
        (W.integrable_malaAcceptanceIntegrand h 0).aestronglyMeasurable
  rw [← hmap]
  have hprob' : μ.real E ≤ ρ ^ n := by
    simpa only [μ, E, neg_mul] using hprob
  apply hsplit.trans
  exact add_le_add hprob' le_rfl

/-- Fixed-Chernoff-parameter form of the origin acceptance estimate.  This
form exposes that the same contraction factor works in every dimension. -/
theorem fixedStepHard_malaAcceptanceProfile_zero_le_mgf_pow
    (n : ℕ) (hn : 1 ≤ n) {m L h t : ℝ}
    (hm : 0 < m) (hmL : m < L) (hh : 0 < h) (ht : 0 < t) :
    (fixedStepHardFirstOrderPotential (d := n + 1) (by omega)
        hm hmL hh).malaAcceptanceProfile h 0 ≤
      (mgf halfShiftedGaussianTrigonometricIncrement
        (gaussianReal 0 (2 : ℝ≥0)) t) ^ n +
      Real.exp (-(((L - m) / 2) * h * hardAcceptanceDrift * n)) := by
  let μ : Measure (Fin (n + 1) → ℝ) :=
    Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 (1 : ℝ≥0))
  let W := fixedStepHardFirstOrderPotential (d := n + 1) (by omega)
    hm hmL hh
  let E : Set (Fin (n + 1) → ℝ) :=
    {ω | -hardAcceptanceDrift * n ≤
      ∑ j : Fin n, gaussianTrigonometricIncrement
        (Real.sqrt 2 * ω j.succ)}
  have hprob := pi_scaledGaussian_tail_le_mgf_pow n ht
  have hE : MeasurableSet E := by
    unfold E
    exact measurableSet_le measurable_const (Finset.measurable_sum _ fun j _ =>
      continuous_gaussianTrigonometricIncrement.measurable.comp
        (measurable_const.mul (measurable_pi_apply j.succ)))
  let f : (Fin (n + 1) → ℝ) → ℝ := fun ω =>
    W.malaAcceptanceIntegrand h 0 (WithLp.toLp 2 ω)
  have hf : StronglyMeasurable f := by
    exact ((W.continuous_malaAcceptanceIntegrand h).comp
      (continuous_const.prodMk (PiLp.continuous_toLp 2 _))).stronglyMeasurable
  have hf0 : ∀ ω, 0 ≤ f ω := fun ω =>
    W.malaAcceptanceIntegrand_nonneg h 0 (WithLp.toLp 2 ω)
  have hf1 : ∀ ω, f ω ≤ 1 := fun ω =>
    W.malaAcceptanceIntegrand_le_one h 0 (WithLp.toLp 2 ω)
  let q : ℝ := Real.exp
    (-(((L - m) / 2) * h * hardAcceptanceDrift * n))
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have hcompl : ∀ ω ∉ E, f ω ≤ q := by
    intro ω hω
    have hsum : (∑ j : Fin n, gaussianTrigonometricIncrement
        (Real.sqrt 2 * ω j.succ)) < -hardAcceptanceDrift * n := by
      simpa [E] using hω
    have hcoef : 0 < ((L - m) / 2) * h := by positivity
    have hratio := hard_malaLogRatio_zero_at_piInnovation_le
      n hn hm hmL hh ω
    have hstrict : W.malaLogRatio h 0
        (Real.sqrt (2 * h) • WithLp.toLp 2 ω) <
          -(((L - m) / 2) * h * hardAcceptanceDrift * n) := by
      apply hratio.trans_lt
      calc
        ((L - m) / 2) * h *
            (∑ j : Fin n, gaussianTrigonometricIncrement
              (Real.sqrt 2 * ω j.succ)) <
            ((L - m) / 2) * h * (-hardAcceptanceDrift * n) := by
          exact mul_lt_mul_of_pos_left hsum hcoef
        _ = -(((L - m) / 2) * h * hardAcceptanceDrift * n) := by ring
    unfold f FirstOrderPotential.malaAcceptanceIntegrand
    have hmean : W.proposalMean h 0 = 0 := by
      simp [FirstOrderPotential.proposalMean, W,
        fixedStepHardFirstOrderPotential_gradU_zero]
    rw [hmean, zero_add]
    exact (min_le_left _ _).trans
      (Real.exp_le_exp.mpr hstrict.le)
  have hsplit := integral_le_measureReal_add_of_le_on_compl
    (μ := μ) (E := E) (f := f) hE hf hf0 hf1 hq hcompl
  have hmap :
      ∫ ω, f ω ∂μ = W.malaAcceptanceProfile h 0 := by
    unfold FirstOrderPotential.malaAcceptanceProfile
    rw [← map_pi_eq_stdGaussian (ι := Fin (n + 1))]
    rw [integral_map]
    · exact (PiLp.continuous_toLp 2 _).measurable.aemeasurable
    · simpa only [map_pi_eq_stdGaussian] using
        (W.integrable_malaAcceptanceIntegrand h 0).aestronglyMeasurable
  rw [← hmap]
  have hprob' : μ.real E ≤
      (mgf halfShiftedGaussianTrigonometricIncrement
        (gaussianReal 0 (2 : ℝ≥0)) t) ^ n := by
    simpa only [μ, E, neg_mul] using hprob
  exact hsplit.trans (add_le_add hprob' le_rfl)

/-- Sticky-region spectral-gap upper bound before compressing the two
exponential terms into the manuscript's `exp(-c n min(s,1))` notation. -/
theorem fixedStepHard_sticky_rayleighSpectralGap_upper
    (n : ℕ) (hn : 1 ≤ n) {m L h : ℝ}
    (hm : 0 < m) (hmL : m < L) (hh : 0 < h) :
    ∃ t ρ : ℝ, 0 < t ∧ 0 ≤ ρ ∧ ρ < 1 ∧
      rayleighSpectralGap
          ((fixedStepHardFirstOrderPotential (d := n + 1) (by omega)
            hm hmL hh).target : Measure (State (n + 1)))
          ((fixedStepHardFirstOrderPotential (d := n + 1) (by omega)
            hm hmL hh).malaKernel h hh) ≤
        ENNReal.ofReal (4 *
          (ρ ^ n + Real.exp
            (-(((L - m) / 2) * h * hardAcceptanceDrift * n)))) := by
  let W := fixedStepHardFirstOrderPotential (d := n + 1) (by omega)
    hm hmL hh
  obtain ⟨t, ρ, ht, hρ0, hρ1, hprofile⟩ :=
    fixedStepHard_malaAcceptanceProfile_zero_le n hn hm hmL hh
  let s : ℝ := ρ ^ n + Real.exp
    (-(((L - m) / 2) * h * hardAcceptanceDrift * n))
  have hspos : 0 < s := by
    dsimp [s]
    positivity
  have horigin : W.malaAcceptanceProfile h 0 < 2 * s := by
    apply hprofile.trans_lt
    dsimp [s]
    linarith
  rcases W.exists_target_ball_rayleighSpectralGap_le_two_mul hh horigin with
    ⟨r, hr, hmass, hhalf, hflow, hgap⟩
  refine ⟨t, ρ, ht, hρ0, hρ1, ?_⟩
  apply hgap.trans_eq
  congr 1
  dsimp [s]
  ring

/-- A single universal product-contraction factor gives the sticky upper
bound simultaneously for all dimensions and all admissible parameters. -/
theorem exists_universal_fixedStepHard_sticky_rayleighSpectralGap_upper :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ (n : ℕ) (hn : 1 ≤ n) {m L h : ℝ}
        (hm : 0 < m) (hmL : m < L) (hh : 0 < h),
        rayleighSpectralGap
            ((fixedStepHardFirstOrderPotential (d := n + 1) (by omega)
              hm hmL hh).target :
              Measure (State (n + 1)))
            ((fixedStepHardFirstOrderPotential (d := n + 1) (by omega)
              hm hmL hh).malaKernel h hh) ≤
          ENNReal.ofReal (4 *
            (ρ ^ n + Real.exp
              (-(((L - m) / 2) * h * hardAcceptanceDrift * n)))) := by
  obtain ⟨t, ht, hcontract⟩ :=
    exists_pos_mgf_halfShiftedGaussianTrigonometricIncrement_lt_one
  let ρ := mgf halfShiftedGaussianTrigonometricIncrement
    (gaussianReal 0 (2 : ℝ≥0)) t
  have hρ0 : 0 ≤ ρ := mgf_nonneg
  refine ⟨ρ, hρ0, hcontract, ?_⟩
  intro n hn m L h hm hmL hh
  let W := fixedStepHardFirstOrderPotential (d := n + 1) (by omega)
    hm hmL hh
  have hprofile := fixedStepHard_malaAcceptanceProfile_zero_le_mgf_pow
    n hn hm hmL hh ht
  let s : ℝ := ρ ^ n + Real.exp
    (-(((L - m) / 2) * h * hardAcceptanceDrift * n))
  have hspos : 0 < s := by
    dsimp [s]
    positivity
  have horigin : W.malaAcceptanceProfile h 0 < 2 * s := by
    apply hprofile.trans_lt
    dsimp [s, ρ]
    linarith
  rcases W.exists_target_ball_rayleighSpectralGap_le_two_mul hh horigin with
    ⟨r, hr, hmass, hhalf, hflow, hgap⟩
  apply hgap.trans_eq
  congr 1
  dsimp [s]
  ring

end

end UniformRandomMALA.Concrete
