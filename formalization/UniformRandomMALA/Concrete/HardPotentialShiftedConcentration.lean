import UniformRandomMALA.Concrete.GaussianTrigonometricConcentration
import UniformRandomMALA.Concrete.HardPotentialLogRatio

/-!
# Linear-threshold concentration for the hard-potential increment

The sticky-region argument needs concentration below a *negative linear*
threshold, rather than merely below zero.  This module shifts the exact
increment by half the magnitude of its negative mean and applies a direct
fixed-parameter Chernoff argument.  No sub-Gaussian-norm equivalence is used.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory Filter SignType
open scoped BigOperators ENNReal NNReal ProbabilityTheory

noncomputable section

/-- Half the magnitude of the negative mean of the oscillatory increment. -/
def hardAcceptanceDrift : ℝ :=
  (1 - 2 / Real.exp 1) / 2

theorem hardAcceptanceDrift_pos : 0 < hardAcceptanceDrift := by
  unfold hardAcceptanceDrift
  have heTwo : 2 < Real.exp 1 := by
    convert Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0) using 1
    all_goals norm_num
  have hePos : 0 < Real.exp 1 := Real.exp_pos 1
  have : 2 / Real.exp 1 < 1 := (div_lt_one hePos).2 heTwo
  linarith

/-- The increment shifted upward by half the magnitude of its mean. -/
def halfShiftedGaussianTrigonometricIncrement (v : ℝ) : ℝ :=
  gaussianTrigonometricIncrement v + hardAcceptanceDrift

theorem continuous_halfShiftedGaussianTrigonometricIncrement :
    Continuous halfShiftedGaussianTrigonometricIncrement := by
  unfold halfShiftedGaussianTrigonometricIncrement
  exact continuous_gaussianTrigonometricIncrement.add continuous_const

theorem integrable_gaussianTrigonometricIncrement :
    Integrable gaussianTrigonometricIncrement
      (gaussianReal 0 (2 : ℝ≥0)) := by
  let μ : Measure ℝ := gaussianReal 0 (2 : ℝ≥0)
  have hcos : Integrable Real.cos μ :=
    (integrable_const (1 : ℝ)).mono (by fun_prop)
      (by filter_upwards with v; simpa using Real.abs_cos_le_one v)
  have hone : Integrable (fun _ : ℝ => (1 : ℝ)) μ := integrable_const 1
  have hid : Integrable id μ := by
    exact (memLp_id_gaussianReal (μ := 0) (v := (2 : ℝ≥0)) 1).integrable (by simp)
  have hvsin : Integrable (fun v : ℝ => v * Real.sin v) μ := by
    have h := hid.mul_bdd Real.continuous_sin.aestronglyMeasurable
      (by filter_upwards with v; simpa using Real.abs_sin_le_one v)
    simpa [id] using h
  change Integrable (fun v : ℝ =>
    (Real.cos v - 1) + (v * Real.sin v) / 2) μ
  exact (hcos.sub hone).add (hvsin.div_const 2)

theorem integrable_halfShiftedGaussianTrigonometricIncrement :
    Integrable halfShiftedGaussianTrigonometricIncrement
      (gaussianReal 0 (2 : ℝ≥0)) := by
  exact integrable_gaussianTrigonometricIncrement.add (integrable_const _)

/-- The shifted increment still has exactly negative mean, now `-δ`. -/
theorem integral_halfShiftedGaussianTrigonometricIncrement :
    ∫ v : ℝ, halfShiftedGaussianTrigonometricIncrement v
        ∂gaussianReal 0 (2 : ℝ≥0) = -hardAcceptanceDrift := by
  rw [show halfShiftedGaussianTrigonometricIncrement =
      fun v => gaussianTrigonometricIncrement v + hardAcceptanceDrift by rfl]
  rw [integral_add integrable_gaussianTrigonometricIncrement (integrable_const _),
    integral_gaussianTrigonometricIncrement]
  simp only [integral_const]
  have hmass : (gaussianReal 0 (2 : ℝ≥0)).real Set.univ = 1 := by simp
  rw [hmass]
  unfold hardAcceptanceDrift
  ring

theorem integral_halfShiftedGaussianTrigonometricIncrement_neg :
    ∫ v : ℝ, halfShiftedGaussianTrigonometricIncrement v
        ∂gaussianReal 0 (2 : ℝ≥0) < 0 := by
  rw [integral_halfShiftedGaussianTrigonometricIncrement]
  exact neg_neg_of_pos hardAcceptanceDrift_pos

theorem integrable_exp_mul_halfShiftedGaussianTrigonometricIncrement (t : ℝ) :
    Integrable (fun v : ℝ =>
      Real.exp (t * halfShiftedGaussianTrigonometricIncrement v))
      (gaussianReal 0 (2 : ℝ≥0)) := by
  have h := (integrable_exp_mul_gaussianTrigonometricIncrement t).const_mul
    (Real.exp (t * hardAcceptanceDrift))
  convert h using 1
  ext v
  rw [halfShiftedGaussianTrigonometricIncrement, mul_add, Real.exp_add]
  ring

@[simp] theorem integrableExpSet_halfShiftedGaussianTrigonometricIncrement :
    integrableExpSet halfShiftedGaussianTrigonometricIncrement
        (gaussianReal 0 (2 : ℝ≥0)) = Set.univ := by
  ext t
  simp [integrableExpSet,
    integrable_exp_mul_halfShiftedGaussianTrigonometricIncrement]

/-- A positive fixed Chernoff parameter at the manuscript's negative linear
threshold. -/
theorem exists_pos_mgf_halfShiftedGaussianTrigonometricIncrement_lt_one :
    ∃ t : ℝ, 0 < t ∧
      mgf halfShiftedGaussianTrigonometricIncrement
        (gaussianReal 0 (2 : ℝ≥0)) t < 1 := by
  let μ : Measure ℝ := gaussianReal 0 (2 : ℝ≥0)
  let F : ℝ → ℝ := fun t =>
    mgf halfShiftedGaussianTrigonometricIncrement μ t - 1
  have hzero : (0 : ℝ) ∈ interior
      (integrableExpSet halfShiftedGaussianTrigonometricIncrement μ) := by
    simp [μ]
  have hderiv : HasDerivAt F
      (∫ v : ℝ, halfShiftedGaussianTrigonometricIncrement v ∂μ) 0 := by
    simpa [F] using (hasDerivAt_mgf
      (X := halfShiftedGaussianTrigonometricIncrement) (μ := μ) hzero).sub_const 1
  have hderivNeg : deriv F 0 < 0 := by
    rw [hderiv.deriv]
    simpa [μ] using integral_halfShiftedGaussianTrigonometricIncrement_neg
  have hFzero : F 0 = 0 := by simp [F, μ]
  have hevent : ∀ᶠ t in nhds (0 : ℝ), sign (F t) = sign (0 - t) :=
    eventually_nhdsWithin_sign_eq_of_deriv_neg hderivNeg hFzero
  rcases mem_nhds_iff_exists_Ioo_subset.mp hevent with ⟨a, b, hab, hsub⟩
  let t := b / 2
  have ht : 0 < t := by dsimp [t]; linarith [hab.2]
  have htin : t ∈ Set.Ioo a b := by
    constructor
    · exact hab.1.trans (by simpa using ht)
    · dsimp [t]
      linarith [hab.2]
  have hsign := hsub htin
  have hFneg : F t < 0 := by
    change sign (F t) = sign (0 - t) at hsign
    have hright : sign (0 - t) = (-1 : SignType) := sign_neg (by linarith)
    exact sign_eq_neg_one_iff.mp (hsign.trans hright)
  exact ⟨t, ht, by simpa [F] using hFneg⟩

/-- Direct product Chernoff bound at the manuscript's negative linear
threshold `-δ card`. -/
theorem independent_gaussianTrigonometric_sum_ge_negativeDrift_le_mgf_pow
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, Measure.map (X i) μ = gaussianReal 0 (2 : ℝ≥0))
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | -hardAcceptanceDrift * Fintype.card ι ≤
        ∑ i, gaussianTrigonometricIncrement (X i ω)} ≤
      (mgf halfShiftedGaussianTrigonometricIncrement
        (gaussianReal 0 (2 : ℝ≥0)) t) ^ Fintype.card ι := by
  let Y : ι → Ω → ℝ := fun i =>
    halfShiftedGaussianTrigonometricIncrement ∘ X i
  have hY : ∀ i, Measurable (Y i) := fun i =>
    continuous_halfShiftedGaussianTrigonometricIncrement.measurable.comp (hX i)
  have hYIndep : iIndepFun Y μ :=
    hIndep.comp (fun _ => halfShiftedGaussianTrigonometricIncrement)
      (fun _ => continuous_halfShiftedGaussianTrigonometricIncrement.measurable)
  have hIdentX (i : ι) : IdentDistrib (X i) id μ
      (gaussianReal 0 (2 : ℝ≥0)) := by
    refine ⟨(hX i).aemeasurable, measurable_id.aemeasurable, ?_⟩
    simpa using hLaw i
  have hIdentY (i : ι) : IdentDistrib (Y i)
      halfShiftedGaussianTrigonometricIncrement μ
      (gaussianReal 0 (2 : ℝ≥0)) := by
    simpa [Y, Function.comp_def] using
      (hIdentX i).comp continuous_halfShiftedGaussianTrigonometricIncrement.measurable
  have hInt : ∀ i, Integrable (fun ω => Real.exp (t * Y i ω)) μ := by
    intro i
    have hIdentExp := (hIdentY i).comp (measurable_const_mul t).exp
    exact hIdentExp.integrable_iff.mpr
      (integrable_exp_mul_halfShiftedGaussianTrigonometricIncrement t)
  have hMGF : ∀ i, mgf (Y i) μ t =
      mgf halfShiftedGaussianTrigonometricIncrement
        (gaussianReal 0 (2 : ℝ≥0)) t := by
    intro i
    exact mgf_congr_of_identDistrib (Y i)
      halfShiftedGaussianTrigonometricIncrement (hIdentY i) t
  have hchernoff := finite_iid_sum_nonnegative_le_mgf_pow
    hY hYIndep ht hInt hMGF
  have hevent : {ω | 0 ≤ (∑ i, Y i) ω} =
      {ω | -hardAcceptanceDrift * Fintype.card ι ≤
        ∑ i, gaussianTrigonometricIncrement (X i ω)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Finset.sum_apply, Y,
      Function.comp_apply, halfShiftedGaussianTrigonometricIncrement]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    constructor <;> intro h <;> linarith
  rw [hevent] at hchernoff
  exact hchernoff

/-- Universal exponential concentration at the exact negative threshold. -/
theorem exists_contraction_factor_for_independent_gaussianTrigonometric_negativeDrift
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, Measure.map (X i) μ = gaussianReal 0 (2 : ℝ≥0)) :
    ∃ t ρ : ℝ, 0 < t ∧ 0 ≤ ρ ∧ ρ < 1 ∧
      μ.real {ω | -hardAcceptanceDrift * Fintype.card ι ≤
        ∑ i, gaussianTrigonometricIncrement (X i ω)} ≤
        ρ ^ Fintype.card ι := by
  obtain ⟨t, ht, hcontract⟩ :=
    exists_pos_mgf_halfShiftedGaussianTrigonometricIncrement_lt_one
  let ρ := mgf halfShiftedGaussianTrigonometricIncrement
    (gaussianReal 0 (2 : ℝ≥0)) t
  refine ⟨t, ρ, ht, mgf_nonneg, hcontract, ?_⟩
  exact independent_gaussianTrigonometric_sum_ge_negativeDrift_le_mgf_pow
    hX hIndep hLaw ht

/-- The previous theorem instantiated on the non-first coordinates of a
finite product standard Gaussian.  Multiplication by `sqrt 2` gives each
coordinate the exact `N(0,2)` law used in the hard-potential formula. -/
theorem exists_contraction_factor_for_pi_scaledGaussian_tail
    (n : ℕ) :
    ∃ t ρ : ℝ, 0 < t ∧ 0 ≤ ρ ∧ ρ < 1 ∧
      (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 (1 : ℝ≥0))).real
        {ω | -hardAcceptanceDrift * n ≤
          ∑ j : Fin n, gaussianTrigonometricIncrement
            (Real.sqrt 2 * ω j.succ)} ≤ ρ ^ n := by
  let μ : Measure (Fin (n + 1) → ℝ) :=
    Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 (1 : ℝ≥0))
  let X : Fin n → (Fin (n + 1) → ℝ) → ℝ :=
    fun j ω => Real.sqrt 2 * ω j.succ
  have hX : ∀ j, Measurable (X j) := by
    intro j
    exact measurable_const.mul (measurable_pi_apply j.succ)
  have hCoord : iIndepFun
      (fun i : Fin (n + 1) => fun ω : Fin (n + 1) → ℝ => ω i) μ := by
    exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hTail : iIndepFun
      (fun j : Fin n => fun ω : Fin (n + 1) → ℝ => ω j.succ) μ := by
    exact hCoord.precomp (Fin.succ_injective n)
  have hIndep : iIndepFun X μ := by
    exact hTail.comp (fun _ v => Real.sqrt 2 * v)
      (fun _ => measurable_const_mul _)
  have hLaw : ∀ j, Measure.map (X j) μ = gaussianReal 0 (2 : ℝ≥0) := by
    intro j
    have heval : Measure.map
        (fun ω : Fin (n + 1) → ℝ => ω j.succ) μ =
          gaussianReal 0 (1 : ℝ≥0) := by
      simpa [μ] using
        (Measure.pi_map_eval
          (fun _ : Fin (n + 1) => gaussianReal 0 (1 : ℝ≥0)) j.succ)
    calc
      Measure.map (X j) μ =
          Measure.map (fun v : ℝ => Real.sqrt 2 * v)
            (Measure.map (fun ω : Fin (n + 1) → ℝ => ω j.succ) μ) := by
        simpa [X, Function.comp_def] using
          (Measure.map_map (measurable_const_mul (Real.sqrt 2))
            (measurable_pi_apply j.succ) (μ := μ)).symm
      _ = Measure.map (fun v : ℝ => Real.sqrt 2 * v)
          (gaussianReal 0 (1 : ℝ≥0)) := by rw [heval]
      _ = gaussianReal 0 (2 : ℝ≥0) := by
        rw [gaussianReal_map_const_mul]
        congr 1
        · simp
        · ext
          simp [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  simpa [μ, X] using
    (exists_contraction_factor_for_independent_gaussianTrigonometric_negativeDrift
      hX hIndep hLaw)

/-- Fixed-parameter version of the product-coordinate concentration bound. -/
theorem pi_scaledGaussian_tail_le_mgf_pow
    (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 (1 : ℝ≥0))).real
        {ω | -hardAcceptanceDrift * n ≤
          ∑ j : Fin n, gaussianTrigonometricIncrement
            (Real.sqrt 2 * ω j.succ)} ≤
      (mgf halfShiftedGaussianTrigonometricIncrement
        (gaussianReal 0 (2 : ℝ≥0)) t) ^ n := by
  let μ : Measure (Fin (n + 1) → ℝ) :=
    Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 (1 : ℝ≥0))
  let X : Fin n → (Fin (n + 1) → ℝ) → ℝ :=
    fun j ω => Real.sqrt 2 * ω j.succ
  have hX : ∀ j, Measurable (X j) := by
    intro j
    exact measurable_const.mul (measurable_pi_apply j.succ)
  have hCoord : iIndepFun
      (fun i : Fin (n + 1) => fun ω : Fin (n + 1) → ℝ => ω i) μ := by
    exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hTail : iIndepFun
      (fun j : Fin n => fun ω : Fin (n + 1) → ℝ => ω j.succ) μ := by
    exact hCoord.precomp (Fin.succ_injective n)
  have hIndep : iIndepFun X μ := by
    exact hTail.comp (fun _ v => Real.sqrt 2 * v)
      (fun _ => measurable_const_mul _)
  have hLaw : ∀ j, Measure.map (X j) μ = gaussianReal 0 (2 : ℝ≥0) := by
    intro j
    have heval : Measure.map
        (fun ω : Fin (n + 1) → ℝ => ω j.succ) μ =
          gaussianReal 0 (1 : ℝ≥0) := by
      simpa [μ] using
        (Measure.pi_map_eval
          (fun _ : Fin (n + 1) => gaussianReal 0 (1 : ℝ≥0)) j.succ)
    calc
      Measure.map (X j) μ =
          Measure.map (fun v : ℝ => Real.sqrt 2 * v)
            (Measure.map (fun ω : Fin (n + 1) → ℝ => ω j.succ) μ) := by
        simpa [X, Function.comp_def] using
          (Measure.map_map (measurable_const_mul (Real.sqrt 2))
            (measurable_pi_apply j.succ) (μ := μ)).symm
      _ = Measure.map (fun v : ℝ => Real.sqrt 2 * v)
          (gaussianReal 0 (1 : ℝ≥0)) := by rw [heval]
      _ = gaussianReal 0 (2 : ℝ≥0) := by
        rw [gaussianReal_map_const_mul]
        congr 1
        · simp
        · ext
          simp [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  simpa [μ, X] using
    (independent_gaussianTrigonometric_sum_ge_negativeDrift_le_mgf_pow
      hX hIndep hLaw ht)

/-- One pair of universal Chernoff constants works simultaneously in every
finite dimension. -/
theorem exists_universal_contraction_factor_for_pi_scaledGaussian_tail :
    ∃ t ρ : ℝ, 0 < t ∧ 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ n : ℕ,
        (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 (1 : ℝ≥0))).real
            {ω | -hardAcceptanceDrift * n ≤
              ∑ j : Fin n, gaussianTrigonometricIncrement
                (Real.sqrt 2 * ω j.succ)} ≤ ρ ^ n := by
  obtain ⟨t, ht, hcontract⟩ :=
    exists_pos_mgf_halfShiftedGaussianTrigonometricIncrement_lt_one
  let ρ := mgf halfShiftedGaussianTrigonometricIncrement
    (gaussianReal 0 (2 : ℝ≥0)) t
  refine ⟨t, ρ, ht, mgf_nonneg, hcontract, ?_⟩
  intro n
  exact pi_scaledGaussian_tail_le_mgf_pow n ht

/-- At an origin proposal written in product-Gaussian coordinates, the
hard-potential log ratio is bounded by the exact oscillatory tail sum. -/
theorem hard_malaLogRatio_zero_at_piInnovation_le
    (n : ℕ) (hn : 1 ≤ n) {m L h : ℝ}
    (hm : 0 < m) (hmL : m < L) (hh : 0 < h)
    (ω : Fin (n + 1) → ℝ) :
    let W := fixedStepHardFirstOrderPotential (d := n + 1) (by omega)
      hm hmL hh
    W.malaLogRatio h 0
        (Real.sqrt (2 * h) • WithLp.toLp 2 ω) ≤
      ((L - m) / 2) * h *
        ∑ j : Fin n, gaussianTrigonometricIncrement
          (Real.sqrt 2 * ω j.succ) := by
  dsimp only
  apply (hard_malaLogRatio_zero_le_shape_sum (by omega) hm hmL hh
    (Real.sqrt (2 * h) • WithLp.toLp 2 ω)).trans
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, if_pos, Fin.val_succ, Nat.succ_ne_zero,
    if_false, zero_add]
  have hs : Real.sqrt h ≠ 0 := (Real.sqrt_pos.2 hh).ne'
  have hratio : ∀ j : Fin n,
      (Real.sqrt (2 * h) • WithLp.toLp 2 ω : State (n + 1)) j.succ /
          Real.sqrt h = Real.sqrt 2 * ω j.succ := by
    intro j
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp [hs]
  simp_rw [hratio]
  change (∑ j : Fin n, ((L - m) / 2) * h *
      gaussianTrigonometricIncrement (Real.sqrt 2 * ω j.succ)) ≤ _
  rw [← Finset.mul_sum]

end

end UniformRandomMALA.Concrete
