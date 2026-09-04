import UniformRandomMALA.Prelude
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Gaussian trigonometric moments and concentration

Elementary Gaussian calculations used by the sticky-region obstruction for
fixed-step MALA.  The variance-two Gaussian is represented by
`gaussianReal 0 2`.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open Filter SignType
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

namespace Concrete

/-- The one-coordinate trigonometric contribution to the log Hastings
ratio at the origin. -/
def gaussianTrigonometricIncrement (v : ℝ) : ℝ :=
  Real.cos v - 1 + v * Real.sin v / 2

theorem continuous_gaussianTrigonometricIncrement :
    Continuous gaussianTrigonometricIncrement := by
  unfold gaussianTrigonometricIncrement
  fun_prop

/-- The characteristic-function calculation
`E[cos V] = exp (-1)` for `V ~ N(0,2)`. -/
theorem integral_cos_gaussianReal_zero_two :
    ∫ v : ℝ, Real.cos v ∂gaussianReal 0 (2 : ℝ≥0) = Real.exp (-1) := by
  have hint : Integrable
      (fun v : ℝ => Complex.exp ((v : ℂ) * Complex.I))
      (gaussianReal 0 (2 : ℝ≥0)) := by
    exact (integrable_const (1 : ℝ)).mono (by fun_prop) (by simp)
  have hre := integral_re hint
  have hchar := charFun_gaussianReal (μ := 0) (v := (2 : ℝ≥0)) (1 : ℝ)
  rw [charFun_apply_real] at hchar
  calc
    ∫ v : ℝ, Real.cos v ∂gaussianReal 0 (2 : ℝ≥0) =
        (∫ v : ℝ, Complex.exp ((v : ℂ) * Complex.I)
          ∂gaussianReal 0 (2 : ℝ≥0)).re := by
      simpa using hre
    _ = (Complex.exp (((1 : ℝ) * 0 * Complex.I) -
          (2 : ℝ≥0) * (1 : ℝ) ^ 2 / 2)).re := by
      simpa using congrArg Complex.re hchar
    _ = Real.exp (-1) := by
      push_cast
      ring_nf
      simpa using Complex.exp_ofReal_re (-1)

/-- The differentiated characteristic-function calculation
`E[V sin V] = 2 exp (-1)` for `V ~ N(0,2)`. -/
theorem integral_mul_sin_gaussianReal_zero_two :
    ∫ v : ℝ, v * Real.sin v ∂gaussianReal 0 (2 : ℝ≥0) =
      2 * Real.exp (-1) := by
  let μ : Measure ℝ := gaussianReal 0 (2 : ℝ≥0)
  have hz : Complex.I.re ∈ interior (integrableExpSet id μ) := by
    simp [μ]
  have hmgf : complexMGF id μ = fun z : ℂ => Complex.exp (z ^ 2) := by
    funext z
    rw [complexMGF_id_gaussianReal]
    congr 1
    push_cast
    ring
  have hderivIntegral := hasDerivAt_complexMGF (X := id) (μ := μ) hz
  rw [hmgf] at hderivIntegral
  have hsquare : HasDerivAt (fun z : ℂ => z ^ 2) (2 * Complex.I) Complex.I := by
    simpa using (hasDerivAt_pow 2 Complex.I)
  have hderivExplicit :
      HasDerivAt (fun z : ℂ => Complex.exp (z ^ 2))
        (Complex.exp (Complex.I ^ 2) * (2 * Complex.I)) Complex.I :=
    (Complex.hasDerivAt_exp (Complex.I ^ 2)).comp Complex.I hsquare
  have hcomplex := hderivIntegral.unique hderivExplicit
  have hint : Integrable
      (fun v : ℝ => (v : ℂ) * Complex.exp (Complex.I * (v : ℂ))) μ := by
    convert integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet
      (X := id) (μ := μ) hz 1 using 1
    all_goals simp [id]
  have him := integral_im hint
  have hcomplexIm := congrArg Complex.im hcomplex
  change ∫ v : ℝ, v * Real.sin v ∂μ = _
  calc
    ∫ v : ℝ, v * Real.sin v ∂μ =
        ∫ v : ℝ, ((v : ℂ) * Complex.exp (Complex.I * (v : ℂ))).im ∂μ := by
      apply integral_congr_ae
      filter_upwards with v
      rw [mul_comm Complex.I (v : ℂ)]
      simp [Complex.mul_im, Complex.exp_ofReal_mul_I_im]
    _ = (∫ v : ℝ, (v : ℂ) * Complex.exp (Complex.I * (v : ℂ)) ∂μ).im := him
    _ = (Complex.exp (Complex.I ^ 2) * (2 * Complex.I)).im := hcomplexIm
    _ = 2 * Real.exp (-1) := by
      rw [show Complex.I ^ 2 = (-1 : ℂ) by simp]
      simpa [mul_comm] using congrArg (fun x : ℝ => 2 * x) (Complex.exp_ofReal_re (-1))

/-- The exact mean of the trigonometric increment. -/
theorem integral_gaussianTrigonometricIncrement :
    ∫ v : ℝ, gaussianTrigonometricIncrement v
        ∂gaussianReal 0 (2 : ℝ≥0) = 2 / Real.exp 1 - 1 := by
  let μ : Measure ℝ := gaussianReal 0 (2 : ℝ≥0)
  have hcos : Integrable Real.cos μ :=
    (integrable_const (1 : ℝ)).mono (by fun_prop)
      (by filter_upwards with v; simpa using Real.abs_cos_le_one v)
  have hone : Integrable (fun _ : ℝ => (1 : ℝ)) μ := integrable_const 1
  have hid : Integrable id μ := by
    exact (memLp_id_gaussianReal (μ := 0) (v := (2 : ℝ≥0)) 1).integrable (by simp)
  have hvsin : Integrable (fun v : ℝ => v * Real.sin v) μ := by
    have := hid.mul_bdd Real.continuous_sin.aestronglyMeasurable
      (by filter_upwards with v; simpa using Real.abs_sin_le_one v)
    simpa [id] using this
  change ∫ v : ℝ, (Real.cos v - 1) + (v * Real.sin v) / 2 ∂μ = _
  have hadd := integral_add (hcos.sub hone) (hvsin.div_const 2)
  have hsub := integral_sub hcos hone
  simp only [Pi.sub_apply] at hadd hsub
  calc
    ∫ v : ℝ, (Real.cos v - 1) + (v * Real.sin v) / 2 ∂μ =
        (∫ v : ℝ, Real.cos v - 1 ∂μ) +
          ∫ v : ℝ, (v * Real.sin v) / 2 ∂μ := by
      simpa only [Pi.add_apply, Pi.sub_apply] using hadd
    _ = 2 / Real.exp 1 - 1 := by
      rw [hsub, integral_div, integral_cos_gaussianReal_zero_two,
        integral_mul_sin_gaussianReal_zero_two]
      simp [μ]
      rw [Real.exp_neg]
      field_simp [Real.exp_ne_zero]
      ring

/-- The mean is strictly negative: `2/e - 1 < 0`. -/
theorem integral_gaussianTrigonometricIncrement_neg :
    ∫ v : ℝ, gaussianTrigonometricIncrement v
        ∂gaussianReal 0 (2 : ℝ≥0) < 0 := by
  rw [integral_gaussianTrigonometricIncrement]
  have heTwo : 2 < Real.exp 1 := by
    convert Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0) using 1
    all_goals norm_num
  have hePos : 0 < Real.exp 1 := Real.exp_pos 1
  apply sub_neg.mpr
  exact (div_lt_one hePos).2 heTwo

/-- A linear-growth bound for the trigonometric increment.  This is the
elementary domination estimate that makes its MGF finite near zero (in fact,
everywhere) under a Gaussian law. -/
theorem abs_gaussianTrigonometricIncrement_le (v : ℝ) :
    |gaussianTrigonometricIncrement v| ≤ 2 + |v| / 2 := by
  rw [gaussianTrigonometricIncrement]
  calc
    |Real.cos v - 1 + v * Real.sin v / 2| ≤
        |Real.cos v - 1| + |v * Real.sin v / 2| := abs_add_le _ _
    _ ≤ (|Real.cos v| + 1) + |v| / 2 := by
      gcongr
      · simpa using abs_sub (Real.cos v) 1
      · rw [abs_div, abs_mul]
        norm_num
        exact (div_le_div_iff_of_pos_right zero_lt_two).2
          (mul_le_of_le_one_right (abs_nonneg v) (Real.abs_sin_le_one v))
    _ ≤ 2 + |v| / 2 := by
      linarith [Real.abs_cos_le_one v]

/-- The exponential of the linear envelope is integrable under `N(0,2)`. -/
theorem integrable_exp_two_add_abs_half_gaussianReal :
    Integrable (fun v : ℝ => Real.exp (2 + |v| / 2))
      (gaussianReal 0 (2 : ℝ≥0)) := by
  let μ : Measure ℝ := gaussianReal 0 (2 : ℝ≥0)
  have hpos : Integrable (fun v : ℝ => Real.exp ((1 / 2 : ℝ) * v)) μ := by
    simpa [μ] using integrable_exp_mul_gaussianReal (μ := 0) (v := (2 : ℝ≥0)) (1 / 2)
  have hneg : Integrable (fun v : ℝ => Real.exp ((-1 / 2 : ℝ) * v)) μ := by
    simpa [μ] using integrable_exp_mul_gaussianReal (μ := 0) (v := (2 : ℝ≥0)) (-1 / 2)
  have hdom : Integrable
      (fun v : ℝ => Real.exp 2 *
        (Real.exp ((1 / 2 : ℝ) * v) + Real.exp ((-1 / 2 : ℝ) * v))) μ := by
    exact (hpos.add hneg).const_mul (Real.exp 2)
  refine hdom.mono (by fun_prop) ?_
  filter_upwards with v
  change |Real.exp (2 + |v| / 2)| ≤
    |Real.exp 2 * (Real.exp ((1 / 2 : ℝ) * v) + Real.exp ((-1 / 2 : ℝ) * v))|
  rw [abs_of_pos (Real.exp_pos _)]
  rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
    (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))]
  rw [Real.exp_add]
  by_cases hv : 0 ≤ v
  · rw [abs_of_nonneg hv]
    have hp : 0 ≤ Real.exp ((-1 / 2 : ℝ) * v) := (Real.exp_pos _).le
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 2).le
    rw [show v / 2 = (1 / 2 : ℝ) * v by ring]
    exact le_add_of_nonneg_right hp
  · rw [abs_of_neg (lt_of_not_ge hv)]
    have hp : 0 ≤ Real.exp ((1 / 2 : ℝ) * v) := (Real.exp_pos _).le
    have heq : (-v) / 2 = (-1 / 2 : ℝ) * v := by ring
    rw [heq]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 2).le
    exact le_add_of_nonneg_left hp

/-- Every real exponential parameter is integrable for the increment under
`N(0,2)`.  The proof reduces arbitrary parameters to Gaussian linear
exponential moments using `|A(v)| ≤ 2 + |v|/2`. -/
theorem integrable_exp_mul_gaussianTrigonometricIncrement (t : ℝ) :
    Integrable (fun v : ℝ =>
      Real.exp (t * gaussianTrigonometricIncrement v))
      (gaussianReal 0 (2 : ℝ≥0)) := by
  let c := max 1 |t|
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hpos : Integrable (fun v : ℝ => Real.exp ((c / 2) * v))
      (gaussianReal 0 (2 : ℝ≥0)) := by
    simpa using integrable_exp_mul_gaussianReal
      (μ := 0) (v := (2 : ℝ≥0)) (c / 2)
  have hneg : Integrable (fun v : ℝ => Real.exp ((-c / 2) * v))
      (gaussianReal 0 (2 : ℝ≥0)) := by
    simpa using integrable_exp_mul_gaussianReal
      (μ := 0) (v := (2 : ℝ≥0)) (-c / 2)
  have hdom : Integrable (fun v : ℝ => Real.exp (2 * c) *
      (Real.exp ((c / 2) * v) + Real.exp ((-c / 2) * v)))
      (gaussianReal 0 (2 : ℝ≥0)) :=
    (hpos.add hneg).const_mul (Real.exp (2 * c))
  refine hdom.mono
    ((Real.continuous_exp.comp
      (continuous_const.mul continuous_gaussianTrigonometricIncrement)).aestronglyMeasurable) ?_
  filter_upwards with v
  change |Real.exp (t * gaussianTrigonometricIncrement v)| ≤
    |Real.exp (2 * c) *
      (Real.exp ((c / 2) * v) + Real.exp ((-c / 2) * v))|
  rw [abs_of_pos (Real.exp_pos _)]
  rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
    (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))]
  apply (Real.exp_le_exp.mpr ?_).trans
    (show Real.exp (c * (2 + |v| / 2)) ≤ _ by
      rw [mul_add, Real.exp_add]
      by_cases hv : 0 ≤ v
      · rw [abs_of_nonneg hv]
        have hp : 0 ≤ Real.exp ((-c / 2) * v) := (Real.exp_pos _).le
        rw [show c * 2 = 2 * c by ring]
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos (2 * c)).le
        rw [show c * (v / 2) = (c / 2) * v by ring]
        exact le_add_of_nonneg_right hp
      · rw [abs_of_neg (lt_of_not_ge hv)]
        have hp : 0 ≤ Real.exp ((c / 2) * v) := (Real.exp_pos _).le
        have heq : c * (-v / 2) = (-c / 2) * v := by ring
        rw [heq]
        rw [show c * 2 = 2 * c by ring]
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos (2 * c)).le
        exact le_add_of_nonneg_left hp)
  calc
    t * gaussianTrigonometricIncrement v ≤
        |t * gaussianTrigonometricIncrement v| := le_abs_self _
    _ = |t| * |gaussianTrigonometricIncrement v| := abs_mul _ _
    _ ≤ c * (2 + |v| / 2) := by
      apply mul_le_mul (le_max_right 1 |t|) (abs_gaussianTrigonometricIncrement_le v)
      · positivity
      · positivity

@[simp] theorem integrableExpSet_gaussianTrigonometricIncrement :
    integrableExpSet gaussianTrigonometricIncrement
        (gaussianReal 0 (2 : ℝ≥0)) = Set.univ := by
  ext t
  simp [integrableExpSet, integrable_exp_mul_gaussianTrigonometricIncrement]

/-- There is a positive, fixed exponential parameter for which the
one-coordinate MGF is strictly contractive.  This is obtained directly from
the exact negative mean and differentiability of the MGF at zero. -/
theorem exists_pos_mgf_gaussianTrigonometricIncrement_lt_one :
    ∃ t : ℝ, 0 < t ∧
      mgf gaussianTrigonometricIncrement (gaussianReal 0 (2 : ℝ≥0)) t < 1 := by
  let μ : Measure ℝ := gaussianReal 0 (2 : ℝ≥0)
  let F : ℝ → ℝ := fun t => mgf gaussianTrigonometricIncrement μ t - 1
  have hzero : (0 : ℝ) ∈ interior
      (integrableExpSet gaussianTrigonometricIncrement μ) := by simp [μ]
  have hderiv : HasDerivAt F
      (∫ v : ℝ, gaussianTrigonometricIncrement v ∂μ) 0 := by
    simpa [F] using (hasDerivAt_mgf
      (X := gaussianTrigonometricIncrement) (μ := μ) hzero).sub_const 1
  have hderivNeg : deriv F 0 < 0 := by
    rw [hderiv.deriv]
    simpa [μ] using integral_gaussianTrigonometricIncrement_neg
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

/-- A finite-product Chernoff bound in the exact form needed below.  If a
finite family is independent, has a common MGF value `ρ` at a positive
parameter, and the exponential moments are integrable, then the probability
that its sum is nonnegative is at most `ρ` to the number of coordinates. -/
theorem finite_iid_sum_nonnegative_le_mgf_pow
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : ι → Ω → ℝ} (hY : ∀ i, Measurable (Y i))
    (hIndep : iIndepFun Y μ) {t ρ : ℝ} (ht : 0 < t)
    (hInt : ∀ i, Integrable (fun ω => Real.exp (t * Y i ω)) μ)
    (hMGF : ∀ i, mgf (Y i) μ t = ρ) :
    μ.real {ω | 0 ≤ (∑ i, Y i) ω} ≤ ρ ^ Fintype.card ι := by
  classical
  have hSumInt : Integrable (fun ω => Real.exp (t * (∑ i, Y i) ω)) μ := by
    simpa using hIndep.integrable_exp_mul_sum hY
      (s := Finset.univ) (fun i _ => hInt i)
  calc
    μ.real {ω | 0 ≤ (∑ i, Y i) ω} ≤
        Real.exp (-t * 0) * mgf (∑ i, Y i) μ t :=
      measure_ge_le_exp_mul_mgf (X := ∑ i, Y i) 0 ht.le hSumInt
    _ = ρ ^ Fintype.card ι := by
      rw [hIndep.mgf_sum hY Finset.univ]
      simp [hMGF]

/-- Chernoff factorization for independent `N(0,2)` coordinates after
applying `gaussianTrigonometricIncrement`.  The right side is a strict
exponential contraction whenever `t` is chosen using
`exists_pos_mgf_gaussianTrigonometricIncrement_lt_one`. -/
theorem independent_gaussianTrigonometric_sum_nonnegative_le_mgf_pow
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, Measure.map (X i) μ = gaussianReal 0 (2 : ℝ≥0))
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | 0 ≤ ∑ i, gaussianTrigonometricIncrement (X i ω)} ≤
      (mgf gaussianTrigonometricIncrement
        (gaussianReal 0 (2 : ℝ≥0)) t) ^ Fintype.card ι := by
  let Y : ι → Ω → ℝ := fun i => gaussianTrigonometricIncrement ∘ X i
  have hY : ∀ i, Measurable (Y i) := fun i =>
    continuous_gaussianTrigonometricIncrement.measurable.comp (hX i)
  have hYIndep : iIndepFun Y μ :=
    hIndep.comp (fun _ => gaussianTrigonometricIncrement)
      (fun _ => continuous_gaussianTrigonometricIncrement.measurable)
  have hIdentX (i : ι) : IdentDistrib (X i) id μ
      (gaussianReal 0 (2 : ℝ≥0)) := by
    refine ⟨(hX i).aemeasurable, measurable_id.aemeasurable, ?_⟩
    simpa using hLaw i
  have hIdentY (i : ι) : IdentDistrib (Y i) gaussianTrigonometricIncrement μ
      (gaussianReal 0 (2 : ℝ≥0)) := by
    simpa [Y, Function.comp_def] using
      (hIdentX i).comp continuous_gaussianTrigonometricIncrement.measurable
  have hInt : ∀ i, Integrable (fun ω => Real.exp (t * Y i ω)) μ := by
    intro i
    have hIdentExp := (hIdentY i).comp (measurable_const_mul t).exp
    exact hIdentExp.integrable_iff.mpr
      (integrable_exp_mul_gaussianTrigonometricIncrement t)
  have hMGF : ∀ i, mgf (Y i) μ t =
      mgf gaussianTrigonometricIncrement (gaussianReal 0 (2 : ℝ≥0)) t := by
    intro i
    exact mgf_congr_of_identDistrib (Y i) gaussianTrigonometricIncrement (hIdentY i) t
  simpa [Y, Function.comp_def] using
    finite_iid_sum_nonnegative_le_mgf_pow hY hYIndep ht hInt hMGF

/-- A self-contained exponential concentration statement: for any finite
independent family of variance-two centered Gaussians there is a universal
contraction factor `ρ < 1` (independent of the family and its cardinality)
whose cardinality-th power bounds the nonnegative-sum event. -/
theorem exists_contraction_factor_for_independent_gaussianTrigonometric_sum
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, Measure.map (X i) μ = gaussianReal 0 (2 : ℝ≥0)) :
    ∃ t ρ : ℝ, 0 < t ∧ 0 ≤ ρ ∧ ρ < 1 ∧
      μ.real {ω | 0 ≤ ∑ i, gaussianTrigonometricIncrement (X i ω)} ≤
        ρ ^ Fintype.card ι := by
  obtain ⟨t, ht, hcontract⟩ :=
    exists_pos_mgf_gaussianTrigonometricIncrement_lt_one
  let ρ := mgf gaussianTrigonometricIncrement
    (gaussianReal 0 (2 : ℝ≥0)) t
  refine ⟨t, ρ, ht, mgf_nonneg, hcontract, ?_⟩
  exact independent_gaussianTrigonometric_sum_nonnegative_le_mgf_pow
    hX hIndep hLaw ht

end Concrete

end

end UniformRandomMALA
