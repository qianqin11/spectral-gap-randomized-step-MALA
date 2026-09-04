import UniformRandomMALA.Concrete.StandardGaussianShift
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Hom.Set
import Mathlib.Topology.Order.AtTopBotIxx
import Mathlib.Topology.Piecewise

/-!
# The Gaussian normal profile

On the open unit interval the normal profile is

`I(s) = phi(Phi⁻¹(s))`.

This file constructs the inverse CDF as an order isomorphism and proves the
calculus identities used by the Gaussian OU interpolation:

`I'(s) = -Phi⁻¹(s)`, `I''(s) = -1 / I(s)`, and `I(s) * I''(s) = -1`.

All inverse and derivative statements are restricted to `0 < s < 1`, so no
extended-real endpoint convention is hidden in the definitions.
-/

namespace UniformRandomMALA

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal Topology Interval

noncomputable section

namespace Concrete

/-- The standard Gaussian CDF is an antiderivative of its density. -/
theorem normalCDFReal_eq_zero_add_integral (x : ℝ) :
    normalCDFReal x = normalCDFReal 0 + ∫ y in (0 : ℝ)..x, normalDensity y := by
  by_cases hx : 0 ≤ x
  · have h := normalCDFReal_sub_eq_intervalIntegral hx
    linarith
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have h := normalCDFReal_sub_eq_intervalIntegral hx'
    rw [intervalIntegral.integral_symm] at h
    linarith

/-- The derivative of the standard Gaussian CDF is its density. -/
theorem hasDerivAt_normalCDFReal (x : ℝ) :
    HasDerivAt normalCDFReal (normalDensity x) x := by
  rw [show normalCDFReal = fun z =>
      normalCDFReal 0 + ∫ y in (0 : ℝ)..z, normalDensity y by
    funext z
    exact normalCDFReal_eq_zero_add_integral z]
  exact (continuous_normalDensity.integral_hasStrictDerivAt 0 x).hasDerivAt.const_add
    (normalCDFReal 0)

/-- The real-valued standard Gaussian CDF is strictly increasing. -/
theorem strictMono_normalCDFReal : StrictMono normalCDFReal := by
  intro a b hab
  have hint : 0 < ∫ x in a..b, normalDensity x := by
    apply intervalIntegral.integral_pos hab continuous_normalDensity.continuousOn
    · intro x _
      exact normalDensity_nonneg x
    · refine ⟨(a + b) / 2, ?_, normalDensity_pos _⟩
      constructor <;> linarith
  have hdiff := normalCDFReal_sub_eq_intervalIntegral hab.le
  linarith

lemma normalCDFReal_pos (x : ℝ) : 0 < normalCDFReal x := by
  by_cases hx : 0 ≤ x
  · calc
      0 < normalCDFReal 0 := by
        rw [normalCDFReal, normalCDF_zero]
        norm_num
      _ ≤ normalCDFReal x := by
        rw [← cdf_standardGaussian_eq_normalCDFReal,
          ← cdf_standardGaussian_eq_normalCDFReal]
        exact monotone_cdf standardGaussianMeasure hx
  · have hneg : 0 ≤ -x := by linarith
    have hmills := mills_lower (-x) hneg
    have hpos : 0 < normalDensity (-x) / (1 + -x) :=
      div_pos (normalDensity_pos _) (by linarith)
    have htail : 0 < normalTailReal (-x) := hpos.trans_le hmills
    calc
      0 < normalTailReal (-x) := htail
      _ = normalCDFReal x := by
        simpa using (normalCDFReal_neg (-x)).symm

lemma normalTailReal_pos (x : ℝ) : 0 < normalTailReal x := by
  rw [← normalCDFReal_neg]
  exact normalCDFReal_pos (-x)

lemma normalCDFReal_add_tail (x : ℝ) :
    normalCDFReal x + normalTailReal x = 1 := by
  unfold normalCDFReal normalTailReal
  rw [← ENNReal.toReal_add
    ((normalCDF_le_one x).trans_lt ENNReal.one_lt_top).ne
    ((normalTail_le_one x).trans_lt ENNReal.one_lt_top).ne,
    normalCDF_add_tail, ENNReal.toReal_one]

lemma normalCDFReal_lt_one (x : ℝ) : normalCDFReal x < 1 := by
  have hsum := normalCDFReal_add_tail x
  have htail := normalTailReal_pos x
  linarith

/-- The standard Gaussian CDF, with its range bundled as `(0,1)`. -/
def standardGaussianCDFIoo (x : ℝ) : Set.Ioo (0 : ℝ) 1 :=
  ⟨normalCDFReal x, normalCDFReal_pos x, normalCDFReal_lt_one x⟩

theorem strictMono_standardGaussianCDFIoo :
    StrictMono standardGaussianCDFIoo := by
  intro a b hab
  exact strictMono_normalCDFReal hab

theorem surjective_standardGaussianCDFIoo :
    Function.Surjective standardGaussianCDFIoo := by
  intro s
  refine ⟨lowerQuantile standardGaussianMeasure s, ?_⟩
  apply Subtype.ext
  change normalCDFReal (lowerQuantile standardGaussianMeasure s) = s
  rw [← cdf_standardGaussian_eq_normalCDFReal]
  exact cdf_lowerQuantile_eq standardGaussianMeasure
    continuous_standardGaussianCDF s.2.1 s.2.2

/-- The standard Gaussian CDF as an order isomorphism `ℝ ≃o (0,1)`. -/
def normalCDFOrderIso : ℝ ≃o Set.Ioo (0 : ℝ) 1 :=
  StrictMono.orderIsoOfSurjective standardGaussianCDFIoo
    strictMono_standardGaussianCDFIoo surjective_standardGaussianCDFIoo

@[simp] theorem normalCDFOrderIso_apply (x : ℝ) :
    (normalCDFOrderIso x : ℝ) = normalCDFReal x := rfl

theorem normalCDFOrderIso_symm_apply (s : Set.Ioo (0 : ℝ) 1) :
    normalCDFOrderIso.symm s = lowerQuantile standardGaussianMeasure s := by
  apply normalCDFOrderIso.injective
  rw [normalCDFOrderIso.apply_symm_apply]
  apply Subtype.ext
  change (s : ℝ) = normalCDFReal (lowerQuantile standardGaussianMeasure s)
  rw [← cdf_standardGaussian_eq_normalCDFReal]
  exact (cdf_lowerQuantile_eq standardGaussianMeasure
    continuous_standardGaussianCDF s.2.1 s.2.2).symm

/-- Symmetry of the standard Gaussian quantile on the open unit interval. -/
theorem lowerQuantile_standardGaussian_one_sub
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    lowerQuantile standardGaussianMeasure (1 - s) =
      -lowerQuantile standardGaussianMeasure s := by
  let u : Set.Ioo (0 : ℝ) 1 := ⟨s, hs⟩
  have hsub : 1 - s ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hs.1, hs.2]
  let v : Set.Ioo (0 : ℝ) 1 := ⟨1 - s, hsub⟩
  rw [← normalCDFOrderIso_symm_apply v, ← normalCDFOrderIso_symm_apply u]
  apply normalCDFOrderIso.injective
  rw [normalCDFOrderIso.apply_symm_apply]
  apply Subtype.ext
  change 1 - s = normalCDFReal (-normalCDFOrderIso.symm u)
  rw [normalCDFReal_neg]
  have hcdf := congrArg Subtype.val (normalCDFOrderIso.apply_symm_apply u)
  change normalCDFReal (normalCDFOrderIso.symm u) = s at hcdf
  linarith [normalCDFReal_add_tail (normalCDFOrderIso.symm u)]

/-- The generalized inverse is continuous at every interior probability. -/
theorem continuousAt_lowerQuantile_standardGaussian
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    ContinuousAt (lowerQuantile standardGaussianMeasure) s := by
  have hrestrict : Continuous
      ((Set.Ioo (0 : ℝ) 1).domRestrict
        (lowerQuantile standardGaussianMeasure)) := by
    have h := normalCDFOrderIso.toHomeomorph.continuous_invFun
    convert h using 1
    funext u
    exact (normalCDFOrderIso_symm_apply u).symm
  have hOn : ContinuousOn (lowerQuantile standardGaussianMeasure)
      (Set.Ioo (0 : ℝ) 1) :=
    continuousOn_iff_continuous_domRestrict.mpr hrestrict
  exact hOn.continuousAt (isOpen_Ioo.mem_nhds hs)

/-- The derivative of the interior Gaussian quantile. -/
theorem hasDerivAt_lowerQuantile_standardGaussian
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (lowerQuantile standardGaussianMeasure)
      (normalDensity (lowerQuantile standardGaussianMeasure s))⁻¹ s := by
  apply HasDerivAt.of_local_left_inverse
    (f := cdf standardGaussianMeasure)
    (g := lowerQuantile standardGaussianMeasure)
    (continuousAt_lowerQuantile_standardGaussian hs)
    (by
      apply (hasDerivAt_normalCDFReal _).congr_of_eventuallyEq
      exact Eventually.of_forall cdf_standardGaussian_eq_normalCDFReal)
    (normalDensity_pos _).ne'
  filter_upwards [isOpen_Ioo.eventually_mem hs] with u hu
  exact cdf_lowerQuantile_eq standardGaussianMeasure
    continuous_standardGaussianCDF hu.1 hu.2

/-- The Gaussian normal profile `I(s) = phi(Phi⁻¹(s))`. -/
def normalProfile (s : ℝ) : ℝ :=
  normalDensity (lowerQuantile standardGaussianMeasure s)

lemma normalProfile_pos {s : ℝ} (_hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    0 < normalProfile s := by
  exact normalDensity_pos _

/-- The normal profile is symmetric about `1/2`. -/
theorem normalProfile_one_sub {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    normalProfile (1 - s) = normalProfile s := by
  unfold normalProfile
  rw [lowerQuantile_standardGaussian_one_sub hs]
  unfold normalDensity ProbabilityTheory.gaussianPDFReal
  congr 3
  ring

/-- The standard Gaussian quantile tends to positive infinity as its
probability argument approaches one through `(0,1)`. -/
theorem lowerQuantile_tendsto_atTop_Ioo :
    Tendsto (fun s : Set.Ioo (0 : ℝ) 1 =>
      lowerQuantile standardGaussianMeasure (s : ℝ)) atTop atTop := by
  apply normalCDFOrderIso.symm.tendsto_atTop.congr'
  exact Eventually.of_forall fun s => normalCDFOrderIso_symm_apply s

/-- The standard Gaussian quantile tends to negative infinity as its
probability argument approaches zero through `(0,1)`. -/
theorem lowerQuantile_tendsto_atBot_Ioo :
    Tendsto (fun s : Set.Ioo (0 : ℝ) 1 =>
      lowerQuantile standardGaussianMeasure (s : ℝ)) atBot atBot := by
  apply normalCDFOrderIso.symm.tendsto_atBot.congr'
  exact Eventually.of_forall fun s => normalCDFOrderIso_symm_apply s

/-- The normal profile vanishes at the right endpoint of the unit interval. -/
theorem normalProfile_tendsto_one_left :
    Tendsto normalProfile (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by
  rw [← tendsto_comp_coe_Ioo_atTop (show (0 : ℝ) < 1 by norm_num)]
  exact normalDensity_tendsto_atTop.comp lowerQuantile_tendsto_atTop_Ioo

/-- The normal profile vanishes at the left endpoint of the unit interval. -/
theorem normalProfile_tendsto_zero_right :
    Tendsto normalProfile (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  rw [← tendsto_comp_coe_Ioo_atBot (show (0 : ℝ) < 1 by norm_num)]
  exact normalDensity_tendsto_atBot.comp lowerQuantile_tendsto_atBot_Ioo

/-- The normal profile with its canonical endpoint values, extended by zero
outside the unit interval. -/
def normalProfileClosed (s : ℝ) : ℝ :=
  if s ∈ Set.Ioo (0 : ℝ) 1 then normalProfile s else 0

theorem normalProfileClosed_eq_normalProfile
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    normalProfileClosed s = normalProfile s := by
  simp [normalProfileClosed, hs]

@[simp] theorem normalProfileClosed_zero : normalProfileClosed 0 = 0 := by
  simp [normalProfileClosed]

@[simp] theorem normalProfileClosed_one : normalProfileClosed 1 = 0 := by
  simp [normalProfileClosed]

theorem normalProfileClosed_nonneg (s : ℝ) :
    0 ≤ normalProfileClosed s := by
  by_cases hs : s ∈ Set.Ioo (0 : ℝ) 1
  · rw [normalProfileClosed_eq_normalProfile hs]
    exact (normalProfile_pos hs).le
  · simp [normalProfileClosed, hs]

/-- A uniform elementary bound for the closed normal profile. -/
theorem normalProfileClosed_le_inv_sqrt_two_pi (s : ℝ) :
    normalProfileClosed s ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by
  by_cases hs : s ∈ Set.Ioo (0 : ℝ) 1
  · rw [normalProfileClosed_eq_normalProfile hs]
    unfold normalProfile
    rw [normalDensity_def]
    have hexp : Real.exp
        (-lowerQuantile standardGaussianMeasure s ^ 2 / 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [sq_nonneg (lowerQuantile standardGaussianMeasure s)]
    have hmul := mul_le_mul_of_nonneg_left hexp
      (inv_nonneg.mpr (Real.sqrt_nonneg (2 * Real.pi)))
    simpa only [mul_one] using hmul
  · simp [normalProfileClosed, hs, inv_nonneg.mpr (Real.sqrt_nonneg _)]

/-- The canonical closed normal profile is continuous, including at both
singular endpoints. -/
theorem continuous_normalProfileClosed : Continuous normalProfileClosed := by
  unfold normalProfileClosed
  apply continuous_if'
  · intro a ha
    change a ∈ frontier (Set.Ioo (0 : ℝ) 1) at ha
    rw [frontier_Ioo (show (0 : ℝ) < 1 by norm_num)] at ha
    rcases ha with (rfl | rfl)
    · simp only [Set.mem_Ioo, lt_self_iff_false, false_and, ↓reduceIte]
      change Tendsto normalProfile
        (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds 0)
      exact (normalProfile_tendsto_zero_right).mono_left
        (nhdsWithin_mono _ Set.Ioo_subset_Ioi_self)
    · simp only [Set.mem_Ioo, lt_self_iff_false, and_false, ↓reduceIte]
      change Tendsto normalProfile
        (nhdsWithin (1 : ℝ) (Set.Ioo 0 1)) (nhds 0)
      exact (normalProfile_tendsto_one_left).mono_left
        (nhdsWithin_mono _ Set.Ioo_subset_Iio_self)
  · intro a ha
    change a ∈ frontier (Set.Ioo (0 : ℝ) 1) at ha
    rw [frontier_Ioo (show (0 : ℝ) < 1 by norm_num)] at ha
    rcases ha with (rfl | rfl)
    · simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ))
        (nhdsWithin (0 : ℝ) {x | x ∉ Set.Ioo (0 : ℝ) 1}) (nhds 0))
    · simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ))
        (nhdsWithin (1 : ℝ) {x | x ∉ Set.Ioo (0 : ℝ) 1}) (nhds 0))
  · intro a ha
    exact (continuous_normalDensity.continuousAt.comp
      (continuousAt_lowerQuantile_standardGaussian ha)).continuousWithinAt
  · exact continuous_const.continuousOn

/-- First normal-profile identity: `I'(s) = -Phi⁻¹(s)`. -/
theorem hasDerivAt_normalProfile
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt normalProfile
      (-lowerQuantile standardGaussianMeasure s) s := by
  let q := lowerQuantile standardGaussianMeasure s
  have hcomp := (hasDerivAt_normalDensity q).comp s
    (hasDerivAt_lowerQuantile_standardGaussian hs)
  have hne : normalDensity (lowerQuantile standardGaussianMeasure s) ≠ 0 :=
    (normalDensity_pos _).ne'
  have hcoeff :
      -q * normalDensity q *
          (normalDensity (lowerQuantile standardGaussianMeasure s))⁻¹ =
        -lowerQuantile standardGaussianMeasure s := by
    dsimp only [q]
    field_simp
  have hcomp' := hcomp.congr_deriv hcoeff
  apply hcomp'.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun _ => rfl

theorem deriv_normalProfile
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    deriv normalProfile s = -lowerQuantile standardGaussianMeasure s :=
  (hasDerivAt_normalProfile hs).deriv

/-- Derivative of the first-profile derivative on `(0,1)`. -/
theorem hasDerivAt_neg_lowerQuantile_standardGaussian
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (-(lowerQuantile standardGaussianMeasure))
      (-(normalProfile s)⁻¹) s := by
  simpa only [normalProfile] using
    (hasDerivAt_lowerQuantile_standardGaussian hs).neg

/-- Second normal-profile identity: `I''(s) = -1/I(s)`. -/
theorem hasDerivAt_deriv_normalProfile
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (deriv normalProfile) (-(normalProfile s)⁻¹) s := by
  apply (hasDerivAt_neg_lowerQuantile_standardGaussian hs).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.eventually_mem hs] with u hu
  exact deriv_normalProfile hu

theorem deriv_succ_normalProfile
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (deriv normalProfile) s = -(normalProfile s)⁻¹ :=
  (hasDerivAt_deriv_normalProfile hs).deriv

/-- The scalar identity used in the OU Bochner calculation. -/
theorem normalProfile_mul_secondDeriv
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    normalProfile s * deriv (deriv normalProfile) s = -1 := by
  rw [deriv_succ_normalProfile hs]
  have hne : normalProfile s ≠ 0 := (normalProfile_pos hs).ne'
  field_simp

/-- The normal profile is strictly concave on its nonsingular domain. -/
theorem strictConcaveOn_normalProfile :
    StrictConcaveOn ℝ (Set.Ioo (0 : ℝ) 1) normalProfile := by
  apply strictConcaveOn_of_deriv2_neg' (convex_Ioo (𝕜 := ℝ) 0 1)
  · intro x hx
    exact (hasDerivAt_normalProfile hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [show (deriv^[2] normalProfile) x = deriv (deriv normalProfile) x by rfl]
    rw [deriv_succ_normalProfile hx]
    exact neg_neg_iff_pos.mpr (inv_pos.mpr (normalProfile_pos hx))

end Concrete

end

end UniformRandomMALA
