import UniformRandomMALA.Concrete.GaussianMills
import UniformRandomMALA.Concrete.Quantile
import UniformRandomMALA.Concrete.SeparatedSets
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The elementary standard-Gaussian shift bound

This file discharges the one-dimensional Gaussian input used after
Bakry--Ledoux.  The proof uses only the Gaussian density formula, the Mills
bounds proved in `GaussianMills`, elementary interval integration, and the
generalized-inverse lemma from `Quantile`.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped ENNReal ProbabilityTheory Topology Interval

noncomputable section

namespace Concrete

/-- An atomless probability measure has a continuous CDF.  This small lemma
bridges Mathlib's right-continuous Stieltjes API to ordinary continuity. -/
theorem continuous_cdf_of_nullSingleton
    (mu : Measure ℝ) [IsProbabilityMeasure mu] [NullSingletonClass mu] :
    Continuous (cdf mu) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hmono : Monotone (cdf mu) := monotone_cdf mu
  rw [hmono.continuousAt_iff_leftLim_eq_rightLim]
  have hzero : (cdf mu).measure {x} = 0 := by
    rw [measure_cdf mu]
    simp
  have hof : ENNReal.ofReal (cdf mu x - leftLim (cdf mu) x) = 0 := by
    simpa only [StieltjesFunction.measure_singleton] using hzero
  have hdiff : cdf mu x - leftLim (cdf mu) x ≤ 0 :=
    ENNReal.ofReal_eq_zero.mp hof
  have hleft : leftLim (cdf mu) x = cdf mu x := by
    have hle : leftLim (cdf mu) x ≤ cdf mu x :=
      hmono.leftLim_le le_rfl
    linarith
  have hright : rightLim (cdf mu) x = cdf mu x := by
    apply hmono.continuousWithinAt_Ioi_iff_rightLim_eq.mp
    exact ((cdf mu).right_continuous x).mono Ioi_subset_Ici_self
  exact hleft.trans hright.symm

theorem continuous_standardGaussianCDF :
    Continuous (cdf standardGaussianMeasure) :=
  continuous_cdf_of_nullSingleton standardGaussianMeasure

theorem cdf_standardGaussian_eq_normalCDFReal (x : ℝ) :
    cdf standardGaussianMeasure x = normalCDFReal x := by
  rw [cdf_eq_real]
  rfl

/-- A Gaussian CDF increment is the integral of its density over the
corresponding compact interval. -/
theorem normalCDFReal_sub_eq_intervalIntegral
    {a b : ℝ} (hab : a ≤ b) :
    normalCDFReal b - normalCDFReal a =
      ∫ x in a..b, normalDensity x := by
  have hdiff : standardGaussianMeasure.real (Iic b \ Iic a) =
      standardGaussianMeasure.real (Iic b) -
        standardGaussianMeasure.real (Iic a) :=
    measureReal_sdiff (Iic_subset_Iic.mpr hab) measurableSet_Iic
  have hset : Iic b \ Iic a = Ioc a b := by
    ext x
    simp only [mem_diff, mem_Iic, mem_Ioc]
    constructor
    · rintro ⟨hxb, hnot⟩
      exact ⟨lt_of_not_ge hnot, hxb⟩
    · rintro ⟨hax, hxb⟩
      exact ⟨hxb, not_le.mpr hax⟩
  have hint : standardGaussianMeasure.real (Ioc a b) =
      ∫ x in Ioc a b, normalDensity x := by
    rw [measureReal_def]
    unfold standardGaussianMeasure normalDensity
    rw [gaussianReal_apply_eq_integral 0 (by norm_num)]
    rw [ENNReal.toReal_ofReal]
    exact integral_nonneg_of_ae
      (ae_restrict_of_forall_mem measurableSet_Ioc fun x _ =>
        normalDensity_nonneg x)
  rw [intervalIntegral.integral_of_le hab]
  change standardGaussianMeasure.real (Iic b) -
      standardGaussianMeasure.real (Iic a) = _
  rw [← hdiff, hset, hint]

lemma sqrt_two_pi_le_exp_one :
    Real.sqrt (2 * Real.pi) ≤ Real.exp 1 := by
  have hsquare : (Real.sqrt (2 * Real.pi)) ^ 2 = 2 * Real.pi := by
    rw [Real.sq_sqrt]
    positivity
  have hsqrtlt : Real.sqrt (2 * Real.pi) < (2.6 : ℝ) := by
    have hpi := Real.pi_lt_d2
    have hsqrt0 := Real.sqrt_nonneg (2 * Real.pi)
    nlinarith
  have hexp : (2.6 : ℝ) < Real.exp 1 :=
    lt_trans (by norm_num) Real.exp_one_gt_d9
  exact (le_of_lt hsqrtlt).trans (le_of_lt hexp)

/-- A deliberately coarse exponential form of the lower Mills bound.  It is
chosen because taking logarithms immediately gives the estimate required by
the Gaussian-shift arithmetic. -/
lemma exp_neg_one_add_sq_le_normalTailReal
    (a : ℝ) (ha : 0 ≤ a) :
    Real.exp (-(1 + a) ^ 2) ≤ normalTailReal a := by
  apply le_trans ?_ (mills_lower a ha)
  have hsqrt0 : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have honea0 : 0 < 1 + a := by linarith
  have honeaexp : 1 + a ≤ Real.exp a := by
    simpa [add_comm] using Real.add_one_le_exp a
  have hprod : Real.sqrt (2 * Real.pi) * (1 + a) ≤
      Real.exp (1 + a) := by
    have hmul := mul_le_mul sqrt_two_pi_le_exp_one honeaexp
      (by linarith : 0 ≤ 1 + a) (Real.exp_pos 1).le
    simpa [Real.exp_add] using hmul
  have hmul := mul_le_mul_of_nonneg_right hprod
    (Real.exp_pos (-(1 + a) ^ 2)).le
  have hexpcomp :
      Real.exp (1 + a - (1 + a) ^ 2) ≤ Real.exp (-(a ^ 2) / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg a]
  have hcross :
      Real.sqrt (2 * Real.pi) * (1 + a) *
          Real.exp (-(1 + a) ^ 2) ≤
        Real.exp (-(a ^ 2) / 2) := by
    calc
      Real.sqrt (2 * Real.pi) * (1 + a) *
          Real.exp (-(1 + a) ^ 2) ≤
          Real.exp (1 + a) * Real.exp (-(1 + a) ^ 2) := hmul
      _ = Real.exp (1 + a - (1 + a) ^ 2) := by
        rw [← Real.exp_add]
        congr 1
      _ ≤ Real.exp (-(a ^ 2) / 2) := hexpcomp
  rw [normalDensity_def, inv_mul_eq_div]
  rw [le_div_iff₀ honea0, le_div_iff₀ hsqrt0]
  convert hcross using 1
  all_goals first | rfl | ring

lemma log_one_div_normalTailReal_le
    (a : ℝ) (ha : 0 ≤ a) :
    Real.log (1 / normalTailReal a) ≤ (1 + a) ^ 2 := by
  have htail0 : 0 < normalTailReal a := by
    exact (div_pos (normalDensity_pos a) (by linarith)).trans_le
      (mills_lower a ha)
  have hinv : (normalTailReal a)⁻¹ ≤
      (Real.exp (-(1 + a) ^ 2))⁻¹ :=
    (inv_le_inv₀ htail0 (Real.exp_pos _)).2
      (exp_neg_one_add_sq_le_normalTailReal a ha)
  have hrecip : 1 / normalTailReal a ≤ Real.exp ((1 + a) ^ 2) := by
    simpa only [one_div, Real.exp_neg, inv_inv] using hinv
  exact (Real.log_le_iff_le_exp (one_div_pos.mpr htail0)).2 hrecip

private lemma normalDensity_interval_lower
    {a u x : ℝ} (ha : 0 ≤ a) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hx : x ∈ Icc (-a) (-a + u)) :
    Real.exp (-(1 / 2 : ℝ)) * normalDensity a ≤ normalDensity x := by
  have hv0 : 0 ≤ x + a := by linarith [hx.1]
  have hv1 : x + a ≤ 1 := by linarith [hx.2]
  have hvsq : (x + a) ^ 2 ≤ 1 := by nlinarith
  have hav : 0 ≤ a * (x + a) := mul_nonneg ha hv0
  have hxsq : x ^ 2 ≤ a ^ 2 + 1 := by
    nlinarith
  have hexp : Real.exp (-(1 / 2 : ℝ) - a ^ 2 / 2) ≤
      Real.exp (-(x ^ 2) / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hc0 : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  rw [normalDensity_def, normalDensity_def]
  calc
    Real.exp (-(1 / 2 : ℝ)) *
        ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(a ^ 2) / 2)) =
        (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.exp (-(1 / 2 : ℝ) - a ^ 2 / 2) := by
      calc
        _ = (Real.sqrt (2 * Real.pi))⁻¹ *
            (Real.exp (-(1 / 2 : ℝ)) * Real.exp (-(a ^ 2) / 2)) := by
              ring
        _ = (Real.sqrt (2 * Real.pi))⁻¹ *
            Real.exp (-(1 / 2 : ℝ) + (-(a ^ 2) / 2)) := by
              rw [Real.exp_add]
        _ = _ := by congr 2 <;> ring
    _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp (-(x ^ 2) / 2) :=
      mul_le_mul_of_nonneg_left hexp hc0

/-- The CDF gain over a nonnegative shift is bounded below by integrating a
uniform density lower bound over the first unit of the interval. -/
lemma normalCDFReal_increment_lower
    (a s : ℝ) (ha : 0 ≤ a) (hs : 0 ≤ s) :
    Real.exp (-(1 / 2 : ℝ)) * normalDensity a * min s 1 ≤
      normalCDFReal (-a + s) - normalCDFReal (-a) := by
  let u : ℝ := min s 1
  have hu0 : 0 ≤ u := min_nonneg_of_nonneg hs (by norm_num)
  have hu1 : u ≤ 1 := min_le_right _ _
  have hus : u ≤ s := min_le_left _ _
  have hab : -a ≤ -a + u := by linarith
  have hconstInt : IntervalIntegrable
      (fun _ : ℝ => Real.exp (-(1 / 2 : ℝ)) * normalDensity a)
      volume (-a) (-a + u) := intervalIntegrable_const
  have hdensityInt : IntervalIntegrable normalDensity volume (-a) (-a + u) :=
    integrable_normalDensity.intervalIntegrable
  have hint :
      (∫ _x in (-a)..(-a + u),
          Real.exp (-(1 / 2 : ℝ)) * normalDensity a) ≤
        ∫ x in (-a)..(-a + u), normalDensity x := by
    exact intervalIntegral.integral_mono_on hab hconstInt hdensityInt
      (fun x hx => normalDensity_interval_lower ha hu0 hu1 hx)
  have hint' :
      Real.exp (-(1 / 2 : ℝ)) * normalDensity a * u ≤
        normalCDFReal (-a + u) - normalCDFReal (-a) := by
    rw [normalCDFReal_sub_eq_intervalIntegral hab]
    convert hint using 1
    all_goals first | rfl | simp [smul_eq_mul]; ring
  have hcdf : normalCDFReal (-a + u) ≤ normalCDFReal (-a + s) := by
    rw [← cdf_standardGaussian_eq_normalCDFReal,
      ← cdf_standardGaussian_eq_normalCDFReal]
    exact monotone_cdf standardGaussianMeasure (by linarith)
  have hdiff :
      normalCDFReal (-a + u) - normalCDFReal (-a) ≤
        normalCDFReal (-a + s) - normalCDFReal (-a) :=
    sub_le_sub_right hcdf _
  simpa only [u] using hint'.trans hdiff

lemma cdf_standardGaussian_zero :
    cdf standardGaussianMeasure 0 = 1 / 2 := by
  rw [cdf_standardGaussian_eq_normalCDFReal]
  unfold normalCDFReal
  rw [normalCDF_zero]
  norm_num

lemma normalCDFReal_neg (a : ℝ) :
    normalCDFReal (-a) = normalTailReal a := by
  unfold normalCDFReal normalTailReal
  rw [normalCDF_neg]

/-- The abstract Gaussian-shift hypothesis used by the separated-set proof,
now instantiated by Mathlib's standard Gaussian measure and the elementary
lower quantile. -/
theorem standardGaussianShift :
    GaussianShift (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure) := by
  intro q s hq hqhalf hs
  have hq1 : q < 1 := lt_of_le_of_lt hqhalf (by norm_num)
  let z : ℝ := lowerQuantile standardGaussianMeasure q
  let a : ℝ := -z
  have hcdfz : cdf standardGaussianMeasure z = q := by
    dsimp only [z]
    exact cdf_lowerQuantile_eq standardGaussianMeasure
      continuous_standardGaussianCDF hq hq1
  have hz0 : z ≤ 0 := by
    apply (lowerQuantile_le_iff standardGaussianMeasure hq hq1).2
    exact hqhalf.trans_eq cdf_standardGaussian_zero.symm
  have ha : 0 ≤ a := by
    dsimp only [a]
    linarith
  have hnega : -a = z := by simp [a]
  have htailq : normalTailReal a = q := by
    calc
      normalTailReal a = normalCDFReal (-a) := (normalCDFReal_neg a).symm
      _ = cdf standardGaussianMeasure (-a) :=
        (cdf_standardGaussian_eq_normalCDFReal (-a)).symm
      _ = cdf standardGaussianMeasure z := by rw [hnega]
      _ = q := hcdfz
  have hqle1 : q ≤ 1 := hqhalf.trans (by norm_num)
  have honele : 1 ≤ 1 / q := by
    rw [le_div_iff₀ hq]
    simpa using hqle1
  have hell : 0 ≤ Real.log (1 / q) := Real.log_nonneg honele
  have hlog : Real.log (1 / q) ≤ (1 + a) ^ 2 := by
    have h := log_one_div_normalTailReal_le a ha
    rwa [htailq] at h
  have hmills := mills_upper a ha
  rw [htailq] at hmills
  have honea0 : 0 < 1 + a := by linarith
  have hqa : q * (1 + a) ≤ 2 * normalDensity a := by
    have hmul := mul_le_mul_of_nonneg_right hmills honea0.le
    calc
      q * (1 + a) ≤ (2 * normalDensity a / (1 + a)) * (1 + a) := hmul
      _ = 2 * normalDensity a := by field_simp
  have hcoef : q * (1 + a) / 2 ≤ normalDensity a := by
    linarith
  have hmin0 : 0 ≤ min s 1 := min_nonneg_of_nonneg hs (by norm_num)
  have hscaled :
      Real.exp (-(1 / 2 : ℝ)) * (q * (1 + a) / 2) * min s 1 ≤
        Real.exp (-(1 / 2 : ℝ)) * normalDensity a * min s 1 := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcoef (Real.exp_pos _).le) hmin0
  have hleft :
      q * (Real.exp (-(1 / 2 : ℝ)) / 2) *
          ((1 + a) * min s 1) ≤
        Real.exp (-(1 / 2 : ℝ)) * normalDensity a * min s 1 := by
    convert hscaled using 1
    all_goals first | rfl | ring
  have hincrement := normalCDFReal_increment_lower a s ha hs
  have hintegral :
      q * (Real.exp (-(1 / 2 : ℝ)) / 2) *
          ((1 + a) * min s 1) ≤
        cdf standardGaussianMeasure (z + s) - q := by
    calc
      _ ≤ Real.exp (-(1 / 2 : ℝ)) * normalDensity a * min s 1 := hleft
      _ ≤ normalCDFReal (-a + s) - normalCDFReal (-a) := hincrement
      _ = cdf standardGaussianMeasure (z + s) - q := by
        rw [← cdf_standardGaussian_eq_normalCDFReal,
          ← cdf_standardGaussian_eq_normalCDFReal, hnega, hcdfz]
  have hfinal := gaussian_shift_arithmetic q a s (Real.log (1 / q))
    (cdf standardGaussianMeasure (z + s) - q)
    hq.le ha hs hell hlog hintegral
  simpa only [z] using hfinal

/-- Consequently, after the standard Gaussian has been made concrete, the
separated-set estimate has Bakry--Ledoux as its only analytic hypothesis. -/
theorem separatedSets_of_bakryLedoux
    {alpha : Type*} [MeasurableSpace alpha] [PseudoMetricSpace alpha]
    (pi : Measure alpha) [IsProbabilityMeasure pi]
    (m : ℝ) (hm : 0 ≤ m)
    (hBL : BakryLedouxEnlargement pi m
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure)) :
    SeparatedSets pi m :=
  separatedSets_of_bakryLedoux_of_gaussianShift pi m hm
    (cdf standardGaussianMeasure) (lowerQuantile standardGaussianMeasure)
    hBL standardGaussianShift

end Concrete

end

end UniformRandomMALA
