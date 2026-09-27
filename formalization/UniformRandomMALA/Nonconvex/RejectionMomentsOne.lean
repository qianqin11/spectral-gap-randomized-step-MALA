import UniformRandomMALA.Nonconvex.MALARejectionDefinitions
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import UniformRandomMALA.DiscreteTime.MomentInterpolation

/-!
# Stationary rejection for every real `p ≥ 1` without convexity

Jensen interpolation extends the finite Gaussian likelihood estimate to
`1 ≤ p < 2`. The public theorem is Proposition B.1
(`prop:stationary-rejection`) under exactly the appendix's nonconvex assumptions.
-/

namespace UniformRandomMALA.Concrete.NonconvexPotential

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

variable {d : ℕ} (V : NonconvexPotential d)

/-- The fixed-step rejection moment statement with the revised exponent range. -/
def StationaryMALARejectionMomentBoundOne (cr Cr : ℝ) : Prop :=
  ∀ p h : ℝ, 1 ≤ p → 0 < h →
    h ≤ cr / (V.L * Real.sqrt (p * ((d : ℝ) + p))) →
    (∫ x : State d,
      ((1 - MetropolisHastings.acceptanceMass
        (V.gaussianDensityProposal h) (V.malaAcceptance h) x).toReal) ^ p
        ∂(V.target : Measure (State d))) ≤
      ((Cr / 3) * V.L * h * Real.sqrt (p * ((d : ℝ) + p))) ^ p

lemma integrable_malaRejectionMassReal_rpow (h : ℝ) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun x => (V.malaRejectionMassReal h x) ^ p)
      (V.target : Measure (State d)) := by
  have hr : Measurable (V.malaRejectionMassReal h) :=
    V.measurable_malaRejectionMassReal h
  have hrp : Measurable (fun x => (V.malaRejectionMassReal h x) ^ p) :=
    (Real.continuous_rpow_const hp).measurable.comp hr
  apply Integrable.of_bound hrp.aestronglyMeasurable 1
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (V.malaRejectionMassReal_nonneg h x) p)]
    exact Real.rpow_le_one (V.malaRejectionMassReal_nonneg h x)
      (V.malaRejectionMassReal_le_one h x) hp

/-- Interpolation extends the old moment family; neither a diffusion theorem
nor a new analytic certificate is required. -/
theorem stationaryMALARejectionMomentBoundOne_of_two
    {cr Cr : ℝ} (hcr : 0 < cr) (hCr : 0 ≤ Cr)
    (hold : V.StationaryMALARejectionMomentBound cr Cr) :
    V.StationaryMALARejectionMomentBoundOne (cr / 2) (2 * Cr) := by
  intro p h hp hh hstep
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hdpos := V.dimension_real_pos
  let s : ℝ := Real.sqrt (p * ((d : ℝ) + p))
  have hspos : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hden : 0 < V.L * s := mul_pos V.hL hspos
  have hbase0 : 0 ≤ (Cr / 3) * V.L * h * s := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (div_nonneg hCr (by norm_num)) V.hL.le) hh.le)
      hspos.le
  by_cases hp2 : 2 ≤ p
  · have hstep_old : h ≤ cr / (V.L * s) := by
      exact hstep.trans (div_le_div_of_nonneg_right (by linarith) hden.le)
    have hbound := hold p h hp2 hh hstep_old
    have hbase : (Cr / 3) * V.L * h * s ≤
        ((2 * Cr) / 3) * V.L * h * s := by
      calc
        (Cr / 3) * V.L * h * s ≤ 2 * ((Cr / 3) * V.L * h * s) := by linarith
        _ = ((2 * Cr) / 3) * V.L * h * s := by ring
    exact hbound.trans (Real.rpow_le_rpow hbase0 hbase hp0)
  · have hp_le_two : p ≤ 2 := le_of_lt (lt_of_not_ge hp2)
    let s2 : ℝ := Real.sqrt (2 * ((d : ℝ) + 2))
    have hs2pos : 0 < s2 := Real.sqrt_pos.2 (by positivity)
    have hscales : s2 ≤ 2 * s := by
      have hd1 := V.dimension_real_one
      have hprod : (d : ℝ) + 1 ≤ p * ((d : ℝ) + p) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hp) (by positivity : 0 ≤ (d : ℝ)),
          sq_nonneg (p - 1)]
      have hsp := Real.sq_sqrt (by positivity : 0 ≤ p * ((d : ℝ) + p))
      have hs2 := Real.sq_sqrt (by positivity : 0 ≤ 2 * ((d : ℝ) + 2))
      have hnsp := Real.sqrt_nonneg (p * ((d : ℝ) + p))
      have hns2 := Real.sqrt_nonneg (2 * ((d : ℝ) + 2))
      dsimp [s, s2]
      nlinarith
    have hhprod : h * (V.L * s) ≤ cr / 2 :=
      (le_div_iff₀ hden).1 hstep
    have hhprod2 : h * (V.L * s2) ≤ cr := by
      have hm := mul_le_mul_of_nonneg_left hscales
        (mul_nonneg hh.le V.hL.le)
      nlinarith
    have hstep2 : h ≤ cr / (V.L * s2) :=
      (le_div_iff₀ (mul_pos V.hL hs2pos)).2 hhprod2
    have hsecond := hold 2 h (by norm_num) hh hstep2
    have hsecond' :
        (∫ x : State d, (V.malaRejectionMassReal h x) ^ (2 : ℝ)
          ∂(V.target : Measure (State d))) ≤
        ((Cr / 3) * V.L * h * s2) ^ (2 : ℝ) := by
      simpa only [V.malaRejectionMassReal_eq_fixed hh] using hsecond
    have hpbound := DiscreteTime.integral_rpow_le_of_second_moment
      hp hp_le_two (show 0 ≤ (Cr / 3) * V.L * h * s2 by
        exact mul_nonneg
          (mul_nonneg (mul_nonneg (div_nonneg hCr (by norm_num)) V.hL.le) hh.le)
          hs2pos.le)
      (V.malaRejectionMassReal_nonneg h)
      (V.integrable_malaRejectionMassReal_rpow h hp0)
      (V.integrable_malaRejectionMassReal_rpow h (by norm_num)) hsecond'
    have hcoef0 : 0 ≤ (Cr / 3) * V.L * h := by
      exact mul_nonneg
        (mul_nonneg (div_nonneg hCr (by norm_num)) V.hL.le) hh.le
    have hbase : (Cr / 3) * V.L * h * s2 ≤
        ((2 * Cr) / 3) * V.L * h * s := by
      have hm := mul_le_mul_of_nonneg_left hscales hcoef0
      nlinarith
    have hbound := hpbound.trans (Real.rpow_le_rpow
      (show 0 ≤ (Cr / 3) * V.L * h * s2 by
        exact mul_nonneg hcoef0 hs2pos.le) hbase hp0)
    simpa only [V.malaRejectionMassReal_eq_fixed hh] using hbound

/-- Boundedness of rejection gives actual membership in every finite `L^p` space. -/
theorem memLp_malaRejectionMassReal (h : ℝ) (p : ℝ≥0∞) :
    MemLp (V.malaRejectionMassReal h) p (V.target : Measure (State d)) := by
  apply MemLp.of_bound (V.measurable_malaRejectionMassReal h).aestronglyMeasurable 1
  exact ae_of_all _ fun x => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (V.malaRejectionMassReal_nonneg h x)]
      using V.malaRejectionMassReal_le_one h x

/-- The power-moment interface implies the literal real `L^p` norm bound. -/
theorem stationaryMALARejection_lpNorm_le_of_moments
    {cr Cr p h : ℝ} (hCr : 0 ≤ Cr)
    (hold : V.StationaryMALARejectionMomentBoundOne cr Cr)
    (hp : 1 ≤ p) (hh : 0 < h)
    (hstep : h ≤ cr / (V.L * Real.sqrt (p * ((d : ℝ) + p)))) :
    lpNorm (V.malaRejectionMassReal h) (ENNReal.ofReal p)
      (V.target : Measure (State d)) ≤
        (Cr / 3) * V.L * h * Real.sqrt (p * ((d : ℝ) + p)) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hbound := hold p h hp hh hstep
  have hbase : 0 ≤ (Cr / 3) * V.L * h * Real.sqrt (p * ((d : ℝ) + p)) := by
    exact mul_nonneg (mul_nonneg
      (mul_nonneg (div_nonneg hCr (by norm_num)) V.hL.le) hh.le)
      (Real.sqrt_nonneg _)
  have hInt : 0 ≤ ∫ x : State d, (V.malaRejectionMassReal h x) ^ p
      ∂(V.target : Measure (State d)) :=
    integral_nonneg fun x => Real.rpow_nonneg (V.malaRejectionMassReal_nonneg h x) p
  have hroot := Real.rpow_le_rpow hInt hbound (inv_nonneg.mpr hp0.le)
  rw [← Real.rpow_mul hbase, mul_inv_cancel₀ hp0.ne', Real.rpow_one] at hroot
  rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) ENNReal.ofReal_ne_top
    (V.measurable_malaRejectionMassReal h).aestronglyMeasurable]
  simpa only [ENNReal.toReal_ofReal hp0.le, Real.norm_eq_abs,
    malaRejectionMassReal, abs_of_nonneg ENNReal.toReal_nonneg] using hroot

end
end UniformRandomMALA.Concrete.NonconvexPotential
