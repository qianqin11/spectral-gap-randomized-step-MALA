import UniformRandomMALA.Concrete.MALAOverlapBounds
import UniformRandomMALA.DiscreteTime.MomentInterpolation

/-!
# Stationary rejection and overlap for every real `p ≥ 1`

The finite Gaussian likelihood proof remains unchanged. For `1 ≤ p < 2`,
we use its second-moment conclusion and Jensen interpolation. The new public
step constant is half the old one, and the new exceptional-set constant is
twice the old one. The original sharper `p ≥ 2` interfaces remain available
and are still used internally by the multiscale spectral-gap proof.
-/

namespace UniformRandomMALA.Concrete.FirstOrderPotential

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

variable {d : ℕ} (V : FirstOrderPotential d)

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
    V.measurable_uncurry_malaRejectionMassReal.comp
      (measurable_const.prodMk measurable_id)
  have hrp : Measurable (fun x => (V.malaRejectionMassReal h x) ^ p) :=
    (Real.continuous_rpow_const hp).measurable.comp hr
  apply Integrable.of_bound hrp.aestronglyMeasurable 1
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (V.malaRejectionMassReal_nonneg h x) p)]
    exact Real.rpow_le_one (V.malaRejectionMassReal_nonneg h x)
      (V.malaRejectionMassReal_le_one h x) hp

include V in
lemma sqrt_second_moment_scale_le {p : ℝ} (hp : 1 ≤ p) :
    Real.sqrt (2 * ((d : ℝ) + 2)) ≤
      2 * Real.sqrt (p * ((d : ℝ) + p)) := by
  have hd1 : 1 ≤ (d : ℝ) := V.dimension_real_one
  have hd0 : 0 ≤ (d : ℝ) := le_trans zero_le_one hd1
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  have hinsp : 0 ≤ p * ((d : ℝ) + p) := by positivity
  have hins2 : 0 ≤ 2 * ((d : ℝ) + 2) := by positivity
  have hprod : (d : ℝ) + 1 ≤ p * ((d : ℝ) + p) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) hd0, sq_nonneg (p - 1)]
  have hsp := Real.sq_sqrt hinsp
  have hs2 := Real.sq_sqrt hins2
  have hnsp := Real.sqrt_nonneg (p * ((d : ℝ) + p))
  have hns2 := Real.sqrt_nonneg (2 * ((d : ℝ) + 2))
  nlinarith

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
    have hscales : s2 ≤ 2 * s := V.sqrt_second_moment_scale_le hp
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

/-- Both clauses of the overlap proposition, now with `p ≥ 1` in its first clause. -/
theorem proposition32_of_stationaryMALARejectionMomentBoundOne
    {cr Cr : ℝ} (_hcr : 0 < cr) (hcr1 : cr ≤ 1) (hCr : 0 < Cr)
    (hrej : V.StationaryMALARejectionMomentBoundOne cr Cr) :
    (∀ p t : ℝ, 1 ≤ p → ∀ ht : 0 < t,
      t ≤ cr / (V.L * Real.sqrt (p * ((d : ℝ) + p))) →
      ∃ G : Set (State d),
        MeasurableSet G ∧
        (V.target : Measure (State d)) Gᶜ ≤
          ENNReal.ofReal
            ((Cr * V.L * t * Real.sqrt (p * ((d : ℝ) + p))) ^ p) ∧
        ∀ x ∈ G, ∀ y ∈ G,
          ‖x - y‖ ≤ Real.sqrt t / 16 →
          setwiseTV (V.dyadicMALA t ht x)
            (V.dyadicMALA t ht y) ≤ 3 / 4) ∧
    (∀ t : ℝ, ∀ ht : 0 < t,
      t ≤ 1 / (2 * V.L * (d : ℝ)) →
      ∀ x y : State d,
        ‖x - y‖ ≤ Real.sqrt t / 16 →
        setwiseTV (V.dyadicMALA t ht x)
          (V.dyadicMALA t ht y) ≤ 3 / 4) := by
  constructor
  · intro p t hp ht hstep
    let s : ℝ := Real.sqrt (p * ((d : ℝ) + p))
    let C : ℝ := (Cr / 3) * V.L * t * s
    have hp0 : 0 ≤ p := by linarith
    have hd1 : 1 ≤ (d : ℝ) := V.dimension_real_one
    have hins : 1 ≤ p * ((d : ℝ) + p) := by
      have hsum : 1 ≤ (d : ℝ) + p := by linarith
      simpa only [one_mul] using
        (mul_le_mul hp hsum (show (0 : ℝ) ≤ 1 by norm_num) hp0)
    have hs1 : 1 ≤ s := by
      dsimp [s]
      exact Real.one_le_sqrt.mpr hins
    have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs1
    have hden : 0 < V.L * s := mul_pos V.hL hspos
    have hthreshold_le : cr / (V.L * s) ≤ 1 / V.L := by
      calc
        cr / (V.L * s) ≤ 1 / (V.L * s) :=
          div_le_div_of_nonneg_right hcr1 hden.le
        _ ≤ 1 / V.L := by
          apply div_le_div_of_nonneg_left zero_le_one V.hL
          simpa using mul_le_mul_of_nonneg_left hs1 V.hL.le
    have htL : t ≤ 2 / V.L := by
      have ht_one : t ≤ 1 / V.L := by
        exact hstep.trans (by simpa only [s] using hthreshold_le)
      exact ht_one.trans (div_le_div_of_nonneg_right (by norm_num) V.hL.le)
    have hC0 : 0 ≤ C := by
      dsimp [C]
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (div_nonneg hCr.le (by norm_num)) V.hL.le) ht.le)
        (Real.sqrt_nonneg _)
    have hmoment : ∀ h ∈ Set.Ioc (t / 2) t,
        (∫ x : State d,
          ((1 - MetropolisHastings.acceptanceMass
            (V.gaussianDensityProposal h) (V.malaAcceptance h) x).toReal) ^ p
            ∂(V.target : Measure (State d))) ≤ C ^ p := by
      intro h hhmem
      have hh : 0 < h := lt_of_lt_of_le (by linarith [ht]) hhmem.1.le
      have hhstep : h ≤ cr / (V.L * Real.sqrt (p * ((d : ℝ) + p))) :=
        hhmem.2.trans hstep
      have hfixed := hrej p h hp hh hhstep
      have hbase0 :
          0 ≤ (Cr / 3) * V.L * h * Real.sqrt (p * ((d : ℝ) + p)) := by
        exact mul_nonneg
          (mul_nonneg (mul_nonneg (div_nonneg hCr.le (by norm_num)) V.hL.le) hh.le)
          (Real.sqrt_nonneg _)
      have hbase_le :
          (Cr / 3) * V.L * h * Real.sqrt (p * ((d : ℝ) + p)) ≤ C := by
        have hfac0 : 0 ≤ (Cr / 3) * V.L *
            Real.sqrt (p * ((d : ℝ) + p)) := by
          exact mul_nonneg
            (mul_nonneg (div_nonneg hCr.le (by norm_num)) V.hL.le)
            (Real.sqrt_nonneg _)
        dsimp [C, s]
        calc
          (Cr / 3) * V.L * h * Real.sqrt (p * ((d : ℝ) + p)) =
              ((Cr / 3) * V.L * Real.sqrt (p * ((d : ℝ) + p))) * h := by ring
          _ ≤ ((Cr / 3) * V.L * Real.sqrt (p * ((d : ℝ) + p))) * t :=
            mul_le_mul_of_nonneg_left hhmem.2 hfac0
          _ = (Cr / 3) * V.L * t * Real.sqrt (p * ((d : ℝ) + p)) := by ring
      exact hfixed.trans (Real.rpow_le_rpow hbase0 hbase_le hp0)
    obtain ⟨G, hG, hGmass, hlocal⟩ :=
      V.exists_dyadicMALALocalOverlap_goodSet
        ht htL (show 1 ≤ p by linarith) hC0 hmoment
    refine ⟨G, hG, ?_, hlocal⟩
    have hcoef : 3 * C = Cr * V.L * t *
        Real.sqrt (p * ((d : ℝ) + p)) := by
      dsimp [C, s]
      ring
    rwa [hcoef] at hGmass
  · intro t ht hsmall x y hxy
    exact V.setwiseTV_dyadicMALA_le_three_quarters ht hsmall x y hxy


/-- Universal small-step constant for the full `p ≥ 1` family. -/
def proposition32CrSmallOne : ℝ := proposition32CrSmall / 2

/-- Universal exceptional-mass constant for the full `p ≥ 1` family. -/
def proposition32CrLargeOne : ℝ := 2 * proposition32CrLarge

lemma proposition32CrSmallOne_pos : 0 < proposition32CrSmallOne :=
  div_pos proposition32CrSmall_pos (by norm_num)

lemma proposition32CrSmallOne_le_one : proposition32CrSmallOne ≤ 1 := by
  dsimp [proposition32CrSmallOne]
  linarith [proposition32CrSmall_le_one, proposition32CrSmall_pos]

lemma proposition32CrLargeOne_pos : 0 < proposition32CrLargeOne :=
  mul_pos (by norm_num) proposition32CrLarge_pos

/-- Proposition B.1 for `p ≥ 1` under the standing first-order, strongly convex
assumptions. The manuscript's additional nonconvex scope is not asserted here. -/
theorem stationaryMALARejectionMomentBoundOne_proposition32 :
    V.StationaryMALARejectionMomentBoundOne
      proposition32CrSmallOne proposition32CrLargeOne :=
  V.stationaryMALARejectionMomentBoundOne_of_two
    proposition32CrSmall_pos proposition32CrLarge_pos.le
    V.stationaryMALARejectionMomentBound_proposition32

/-- Proposition 3.2 with its full manuscript range and explicit universal
constants `cr = 1/(32e)` and `Cr = 12288e³`. -/
theorem mala_overlap_bounds_p1 :
    (∀ p t : ℝ, 1 ≤ p → ∀ ht : 0 < t,
      t ≤ proposition32CrSmallOne /
        (V.L * Real.sqrt (p * ((d : ℝ) + p))) →
      ∃ G : Set (State d),
        MeasurableSet G ∧
        (V.target : Measure (State d)) Gᶜ ≤
          ENNReal.ofReal
            ((proposition32CrLargeOne * V.L * t *
              Real.sqrt (p * ((d : ℝ) + p))) ^ p) ∧
        ∀ x ∈ G, ∀ y ∈ G,
          ‖x - y‖ ≤ Real.sqrt t / 16 →
          setwiseTV (V.dyadicMALA t ht x)
            (V.dyadicMALA t ht y) ≤ 3 / 4) ∧
    (∀ t : ℝ, ∀ ht : 0 < t,
      t ≤ 1 / (2 * V.L * (d : ℝ)) →
      ∀ x y : State d,
        ‖x - y‖ ≤ Real.sqrt t / 16 →
        setwiseTV (V.dyadicMALA t ht x)
          (V.dyadicMALA t ht y) ≤ 3 / 4) :=
  V.proposition32_of_stationaryMALARejectionMomentBoundOne
    proposition32CrSmallOne_pos proposition32CrSmallOne_le_one
    proposition32CrLargeOne_pos
    V.stationaryMALARejectionMomentBoundOne_proposition32

end

end UniformRandomMALA.Concrete.FirstOrderPotential
