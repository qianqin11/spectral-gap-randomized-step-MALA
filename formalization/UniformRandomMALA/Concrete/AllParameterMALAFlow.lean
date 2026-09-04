import UniformRandomMALA.BakryLedoux

/-!
# All-parameter one-step flow bounds for MALA

This module packages the two clauses of the paper's one-step-flow result for
the concrete dyadic MALA kernel.  Unlike the ladder-specialized declarations,
the local clause is stated for every real moment `p` above the universal
threshold and every `theta ∈ (0,1]`.

The only analytic inputs are the already established local MALA overlap bound
and the unconditional Bakry--Ledoux enlargement theorem for the target.  The
remaining work is the scalar exceptional-set budget.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace Concrete
namespace FirstOrderPotential

variable {d : ℕ} (V : FirstOrderPotential d)

/-- The moment threshold in the paper's all-parameter flow proposition. -/
def malaFlowMomentThreshold : ℝ :=
  concreteA0 *
    (1 + Real.log ((d : ℝ) + 1) + Real.log (V.L / V.m))

/-- The local dyadic endpoint associated with a moment and a multiplier. -/
def malaFlowStep (p theta : ℝ) : ℝ :=
  theta * concreteB0 /
    (V.L * Real.sqrt (p * ((d : ℝ) + p)))

lemma malaFlowMomentThreshold_ge_two :
    2 ≤ V.malaFlowMomentThreshold := by
  let params := V.universalParameters 1 (by norm_num)
  have h := params.two_le_pStar
  simpa only [params, malaFlowMomentThreshold, universalParameters,
    toParameters] using h

lemma malaFlowStep_pos
    {p theta : ℝ} (hp : V.malaFlowMomentThreshold ≤ p)
    (htheta : 0 < theta) :
    0 < V.malaFlowStep p theta := by
  have hp0 : 0 < p := lt_of_lt_of_le (by nlinarith [V.malaFlowMomentThreshold_ge_two]) hp
  have hsum : 0 < (d : ℝ) + p := add_pos V.dimension_real_pos hp0
  unfold malaFlowStep
  exact div_pos (mul_pos htheta concreteB0_pos)
    (mul_pos V.hL (Real.sqrt_pos.2 (mul_pos hp0 hsum)))

/-- The coefficient-wise choice of `A₀` implies the logarithmic exceptional
budget condition for every moment above the threshold, not only for moments
on the geometric ladder. -/
lemma malaFlow_log_condition
    {p : ℝ} (hp : V.malaFlowMomentThreshold ≤ p) :
    p * (Real.log 16 - 1 / 2) ≥
      13 * Real.log 2 +
        (1 / 2) * Real.log (2 * (V.L / V.m) / concreteB0) +
        (1 / 4) * Real.log (((d : ℝ) + p) / p) := by
  let C : ℝ := Real.log 16 - 1 / 2
  let B : ℝ := concreteA0 * C
  let ld : ℝ := Real.log ((d : ℝ) + 1)
  let lk : ℝ := Real.log (V.L / V.m)
  let base : ℝ := 13 * Real.log 2 + (1 / 2) * Real.log (2 / concreteB0)
  have hpTwo : 2 ≤ p := V.malaFlowMomentThreshold_ge_two.trans hp
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hpTwo
  have hpOne : 1 ≤ p := (by norm_num : (1 : ℝ) ≤ 2).trans hpTwo
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact exceptionalBudgetSlope_pos.le
  have hld : 0 ≤ ld := by
    dsimp only [ld]
    exact Real.log_nonneg (by linarith [V.dimension_real_one])
  have hlk : 0 ≤ lk := Real.log_nonneg V.conditionNumber_one
  have hratio : ((d : ℝ) + p) / p ≤ (d : ℝ) + 1 := by
    apply (div_le_iff₀ hp0).2
    have hdmul := mul_le_mul_of_nonneg_left hpOne V.dimension_real_pos.le
    nlinarith
  have hlogratio : Real.log (((d : ℝ) + p) / p) ≤ ld := by
    dsimp only [ld]
    exact Real.strictMonoOn_log.monotoneOn
      (div_pos (add_pos V.dimension_real_pos hp0) hp0)
      (add_pos V.dimension_real_pos zero_lt_one) hratio
  have hkappa0 : 0 < V.L / V.m := div_pos V.hL V.hm
  have hlogKappa : Real.log (2 * (V.L / V.m) / concreteB0) =
      Real.log (2 / concreteB0) + lk := by
    rw [show 2 * (V.L / V.m) / concreteB0 =
        (2 / concreteB0) * (V.L / V.m) by ring,
      Real.log_mul (ne_of_gt (div_pos (by norm_num) concreteB0_pos))
        (ne_of_gt hkappa0)]
  have hBbase : base ≤ B := by
    simpa only [base, B, C, exceptionalBudgetSlope] using
      concreteA0_exceptional_choice.1
  have hBone : 1 ≤ B := by
    simpa only [B, C, exceptionalBudgetSlope] using
      concreteA0_exceptional_choice.2
  have hBld : (1 / 4) * ld ≤ B * ld := by
    have := mul_le_mul_of_nonneg_right hBone hld
    nlinarith
  have hBlk : (1 / 2) * lk ≤ B * lk := by
    have := mul_le_mul_of_nonneg_right hBone hlk
    nlinarith
  have hcoeff : base + (1 / 4) * ld + (1 / 2) * lk ≤
      B * (1 + ld + lk) := by
    calc
      base + (1 / 4) * ld + (1 / 2) * lk ≤
          B + B * ld + B * lk := by linarith
      _ = B * (1 + ld + lk) := by ring
  have hthresholdC : V.malaFlowMomentThreshold * C =
      B * (1 + ld + lk) := by
    dsimp only [malaFlowMomentThreshold, B, C, ld, lk]
    ring
  have hpC : V.malaFlowMomentThreshold * C ≤ p * C :=
    mul_le_mul_of_nonneg_right hp hC
  have hmain : base + (1 / 4) * ld + (1 / 2) * lk ≤ p * C :=
    hcoeff.trans (hthresholdC.symm.le.trans hpC)
  rw [hlogKappa]
  dsimp only [C, base, lk] at hmain ⊢
  nlinarith [hlogratio]

/-- Full scalar exceptional-set budget for an arbitrary admissible moment and
multiplier. -/
lemma malaFlow_exceptionalBudget
    {p theta u : ℝ}
    (hp : V.malaFlowMomentThreshold ≤ p)
    (htheta : 0 < theta) (hthetaOne : theta ≤ 1)
    (huLog : Real.log 2 ≤ u) (huUpper : u ≤ p / 2) :
    (theta / 16) ^ p ≤
        (1 / (2 : ℝ) ^ 13) * Real.exp (-u) *
          Real.sqrt (V.m * V.malaFlowStep p theta * u) ∧
      V.m * V.malaFlowStep p theta * u ≤ concreteB0 / 2 := by
  have hpTwo : 2 ≤ p := V.malaFlowMomentThreshold_ge_two.trans hp
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hpTwo
  have ht : 0 < V.malaFlowStep p theta := V.malaFlowStep_pos hp htheta
  have hend :
      (theta / 16) ^ p ≤
        (1 / (2 : ℝ) ^ 13) * Real.exp (-(p / 2)) *
          Real.sqrt (V.m * V.malaFlowStep p theta * (p / 2)) := by
    apply exceptional_budget_endpoint_of_log_condition
      (d : ℝ) V.m V.L (V.L / V.m) concreteB0 theta p
        (V.malaFlowStep p theta)
      V.dimension_real_pos V.hm V.hL rfl (div_pos V.hL V.hm)
      concreteB0_pos htheta hthetaOne hpTwo
    · unfold malaFlowStep
      ring
    · exact V.malaFlow_log_condition hp
  have hu0 : 0 ≤ u := log_two_pos.le.trans huLog
  have hhalf : 1 / 2 ≤ u := by
    exact (by norm_num : (1 / 2 : ℝ) ≤ 0.6931471803).trans
      (Real.log_two_gt_d9.le.trans huLog)
  have hmono : Real.exp (-(p / 2)) * Real.sqrt (p / 2) ≤
      Real.exp (-u) * Real.sqrt u :=
    exp_neg_mul_sqrt_antitone hhalf huUpper
  have hmt0 : 0 ≤ V.m * V.malaFlowStep p theta :=
    mul_nonneg V.hm.le ht.le
  have hscaled := mul_le_mul_of_nonneg_left hmono
    (Real.sqrt_nonneg (V.m * V.malaFlowStep p theta))
  have hright :
      (1 / (2 : ℝ) ^ 13) * Real.exp (-(p / 2)) *
          Real.sqrt (V.m * V.malaFlowStep p theta * (p / 2)) ≤
        (1 / (2 : ℝ) ^ 13) * Real.exp (-u) *
          Real.sqrt (V.m * V.malaFlowStep p theta * u) := by
    rw [Real.sqrt_mul hmt0, Real.sqrt_mul hmt0]
    have hcoef : 0 ≤ (1 / (2 : ℝ) ^ 13) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hscaled hcoef]
  refine ⟨hend.trans hright, ?_⟩
  apply exceptional_budget_unsaturated
    (d : ℝ) V.m V.L (V.L / V.m) concreteB0 theta p u
      (V.malaFlowStep p theta)
    V.dimension_real_pos V.hm V.hL rfl V.conditionNumber_one
    concreteB0_pos hthetaOne hp0 hu0 huUpper
  unfold malaFlowStep
  ring

private lemma log_one_div_le_half_of_exp_neg_half_le
    {p q : ℝ} (hq : 0 < q) (h : Real.exp (-(p / 2)) ≤ q) :
    Real.log (1 / q) ≤ p / 2 := by
  apply (Real.log_le_iff_le_exp (one_div_pos.mpr hq)).2
  have hrecip : 1 / q ≤ 1 / Real.exp (-(p / 2)) := by
    exact one_div_le_one_div_of_le (Real.exp_pos (-(p / 2))) h
  simpa [Real.exp_neg] using hrecip

private lemma log_two_le_log_one_div_of_le_half
    {q : ℝ} (hq : 0 < q) (hqHalf : q ≤ 1 / 2) :
    Real.log 2 ≤ Real.log (1 / q) := by
  have hInv : 2 ≤ 1 / q := by
    apply (le_div_iff₀ hq).2
    nlinarith
  exact Real.strictMonoOn_log.monotoneOn (by norm_num)
    (one_div_pos.mpr hq) hInv

/-- The first clause of the paper's all-parameter one-step-flow proposition,
including its unsaturated assertion `m t log(1/q) ≤ 1`. -/
theorem local_dyadicMALA_boundaryFlow_allParameters
    (p theta : ℝ)
    (hp : V.malaFlowMomentThreshold ≤ p)
    (htheta : 0 < theta) (hthetaOne : theta ≤ 1)
    {S : Set (State d)} (hS : MeasurableSet S)
    (hSmass : Real.exp (-(p / 2)) ≤
      (V.target : Measure (State d)).real S)
    (hShalf : (V.target : Measure (State d)).real S ≤ 1 / 2) :
    let t := V.malaFlowStep p theta
    (V.target : Measure (State d)).real S *
          Real.sqrt (V.m * t * Real.log
            (1 / (V.target : Measure (State d)).real S)) /
          (2 : ℝ) ^ 13 ≤
        (boundaryFlow (V.target : Measure (State d))
          (V.dyadicMALA t (V.malaFlowStep_pos hp htheta)) S).toReal ∧
      V.m * t * Real.log
        (1 / (V.target : Measure (State d)).real S) ≤ 1 := by
  dsimp only
  let q : ℝ := (V.target : Measure (State d)).real S
  let u : ℝ := Real.log (1 / q)
  let t : ℝ := V.malaFlowStep p theta
  have ht : 0 < t := V.malaFlowStep_pos hp htheta
  have hq : 0 < q := (Real.exp_pos (-(p / 2))).trans_le hSmass
  have huLog : Real.log 2 ≤ u := by
    exact log_two_le_log_one_div_of_le_half hq hShalf
  have huUpper : u ≤ p / 2 :=
    log_one_div_le_half_of_exp_neg_half_le hq hSmass
  have hbudgetScalar :=
    V.malaFlow_exceptionalBudget hp htheta hthetaOne huLog huUpper
  have hmtuOne : V.m * t * u ≤ 1 :=
    hbudgetScalar.2.trans (by nlinarith [concreteB0_le_half])
  have hsqrtOne : Real.sqrt (V.m * t * u) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hmtuOne
  have hstep : t ≤ proposition32CrSmall /
      (V.L * Real.sqrt (p * ((d : ℝ) + p))) := by
    have hp0 : 0 < p := lt_of_lt_of_le
      (by nlinarith [V.malaFlowMomentThreshold_ge_two]) hp
    have hden : 0 < V.L * Real.sqrt (p * ((d : ℝ) + p)) := by
      exact mul_pos V.hL (Real.sqrt_pos.2
        (mul_pos hp0 (add_pos V.dimension_real_pos hp0)))
    unfold t malaFlowStep
    apply (div_le_div_iff_of_pos_right hden).2
    exact (mul_le_of_le_one_left concreteB0_pos.le hthetaOne).trans
      concreteB0_le_small
  have hbaseEq : proposition32CrLarge * V.L * t *
        Real.sqrt (p * ((d : ℝ) + p)) =
      theta * (proposition32CrLarge * concreteB0) := by
    unfold t malaFlowStep
    have hp0 : 0 < p := lt_of_lt_of_le
      (by nlinarith [V.malaFlowMomentThreshold_ge_two]) hp
    have hroot : 0 < Real.sqrt (p * ((d : ℝ) + p)) :=
      Real.sqrt_pos.2 (mul_pos hp0 (add_pos V.dimension_real_pos hp0))
    field_simp [V.hL.ne', hroot.ne']
  have hbaseLe : proposition32CrLarge * V.L * t *
        Real.sqrt (p * ((d : ℝ) + p)) ≤ theta / 16 := by
    rw [hbaseEq]
    have hmul := mul_le_mul_of_nonneg_left
      concreteB0_large_control htheta.le
    nlinarith
  have hbase0 : 0 ≤ proposition32CrLarge * V.L * t *
      Real.sqrt (p * ((d : ℝ) + p)) := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg proposition32CrLarge_pos.le V.hL.le) ht.le)
      (Real.sqrt_nonneg _)
  have hp0 : 0 ≤ p := (V.malaFlowMomentThreshold_ge_two.trans hp).trans' (by norm_num)
  have hrpow := Real.rpow_le_rpow hbase0 hbaseLe hp0
  have hqexp : Real.exp (-u) = q := by
    dsimp only [u]
    exact exp_neg_log_one_div hq
  have herror :
      (proposition32CrLarge * V.L * t *
          Real.sqrt (p * ((d : ℝ) + p))) ^ p ≤
        q * min 1 (Real.sqrt (V.m * t * Real.log (1 / q))) /
          (2 : ℝ) ^ 13 := by
    calc
      _ ≤ (theta / 16) ^ p := hrpow
      _ ≤ (1 / (2 : ℝ) ^ 13) * Real.exp (-u) *
          Real.sqrt (V.m * t * u) := hbudgetScalar.1
      _ = q * min 1 (Real.sqrt (V.m * t * Real.log (1 / q))) /
          (2 : ℝ) ^ 13 := by
        rw [hqexp, min_eq_right hsqrtOne]
        ring
  have hraw := V.local_dyadicMALA_boundaryFlow_lower_of_bakryLedoux
    (DiscreteTime.target_bakryLedoux V 0)
    p t (V.malaFlowMomentThreshold_ge_two.trans hp) ht hstep
    hS hq hShalf herror
  refine ⟨?_, ?_⟩
  · have hminEq : min 1 (Real.sqrt (V.m * t * Real.log (1 / q))) =
        Real.sqrt (V.m * t * Real.log (1 / q)) := by
      exact min_eq_right hsqrtOne
    simpa only [q, u, hminEq] using hraw
  · simpa only [t, q, u] using hmtuOne

/-- The second, globally safe clause of the paper's all-parameter one-step
flow proposition. -/
theorem safe_dyadicMALA_boundaryFlow_allParameters
    (t : ℝ) (ht : 0 < t)
    (hsmall : t ≤ 1 / (2 * V.L * (d : ℝ)))
    {S : Set (State d)} (hS : MeasurableSet S)
    (hSpos : 0 < (V.target : Measure (State d)).real S)
    (hShalf : (V.target : Measure (State d)).real S ≤ 1 / 2) :
    (V.target : Measure (State d)).real S *
          min 1 (Real.sqrt
            (V.m * t * Real.log
              (1 / (V.target : Measure (State d)).real S))) /
          (2 : ℝ) ^ 13 ≤
      (boundaryFlow (V.target : Measure (State d))
        (V.dyadicMALA t ht) S).toReal := by
  exact V.safe_dyadicMALA_boundaryFlow_lower_of_bakryLedoux
    (DiscreteTime.target_bakryLedoux V 0)
    t ht hsmall hS hSpos hShalf

/-- The two clauses of the all-parameter dyadic MALA flow theorem, bundled
with names matching their mathematical roles. -/
structure AllParameterMALAFlowBounds {d : ℕ}
    (V : FirstOrderPotential d) : Prop where
  localBound :
    ∀ (p theta : ℝ)
      (hp : V.malaFlowMomentThreshold ≤ p)
      (htheta : 0 < theta) (_hthetaOne : theta ≤ 1)
      {S : Set (State d)} (_hS : MeasurableSet S)
      (_hSmass : Real.exp (-(p / 2)) ≤
        (V.target : Measure (State d)).real S)
      (_hShalf : (V.target : Measure (State d)).real S ≤ 1 / 2),
        let t := V.malaFlowStep p theta
        (V.target : Measure (State d)).real S *
              Real.sqrt (V.m * t * Real.log
                (1 / (V.target : Measure (State d)).real S)) /
              (2 : ℝ) ^ 13 ≤
            (boundaryFlow (V.target : Measure (State d))
              (V.dyadicMALA t (V.malaFlowStep_pos hp htheta)) S).toReal ∧
          V.m * t * Real.log
            (1 / (V.target : Measure (State d)).real S) ≤ 1
  safeBound :
    ∀ (t : ℝ) (ht : 0 < t)
      (_hsmall : t ≤ 1 / (2 * V.L * (d : ℝ)))
      {S : Set (State d)} (_hS : MeasurableSet S)
      (_hSpos : 0 < (V.target : Measure (State d)).real S)
      (_hShalf : (V.target : Measure (State d)).real S ≤ 1 / 2),
        (V.target : Measure (State d)).real S *
              min 1 (Real.sqrt
                (V.m * t * Real.log
                  (1 / (V.target : Measure (State d)).real S))) /
              (2 : ℝ) ^ 13 ≤
          (boundaryFlow (V.target : Measure (State d))
            (V.dyadicMALA t ht) S).toReal

/-- Proposition 3.4 in its full parameter range, with the paper's universal
constants instantiated by `concreteA0` and `concreteB0`. -/
theorem allParameterMALAFlowBounds : AllParameterMALAFlowBounds V where
  localBound p theta hp htheta hthetaOne _S hS hSmass hShalf :=
    V.local_dyadicMALA_boundaryFlow_allParameters
      p theta hp htheta hthetaOne hS hSmass hShalf
  safeBound t ht hsmall _S hS hSpos hShalf :=
    V.safe_dyadicMALA_boundaryFlow_allParameters
      t ht hsmall hS hSpos hShalf

end FirstOrderPotential
end Concrete

end

end UniformRandomMALA
