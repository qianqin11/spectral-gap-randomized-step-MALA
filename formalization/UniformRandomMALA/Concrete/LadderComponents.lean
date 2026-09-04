import UniformRandomMALA.Concrete.SafeComponent
import UniformRandomMALA.ExceptionalBudgetArithmetic

/-!
# Concrete multiscale MALA components

This module turns the geometric ladder into the finite kernel family used by
component aggregation.  The measure-theoretic cut assignment is separated
from the scalar exceptional-set estimate, so the latter can be discharged by
elementary real arithmetic without changing any kernel proof.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

namespace Concrete

/-- The abstract arithmetic parameters refer to the same dimension and
convexity/smoothness constants as the concrete potential. -/
structure PotentialParametersMatch {d : ℕ}
    (V : FirstOrderPotential d) (p : Parameters) : Prop where
  dimension : p.d = d
  strongConvexity : p.m = V.m
  smoothness : p.L = V.L

lemma ladderMoment_ge_pStar (p : Parameters) (j : ℕ) :
    p.pStar ≤ ladderMoment p j := by
  unfold ladderMoment
  have hpow : (1 : ℝ) ≤ (4 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_right hpow p.pStar_nonneg]

lemma two_le_ladderMoment (p : Parameters) (j : ℕ) :
    2 ≤ ladderMoment p j :=
  p.two_le_pStar.trans (ladderMoment_ge_pStar p j)

/-- The number of noninitial ladder levels is at most `p⋆`.  This coarse
bound is sufficient for the harmonic sum and avoids ceilings or base-four
logarithms in the final estimate. -/
lemma ladderTopIndex_cast_le_pStar
    (p : Parameters) :
    (ladderTopIndex p : ℝ) ≤ p.pStar := by
  let J : ℕ := ladderTopIndex p
  by_cases hJ : J = 0
  · simp [J, hJ, p.pStar_nonneg]
  have hJone : 1 ≤ J := Nat.one_le_iff_ne_zero.mpr hJ
  have hpred : J - 1 < ladderTopIndex p := by
    simpa only [J] using (Nat.sub_lt (Nat.zero_lt_of_ne_zero hJ) (by norm_num))
  have hbelow := ladderMoment_before_top_lt p hpred
  have hlogBelow : Real.log (ladderMoment p (J - 1)) < Real.log p.d := by
    exact Real.strictMonoOn_log (ladderMoment_pos p (J - 1)) p.hd hbelow
  have hpow0 : (4 : ℝ) ^ (J - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hp0 : p.pStar ≠ 0 := p.hpStar_pos.ne'
  unfold ladderMoment at hlogBelow
  rw [Real.log_mul hpow0 hp0, Real.log_pow] at hlogBelow
  have hlogp : 0 ≤ Real.log p.pStar :=
    Real.log_nonneg ((by norm_num : (1 : ℝ) ≤ 2).trans p.two_le_pStar)
  have hlog4 : 1 ≤ Real.log 4 := by
    have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [hlog4eq]
    nlinarith [Real.log_two_gt_d9]
  have hpredLog : ((J - 1 : ℕ) : ℝ) < Real.log p.d := by
    have hmul := mul_le_mul_of_nonneg_left hlog4 (Nat.cast_nonneg (J - 1))
    simp only [mul_one] at hmul
    nlinarith
  have hJcast : (J : ℝ) = (J - 1 : ℕ) + 1 := by
    exact_mod_cast (Nat.sub_add_cancel hJone).symm
  have hlogd : Real.log p.d ≤ Real.log (p.d + 1) := by
    exact Real.strictMonoOn_log.monotoneOn p.hd (add_pos p.hd zero_lt_one)
      (le_add_of_nonneg_right zero_le_one)
  have hfactor0 : 0 ≤ 1 + Real.log (p.d + 1) + Real.log p.kappa := by
    have hdlog : 0 ≤ Real.log (p.d + 1) :=
      Real.log_nonneg (by linarith [p.hd_one])
    have hklog := Real.log_nonneg p.hkappa_one
    linarith
  have hpstarLower :
      2 * (1 + Real.log (p.d + 1) + Real.log p.kappa) ≤ p.pStar := by
    rw [p.hpStar]
    exact mul_le_mul_of_nonneg_right p.hA0 hfactor0
  have hklog := Real.log_nonneg p.hkappa_one
  dsimp only [J] at hJcast ⊢
  nlinarith

/-- The component conductance coefficient: the first component uses
`log 2`, while later components use the preceding-quarter lower edge of the
moment partition. -/
def ladderConductanceReal (p : Parameters) (j : ℕ) : ℝ :=
  if j = 0 then
    Real.sqrt (p.m * ladderEndpoint p j * Real.log 2) / (2 : ℝ) ^ 13
  else
    Real.sqrt (p.m * ladderEndpoint p j * ladderMoment p j / 8) /
      (2 : ℝ) ^ 13

def ladderConductance (p : Parameters) (j : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (ladderConductanceReal p j)

/-- Scalar exceptional-set budget specialized to the already constructed
ladder.  This is the only input to the cut-assignment proof that still
contains the universal `A₀,b₀` arithmetic. -/
def LadderExceptionalBudget (p : Parameters) : Prop :=
  ∀ j : ℕ, ∀ u : ℝ, Real.log 2 ≤ u → u ≤ ladderMoment p j / 2 →
    (p.ladderTheta / 16) ^ (ladderMoment p j) ≤
        (1 / (2 : ℝ) ^ 13) * Real.exp (-u) *
          Real.sqrt (p.m * ladderEndpoint p j * u) ∧
      p.m * ladderEndpoint p j * u ≤ p.b0 / 2

/-- The finite endpoint form of the exceptional budget.  Antitonicity of
`exp (-u) * sqrt u` will extend it to each full logarithmic band. -/
def LadderEndpointExceptionalBudget (p : Parameters) : Prop :=
  ∀ j : ℕ,
    (p.ladderTheta / 16) ^ (ladderMoment p j) ≤
      (1 / (2 : ℝ) ^ 13) *
        Real.exp (-(ladderMoment p j / 2)) *
        Real.sqrt
          (p.m * ladderEndpoint p j * (ladderMoment p j / 2))

/-- Explicit coefficient-wise condition on the universal choice of `A₀`.
It is equivalent to the two numerical comparisons used in the paper's
displayed sufficient choice, but avoids division by `log 16 - 1/2`. -/
def ExceptionalBudgetParameterChoice (p : Parameters) : Prop :=
  13 * Real.log 2 + (1 / 2) * Real.log (2 / p.b0) ≤
      p.A0 * (Real.log 16 - 1 / 2) ∧
    1 ≤ p.A0 * (Real.log 16 - 1 / 2)

lemma ladder_log_condition_of_parameterChoice
    (p : Parameters) (hchoice : ExceptionalBudgetParameterChoice p)
    (j : ℕ) :
    ladderMoment p j * (Real.log 16 - 1 / 2) ≥
      13 * Real.log 2 +
        (1 / 2) * Real.log (2 * p.kappa / p.b0) +
        (1 / 4) * Real.log
          ((p.d + ladderMoment p j) / ladderMoment p j) := by
  let moment : ℝ := ladderMoment p j
  let C : ℝ := Real.log 16 - 1 / 2
  let B : ℝ := p.A0 * C
  let ld : ℝ := Real.log (p.d + 1)
  let lk : ℝ := Real.log p.kappa
  let base : ℝ := 13 * Real.log 2 + (1 / 2) * Real.log (2 / p.b0)
  have hmom : 0 < moment := ladderMoment_pos p j
  have hmomOne : 1 ≤ moment := (two_le_ladderMoment p j).trans' (by norm_num)
  have hC : 0 ≤ C := by
    have hlog16 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      norm_num
    dsimp only [C]
    rw [hlog16]
    nlinarith [Real.log_two_gt_d9]
  have hld : 0 ≤ ld := by
    dsimp only [ld]
    exact Real.log_nonneg (by linarith [p.hd_one])
  have hlk : 0 ≤ lk := by
    dsimp only [lk]
    exact Real.log_nonneg p.hkappa_one
  have hratio : (p.d + moment) / moment ≤ p.d + 1 := by
    apply (div_le_iff₀ hmom).2
    have hdmul := mul_le_mul_of_nonneg_left hmomOne p.hd.le
    nlinarith
  have hlogratio : Real.log ((p.d + moment) / moment) ≤ ld := by
    dsimp only [ld]
    exact Real.strictMonoOn_log.monotoneOn
      (div_pos (add_pos p.hd hmom) hmom)
      (add_pos p.hd zero_lt_one) hratio
  have hlogKappa : Real.log (2 * p.kappa / p.b0) =
      Real.log (2 / p.b0) + lk := by
    have hk0 : 0 < p.kappa := lt_of_lt_of_le zero_lt_one p.hkappa_one
    rw [show 2 * p.kappa / p.b0 = (2 / p.b0) * p.kappa by ring,
      Real.log_mul (ne_of_gt (div_pos (by norm_num) p.hb0)) (ne_of_gt hk0)]
  have hBbase : base ≤ B := by simpa only [base, B, C] using hchoice.1
  have hBone : 1 ≤ B := by simpa only [B, C] using hchoice.2
  have hB0 : 0 ≤ B := zero_le_one.trans hBone
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
  have hmomStar : p.pStar ≤ moment := ladderMoment_ge_pStar p j
  have hmomentC : p.pStar * C ≤ moment * C :=
    mul_le_mul_of_nonneg_right hmomStar hC
  have hpstarC : p.pStar * C = B * (1 + ld + lk) := by
    dsimp only [B, C, ld, lk]
    rw [p.hpStar]
    ring
  have hmain : base + (1 / 4) * ld + (1 / 2) * lk ≤ moment * C :=
    hcoeff.trans (hpstarC.symm.le.trans hmomentC)
  rw [hlogKappa]
  dsimp only [moment, C, base, lk] at hmain ⊢
  nlinarith

theorem ladderEndpointExceptionalBudget_of_parameterChoice
    (p : Parameters) (hchoice : ExceptionalBudgetParameterChoice p) :
    LadderEndpointExceptionalBudget p := by
  intro j
  apply exceptional_budget_endpoint_of_log_condition
    p.d p.m p.L p.kappa p.b0 p.ladderTheta
      (ladderMoment p j) (ladderEndpoint p j)
    p.hd p.hm p.hL p.hkappa (lt_of_lt_of_le zero_lt_one p.hkappa_one)
    p.hb0 p.ladderTheta_pos p.ladderTheta_le_one
    (two_le_ladderMoment p j)
  · unfold ladderEndpoint ladderNominalEndpoint
    ring
  · exact ladder_log_condition_of_parameterChoice p hchoice j

/-- Endpoint control plus the already checked unsaturated arithmetic imply
the full exceptional budget. -/
theorem ladderExceptionalBudget_of_endpoint
    (p : Parameters) (hend : LadderEndpointExceptionalBudget p) :
    LadderExceptionalBudget p := by
  intro j u huLog huUpper
  let moment : ℝ := ladderMoment p j
  let t : ℝ := ladderEndpoint p j
  have hmom : 0 < moment := ladderMoment_pos p j
  have ht : 0 < t := ladderEndpoint_pos p j
  have hu0 : 0 ≤ u := log_two_pos.le.trans huLog
  have hhalf : 1 / 2 ≤ u := by
    exact (by norm_num : (1 / 2 : ℝ) ≤ 0.6931471803).trans
      (Real.log_two_gt_d9.le.trans huLog)
  have hmono : Real.exp (-(moment / 2)) * Real.sqrt (moment / 2) ≤
      Real.exp (-u) * Real.sqrt u :=
    exp_neg_mul_sqrt_antitone hhalf huUpper
  have hmt0 : 0 ≤ p.m * t := mul_nonneg p.m_nonneg ht.le
  have hscaled := mul_le_mul_of_nonneg_left hmono
    (Real.sqrt_nonneg (p.m * t))
  have hright :
      (1 / (2 : ℝ) ^ 13) * Real.exp (-(moment / 2)) *
          Real.sqrt (p.m * t * (moment / 2)) ≤
        (1 / (2 : ℝ) ^ 13) * Real.exp (-u) *
          Real.sqrt (p.m * t * u) := by
    rw [Real.sqrt_mul hmt0, Real.sqrt_mul hmt0]
    have hcoef : 0 ≤ (1 / (2 : ℝ) ^ 13) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hscaled hcoef]
  refine ⟨(hend j).trans ?_, ?_⟩
  · simpa only [moment, t] using hright
  · apply exceptional_budget_unsaturated p.d p.m p.L p.kappa p.b0
      p.ladderTheta moment u t p.hd p.hm p.hL p.hkappa p.hkappa_one
      p.hb0 p.ladderTheta_le_one hmom hu0 huUpper
    dsimp only [t, moment]
    unfold ladderEndpoint ladderNominalEndpoint
    ring

/-- The paper's explicit universal parameter choice discharges the entire
ladder exceptional budget. -/
theorem ladderExceptionalBudget_of_parameterChoice
    (p : Parameters) (hchoice : ExceptionalBudgetParameterChoice p) :
    LadderExceptionalBudget p :=
  ladderExceptionalBudget_of_endpoint p
    (ladderEndpointExceptionalBudget_of_parameterChoice p hchoice)

lemma exp_neg_log_one_div {q : ℝ} (hq : 0 < q) :
    Real.exp (-Real.log (1 / q)) = q := by
  rw [Real.exp_neg, Real.exp_log (one_div_pos.mpr hq)]
  field_simp

lemma ladderConductanceReal_pos (p : Parameters) (j : ℕ) :
    0 < ladderConductanceReal p j := by
  unfold ladderConductanceReal
  split_ifs
  · exact div_pos
      (Real.sqrt_pos.2 (mul_pos (mul_pos p.hm (ladderEndpoint_pos p j)) log_two_pos))
      (by positivity)
  · exact div_pos
      (Real.sqrt_pos.2 (div_pos
        (mul_pos (mul_pos p.hm (ladderEndpoint_pos p j)) (ladderMoment_pos p j))
        (by norm_num)))
      (by positivity)

lemma ladderConductance_ne_zero (p : Parameters) (j : ℕ) :
    ladderConductance p j ≠ 0 :=
  (ENNReal.ofReal_pos.mpr (ladderConductanceReal_pos p j)).ne'

lemma ladderConductance_ne_top (p : Parameters) (j : ℕ) :
    ladderConductance p j ≠ ∞ := ENNReal.ofReal_ne_top

lemma ladderSelectionWeight_ne_zero (p : Parameters) (j : ℕ) :
    FirstOrderPotential.ladderSelectionWeight p j ≠ 0 := by
  exact mul_ne_zero
    (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
    (ENNReal.ofReal_pos.mpr (by linarith [ladderEndpoint_pos p j])).ne'

lemma ladderSelectionWeight_ne_top (p : Parameters) (j : ℕ) :
    FirstOrderPotential.ladderSelectionWeight p j ≠ ∞ := by
  exact ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr p.hH).ne')
    ENNReal.ofReal_ne_top

/-! ## Elementary harmonic-sum estimate -/

/-- The ENNReal selection weight has the expected ordinary-real value. -/
lemma ladderSelectionWeight_toReal (p : Parameters) (j : ℕ) :
    (FirstOrderPotential.ladderSelectionWeight p j).toReal =
      componentWeight p.H (ladderEndpoint p j) := by
  rw [FirstOrderPotential.ladderSelectionWeight, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal p.hH.le,
    ENNReal.toReal_ofReal
      (div_nonneg (ladderEndpoint_pos p j).le (by norm_num))]
  unfold componentWeight
  field_simp [p.hH.ne']

/-- Squaring the real conductance removes the square root and recovers the
two scalar conductance formulas used in the paper. -/
lemma ladderConductance_toReal_sq (p : Parameters) (j : ℕ) :
    (ladderConductance p j).toReal ^ 2 =
      if j = 0 then safePhiSq p.m (ladderEndpoint p j)
      else ladderPhiSq p.m (ladderEndpoint p j) (ladderMoment p j) := by
  rw [ladderConductance, ENNReal.toReal_ofReal
    (ladderConductanceReal_pos p j).le]
  unfold ladderConductanceReal safePhiSq ladderPhiSq
  split_ifs
  · have hs := Real.sq_sqrt
      (mul_nonneg (mul_nonneg p.m_nonneg (ladderEndpoint_pos p j).le)
        log_two_pos.le)
    nlinarith
  · have hs := Real.sq_sqrt
      (div_nonneg
        (mul_nonneg (mul_nonneg p.m_nonneg (ladderEndpoint_pos p j).le)
          (ladderMoment_pos p j).le) (by norm_num : (0 : ℝ) ≤ 8))
    nlinarith

/-- Exact ordinary-real value of one ENNReal harmonic summand. -/
lemma ladder_harmonic_term_toReal (p : Parameters) (j : ℕ) :
    ((FirstOrderPotential.ladderSelectionWeight p j *
        (ladderConductance p j) ^ 2)⁻¹).toReal =
      if j = 0 then
        (2 : ℝ) ^ 27 * p.H /
          (p.m * (ladderEndpoint p j) ^ 2 * Real.log 2)
      else
        (2 : ℝ) ^ 30 * p.H /
          (p.m * (ladderEndpoint p j) ^ 2 * ladderMoment p j) := by
  rw [ENNReal.toReal_inv, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ladderSelectionWeight_toReal, ladderConductance_toReal_sq]
  split_ifs
  · simpa only [one_div] using
      safe_component_reciprocal p.H p.m (ladderEndpoint p j)
        p.hH p.hm (ladderEndpoint_pos p j)
  · simpa only [one_div] using
      ladder_component_reciprocal p.H p.m (ladderEndpoint p j)
        (ladderMoment p j) p.hH p.hm (ladderEndpoint_pos p j)
        (ladderMoment_pos p j)

/-- Substitution of the explicit ladder endpoint into one harmonic
summand.  The noninitial moment cancels exactly. -/
lemma ladder_harmonic_term_closed (p : Parameters) (j : ℕ) :
    ((FirstOrderPotential.ladderSelectionWeight p j *
        (ladderConductance p j) ^ 2)⁻¹).toReal =
      if j = 0 then
        (2 : ℝ) ^ 27 * p.H * p.L ^ 2 * p.pStar * (p.d + p.pStar) /
          (p.m * p.ladderTheta ^ 2 * p.b0 ^ 2 * Real.log 2)
      else
        (2 : ℝ) ^ 30 * p.H * p.L ^ 2 *
          (p.d + ladderMoment p j) /
          (p.m * p.ladderTheta ^ 2 * p.b0 ^ 2) := by
  rw [ladder_harmonic_term_toReal]
  split_ifs
  · subst j
    rw [ladderEndpoint, ladderNominalEndpoint, ladderMoment_zero]
    have harg : 0 ≤ p.pStar * (p.d + p.pStar) :=
      p.rejectionArgument_pos.le
    have hsqrt := Real.sq_sqrt harg
    field_simp [p.hm.ne', p.hL.ne', p.hb0.ne', p.ladderTheta_pos.ne',
      p.hpStar_pos.ne', (add_pos p.hd p.hpStar_pos).ne', log_two_ne_zero,
      (Real.sqrt_pos.2 p.rejectionArgument_pos).ne']
    rw [hsqrt]
    ring
  · rw [ladderEndpoint, ladderNominalEndpoint]
    have hargpos : 0 < ladderMoment p j * (p.d + ladderMoment p j) :=
      mul_pos (ladderMoment_pos p j)
        (add_pos p.hd (ladderMoment_pos p j))
    have harg : 0 ≤ ladderMoment p j * (p.d + ladderMoment p j) :=
      hargpos.le
    have hsqrt := Real.sq_sqrt harg
    field_simp [p.hm.ne', p.hL.ne', p.hb0.ne', p.ladderTheta_pos.ne',
      (ladderMoment_pos p j).ne',
      (add_pos p.hd (ladderMoment_pos p j)).ne',
      (Real.sqrt_pos.2 hargpos).ne']
    rw [hsqrt]
    ring

/-- The finite harmonic sum represented in ordinary reals. -/
def ladderHarmonicReal (p : Parameters) : ℝ :=
  ∑ j : Fin (ladderTopIndex p + 1),
    if j.val = 0 then
      (2 : ℝ) ^ 27 * p.H * p.L ^ 2 * p.pStar * (p.d + p.pStar) /
        (p.m * p.ladderTheta ^ 2 * p.b0 ^ 2 * Real.log 2)
    else
      (2 : ℝ) ^ 30 * p.H * p.L ^ 2 *
        (p.d + ladderMoment p j.val) /
        (p.m * p.ladderTheta ^ 2 * p.b0 ^ 2)

/-- The ENNReal harmonic cost equals its finite ordinary-real expansion. -/
lemma ladder_harmonicCost_toReal (p : Parameters) :
    (harmonicCost
      (fun j : Fin (ladderTopIndex p + 1) =>
        FirstOrderPotential.ladderSelectionWeight p j.val)
      (fun j : Fin (ladderTopIndex p + 1) =>
        ladderConductance p j.val)).toReal = ladderHarmonicReal p := by
  unfold harmonicCost ladderHarmonicReal
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro j hj
    exact ladder_harmonic_term_closed p j.val
  · intro j hj
    apply ENNReal.inv_ne_top.mpr
    exact mul_ne_zero (ladderSelectionWeight_ne_zero p j.val)
      (pow_ne_zero 2 (ladderConductance_ne_zero p j.val))

lemma ladderMoment_mono (p : Parameters) {i j : ℕ} (hij : i ≤ j) :
    ladderMoment p i ≤ ladderMoment p j := by
  unfold ladderMoment
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hij) p.pStar_nonneg

/-- A concrete universal upper bound for the ladder harmonic sum. -/
def ladderHarmonicBound (p : Parameters) : ℝ :=
  (6 * (2 : ℝ) ^ 30) * p.H * p.L ^ 2 * p.pStar * (p.d + p.pStar) /
    (p.m * p.ladderTheta ^ 2 * p.b0 ^ 2)

lemma ladderHarmonicBound_pos (p : Parameters) :
    0 < ladderHarmonicBound p := by
  unfold ladderHarmonicBound
  exact div_pos
    (mul_pos
      (mul_pos
        (mul_pos
          (mul_pos (by positivity : 0 < 6 * (2 : ℝ) ^ 30) p.hH)
          (sq_pos_of_pos p.hL))
        p.hpStar_pos)
      (add_pos p.hd p.hpStar_pos))
    (mul_pos (mul_pos p.hm (sq_pos_of_pos p.ladderTheta_pos))
      (sq_pos_of_pos p.hb0))

/-- Elementary proof of the harmonic-sum estimate.  The only ingredients
are `p_J < 4d`, the coarse cardinality bound `J ≤ p⋆`, and the exact
summand identities above. -/
theorem ladderHarmonicReal_le (p : Parameters) (hsmall : p.pStar < p.d) :
    ladderHarmonicReal p ≤ ladderHarmonicBound p := by
  let J : ℕ := ladderTopIndex p
  let D : ℝ := p.m * p.ladderTheta ^ 2 * p.b0 ^ 2
  let X : ℝ := p.H * p.L ^ 2 * p.pStar * (p.d + p.pStar)
  let T : ℝ := 5 * (2 : ℝ) ^ 30 * p.H * p.L ^ 2 *
    (p.d + p.pStar) / D
  have hD : 0 < D := by
    dsimp only [D]
    exact mul_pos (mul_pos p.hm (sq_pos_of_pos p.ladderTheta_pos))
      (sq_pos_of_pos p.hb0)
  have hX : 0 < X := by
    dsimp only [X]
    exact mul_pos
      (mul_pos (mul_pos p.hH (sq_pos_of_pos p.hL)) p.hpStar_pos)
      (add_pos p.hd p.hpStar_pos)
  have hT : 0 ≤ T := by
    dsimp only [T]
    exact (div_pos
      (mul_pos
        (mul_pos
          (mul_pos (by positivity : 0 < 5 * (2 : ℝ) ^ 30) p.hH)
          (sq_pos_of_pos p.hL))
        (add_pos p.hd p.hpStar_pos)) hD).le
  have htop := (ladderMoment_top_range p hsmall).2
  have htailTerm : ∀ i : Fin J,
      (2 : ℝ) ^ 30 * p.H * p.L ^ 2 *
          (p.d + ladderMoment p i.succ.val) / D ≤ T := by
    intro i
    have hiJ : i.succ.val ≤ ladderTopIndex p := by
      change i.val + 1 ≤ ladderTopIndex p
      simpa only [J] using Nat.succ_le_of_lt i.isLt
    have hmom := ladderMoment_mono p hiJ
    have hdim : p.d + ladderMoment p i.succ.val ≤
        5 * (p.d + p.pStar) := by
      nlinarith [p.hpStar_pos]
    dsimp only [T]
    apply (div_le_div_iff_of_pos_right hD).2
    have hscale : 0 ≤ (2 : ℝ) ^ 30 * p.H * p.L ^ 2 :=
      mul_nonneg
        (mul_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ 30) p.hH.le)
        (sq_nonneg p.L)
    have := mul_le_mul_of_nonneg_left hdim hscale
    nlinarith
  have htail :
      (∑ i : Fin J,
        (2 : ℝ) ^ 30 * p.H * p.L ^ 2 *
          (p.d + ladderMoment p i.succ.val) / D) ≤ (J : ℝ) * T := by
    have hsum := Finset.sum_le_card_nsmul Finset.univ
      (fun i : Fin J =>
        (2 : ℝ) ^ 30 * p.H * p.L ^ 2 *
          (p.d + ladderMoment p i.succ.val) / D)
      T (fun i hi => htailTerm i)
    simpa [Finset.card_fin, nsmul_eq_mul] using hsum
  have hJ : (J : ℝ) ≤ p.pStar := by
    simpa only [J] using ladderTopIndex_cast_le_pStar p
  have htail' :
      (∑ i : Fin J,
        (2 : ℝ) ^ 30 * p.H * p.L ^ 2 *
          (p.d + ladderMoment p i.succ.val) / D) ≤ p.pStar * T :=
    htail.trans (mul_le_mul_of_nonneg_right hJ hT)
  have hsafe :
      (2 : ℝ) ^ 27 * p.H * p.L ^ 2 * p.pStar * (p.d + p.pStar) /
          (D * Real.log 2) ≤ (2 : ℝ) ^ 30 * X / D := by
    have hcoef : (2 : ℝ) ^ 27 / Real.log 2 ≤ (2 : ℝ) ^ 30 := by
      apply (div_le_iff₀ log_two_pos).2
      nlinarith [Real.log_two_gt_d9]
    have hscaled := mul_le_mul_of_nonneg_right hcoef hX.le
    calc
      (2 : ℝ) ^ 27 * p.H * p.L ^ 2 * p.pStar * (p.d + p.pStar) /
          (D * Real.log 2) = ((2 : ℝ) ^ 27 / Real.log 2) * X / D := by
            dsimp only [X]
            field_simp [hD.ne', log_two_ne_zero]
      _ ≤ (2 : ℝ) ^ 30 * X / D :=
        (div_le_div_iff_of_pos_right hD).2 hscaled
  rw [ladderHarmonicReal, Fin.sum_univ_succ]
  simp only [Fin.val_zero, ↓reduceIte, Fin.val_succ, Nat.succ_ne_zero]
  change
    (2 : ℝ) ^ 27 * p.H * p.L ^ 2 * p.pStar * (p.d + p.pStar) /
          (D * Real.log 2) +
        (∑ i : Fin J, (2 : ℝ) ^ 30 * p.H * p.L ^ 2 *
          (p.d + ladderMoment p i.succ.val) / D) ≤ ladderHarmonicBound p
  calc
    _ ≤ (2 : ℝ) ^ 30 * X / D + p.pStar * T :=
      add_le_add hsafe htail'
    _ = ladderHarmonicBound p := by
      dsimp only [ladderHarmonicBound, D, X, T]
      ring

/-- ENNReal form of the elementary harmonic-sum estimate. -/
theorem ladder_harmonicCost_le (p : Parameters) (hsmall : p.pStar < p.d) :
    harmonicCost
      (fun j : Fin (ladderTopIndex p + 1) =>
        FirstOrderPotential.ladderSelectionWeight p j.val)
      (fun j : Fin (ladderTopIndex p + 1) => ladderConductance p j.val) ≤
      ENNReal.ofReal (ladderHarmonicBound p) := by
  let γ : Fin (ladderTopIndex p + 1) → ℝ≥0∞ := fun j =>
    FirstOrderPotential.ladderSelectionWeight p j.val
  let φ : Fin (ladderTopIndex p + 1) → ℝ≥0∞ := fun j =>
    ladderConductance p j.val
  have htop : harmonicCost γ φ ≠ ∞ :=
    harmonicCost_ne_top γ φ
      (fun j => ladderSelectionWeight_ne_zero p j.val)
      (fun j => ladderConductance_ne_zero p j.val)
  apply (ENNReal.toReal_le_toReal htop ENNReal.ofReal_ne_top).mp
  rw [ladder_harmonicCost_toReal,
    ENNReal.toReal_ofReal (ladderHarmonicBound_pos p).le]
  exact ladderHarmonicReal_le p hsmall

/-- The explicit lower coefficient obtained by inverting twice the
harmonic bound. -/
def ladderGapBound (p : Parameters) : ℝ :=
  p.m * p.ladderTheta ^ 2 * p.b0 ^ 2 /
    (12 * (2 : ℝ) ^ 30 * p.H * p.L ^ 2 * p.pStar * (p.d + p.pStar))

lemma ladderGapBound_pos (p : Parameters) : 0 < ladderGapBound p := by
  unfold ladderGapBound
  exact div_pos
    (mul_pos (mul_pos p.hm (sq_pos_of_pos p.ladderTheta_pos))
      (sq_pos_of_pos p.hb0))
    (mul_pos
      (mul_pos
        (mul_pos
          (mul_pos (by positivity : 0 < 12 * (2 : ℝ) ^ 30) p.hH)
          (sq_pos_of_pos p.hL))
        p.hpStar_pos)
      (add_pos p.hd p.hpStar_pos))

/-- Exact ENNReal identity between the explicit ladder coefficient and the
reciprocal of twice the harmonic upper bound. -/
lemma ladderGapBound_eq_inv_harmonicBound (p : Parameters) :
    ENNReal.ofReal (ladderGapBound p) =
      ((2 : ℝ≥0∞) * ENNReal.ofReal (ladderHarmonicBound p))⁻¹ := by
  have hbase0 : ENNReal.ofReal (ladderHarmonicBound p) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (ladderHarmonicBound_pos p)).ne'
  have hrightTop :
      ((2 : ℝ≥0∞) * ENNReal.ofReal (ladderHarmonicBound p))⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr (mul_ne_zero (by norm_num) hbase0)
  apply (ENNReal.toReal_eq_toReal_iff' ENNReal.ofReal_ne_top hrightTop).mp
  rw [ENNReal.toReal_ofReal (ladderGapBound_pos p).le, ENNReal.toReal_inv,
    ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (ladderHarmonicBound_pos p).le]
  unfold ladderGapBound ladderHarmonicBound
  field_simp [p.hm.ne', p.hH.ne', p.hL.ne', p.hb0.ne',
    p.hpStar_pos.ne', (add_pos p.hd p.hpStar_pos).ne',
    p.ladderTheta_pos.ne']
  ring

namespace FirstOrderPotential

variable {d : ℕ} (V : FirstOrderPotential d)

/-- Every ladder step satisfies Proposition 3.2's moment-dependent step
restriction when `b₀` is chosen below its small constant. -/
lemma ladderEndpoint_le_proposition32_scale
    (p : Parameters) (hmatch : PotentialParametersMatch V p)
    (hbSmall : p.b0 ≤ proposition32CrSmall) (j : ℕ) :
    ladderEndpoint p j ≤ proposition32CrSmall /
      (V.L * Real.sqrt
        (ladderMoment p j * ((d : ℝ) + ladderMoment p j))) := by
  have htheta := p.ladderTheta_le_one
  have hroot : 0 < Real.sqrt
      (ladderMoment p j * ((d : ℝ) + ladderMoment p j)) := by
    apply Real.sqrt_pos.2
    exact mul_pos (ladderMoment_pos p j)
      (add_pos V.dimension_real_pos (ladderMoment_pos p j))
  have hden : 0 < V.L * Real.sqrt
      (ladderMoment p j * ((d : ℝ) + ladderMoment p j)) :=
    mul_pos V.hL hroot
  unfold ladderEndpoint ladderNominalEndpoint
  rw [hmatch.dimension, hmatch.smoothness]
  calc
    p.ladderTheta *
        (p.b0 / (V.L * Real.sqrt
          (ladderMoment p j * ((d : ℝ) + ladderMoment p j)))) =
      (p.ladderTheta * p.b0) /
        (V.L * Real.sqrt
          (ladderMoment p j * ((d : ℝ) + ladderMoment p j))) := by ring
    _ ≤ proposition32CrSmall /
        (V.L * Real.sqrt
          (ladderMoment p j * ((d : ℝ) + ladderMoment p j))) := by
      apply (div_le_div_iff_of_pos_right hden).2
      exact (mul_le_of_le_one_left p.hb0.le htheta).trans hbSmall

/-- A ladder component assigned to a logarithmic-mass band has the claimed
flow.  All probability and kernel reasoning is concrete; the specialized
scalar exceptional budget is its only non-geometric input. -/
theorem local_ladder_boundaryFlow_lower_of_bakryLedoux
    (p : Parameters) (hmatch : PotentialParametersMatch V p)
    (hbSmall : p.b0 ≤ proposition32CrSmall)
    (hbLarge : proposition32CrLarge * p.b0 ≤ 1 / 16)
    (hbudget : LadderExceptionalBudget p)
    (hBL : BakryLedouxEnlargement
      (V.target : Measure (State d)) V.m
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure))
    (j : ℕ) (u : ℝ)
    (huLog : Real.log 2 ≤ u)
    (huUpper : u ≤ ladderMoment p j / 2)
    (huLower : if j = 0 then Real.log 2 ≤ u
      else ladderMoment p j / 8 ≤ u)
    {S : Set (State d)} (hS : MeasurableSet S)
    (hSpos : 0 < (V.target : Measure (State d)).real S)
    (hu : u = Real.log (1 / (V.target : Measure (State d)).real S)) :
    ladderConductance p j * (V.target : Measure (State d)) S ≤
      boundaryFlow (V.target : Measure (State d))
        (V.dyadicMALA (ladderEndpoint p j) (ladderEndpoint_pos p j)) S := by
  let moment : ℝ := ladderMoment p j
  let t : ℝ := ladderEndpoint p j
  let q : ℝ := (V.target : Measure (State d)).real S
  have hmom : 0 < moment := ladderMoment_pos p j
  have hmomTwo : 2 ≤ moment := two_le_ladderMoment p j
  have ht : 0 < t := ladderEndpoint_pos p j
  have hq : 0 < q := hSpos
  have hbudget' := hbudget j u huLog huUpper
  have hmtu : p.m * t * u ≤ p.b0 / 2 := hbudget'.2
  have hu0 : 0 ≤ u := log_two_pos.le.trans huLog
  have hinside :
      (if j = 0 then p.m * t * Real.log 2
        else p.m * t * moment / 8) ≤ p.m * t * u := by
    split_ifs with hj
    · exact mul_le_mul_of_nonneg_left huLog
        (mul_nonneg p.m_nonneg ht.le)
    · have hlower : moment / 8 ≤ u := by simpa [hj] using huLower
      have hmul := mul_le_mul_of_nonneg_left hlower
        (mul_nonneg p.m_nonneg ht.le)
      nlinarith
  have hinside0 : 0 ≤ (if j = 0 then p.m * t * Real.log 2
      else p.m * t * moment / 8) := by
    split_ifs
    · exact mul_nonneg (mul_nonneg p.m_nonneg ht.le) log_two_pos.le
    · exact div_nonneg
        (mul_nonneg (mul_nonneg p.m_nonneg ht.le) hmom.le) (by norm_num)
  have hinsideOne :
      (if j = 0 then p.m * t * Real.log 2
        else p.m * t * moment / 8) ≤ 1 := by
    have hbdiv : p.b0 / 2 ≤ 1 := by nlinarith [p.hb0_half]
    exact hinside.trans (hmtu.trans hbdiv)
  have hfactor : ladderConductanceReal p j ≤
      min 1 (Real.sqrt (p.m * t * u)) / (2 : ℝ) ^ 13 := by
    have hsqrtInside : Real.sqrt
        (if j = 0 then p.m * t * Real.log 2
          else p.m * t * moment / 8) ≤ 1 := by
      simpa using Real.sqrt_le_sqrt hinsideOne
    have hsqrtU : Real.sqrt
        (if j = 0 then p.m * t * Real.log 2
          else p.m * t * moment / 8) ≤ Real.sqrt (p.m * t * u) :=
      Real.sqrt_le_sqrt hinside
    have hform : ladderConductanceReal p j =
        Real.sqrt (if j = 0 then p.m * t * Real.log 2
          else p.m * t * moment / 8) / (2 : ℝ) ^ 13 := by
      unfold ladderConductanceReal
      dsimp only [t, moment]
      split_ifs <;> rfl
    rw [hform]
    exact div_le_div_of_nonneg_right
      (le_min hsqrtInside hsqrtU) (by positivity)
  have hstep := V.ladderEndpoint_le_proposition32_scale p hmatch hbSmall j
  have hbaseEq : proposition32CrLarge * V.L * t *
        Real.sqrt (moment * ((d : ℝ) + moment)) =
      p.ladderTheta * (proposition32CrLarge * p.b0) := by
    dsimp only [t, moment]
    unfold ladderEndpoint ladderNominalEndpoint
    rw [← hmatch.dimension, ← hmatch.smoothness]
    have hroot : 0 < Real.sqrt
        (ladderMoment p j * (p.d + ladderMoment p j)) := by
      exact Real.sqrt_pos.2 (mul_pos (ladderMoment_pos p j)
        (add_pos p.hd (ladderMoment_pos p j)))
    field_simp [ne_of_gt p.hL, ne_of_gt hroot]
  have hbaseLe : proposition32CrLarge * V.L * t *
        Real.sqrt (moment * ((d : ℝ) + moment)) ≤ p.ladderTheta / 16 := by
    rw [hbaseEq]
    have := mul_le_mul_of_nonneg_left hbLarge p.ladderTheta_pos.le
    nlinarith
  have hbase0 : 0 ≤ proposition32CrLarge * V.L * t *
      Real.sqrt (moment * ((d : ℝ) + moment)) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg proposition32CrLarge_pos.le V.hL.le) ht.le)
      (Real.sqrt_nonneg _)
  have herror :
      (proposition32CrLarge * V.L * t *
          Real.sqrt (moment * ((d : ℝ) + moment))) ^ moment ≤
        q * min 1 (Real.sqrt (V.m * t * Real.log (1 / q))) /
          (2 : ℝ) ^ 13 := by
    have hrpow := Real.rpow_le_rpow hbase0 hbaseLe hmom.le
    have hqexp : Real.exp (-u) = q := by
      rw [hu]
      exact exp_neg_log_one_div hq
    have hbudgetReal : (p.ladderTheta / 16) ^ moment ≤
        (1 / (2 : ℝ) ^ 13) * q * Real.sqrt (V.m * t * u) := by
      rw [hmatch.strongConvexity, hqexp] at hbudget'
      simpa only [moment, t, mul_assoc] using hbudget'.1
    calc
      _ ≤ (p.ladderTheta / 16) ^ moment := hrpow
      _ ≤ (1 / (2 : ℝ) ^ 13) * q * Real.sqrt (V.m * t * u) := hbudgetReal
      _ ≤ q * min 1 (Real.sqrt (V.m * t * u)) / (2 : ℝ) ^ 13 := by
        have hminEq : min 1 (Real.sqrt (V.m * t * u)) =
            Real.sqrt (V.m * t * u) := by
          rw [min_eq_right]
          rw [hmatch.strongConvexity] at hmtu
          have : V.m * t * u ≤ 1 :=
            hmtu.trans (by nlinarith [p.hb0_half])
          simpa using Real.sqrt_le_sqrt this
        rw [hminEq]
        ring_nf
        exact le_rfl
      _ = q * min 1 (Real.sqrt (V.m * t * Real.log (1 / q))) /
          (2 : ℝ) ^ 13 := by rw [← hu]
  have hShalf : q ≤ 1 / 2 := by
    have hlogInv : Real.log 2 ≤ Real.log (1 / q) := by
      rw [← hu]
      exact huLog
    have hInv : 2 ≤ 1 / q := by
      have hexp := Real.exp_le_exp.mpr hlogInv
      rw [Real.exp_log (by norm_num),
        Real.exp_log (one_div_pos.mpr hq)] at hexp
      exact hexp
    have htwoq : 2 * q ≤ 1 := (le_div_iff₀ hq).mp hInv
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    nlinarith
  have hraw := V.local_dyadicMALA_boundaryFlow_lower_of_bakryLedoux
    hBL moment t hmomTwo ht hstep hS hq hShalf herror
  have hflowtop : boundaryFlow (V.target : Measure (State d))
      (V.dyadicMALA t ht) S ≠ ∞ := by
    letI : IsMarkovKernel (V.dyadicMALA t ht) :=
      V.dyadicMALA_isMarkovKernel t ht
    exact flow_ne_top (V.target : Measure (State d))
      (V.dyadicMALA t ht) S Sᶜ hS
  have hStop : (V.target : Measure (State d)) S ≠ ∞ := measure_ne_top _ _
  have hreal : ladderConductanceReal p j * q ≤
      (boundaryFlow (V.target : Measure (State d))
        (V.dyadicMALA t ht) S).toReal := by
    calc
      _ ≤ q * min 1 (Real.sqrt (V.m * t * u)) / (2 : ℝ) ^ 13 := by
        rw [hmatch.strongConvexity] at hfactor
        calc
          ladderConductanceReal p j * q = q * ladderConductanceReal p j := by ring
          _ ≤ q * (min 1 (Real.sqrt (V.m * t * u)) /
              (2 : ℝ) ^ 13) := mul_le_mul_of_nonneg_left hfactor hq.le
          _ = _ := by ring
      _ = q * min 1 (Real.sqrt (V.m * t * Real.log (1 / q))) /
          (2 : ℝ) ^ 13 := by rw [← hu]
      _ ≤ _ := hraw
  change ENNReal.ofReal (ladderConductanceReal p j) *
      (V.target : Measure (State d)) S ≤
    boundaryFlow (V.target : Measure (State d))
      (V.dyadicMALA t ht) S
  rw [← ENNReal.ofReal_toReal hflowtop, ← ENNReal.ofReal_toReal hStop,
    ← measureReal_def, ← ENNReal.ofReal_mul (ladderConductanceReal_pos p j).le]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Above the final moment band, the top ladder component is globally safe
and provides the same noninitial conductance coefficient. -/
theorem terminal_ladder_boundaryFlow_lower_of_bakryLedoux
    (p : Parameters) (hmatch : PotentialParametersMatch V p)
    (hsmall : p.pStar < p.d)
    (hBL : BakryLedouxEnlargement
      (V.target : Measure (State d)) V.m
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure))
    (u : ℝ)
    (huLower : ladderMoment p (ladderTopIndex p) / 2 < u)
    {S : Set (State d)} (hS : MeasurableSet S)
    (hSpos : 0 < (V.target : Measure (State d)).real S)
    (hShalf : (V.target : Measure (State d)).real S ≤ 1 / 2)
    (hu : u = Real.log (1 / (V.target : Measure (State d)).real S)) :
    ladderConductance p (ladderTopIndex p) *
        (V.target : Measure (State d)) S ≤
      boundaryFlow (V.target : Measure (State d))
        (V.dyadicMALA (ladderEndpoint p (ladderTopIndex p))
          (ladderEndpoint_pos p (ladderTopIndex p))) S := by
  let J : ℕ := ladderTopIndex p
  let moment : ℝ := ladderMoment p J
  let t : ℝ := ladderEndpoint p J
  let q : ℝ := (V.target : Measure (State d)).real S
  have hmom : 0 < moment := ladderMoment_pos p J
  have ht : 0 < t := ladderEndpoint_pos p J
  have hq : 0 < q := hSpos
  have htop := ladderMoment_top_range p hsmall
  have hdmom : p.d ≤ moment := by simpa only [moment, J] using htop.1
  have hroot : 0 < Real.sqrt (moment * (p.d + moment)) := by
    exact Real.sqrt_pos.2 (mul_pos hmom (add_pos p.hd hmom))
  have hrootSq : (Real.sqrt (moment * (p.d + moment))) ^ 2 =
      moment * (p.d + moment) := Real.sq_sqrt
        (mul_nonneg hmom.le (add_nonneg p.hd.le hmom.le))
  have hdroot : p.d ≤ Real.sqrt (moment * (p.d + moment)) := by
    have hd0 := p.hd.le
    have hs0 := hroot.le
    nlinarith
  have htSafeP : t ≤ 1 / (2 * p.L * p.d) := by
    have hden : 0 < p.L * Real.sqrt (moment * (p.d + moment)) :=
      mul_pos p.hL hroot
    have hdenSafe : 0 < 2 * p.L * p.d :=
      mul_pos (mul_pos (by norm_num) p.hL) p.hd
    have hnum : p.ladderTheta * p.b0 ≤ 1 / 2 :=
      (mul_le_of_le_one_left p.hb0.le p.ladderTheta_le_one).trans p.hb0_half
    dsimp only [t, J, moment]
    unfold ladderEndpoint ladderNominalEndpoint
    rw [show p.ladderTheta *
        (p.b0 / (p.L * Real.sqrt
          (ladderMoment p (ladderTopIndex p) *
            (p.d + ladderMoment p (ladderTopIndex p))))) =
      (p.ladderTheta * p.b0) /
        (p.L * Real.sqrt
          (ladderMoment p (ladderTopIndex p) *
            (p.d + ladderMoment p (ladderTopIndex p)))) by ring]
    apply (div_le_iff₀ hden).2
    have hrhs : (1 / (2 * p.L * p.d)) *
        (p.L * Real.sqrt (moment * (p.d + moment))) =
        Real.sqrt (moment * (p.d + moment)) / (2 * p.d) := by
      field_simp [ne_of_gt p.hL, ne_of_gt p.hd]
    rw [hrhs]
    apply (le_div_iff₀ (mul_pos (by norm_num) p.hd)).2
    calc
      (p.ladderTheta * p.b0) * (2 * p.d) ≤
          (1 / 2) * (2 * p.d) :=
        mul_le_mul_of_nonneg_right hnum
          (mul_nonneg (by norm_num) p.hd.le)
      _ = p.d := by ring
      _ ≤ Real.sqrt (moment * (p.d + moment)) := hdroot
  have htSafe : t ≤ 1 / (2 * V.L * (d : ℝ)) := by
    rw [← hmatch.dimension, ← hmatch.smoothness]
    exact htSafeP
  have hunsatP : p.m * t * (moment / 8) ≤ p.b0 / 2 := by
    apply exceptional_budget_unsaturated p.d p.m p.L p.kappa p.b0
      p.ladderTheta moment (moment / 8) t p.hd p.hm p.hL p.hkappa
      p.hkappa_one p.hb0 p.ladderTheta_le_one hmom (by positivity)
      (by linarith) ?_
    dsimp only [t, moment, J]
    unfold ladderEndpoint ladderNominalEndpoint
    ring
  have hunsat : V.m * t * (moment / 8) ≤ 1 := by
    rw [← hmatch.strongConvexity]
    exact hunsatP.trans (by nlinarith [p.hb0_half])
  have hinside : V.m * t * (moment / 8) ≤ V.m * t * u := by
    have hlower : moment / 8 ≤ u := by linarith
    exact mul_le_mul_of_nonneg_left hlower
      (mul_nonneg V.hm.le ht.le)
  have hfactor : ladderConductanceReal p J ≤
      min 1 (Real.sqrt (V.m * t * u)) / (2 : ℝ) ^ 13 := by
    have hJne : J ≠ 0 := by
      intro hJ
      have := htop.1
      have hJ' : ladderTopIndex p = 0 := by simpa only [J] using hJ
      rw [hJ', ladderMoment_zero] at this
      linarith
    have hform : ladderConductanceReal p J =
        Real.sqrt (V.m * t * moment / 8) / (2 : ℝ) ^ 13 := by
      unfold ladderConductanceReal
      rw [if_neg hJne, hmatch.strongConvexity]
    rw [hform]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply le_min
    · have : Real.sqrt (V.m * t * (moment / 8)) ≤ 1 := by
        simpa using Real.sqrt_le_sqrt hunsat
      rw [show V.m * t * moment / 8 = V.m * t * (moment / 8) by ring]
      exact this
    · have := Real.sqrt_le_sqrt hinside
      rw [show V.m * t * moment / 8 = V.m * t * (moment / 8) by ring]
      exact this
  have hraw := V.safe_dyadicMALA_boundaryFlow_lower_of_bakryLedoux
    hBL t ht htSafe hS hSpos hShalf
  have hflowtop : boundaryFlow (V.target : Measure (State d))
      (V.dyadicMALA t ht) S ≠ ∞ := by
    letI : IsMarkovKernel (V.dyadicMALA t ht) :=
      V.dyadicMALA_isMarkovKernel t ht
    exact flow_ne_top (V.target : Measure (State d))
      (V.dyadicMALA t ht) S Sᶜ hS
  have hStop : (V.target : Measure (State d)) S ≠ ∞ := measure_ne_top _ _
  have hreal : ladderConductanceReal p J * q ≤
      (boundaryFlow (V.target : Measure (State d))
        (V.dyadicMALA t ht) S).toReal := by
    calc
      _ ≤ q * min 1 (Real.sqrt (V.m * t * u)) / (2 : ℝ) ^ 13 := by
        calc
          ladderConductanceReal p J * q = q * ladderConductanceReal p J := by ring
          _ ≤ q * (min 1 (Real.sqrt (V.m * t * u)) /
              (2 : ℝ) ^ 13) := mul_le_mul_of_nonneg_left hfactor hq.le
          _ = _ := by ring
      _ = q * min 1 (Real.sqrt (V.m * t * Real.log (1 / q))) /
          (2 : ℝ) ^ 13 := by rw [← hu]
      _ ≤ _ := hraw
  change ENNReal.ofReal (ladderConductanceReal p J) *
      (V.target : Measure (State d)) S ≤
    boundaryFlow (V.target : Measure (State d))
      (V.dyadicMALA t ht) S
  rw [← ENNReal.ofReal_toReal hflowtop, ← ENNReal.ofReal_toReal hStop,
    ← measureReal_def, ← ENNReal.ofReal_mul (ladderConductanceReal_pos p J).le]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The logarithmic mass bands exhaust all cuts of mass at most one half.
This is the complete finite cut assignment consumed by component
aggregation. -/
theorem ladder_flowAssignment_of_bakryLedoux
    (p : Parameters) (hmatch : PotentialParametersMatch V p)
    (hsmall : p.pStar < p.d)
    (hbSmall : p.b0 ≤ proposition32CrSmall)
    (hbLarge : proposition32CrLarge * p.b0 ≤ 1 / 16)
    (hbudget : LadderExceptionalBudget p)
    (hBL : BakryLedouxEnlargement
      (V.target : Measure (State d)) V.m
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure)) :
    ∀ S : Set (State d), MeasurableSet S →
      0 < (V.target : Measure (State d)) S →
      (V.target : Measure (State d)) S ≤ (2 : ℝ≥0∞)⁻¹ →
      ∃ j : Fin (ladderTopIndex p + 1),
        ladderConductance p j.val * (V.target : Measure (State d)) S ≤
          boundaryFlow (V.target : Measure (State d))
            (V.dyadicMALA (ladderEndpoint p j.val)
              (ladderEndpoint_pos p j.val)) S := by
  intro S hS hSpos hShalf
  let q : ℝ := (V.target : Measure (State d)).real S
  let u : ℝ := Real.log (1 / q)
  let J : ℕ := ladderTopIndex p
  have hStop : (V.target : Measure (State d)) S ≠ ∞ := measure_ne_top _ _
  have hq : 0 < q := by
    dsimp only [q]
    rw [measureReal_def]
    exact ENNReal.toReal_pos hSpos.ne' hStop
  have hqhalf : q ≤ 1 / 2 := by
    dsimp only [q]
    rw [measureReal_def]
    have h := ENNReal.toReal_mono
      (by norm_num : (2 : ℝ≥0∞)⁻¹ ≠ ∞) hShalf
    norm_num at h ⊢
    exact h
  have htwoInv : 2 ≤ 1 / q := by
    apply (le_div_iff₀ hq).2
    linarith
  have huLog : Real.log 2 ≤ u := by
    dsimp only [u]
    exact Real.strictMonoOn_log.monotoneOn
      (by norm_num) (one_div_pos.mpr hq) htwoInv
  have huEq : u = Real.log
      (1 / (V.target : Measure (State d)).real S) := rfl
  by_cases hu0 : u ≤ ladderMoment p 0 / 2
  · let j : Fin (ladderTopIndex p + 1) := ⟨0, Nat.zero_lt_succ _⟩
    refine ⟨j, ?_⟩
    simpa only [j, Fin.val_mk] using
      V.local_ladder_boundaryFlow_lower_of_bakryLedoux p hmatch hbSmall
        hbLarge hbudget hBL 0 u huLog hu0 (by simpa using huLog)
        hS (by simpa only [q] using hq) huEq
  · by_cases huJ : u ≤ ladderMoment p J / 2
    · let hex : ∃ k : ℕ, u ≤ ladderMoment p k / 2 := ⟨J, huJ⟩
      let k : ℕ := Nat.find hex
      have huk : u ≤ ladderMoment p k / 2 := Nat.find_spec hex
      have hkJ : k ≤ J := Nat.find_min' hex huJ
      have hk0 : k ≠ 0 := by
        intro hk
        apply hu0
        simpa [hk] using huk
      have hkpred : k - 1 < k := by omega
      have hupred : ladderMoment p (k - 1) / 2 < u := by
        exact lt_of_not_ge (Nat.find_min hex hkpred)
      have hsucc : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)
      have hquarter : ladderMoment p (k - 1) = ladderMoment p k / 4 := by
        have hs := ladderMoment_succ p (k - 1)
        rw [hsucc] at hs
        nlinarith
      have hulower : ladderMoment p k / 8 ≤ u := by
        calc
          ladderMoment p k / 8 = (ladderMoment p k / 4) / 2 := by ring
          _ = ladderMoment p (k - 1) / 2 := by rw [hquarter]
          _ ≤ u := hupred.le
      let j : Fin (ladderTopIndex p + 1) :=
        ⟨k, Nat.lt_succ_of_le (by simpa only [J] using hkJ)⟩
      refine ⟨j, ?_⟩
      simpa only [j, Fin.val_mk] using
        V.local_ladder_boundaryFlow_lower_of_bakryLedoux p hmatch hbSmall
          hbLarge hbudget hBL k u huLog huk (by simp [hk0, hulower])
          hS (by simpa only [q] using hq) huEq
    · let j : Fin (ladderTopIndex p + 1) :=
        ⟨ladderTopIndex p, Nat.lt_succ_self _⟩
      refine ⟨j, ?_⟩
      apply V.terminal_ladder_boundaryFlow_lower_of_bakryLedoux
        p hmatch hsmall hBL u
      · simpa only [J] using lt_of_not_ge huJ
      · exact hS
      · simpa only [q] using hq
      · exact hqhalf
      · exact huEq

/-- Concrete aggregation of the entire geometric ladder.  At this stage the
only hypotheses beyond Bakry--Ledoux are the explicit universal-constant
choices and the scalar exceptional-budget inequality. -/
theorem ladder_component_spectralGap_of_bakryLedoux
    (p : Parameters) (hmatch : PotentialParametersMatch V p)
    (hsmall : p.pStar < p.d)
    (hbSmall : p.b0 ≤ proposition32CrSmall)
    (hbLarge : proposition32CrLarge * p.b0 ≤ 1 / 16)
    (hbudget : LadderExceptionalBudget p)
    (hBL : BakryLedouxEnlargement
      (V.target : Measure (State d)) V.m
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure)) :
    ((2 : ℝ≥0∞) * harmonicCost
      (fun j : Fin (ladderTopIndex p + 1) =>
        ladderSelectionWeight p j.val)
      (fun j : Fin (ladderTopIndex p + 1) =>
        ladderConductance p j.val))⁻¹ ≤
      spectralGap (V.target : Measure (State d))
        (V.uniformMALA p.H p.hH) := by
  let N : ℕ := ladderTopIndex p + 1
  let K : Fin N → Kernel (State d) (State d) := fun j =>
    V.dyadicMALA (ladderEndpoint p j.val) (ladderEndpoint_pos p j.val)
  let γ : Fin N → ℝ≥0∞ := fun j => ladderSelectionWeight p j.val
  let φ : Fin N → ℝ≥0∞ := fun j => ladderConductance p j.val
  letI : IsMarkovKernel (V.uniformMALA p.H p.hH) :=
    V.uniformMALA_isMarkovKernel p.H p.hH
  apply componentAggregation_le_spectralGap (N := N) (by simp [N])
    (V.target : Measure (State d)) (V.uniformMALA p.H p.hH) K
    (hK := fun j => V.dyadicMALA_isMarkovKernel
      (ladderEndpoint p j.val) (ladderEndpoint_pos p j.val))
    (fun j => V.dyadicMALA_isReversible
      (ladderEndpoint p j.val) (ladderEndpoint_pos p j.val))
    γ φ
    (fun j => ladderSelectionWeight_ne_zero p j.val)
    (fun j => ladderSelectionWeight_ne_top p j.val)
    (fun j => ladderConductance_ne_zero p j.val)
    (fun j => ladderConductance_ne_top p j.val)
  · intro f hf
    let F : ℕ → ℝ≥0∞ := fun j =>
      ladderSelectionWeight p j *
        Dirichlet.energy (V.target : Measure (State d))
          (V.dyadicMALA (ladderEndpoint p j) (ladderEndpoint_pos p j)) f
    change (∑ j : Fin N, F j.val) ≤
      Dirichlet.energy (V.target : Measure (State d))
        (V.uniformMALA p.H p.hH) f
    rw [Fin.sum_univ_eq_sum_range]
    simpa only [N, F] using V.ladder_energy_domination p f hf
  · simpa only [N, K, φ] using
      V.ladder_flowAssignment_of_bakryLedoux p hmatch hsmall hbSmall
        hbLarge hbudget hBL

/-- Version of the ladder aggregation theorem with the exceptional budget
discharged by the explicit universal `A₀` choice. -/
theorem ladder_component_spectralGap_of_bakryLedoux_parameterChoice
    (p : Parameters) (hmatch : PotentialParametersMatch V p)
    (hsmall : p.pStar < p.d)
    (hbSmall : p.b0 ≤ proposition32CrSmall)
    (hbLarge : proposition32CrLarge * p.b0 ≤ 1 / 16)
    (hchoice : ExceptionalBudgetParameterChoice p)
    (hBL : BakryLedouxEnlargement
      (V.target : Measure (State d)) V.m
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure)) :
    ((2 : ℝ≥0∞) * harmonicCost
      (fun j : Fin (ladderTopIndex p + 1) =>
        ladderSelectionWeight p j.val)
      (fun j : Fin (ladderTopIndex p + 1) =>
        ladderConductance p j.val))⁻¹ ≤
      spectralGap (V.target : Measure (State d))
        (V.uniformMALA p.H p.hH) :=
  V.ladder_component_spectralGap_of_bakryLedoux p hmatch hsmall hbSmall
    hbLarge (ladderExceptionalBudget_of_parameterChoice p hchoice) hBL

/-- Explicit ladder-regime spectral-gap estimate.  Every probabilistic and
analytic step below the conclusion has now been discharged except for the
Bakry--Ledoux enlargement inequality. -/
theorem ladderGap_lower_of_bakryLedoux
    (p : Parameters) (hmatch : PotentialParametersMatch V p)
    (hsmall : p.pStar < p.d)
    (hbSmall : p.b0 ≤ proposition32CrSmall)
    (hbLarge : proposition32CrLarge * p.b0 ≤ 1 / 16)
    (hchoice : ExceptionalBudgetParameterChoice p)
    (hBL : BakryLedouxEnlargement
      (V.target : Measure (State d)) V.m
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure)) :
    ENNReal.ofReal (ladderGapBound p) ≤
      spectralGap (V.target : Measure (State d))
        (V.uniformMALA p.H p.hH) := by
  let γ : Fin (ladderTopIndex p + 1) → ℝ≥0∞ := fun j =>
    ladderSelectionWeight p j.val
  let φ : Fin (ladderTopIndex p + 1) → ℝ≥0∞ := fun j =>
    ladderConductance p j.val
  calc
    ENNReal.ofReal (ladderGapBound p) =
        ((2 : ℝ≥0∞) * ENNReal.ofReal (ladderHarmonicBound p))⁻¹ :=
      ladderGapBound_eq_inv_harmonicBound p
    _ ≤ ((2 : ℝ≥0∞) * harmonicCost γ φ)⁻¹ :=
      ENNReal.inv_le_inv.mpr
        (mul_le_mul_of_nonneg_left (ladder_harmonicCost_le p hsmall)
          (by positivity))
    _ ≤ spectralGap (V.target : Measure (State d))
        (V.uniformMALA p.H p.hH) := by
      simpa only [γ, φ] using
        V.ladder_component_spectralGap_of_bakryLedoux_parameterChoice
          p hmatch hsmall hbSmall hbLarge hchoice hBL

/-- Paper-scale truncated form of the preceding explicit ladder bound. -/
theorem ladder_truncated_spectralGap_lower_of_bakryLedoux
    (p : Parameters) (hmatch : PotentialParametersMatch V p)
    (hsmall : p.pStar < p.d)
    (hbSmall : p.b0 ≤ proposition32CrSmall)
    (hbLarge : proposition32CrLarge * p.b0 ≤ 1 / 16)
    (hchoice : ExceptionalBudgetParameterChoice p)
    (hBL : BakryLedouxEnlargement
      (V.target : Measure (State d)) V.m
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure)) :
    ENNReal.ofReal
        ((1 / (12 * (2 : ℝ) ^ 30)) * (p.m / p.H) *
          (min p.H p.rejectionScale) ^ 2) ≤
      spectralGap (V.target : Measure (State d))
        (V.uniformMALA p.H p.hH) := by
  have hid : ladderGapBound p =
      (1 / (12 * (2 : ℝ) ^ 30)) * (p.m / p.H) *
        (min p.H p.rejectionScale) ^ 2 := by
    unfold ladderGapBound
    convert p.ladder_coefficient_identity
      (6 * (2 : ℝ) ^ 30) (by positivity) using 1 <;> ring
  rw [← hid]
  exact V.ladderGap_lower_of_bakryLedoux p hmatch hsmall hbSmall hbLarge
    hchoice hBL

end FirstOrderPotential

end Concrete

end

end UniformRandomMALA
