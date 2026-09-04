import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Scalar compression and optimization for the fixed-step obstruction

This file isolates the elementary real-variable estimates used after the
probabilistic part of the fixed-step MALA obstruction.  The first result
compresses a geometric exceptional-probability term and an exponential
penalty into a single exponential with `min s 1`.  The second group controls
the minimum of the local and sticky branches uniformly over the step size.
-/

namespace UniformRandomMALA.Concrete

open scoped ENNReal NNReal

noncomputable section

/-- A geometric term `ρ^n`, with `0 < ρ < 1`, is dominated by every
exponential rate no larger than `-log ρ`.  The extra `min s 1` only weakens
the desired upper bound. -/
theorem pow_le_exp_neg_mul_min
    {ρ c s : ℝ} {n : ℕ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hc0 : 0 ≤ c) (hcρ : c ≤ -Real.log ρ) (hs : 0 ≤ s) :
    ρ ^ n ≤ Real.exp (-c * n * min s 1) := by
  have hlog : Real.log ρ < 0 := Real.log_neg hρ hρ1
  have hmin0 : 0 ≤ min s 1 := le_min hs zero_le_one
  have hmin1 : min s 1 ≤ 1 := min_le_right _ _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hfirst : ρ ^ n = Real.exp (Real.log ρ * n) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hρ]
  rw [hfirst]
  apply Real.exp_le_exp.mpr
  calc
    Real.log ρ * n ≤ -c * n := by
      have : Real.log ρ ≤ -c := by linarith
      exact mul_le_mul_of_nonneg_right this hn0
    _ ≤ -c * n * min s 1 := by
      have hcn : -c * n ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc0) hn0
      nlinarith

/-- Decreasing an exponential rate and replacing `s` by `min s 1` gives a
larger exponential. -/
theorem exp_neg_mul_le_exp_neg_mul_min
    {a c s : ℝ} {n : ℕ} (ha : 0 ≤ a) (_hc0 : 0 ≤ c) (hca : c ≤ a)
    (hs : 0 ≤ s) :
    Real.exp (-a * n * s) ≤ Real.exp (-c * n * min s 1) := by
  apply Real.exp_le_exp.mpr
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hmin0 : 0 ≤ min s 1 := le_min hs zero_le_one
  have hmins : min s 1 ≤ s := min_le_left _ _
  have hmul : c * n * min s 1 ≤ a * n * s := by
    calc
      c * n * min s 1 ≤ a * n * min s 1 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hca hn0) hmin0
      _ ≤ a * n * s := by
        exact mul_le_mul_of_nonneg_left hmins (mul_nonneg ha hn0)
  linarith

/-- A geometric tail plus an exponential penalty is bounded by a single
exponential.  The rate `c` depends only on the two one-coordinate constants
`ρ` and `a`, and is independent of `n` and `s`. -/
theorem exists_exponential_compression_rate
    {ρ a : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (s : ℝ), 1 ≤ n → 0 ≤ s →
      ρ ^ n + Real.exp (-a * n * s) ≤
        2 * Real.exp (-c * n * min s 1) := by
  by_cases hρz : ρ = 0
  · refine ⟨a, ha, ?_⟩
    intro n s hn hs
    have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    rw [hρz, zero_pow hn0]
    have hexp := exp_neg_mul_le_exp_neg_mul_min
      ha.le ha.le le_rfl (n := n) hs
    have hpos := Real.exp_pos (-a * n * min s 1)
    linarith

  · have hρ : 0 < ρ := lt_of_le_of_ne hρ0 (Ne.symm hρz)
    let c : ℝ := min a (-Real.log ρ)
    have hlog : 0 < -Real.log ρ := neg_pos.mpr (Real.log_neg hρ hρ1)
    have hc : 0 < c := lt_min ha hlog
    refine ⟨c, hc, ?_⟩
    intro n s _ hs
    have hpow := pow_le_exp_neg_mul_min hρ hρ1 hc.le
      (min_le_right _ _) (n := n) hs
    have hexp := exp_neg_mul_le_exp_neg_mul_min ha.le hc.le
      (min_le_left _ _) (n := n) hs
    linarith

/-- `ℝ≥0∞` form of `exists_exponential_compression_rate`, ready to be
composed with an extended-valued Rayleigh-gap estimate.  The nonnegative
prefactor allows, for example, the factor `4` produced by the small-ball cut
argument to be carried through in one step. -/
theorem exists_ennreal_exponential_compression_rate
    {ρ a : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧ ∀ (C : ℝ) (n : ℕ) (s : ℝ),
      0 ≤ C → 1 ≤ n → 0 ≤ s →
      ENNReal.ofReal
          (C * (ρ ^ n + Real.exp (-a * n * s))) ≤
        ENNReal.ofReal
          (2 * C * Real.exp (-c * n * min s 1)) := by
  obtain ⟨c, hc, hcompress⟩ :=
    exists_exponential_compression_rate hρ0 hρ1 ha
  refine ⟨c, hc, ?_⟩
  intro C n s hC hn hs
  apply ENNReal.ofReal_le_ofReal
  have hmul := mul_le_mul_of_nonneg_left (hcompress n s hn hs) hC
  nlinarith

/-- The scalar envelope obtained by taking the better of the local
test-function obstruction and the sticky-region obstruction. -/
def fixedStepTwoBranchEnvelope (κ d c t : ℝ) : ℝ :=
  min (κ⁻¹ * t)
    (Real.exp (-c * d * min ((1 - κ⁻¹) * t) 1))

/-- The step-size threshold used to balance the local and sticky branches. -/
def fixedStepBalanceThreshold (κ d c : ℝ) : ℝ :=
  2 * Real.log (κ * d) / (c * (1 - κ⁻¹) * d)

/-- Exact balance-point estimate with the condition number `κ` left in the
denominator.  This is the core scalar optimization; later results only
weaken its first denominator uniformly over `κ ≥ κ₀`. -/
theorem fixedStepTwoBranchEnvelope_le_balanceMax
    {κ d c t : ℝ} (hκ : 1 < κ) (hd : 2 ≤ d)
    (hc : 0 < c) (_ht : 0 ≤ t) :
    fixedStepTwoBranchEnvelope κ d c t ≤
      max
        (2 * Real.log (κ * d) /
          (c * (1 - κ⁻¹) * κ * d))
        (max ((κ * d)⁻¹ ^ 2) (Real.exp (-c * d))) := by
  have hκ0 : 0 < κ := zero_lt_one.trans hκ
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hz : 1 < κ * d := by nlinarith
  have hz0 : 0 < κ * d := zero_lt_one.trans hz
  have hlog : 0 < Real.log (κ * d) := Real.log_pos hz
  have hq : 0 < 1 - κ⁻¹ := sub_pos.mpr ((inv_lt_one₀ hκ0).mpr hκ)
  have hden : 0 < c * (1 - κ⁻¹) * d := mul_pos (mul_pos hc hq) hd0
  let T := fixedStepBalanceThreshold κ d c
  have hT : 0 < T := by
    dsimp [T, fixedStepBalanceThreshold]
    positivity
  by_cases hsmall : t ≤ T
  · apply (min_le_left _ _).trans
    have hkinv : 0 ≤ κ⁻¹ := (inv_pos.mpr hκ0).le
    have hstep : κ⁻¹ * t ≤ κ⁻¹ * T :=
      mul_le_mul_of_nonneg_left hsmall hkinv
    apply hstep.trans
    apply le_max_of_le_left
    dsimp [T, fixedStepBalanceThreshold]
    field_simp [hc.ne', hq.ne', hκ0.ne', hd0.ne', hκ.ne']
    exact le_rfl
  · have hlarge : T < t := lt_of_not_ge hsmall
    apply (min_le_right _ _).trans
    apply le_max_of_le_right
    have hqt : (1 - κ⁻¹) * T ≤ (1 - κ⁻¹) * t :=
      (mul_lt_mul_of_pos_left hlarge hq).le
    have hmin : min ((1 - κ⁻¹) * T) 1 ≤
        min ((1 - κ⁻¹) * t) 1 := min_le_min_right _ hqt
    have hcd : 0 < c * d := mul_pos hc hd0
    have hexpMono :
        Real.exp (-c * d * min ((1 - κ⁻¹) * t) 1) ≤
          Real.exp (-c * d * min ((1 - κ⁻¹) * T) 1) := by
      apply Real.exp_le_exp.mpr
      have hnegcd : -c * d ≤ 0 := by nlinarith
      exact mul_le_mul_of_nonpos_left hmin hnegcd
    apply hexpMono.trans
    have hbalance : (1 - κ⁻¹) * T =
        2 * Real.log (κ * d) / (c * d) := by
      dsimp [T, fixedStepBalanceThreshold]
      field_simp [hc.ne', hq.ne', hd0.ne', hκ0.ne', hκ.ne']
      exact div_self (by linarith)
    rw [hbalance]
    by_cases hu : 2 * Real.log (κ * d) / (c * d) ≤ 1
    · rw [min_eq_left hu]
      apply le_max_of_le_left
      have hexact :
          Real.exp (-c * d * (2 * Real.log (κ * d) / (c * d))) =
            (κ * d)⁻¹ ^ 2 := by
        have hcdne : c * d ≠ 0 := hcd.ne'
        rw [show -c * d * (2 * Real.log (κ * d) / (c * d)) =
            -(Real.log (κ * d)) + -(Real.log (κ * d)) by
          field_simp
          ring]
        rw [Real.exp_add, Real.exp_neg, Real.exp_log hz0]
        ring
      exact hexact.le
    · rw [min_eq_right (le_of_not_ge hu)]
      simpa only [mul_one] using
        (le_max_right ((κ * d)⁻¹ ^ 2) (Real.exp (-c * d)))

/-- The exact three-term bound obtained from the balance-point argument,
before absorbing the harmless `(κ d)⁻²` term. -/
theorem fixedStepTwoBranchEnvelope_le_threeTermMax
    {κ₀ κ d c t : ℝ}
    (hκ₀ : 1 < κ₀) (hκ : κ₀ ≤ κ) (hd : 2 ≤ d)
    (hc : 0 < c) (ht : 0 ≤ t) :
    fixedStepTwoBranchEnvelope κ d c t ≤
      max
        (2 * Real.log (κ * d) /
          (c * (1 - κ₀⁻¹) * κ * d))
        (max ((κ * d)⁻¹ ^ 2) (Real.exp (-c * d))) := by
  have hκ1 : 1 < κ := hκ₀.trans_le hκ
  have hκ₀0 : 0 < κ₀ := zero_lt_one.trans hκ₀
  have hκ0 : 0 < κ := zero_lt_one.trans hκ1
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hq₀ : 0 < 1 - κ₀⁻¹ :=
    sub_pos.mpr ((inv_lt_one₀ hκ₀0).mpr hκ₀)
  have hq : 0 < 1 - κ⁻¹ :=
    sub_pos.mpr ((inv_lt_one₀ hκ0).mpr hκ1)
  have hqinverse : κ⁻¹ ≤ κ₀⁻¹ :=
    (inv_le_inv₀ hκ0 hκ₀0).mpr hκ
  have hqmono : 1 - κ₀⁻¹ ≤ 1 - κ⁻¹ := by linarith
  have hz : 1 < κ * d := by nlinarith
  have hn : 0 ≤ 2 * Real.log (κ * d) :=
    (mul_nonneg (by norm_num) (Real.log_pos hz).le)
  have hden₀ : 0 < c * (1 - κ₀⁻¹) * κ * d := by positivity
  have hden : 0 < c * (1 - κ⁻¹) * κ * d := by positivity
  have hdenmono :
      c * (1 - κ₀⁻¹) * κ * d ≤
        c * (1 - κ⁻¹) * κ * d := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hqmono hc.le) hκ0.le)
      hd0.le
  have hfirst :
      2 * Real.log (κ * d) / (c * (1 - κ⁻¹) * κ * d) ≤
        2 * Real.log (κ * d) / (c * (1 - κ₀⁻¹) * κ * d) :=
    div_le_div_of_nonneg_left hn hden₀ hdenmono
  exact (fixedStepTwoBranchEnvelope_le_balanceMax hκ1 hd hc ht).trans
    (max_le_max_right _ hfirst)

/-- If the universal exponential rate is normalized to at most one, the
quadratic reciprocal in the exact balance estimate is absorbed by the
logarithmic term.  This is the scalar estimate used in the minimax theorem. -/
theorem fixedStepTwoBranchEnvelope_le_log_max_exp
    {κ₀ κ d c t : ℝ}
    (hκ₀ : 1 < κ₀) (hκ : κ₀ ≤ κ) (hd : 2 ≤ d)
    (hc : 0 < c) (hc1 : c ≤ 1) (ht : 0 ≤ t) :
    fixedStepTwoBranchEnvelope κ d c t ≤
      max
        (2 * Real.log (κ * d) /
          (c * (1 - κ₀⁻¹) * κ * d))
        (Real.exp (-c * d)) := by
  have hκ1 : 1 < κ := hκ₀.trans_le hκ
  have hκ₀0 : 0 < κ₀ := zero_lt_one.trans hκ₀
  have hκ0 : 0 < κ := zero_lt_one.trans hκ1
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hz2 : 2 ≤ κ * d := by nlinarith
  have hz0 : 0 < κ * d := by positivity
  have hq₀ : 0 < 1 - κ₀⁻¹ :=
    sub_pos.mpr ((inv_lt_one₀ hκ₀0).mpr hκ₀)
  have hloghalf : (1 / 2 : ℝ) ≤ Real.log (κ * d) := by
    have hlogmono : Real.log 2 ≤ Real.log (κ * d) :=
      Real.log_le_log (by norm_num) hz2
    have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
      have := Real.log_two_gt_d9
      norm_num at this ⊢
      linarith
    exact hlog2.le.trans hlogmono
  have hzinv : (κ * d)⁻¹ ≤ (1 / 2 : ℝ) := by
    have := (inv_le_inv₀ hz0 (by norm_num : (0 : ℝ) < 2)).mpr hz2
    norm_num at this ⊢
    exact this
  have hq₀1 : 1 - κ₀⁻¹ ≤ 1 := by
    exact sub_le_self _ (inv_nonneg.mpr hκ₀0.le)
  have hcq₀1 : c * (1 - κ₀⁻¹) ≤ 1 := by
    calc
      c * (1 - κ₀⁻¹) ≤ 1 * (1 - κ₀⁻¹) :=
        mul_le_mul_of_nonneg_right hc1 hq₀.le
      _ ≤ 1 := by simpa using hq₀1
  have hnum0 : 0 ≤ 2 * Real.log (κ * d) := by positivity
  have hratio :
      (κ * d)⁻¹ ≤
        2 * Real.log (κ * d) / (c * (1 - κ₀⁻¹)) := by
    calc
      (κ * d)⁻¹ ≤ (1 / 2 : ℝ) := hzinv
      _ ≤ 2 * Real.log (κ * d) := by linarith
      _ ≤ 2 * Real.log (κ * d) / (c * (1 - κ₀⁻¹)) := by
        apply (le_div_iff₀ (mul_pos hc hq₀)).2
        exact mul_le_of_le_one_right hnum0 hcq₀1
  have hquadratic :
      (κ * d)⁻¹ ^ 2 ≤
        2 * Real.log (κ * d) /
          (c * (1 - κ₀⁻¹) * κ * d) := by
    calc
      (κ * d)⁻¹ ^ 2 = (κ * d)⁻¹ * (κ * d)⁻¹ := by ring
      _ ≤ (2 * Real.log (κ * d) / (c * (1 - κ₀⁻¹))) *
          (κ * d)⁻¹ :=
        mul_le_mul_of_nonneg_right hratio (inv_nonneg.mpr hz0.le)
      _ = 2 * Real.log (κ * d) /
          (c * (1 - κ₀⁻¹) * κ * d) := by
        field_simp [hc.ne', hq₀.ne', hκ0.ne', hd0.ne']
  apply (fixedStepTwoBranchEnvelope_le_threeTermMax
    hκ₀ hκ hd hc ht).trans
  apply max_le
  · exact le_max_left _ _
  · apply max_le
    · exact hquadratic.trans (le_max_left _ _)
    · exact le_max_right _ _

/-- Extended-valued supremum form of the scalar minimax optimization.  It
states directly that taking the supremum over every nonnegative step-size
parameter does not enlarge the logarithmic/exponential ceiling. -/
theorem iSup_fixedStepTwoBranchEnvelope_le_log_max_exp
    {κ₀ κ d c : ℝ}
    (hκ₀ : 1 < κ₀) (hκ : κ₀ ≤ κ) (hd : 2 ≤ d)
    (hc : 0 < c) (hc1 : c ≤ 1) :
    (⨆ t : {t : ℝ // 0 ≤ t},
      ENNReal.ofReal (fixedStepTwoBranchEnvelope κ d c t)) ≤
      ENNReal.ofReal
        (max
          (2 * Real.log (κ * d) /
            (c * (1 - κ₀⁻¹) * κ * d))
          (Real.exp (-c * d))) := by
  apply iSup_le
  intro t
  exact ENNReal.ofReal_le_ofReal
    (fixedStepTwoBranchEnvelope_le_log_max_exp
      hκ₀ hκ hd hc hc1 t.property)

end

end UniformRandomMALA.Concrete
