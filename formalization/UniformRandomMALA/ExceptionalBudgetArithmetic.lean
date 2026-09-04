import UniformRandomMALA.AggregationArithmetic

/-!
# Arithmetic in the exceptional-set budget

This file proves the unsaturated estimate `m t u ≤ b₀/2` in
`lem:exceptional-budget`.  The exponential/rpow comparison that fixes the
universal moment constant `A₀` remains an analytic-real-arithmetic
obligation in `ExceptionalSetBudget`.
-/

namespace UniformRandomMALA

noncomputable section

/--
For the ladder step
` t = theta*b / (L*sqrt(moment*(d+moment))) `,
the range `u ≤ moment/2` forces `m*t*u ≤ b/2` whenever
`kappa = L/m ≥ 1` and `theta ≤ 1`.
-/
theorem exceptional_budget_unsaturated
    (d m L kappa b theta moment u t : ℝ)
    (hd : 0 < d) (hm : 0 < m) (hL : 0 < L)
    (hkappa : kappa = L / m) (hkappaOne : 1 ≤ kappa)
    (hb : 0 < b) (hthetaOne : theta ≤ 1)
    (hmoment : 0 < moment) (hu0 : 0 ≤ u) (hu : u ≤ moment / 2)
    (ht : t = theta * b /
      (L * Real.sqrt (moment * (d + moment)))) :
    m * t * u ≤ b / 2 := by
  have hsum : 0 < d + moment := add_pos hd hmoment
  have harg : 0 < moment * (d + moment) := mul_pos hmoment hsum
  have hroot : 0 < Real.sqrt (moment * (d + moment)) :=
    Real.sqrt_pos.2 harg
  have hrootSq :
      (Real.sqrt (moment * (d + moment))) ^ 2 =
        moment * (d + moment) := by
    simpa using Real.sq_sqrt (le_of_lt harg)
  have hmomentRoot :
      moment ≤ Real.sqrt (moment * (d + moment)) := by
    have hrootNonneg : 0 ≤ Real.sqrt (moment * (d + moment)) :=
      Real.sqrt_nonneg _
    nlinarith
  have hkappaPos : 0 < kappa := lt_of_lt_of_le zero_lt_one hkappaOne
  have hden :
      moment ≤ kappa * Real.sqrt (moment * (d + moment)) := by
    have hscale :
        Real.sqrt (moment * (d + moment)) ≤
          kappa * Real.sqrt (moment * (d + moment)) := by
      have := mul_le_mul_of_nonneg_right hkappaOne
        (Real.sqrt_nonneg (moment * (d + moment)))
      simpa using this
    exact le_trans hmomentRoot hscale
  have hthetaU : theta * u ≤ moment / 2 := by
    have htu : theta * u ≤ 1 * u :=
      mul_le_mul_of_nonneg_right hthetaOne hu0
    nlinarith
  have hthetaUDen :
      theta * u ≤
        (kappa * Real.sqrt (moment * (d + moment))) / 2 := by
    nlinarith
  have hbmul := mul_le_mul_of_nonneg_left hthetaUDen (le_of_lt hb)
  have hid :
      m * t * u =
        (b * (theta * u)) /
          (kappa * Real.sqrt (moment * (d + moment))) := by
    rw [ht, hkappa]
    field_simp [ne_of_gt hm, ne_of_gt hL, ne_of_gt hroot]
    <;> ring
  rw [hid]
  apply (div_le_iff₀ (mul_pos hkappaPos hroot)).2
  nlinarith

/-- The logarithmic sufficient condition from Appendix D implies the
exceptional-set inequality at the upper endpoint `u = moment/2`.  This proof
uses logarithms only after establishing strict positivity of both sides. -/
theorem exceptional_budget_endpoint_of_log_condition
    (d m L kappa b theta moment t : ℝ)
    (hd : 0 < d) (hm : 0 < m) (hL : 0 < L)
    (hkappa : kappa = L / m) (hkappa0 : 0 < kappa)
    (hb : 0 < b) (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hp : 2 ≤ moment)
    (ht : t = theta * b / (L * Real.sqrt (moment * (d + moment))))
    (hlog :
      moment * (Real.log 16 - 1 / 2) ≥
        13 * Real.log 2 +
          (1 / 2) * Real.log (2 * kappa / b) +
          (1 / 4) * Real.log ((d + moment) / moment)) :
    (theta / 16) ^ moment ≤
      (1 / (2 : ℝ) ^ 13) * Real.exp (-(moment / 2)) *
        Real.sqrt (m * t * (moment / 2)) := by
  have hp0 : 0 < moment := lt_of_lt_of_le (by norm_num) hp
  have hdp : 0 < d + moment := add_pos hd hp0
  have hroot : 0 < Real.sqrt (moment * (d + moment)) := by positivity
  have ht0 : 0 < t := by rw [ht]; positivity
  have harg : 0 < m * t * (moment / 2) := by positivity
  have hlhs : 0 < (theta / 16) ^ moment :=
    Real.rpow_pos_of_pos (div_pos htheta (by norm_num)) _
  have hrhs : 0 < (1 / (2 : ℝ) ^ 13) * Real.exp (-(moment / 2)) *
      Real.sqrt (m * t * (moment / 2)) := by positivity
  rw [← Real.log_le_log_iff hlhs hrhs]
  rw [Real.log_rpow (div_pos htheta (by norm_num))]
  rw [Real.log_mul
    (x := (1 / (2 : ℝ) ^ 13) * Real.exp (-(moment / 2)))
    (y := Real.sqrt (m * t * (moment / 2))) (by positivity) (by positivity)]
  rw [Real.log_mul (x := 1 / (2 : ℝ) ^ 13)
    (y := Real.exp (-(moment / 2))) (by positivity) (by positivity)]
  rw [Real.log_div (x := (1 : ℝ)) (y := (2 : ℝ) ^ 13)
    (by norm_num) (by positivity)]
  rw [Real.log_pow (2 : ℝ) 13]
  rw [Real.log_exp (-(moment / 2))]
  rw [Real.log_sqrt harg.le]
  rw [Real.log_div (x := theta) (y := (16 : ℝ))
    (ne_of_gt htheta) (by norm_num)]
  rw [Real.log_mul (x := m * t) (y := moment / 2)
    (by positivity) (by positivity)]
  rw [Real.log_mul (x := m) (y := t) (ne_of_gt hm) (ne_of_gt ht0)]
  rw [Real.log_div (x := moment) (y := (2 : ℝ))
    (ne_of_gt hp0) (by norm_num)]
  rw [ht]
  rw [Real.log_div (x := theta * b)
    (y := L * Real.sqrt (moment * (d + moment))) (by positivity) (by positivity)]
  rw [Real.log_mul (x := theta) (y := b) (ne_of_gt htheta) (ne_of_gt hb)]
  rw [Real.log_mul (x := L) (y := Real.sqrt (moment * (d + moment)))
    (ne_of_gt hL) (ne_of_gt hroot)]
  rw [Real.log_sqrt (by positivity)]
  rw [Real.log_mul (x := moment) (y := d + moment)
    (ne_of_gt hp0) (ne_of_gt hdp)]
  rw [Real.log_one]
  have hlog16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have hlogk : Real.log kappa = Real.log L - Real.log m := by
    rw [hkappa, Real.log_div (ne_of_gt hL) (ne_of_gt hm)]
  have hlogkb : Real.log (2 * kappa / b) =
      Real.log 2 + Real.log kappa - Real.log b := by
    rw [Real.log_div (by positivity) (ne_of_gt hb),
      Real.log_mul (by norm_num) (ne_of_gt hkappa0)]
  have hlogratio : Real.log ((d + moment) / moment) =
      Real.log (d + moment) - Real.log moment := by
    rw [Real.log_div (ne_of_gt hdp) (ne_of_gt hp0)]
  rw [hlog16, hlogkb, hlogratio, hlogk] at hlog
  rw [hlog16]
  have hlogtheta : Real.log theta ≤ 0 :=
    Real.log_nonpos htheta.le htheta1
  nlinarith

/-- An elementary replacement for the derivative argument in the paper:
`exp (-u) * sqrt u` is antitone on `[1/2,∞)`.  The proof squares the desired
comparison and uses only `1+x ≤ exp x`. -/
theorem exp_neg_mul_sqrt_antitone
    {u v : ℝ} (hu : 1 / 2 ≤ u) (huv : u ≤ v) :
    Real.exp (-v) * Real.sqrt v ≤ Real.exp (-u) * Real.sqrt u := by
  have hu0 : 0 ≤ u := by linarith
  have hv0 : 0 ≤ v := hu0.trans huv
  let delta : ℝ := v - u
  have hdelta : 0 ≤ delta := sub_nonneg.mpr huv
  have hexp : 1 + 2 * delta ≤ Real.exp (2 * delta) := by
    simpa [add_comm] using Real.add_one_le_exp (2 * delta)
  have huvExp : v ≤ u * Real.exp (2 * delta) := by
    have hmul := mul_le_mul_of_nonneg_left hexp hu0
    dsimp only [delta] at hmul ⊢
    nlinarith
  have hsqrt : Real.sqrt v ≤ Real.exp delta * Real.sqrt u := by
    have hright0 : 0 ≤ Real.exp delta * Real.sqrt u := by positivity
    apply Real.sqrt_le_iff.mpr
    refine ⟨hright0, ?_⟩
    rw [mul_pow, Real.sq_sqrt hu0, ← Real.exp_nat_mul]
    simpa [mul_comm] using huvExp
  have hmul := mul_le_mul_of_nonneg_left hsqrt (Real.exp_pos (-v)).le
  calc
    Real.exp (-v) * Real.sqrt v ≤
        Real.exp (-v) * (Real.exp delta * Real.sqrt u) := hmul
    _ = Real.exp (-u) * Real.sqrt u := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      dsimp only [delta]
      ring

end

end UniformRandomMALA
