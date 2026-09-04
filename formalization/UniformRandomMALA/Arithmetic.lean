import UniformRandomMALA.MinMax

/-!
# Arithmetic used by the safe component and the moment ladder

This file verifies the exact reciprocal constants in the harmonic
aggregation step and the algebra behind the truncation parameter
`theta = min 1 (H / tau)`.
-/

namespace UniformRandomMALA

noncomputable section

/-- Selection weight of an upper dyadic half-interval `[t/2,t]`. -/
def componentWeight (H t : ℝ) : ℝ := t / (2 * H)

/-- Squared conductance constant for the globally safe component. -/
def safePhiSq (m t : ℝ) : ℝ :=
  m * t * Real.log 2 / (2 : ℝ) ^ 26

/-- Squared conductance constant for a noninitial ladder component. -/
def ladderPhiSq (m t p : ℝ) : ℝ :=
  m * t * p / (2 : ℝ) ^ 29

/-- The one-component value in the aggregation lemma. -/
def oneComponentAggregation (gamma phiSq : ℝ) : ℝ :=
  1 / (2 * (1 / (gamma * phiSq)))

lemma log_two_pos : 0 < Real.log (2 : ℝ) := by
  exact Real.log_pos (by norm_num)

lemma log_two_ne_zero : Real.log (2 : ℝ) ≠ 0 :=
  ne_of_gt log_two_pos

/-- Exact first-component reciprocal used in the harmonic sum. -/
theorem safe_component_reciprocal
    (H m t : ℝ) (hH : 0 < H) (hm : 0 < m) (ht : 0 < t) :
    1 / (componentWeight H t * safePhiSq m t) =
      (2 : ℝ) ^ 27 * H / (m * t ^ 2 * Real.log 2) := by
  unfold componentWeight safePhiSq
  field_simp [ne_of_gt hH, ne_of_gt hm, ne_of_gt ht, log_two_ne_zero]
  <;> ring

/-- Exact reciprocal for every noninitial moment-ladder component. -/
theorem ladder_component_reciprocal
    (H m t p : ℝ)
    (hH : 0 < H) (hm : 0 < m) (ht : 0 < t) (hp : 0 < p) :
    1 / (componentWeight H t * ladderPhiSq m t p) =
      (2 : ℝ) ^ 30 * H / (m * t ^ 2 * p) := by
  unfold componentWeight ladderPhiSq
  field_simp [ne_of_gt hH, ne_of_gt hm, ne_of_gt ht, ne_of_gt hp]
  <;> ring

/-- The safe component yields precisely the factor `2⁻²⁸`. -/
theorem safe_one_component_value
    (H m t : ℝ) (hH : 0 < H) (hm : 0 < m) (ht : 0 < t) :
    oneComponentAggregation (componentWeight H t) (safePhiSq m t) =
      m * t ^ 2 * Real.log 2 / ((2 : ℝ) ^ 28 * H) := by
  unfold oneComponentAggregation componentWeight safePhiSq
  field_simp [ne_of_gt hH, ne_of_gt hm, ne_of_gt ht, log_two_ne_zero]
  <;> ring

/-- The endpoint truncation parameter from the paper. -/
def endpointTheta (H tau : ℝ) : ℝ := min 1 (H / tau)

lemma endpointTheta_nonneg
    (H tau : ℝ) (hH : 0 ≤ H) (htau : 0 < tau) :
    0 ≤ endpointTheta H tau := by
  unfold endpointTheta
  apply min_nonneg_of_nonneg
  · norm_num
  · exact div_nonneg hH (le_of_lt htau)

lemma endpointTheta_le_one (H tau : ℝ) : endpointTheta H tau ≤ 1 := by
  unfold endpointTheta
  exact min_le_left _ _

/-- `theta * tau` is the useful portion of the endpoint. -/
theorem endpointTheta_mul
    (H tau : ℝ) (hH : 0 < H) (htau : 0 < tau) :
    endpointTheta H tau * tau = min H tau := by
  rcases le_total H tau with hHtau | htauH
  · have hratio : H / tau ≤ 1 := by
      apply (div_le_iff₀ htau).2
      simpa using hHtau
    rw [endpointTheta, min_eq_right hratio, min_eq_left hHtau]
    field_simp [ne_of_gt htau]
  · have hratio : 1 ≤ H / tau := by
      apply (le_div_iff₀ htau).2
      simpa using htauH
    rw [endpointTheta, min_eq_left hratio, min_eq_right htauH]
    norm_num

/-- Squared form of `endpointTheta_mul`. -/
theorem endpointTheta_sq_mul
    (H tau : ℝ) (hH : 0 < H) (htau : 0 < tau) :
    endpointTheta H tau ^ 2 * tau ^ 2 = (min H tau) ^ 2 := by
  calc
    endpointTheta H tau ^ 2 * tau ^ 2 =
        (endpointTheta H tau * tau) ^ 2 := by ring
    _ = (min H tau) ^ 2 := by rw [endpointTheta_mul H tau hH htau]

/--
If a harmonic denominator is bounded above by `B`, the aggregation lower
bound with the true denominator is at least `1/(2B)`.
-/
theorem aggregation_from_harmonic_upper
    (gap harmonic B : ℝ)
    (hharmonic : 0 < harmonic) (hB : harmonic ≤ B)
    (hgap : 1 / (2 * harmonic) ≤ gap) :
    1 / (2 * B) ≤ gap := by
  have hBpos : 0 < B := lt_of_lt_of_le hharmonic hB
  have hdenB : 0 < 2 * B := mul_pos (by norm_num) hBpos
  have hdenH : 0 < 2 * harmonic := mul_pos (by norm_num) hharmonic
  have hinv : 1 / (2 * B) ≤ 1 / (2 * harmonic) := by
    apply (div_le_div_iff₀ hdenB hdenH).2
    nlinarith
  exact le_trans hinv hgap

/--
Algebraic conversion of the harmonic-sum upper bound into the ladder gap
bound.  This theorem deliberately exposes the constant `C` rather than
renaming its reciprocal as another unspecified universal constant.
-/
theorem ladder_gap_from_harmonic_bound
    (gap H L m theta b p d C harmonic : ℝ)
    (hH : 0 < H) (hL : 0 < L) (hm : 0 < m)
    (htheta : 0 < theta) (hb : 0 < b) (hp : 0 < p)
    (hd : 0 < d) (hC : 0 < C) (hharmonic : 0 < harmonic)
    (hsum : harmonic ≤
      C * H * L ^ 2 * p * (d + p) / (m * theta ^ 2 * b ^ 2))
    (haggregation : 1 / (2 * harmonic) ≤ gap) :
    m * theta ^ 2 * b ^ 2 /
        (2 * C * H * L ^ 2 * p * (d + p)) ≤ gap := by
  let B : ℝ := C * H * L ^ 2 * p * (d + p) /
    (m * theta ^ 2 * b ^ 2)
  have hdp : 0 < d + p := add_pos hd hp
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have hcoarse : 1 / (2 * B) ≤ gap :=
    aggregation_from_harmonic_upper gap harmonic B hharmonic hsum haggregation
  have hid :
      1 / (2 * B) =
        m * theta ^ 2 * b ^ 2 /
          (2 * C * H * L ^ 2 * p * (d + p)) := by
    dsimp [B]
    field_simp [ne_of_gt hH, ne_of_gt hL, ne_of_gt hm,
      ne_of_gt htheta, ne_of_gt hb, ne_of_gt hp, ne_of_gt hdp,
      ne_of_gt hC]
    <;> ring
  rw [hid] at hcoarse
  exact hcoarse

namespace Parameters

/-- The useful endpoint of the safe component. -/
def safeEndpoint (p : Parameters) : ℝ := min p.H p.safeScale

/-- The useful endpoint of the safe component is strictly positive. -/
lemma safeEndpoint_pos (p : Parameters) : 0 < p.safeEndpoint := by
  unfold safeEndpoint
  exact lt_min p.hH p.safeScale_pos

lemma safeComponentWeight_pos (p : Parameters) :
    0 < componentWeight p.H p.safeEndpoint := by
  unfold componentWeight
  exact div_pos p.safeEndpoint_pos (mul_pos (by norm_num) p.hH)

lemma safePhiSq_pos (p : Parameters) :
    0 < safePhiSq p.m p.safeEndpoint := by
  unfold safePhiSq
  exact div_pos (mul_pos (mul_pos p.hm p.safeEndpoint_pos) log_two_pos)
    (by positivity)

lemma safePhiSq_nonneg (p : Parameters) :
    0 ≤ safePhiSq p.m p.safeEndpoint := le_of_lt p.safePhiSq_pos

/-- The moment-ladder truncation parameter `theta`. -/
def ladderTheta (p : Parameters) : ℝ := endpointTheta p.H p.rejectionScale

lemma ladderTheta_pos (p : Parameters) : 0 < ladderTheta p := by
  unfold ladderTheta endpointTheta
  exact lt_min (by norm_num) (div_pos p.hH p.rejectionScale_pos)

lemma ladderTheta_le_one (p : Parameters) : ladderTheta p ≤ 1 := by
  exact endpointTheta_le_one p.H p.rejectionScale

/--
The exact algebraic identity converting the harmonic-sum output into the
paper's truncated rejection-scale bound.
-/
theorem ladder_coefficient_identity
    (p : Parameters) (C : ℝ) (hC : 0 < C) :
    p.m * p.ladderTheta ^ 2 * p.b0 ^ 2 /
        (2 * C * p.H * p.L ^ 2 * p.pStar * (p.d + p.pStar)) =
      (1 / (2 * C)) * (p.m / p.H) *
        (min p.H p.rejectionScale) ^ 2 := by
  have hsqrtSq :
      (Real.sqrt (p.pStar * (p.d + p.pStar))) ^ 2 =
        p.pStar * (p.d + p.pStar) := by
    exact Real.sq_sqrt (le_of_lt p.rejectionArgument_pos)
  have hthetaSq :
      p.ladderTheta ^ 2 * p.rejectionScale ^ 2 =
        (min p.H p.rejectionScale) ^ 2 := by
    exact endpointTheta_sq_mul p.H p.rejectionScale p.hH p.rejectionScale_pos
  rw [← hthetaSq]
  unfold Parameters.rejectionScale Parameters.baseFactor
    Parameters.rejectionShape
  field_simp [ne_of_gt p.hH, ne_of_gt p.hL, ne_of_gt p.hm,
    ne_of_gt p.hpStar_pos, ne_of_gt (add_pos p.hd p.hpStar_pos),
    ne_of_gt p.rejectionSqrt_pos, ne_of_gt hC]
  rw [hsqrtSq]
  ring

end Parameters

end

end UniformRandomMALA
