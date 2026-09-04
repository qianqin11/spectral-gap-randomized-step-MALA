import UniformRandomMALA.DiscreteTime.EulerRWMFiniteRecurrence

/-!
# Vanishing-step Euler--RWM coupling bound

The finite recurrence error is reduced to `δ * sqrt δ` times a fixed
stationary constant.  For a fixed horizon `h`, the elementary choice
`δₙ = h / (n + 1)` then makes the coupled-chain mean-square discrepancy
tend to zero.  This is a finite-dimensional limit statement; no path-space
weak-convergence theorem is used.
-/

namespace UniformRandomMALA
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal ProbabilityTheory unitInterval RealInnerProductSpace Topology
noncomputable section
namespace DiscreteTime
open Concrete
variable {d : ℕ}

lemma stationaryEulerRWMCouplingConstant_nonneg
    (V : FirstOrderPotential d) :
    0 ≤ stationaryEulerRWMCouplingConstant V := by
  rw [← integral_pointwiseEulerRWMCouplingConstant V]
  apply integral_nonneg
  intro x
  unfold pointwiseEulerRWMCouplingConstant gaussianNormMoment
  have h3 : 0 ≤ (∫ z : State d, ‖z‖ ^ 3 ∂stdGaussian (State d)) :=
    integral_nonneg fun _ => pow_nonneg (norm_nonneg _) _
  have h4 : 0 ≤ (∫ z : State d, ‖z‖ ^ 4 ∂stdGaussian (State d)) :=
    integral_nonneg fun _ => pow_nonneg (norm_nonneg _) _
  have h6 : 0 ≤ (∫ z : State d, ‖z‖ ^ 6 ∂stdGaussian (State d)) :=
    integral_nonneg fun _ => pow_nonneg (norm_nonneg _) _
  exact mul_nonneg (by norm_num) <| add_nonneg
    (add_nonneg
      (add_nonneg (mul_nonneg h3 (norm_nonneg _))
        (mul_nonneg V.hL.le h4))
      (mul_nonneg (mul_nonneg (by norm_num) h4) (sq_nonneg _)))
    (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg V.L)) h6)

lemma targetGradNormMoment_nonneg
    (V : FirstOrderPotential d) (p : ℕ) :
    0 ≤ targetGradNormMoment V p := by
  unfold targetGradNormMoment
  exact integral_nonneg fun _ => pow_nonneg (norm_nonneg _) _

lemma stationaryRWMRejectionBiasSqConstant_nonneg
    (V : FirstOrderPotential d) :
    0 ≤ stationaryRWMRejectionBiasSqConstant V := by
  unfold stationaryRWMRejectionBiasSqConstant
  exact integral_nonneg fun _ => sq_nonneg _

def stationaryEulerRWMRecurrenceScaleConstant
    (V : FirstOrderPotential d) : ℝ :=
  2 * Real.sqrt 2 * stationaryEulerRWMCouplingConstant V +
    (2 * targetGradNormMoment V 2 +
      8 * stationaryRWMRejectionBiasSqConstant V)

lemma stationaryEulerRWMRecurrenceScaleConstant_nonneg
    (V : FirstOrderPotential d) :
    0 ≤ stationaryEulerRWMRecurrenceScaleConstant V := by
  unfold stationaryEulerRWMRecurrenceScaleConstant
  exact add_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (stationaryEulerRWMCouplingConstant_nonneg V))
    (add_nonneg
      (mul_nonneg (by norm_num) (targetGradNormMoment_nonneg V 2))
      (mul_nonneg (by norm_num)
        (stationaryRWMRejectionBiasSqConstant_nonneg V)))

lemma sqrt_two_mul_delta_pow_three
    (δ : ℝ) (hδ : 0 ≤ δ) :
    (Real.sqrt (2 * δ)) ^ 3 =
      2 * Real.sqrt 2 * δ * Real.sqrt δ := by
  rw [show Real.sqrt (2 * δ) = Real.sqrt 2 * Real.sqrt δ by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]]
  have h2 : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hd : (Real.sqrt δ) ^ 2 = δ := by rw [Real.sq_sqrt hδ]
  calc
    (Real.sqrt 2 * Real.sqrt δ) ^ 3 =
        (Real.sqrt 2) ^ 2 * Real.sqrt 2 *
          (Real.sqrt δ) ^ 2 * Real.sqrt δ := by ring
    _ = 2 * Real.sqrt 2 * δ * Real.sqrt δ := by rw [h2, hd]

lemma delta_sq_le_delta_mul_sqrt
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    δ ^ 2 ≤ δ * Real.sqrt δ := by
  have hs0 : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt δ) ^ 2 = δ := Real.sq_sqrt hδ
  have hs1 : Real.sqrt δ ≤ 1 := by nlinarith
  have hδs : δ ≤ Real.sqrt δ := by
    calc
      δ = (Real.sqrt δ) ^ 2 := hs2.symm
      _ = Real.sqrt δ * Real.sqrt δ := by ring
      _ ≤ Real.sqrt δ * 1 := mul_le_mul_of_nonneg_left hs1 hs0
      _ = Real.sqrt δ := by ring
  calc
    δ ^ 2 = δ * δ := by ring
    _ ≤ δ * Real.sqrt δ := mul_le_mul_of_nonneg_left hδs hδ

theorem stationaryEulerRWMRecurrenceError_le_scale
    (V : FirstOrderPotential d) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    stationaryEulerRWMRecurrenceError V δ ≤
      stationaryEulerRWMRecurrenceScaleConstant V *
        δ * Real.sqrt δ := by
  let C := stationaryEulerRWMCouplingConstant V
  let D := 2 * targetGradNormMoment V 2 +
    8 * stationaryRWMRejectionBiasSqConstant V
  have hC : 0 ≤ C := stationaryEulerRWMCouplingConstant_nonneg V
  have hD : 0 ≤ D := by
    dsimp [D]
    exact add_nonneg
      (mul_nonneg (by norm_num) (targetGradNormMoment_nonneg V 2))
      (mul_nonneg (by norm_num)
        (stationaryRWMRejectionBiasSqConstant_nonneg V))
  have hδsq := delta_sq_le_delta_mul_sqrt δ hδ hδ1
  unfold stationaryEulerRWMRecurrenceError
    stationaryEulerRWMRecurrenceScaleConstant
  rw [sqrt_two_mul_delta_pow_three δ hδ]
  dsimp [C, D] at hC hD
  nlinarith

theorem stationaryEulerRWMPairChain_energy_fixedHorizon_le
    (V : FirstOrderPotential d) (δ h : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδL : δ ≤ 2 / V.L)
    (n : ℕ) (hhorizon : (n : ℝ) * δ = h) :
    (∫ xy, pairSquaredDistance xy
      ∂stationaryEulerRWMPairChainLaw V δ n) ≤
      stationaryEulerRWMRecurrenceScaleConstant V * h *
        Real.sqrt δ * (1 + δ) ^ n := by
  let a : ℕ → ℝ := fun k =>
    ∫ xy, pairSquaredDistance xy
      ∂stationaryEulerRWMPairChainLaw V δ k
  let B := stationaryEulerRWMRecurrenceScaleConstant V
  have ha0 : a 0 ≤ 0 := by
    dsimp [a]
    rw [integral_pairSquaredDistance_stationaryEulerRWMPairChainLaw_zero]
  have hstep : ∀ k : ℕ,
      a (k + 1) ≤ (1 + 1 * δ) * a k + B * δ * Real.sqrt δ := by
    intro k
    calc
      a (k + 1) ≤ (1 + δ) * a k +
          stationaryEulerRWMRecurrenceError V δ :=
        stationaryEulerRWMPairChain_energy_step V δ hδ hδ1 hδL k
      _ ≤ (1 + 1 * δ) * a k + B * δ * Real.sqrt δ := by
        have herr := stationaryEulerRWMRecurrenceError_le_scale
          V δ hδ.le hδ1
        dsimp [B]
        nlinarith
  have hbound := coupling_recursion_bound_fixed_horizon
    a 1 δ B h n (by norm_num) hδ.le
      (stationaryEulerRWMRecurrenceScaleConstant_nonneg V)
      ha0 hstep hhorizon
  simpa only [a, B, one_mul] using hbound

theorem stationaryEulerRWMPairChain_energy_fixedHorizon_exp_le
    (V : FirstOrderPotential d) (δ h : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδL : δ ≤ 2 / V.L)
    (n : ℕ) (hhorizon : (n : ℝ) * δ = h) :
    (∫ xy, pairSquaredDistance xy
      ∂stationaryEulerRWMPairChainLaw V δ n) ≤
      stationaryEulerRWMRecurrenceScaleConstant V * h *
        Real.sqrt δ * Real.exp h := by
  have hfinite := stationaryEulerRWMPairChain_energy_fixedHorizon_le
    V δ h hδ hδ1 hδL n hhorizon
  have hbase : 1 + δ ≤ Real.exp δ := by
    simpa [add_comm] using Real.add_one_le_exp δ
  have hpow : (1 + δ) ^ n ≤ (Real.exp δ) ^ n :=
    pow_le_pow_left₀ (by positivity) hbase n
  have hpow' : (1 + δ) ^ n ≤ Real.exp h := by
    calc
      (1 + δ) ^ n ≤ (Real.exp δ) ^ n := hpow
      _ = Real.exp ((n : ℝ) * δ) := by rw [Real.exp_nat_mul]
      _ = Real.exp h := by rw [hhorizon]
  have hcoeff : 0 ≤
      stationaryEulerRWMRecurrenceScaleConstant V * h * Real.sqrt δ := by
    have hh : 0 ≤ h := by rw [← hhorizon]; positivity
    exact mul_nonneg
      (mul_nonneg (stationaryEulerRWMRecurrenceScaleConstant_nonneg V) hh)
      (Real.sqrt_nonneg _)
  exact hfinite.trans (mul_le_mul_of_nonneg_left hpow' hcoeff)

theorem tendsto_stationaryEulerRWMPairChain_energy_fixedHorizon
    (V : FirstOrderPotential d) (h : ℝ) (hh : 0 < h) :
    Tendsto (fun n : ℕ =>
      ∫ xy, pairSquaredDistance xy
        ∂stationaryEulerRWMPairChainLaw V
          (h / ((n + 1 : ℕ) : ℝ)) (n + 1))
      atTop (𝓝 0) := by
  let δn : ℕ → ℝ := fun n => h / ((n + 1 : ℕ) : ℝ)
  let B := stationaryEulerRWMRecurrenceScaleConstant V
  have hδlim : Tendsto δn atTop (𝓝 0) := by
    dsimp [δn]
    exact (tendsto_const_div_atTop_nhds_zero_nat h).comp
      (tendsto_add_atTop_nat 1)
  have hδpos : ∀ n, 0 < δn n := by
    intro n
    dsimp [δn]
    exact div_pos hh (by positivity)
  have hev1 : ∀ᶠ n in atTop, δn n < 1 :=
    (tendsto_order.1 hδlim).2 1 zero_lt_one
  have htwoL : 0 < 2 / V.L := div_pos (by norm_num) V.hL
  have hevL : ∀ᶠ n in atTop, δn n < 2 / V.L :=
    (tendsto_order.1 hδlim).2 (2 / V.L) htwoL
  have hupper : Tendsto (fun n => B * h * Real.sqrt (δn n) * Real.exp h)
      atTop (𝓝 0) := by
    simpa [B] using
      ((hδlim.sqrt.const_mul
        (stationaryEulerRWMRecurrenceScaleConstant V * h)).mul_const
          (Real.exp h))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _n : ℕ => (0 : ℝ)) atTop (𝓝 0)) hupper
  · exact Eventually.of_forall fun n =>
      integral_nonneg fun _ => sq_nonneg _
  · filter_upwards [hev1, hevL] with n hn1 hnL
    have hhorizon : (((n + 1 : ℕ) : ℝ)) * δn n = h := by
      dsimp [δn]
      field_simp
    exact stationaryEulerRWMPairChain_energy_fixedHorizon_exp_le
      V (δn n) h (hδpos n) hn1.le hnL.le (n + 1) hhorizon

end DiscreteTime
end
end UniformRandomMALA
