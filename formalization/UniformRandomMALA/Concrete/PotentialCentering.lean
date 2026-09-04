import UniformRandomMALA.Concrete.EuclideanTarget
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Centering a strongly convex potential

This file supplies the elementary centering facts used by the finite
discrete-time energy estimate.  A strongly convex potential attains its
minimum, its recorded gradient vanishes there, and smoothness controls the
gradient by the excess potential energy.
-/

namespace UniformRandomMALA

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace Concrete

namespace FirstOrderPotential

variable {d : ℕ} (V : FirstOrderPotential d)

/-- A radius outside which the quadratic lower bound already exceeds the
value of the potential at the origin. -/
def centeringRadius : ℝ := 2 * ‖V.gradU 0‖ / V.m

lemma centeringRadius_nonneg : 0 ≤ V.centeringRadius := by
  exact div_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) V.hm.le

/-- Outside the centering ball, the potential is no smaller than its value
at the origin. -/
lemma U_zero_le_of_centeringRadius_le_norm {x : State d}
    (hx : V.centeringRadius ≤ ‖x‖) :
    V.U 0 ≤ V.U x := by
  let a : ℝ := ‖V.gradU 0‖
  have ha : 0 ≤ a := norm_nonneg _
  have hscaled : 2 * a ≤ V.m * ‖x‖ := by
    have hdiv : 2 * a / V.m ≤ ‖x‖ := by
      simpa [centeringRadius, a] using hx
    have := (div_le_iff₀ V.hm).mp hdiv
    simpa [mul_comm] using this
  have hsq : (2 * a) ^ 2 ≤ (V.m * ‖x‖) ^ 2 := by
    exact (sq_le_sq₀ (mul_nonneg (by norm_num) ha)
      (mul_nonneg V.hm.le (norm_nonneg _))).2 hscaled
  have henergy : a ^ 2 / V.m ≤ (V.m / 4) * ‖x‖ ^ 2 := by
    apply (div_le_iff₀ V.hm).2
    nlinarith
  have hlower := V.quadraticLowerBound x
  dsimp [a] at henergy
  linarith

/-- A strongly convex first-order potential attains a global minimum.

The proof minimizes on an explicit compact closed ball.  The quadratic
lower bound shows that every point outside this ball has potential at least
`U 0`, whereas the minimum on the ball is at most `U 0`. -/
theorem exists_globalMinimizer :
    ∃ xStar : State d, ∀ x : State d, V.U xStar ≤ V.U x := by
  let K : Set (State d) := Metric.closedBall 0 V.centeringRadius
  have hKcompact : IsCompact K := by
    exact ProperSpace.isCompact_closedBall 0 V.centeringRadius
  have hzeroK : (0 : State d) ∈ K := by
    simp [K, V.centeringRadius_nonneg]
  obtain ⟨xStar, hxStarK, hxStarMin⟩ :=
    hKcompact.exists_isMinOn ⟨0, hzeroK⟩ V.continuous_U.continuousOn
  refine ⟨xStar, fun x => ?_⟩
  by_cases hxK : x ∈ K
  · exact hxStarMin hxK
  · have hxNorm : V.centeringRadius ≤ ‖x‖ := by
      have hnot : ¬ ‖x‖ ≤ V.centeringRadius := by
        simpa [K, Metric.mem_closedBall, dist_zero_right] using hxK
      exact le_of_lt (lt_of_not_ge hnot)
    exact (hxStarMin hzeroK).trans (V.U_zero_le_of_centeringRadius_le_norm hxNorm)

/-- A chosen global minimizer. -/
def minimizer : State d := Classical.choose V.exists_globalMinimizer

lemma minimizer_isGlobalMin (x : State d) :
    V.U V.minimizer ≤ V.U x :=
  (Classical.choose_spec V.exists_globalMinimizer) x

lemma minimizer_energy_nonneg (x : State d) :
    0 ≤ V.U x - V.U V.minimizer := by
  linarith [V.minimizer_isGlobalMin x]

/-- The recorded gradient vanishes at the global minimizer.  This uses only
the upper Taylor inequality, evaluated at one explicit descent point. -/
theorem gradU_minimizer : V.gradU V.minimizer = 0 := by
  let g : State d := V.gradU V.minimizer
  let y : State d := V.minimizer - (1 / V.L) • g
  have hupper := V.upperTaylor V.minimizer y
  have hmin := V.minimizer_isGlobalMin y
  have hnorm : ‖y - V.minimizer‖ ^ 2 = (1 / V.L) ^ 2 * ‖g‖ ^ 2 := by
    change ‖(V.minimizer - (1 / V.L) • g) - V.minimizer‖ ^ 2 = _
    rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg zero_le_one V.hL.le)]
    ring
  have hinner :
      @inner ℝ (State d) _ g (y - V.minimizer) =
        -(1 / V.L) * ‖g‖ ^ 2 := by
    change @inner ℝ (State d) _ g
      ((V.minimizer - (1 / V.L) • g) - V.minimizer) = _
    rw [sub_sub_cancel_left, inner_neg_right, inner_smul_right,
      real_inner_self_eq_norm_sq]
    ring
  have hgSq : ‖g‖ ^ 2 ≤ 0 := by
    rw [hinner, hnorm] at hupper
    have hL := V.hL
    field_simp [ne_of_gt hL] at hupper
    nlinarith
  have hg : ‖g‖ = 0 := by nlinarith [sq_nonneg ‖g‖]
  exact norm_eq_zero.mp hg

/-- Smoothness controls the squared gradient by twice `L` times the excess
energy above the global minimum. -/
theorem gradU_norm_sq_le_potentialGap (x : State d) :
    ‖V.gradU x‖ ^ 2 ≤ 2 * V.L * (V.U x - V.U V.minimizer) := by
  let g : State d := V.gradU x
  let y : State d := x - (1 / V.L) • g
  have hupper := V.upperTaylor x y
  have hmin := V.minimizer_isGlobalMin y
  have hnorm : ‖y - x‖ ^ 2 = (1 / V.L) ^ 2 * ‖g‖ ^ 2 := by
    change ‖(x - (1 / V.L) • g) - x‖ ^ 2 = _
    rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg zero_le_one V.hL.le)]
    ring
  have hinner :
      @inner ℝ (State d) _ g (y - x) = -(1 / V.L) * ‖g‖ ^ 2 := by
    change @inner ℝ (State d) _ g ((x - (1 / V.L) • g) - x) = _
    rw [sub_sub_cancel_left, inner_neg_right, inner_smul_right,
      real_inner_self_eq_norm_sq]
    ring
  rw [hinner, hnorm] at hupper
  have hL := V.hL
  field_simp [ne_of_gt hL] at hupper
  nlinarith

/-- Strong convexity after centering at the minimizer. -/
theorem centered_quadraticLowerBound (x : State d) :
    V.U V.minimizer + (V.m / 2) * ‖x - V.minimizer‖ ^ 2 ≤ V.U x := by
  have h := V.lowerTaylor V.minimizer x
  simpa [V.gradU_minimizer] using h

/-- Convexity in the exact two-point form needed for the scaling argument.
It is derived directly from the lower Taylor inequality, avoiding a separate
abstract differentiability/convexity interface. -/
theorem potential_segment_le (x y : State d) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    V.U ((1 - a) • x + a • y) ≤ (1 - a) * V.U x + a * V.U y := by
  let z : State d := (1 - a) • x + a • y
  have hax : 0 ≤ 1 - a := sub_nonneg.mpr ha1
  have hxTaylor := V.lowerTaylor z x
  have hyTaylor := V.lowerTaylor z y
  have hmx : 0 ≤ (V.m / 2) * ‖x - z‖ ^ 2 :=
    mul_nonneg (div_nonneg V.hm.le (by norm_num)) (sq_nonneg _)
  have hmy : 0 ≤ (V.m / 2) * ‖y - z‖ ^ 2 :=
    mul_nonneg (div_nonneg V.hm.le (by norm_num)) (sq_nonneg _)
  have hxFirst : V.U z + @inner ℝ (State d) _ (V.gradU z) (x - z) ≤ V.U x := by
    linarith
  have hyFirst : V.U z + @inner ℝ (State d) _ (V.gradU z) (y - z) ≤ V.U y := by
    linarith
  have hinner :
      (1 - a) * @inner ℝ (State d) _ (V.gradU z) (x - z) +
          a * @inner ℝ (State d) _ (V.gradU z) (y - z) = 0 := by
    rw [← inner_smul_right, ← inner_smul_right, ← inner_add_right]
    have hvec : (1 - a) • (x - z) + a • (y - z) = 0 := by
      dsimp [z]
      module
    rw [hvec, inner_zero_right]
  have hxScaled := mul_le_mul_of_nonneg_left hxFirst hax
  have hyScaled := mul_le_mul_of_nonneg_left hyFirst ha0
  nlinarith

/-- Scaling a point toward the minimizer can increase the centered potential
by at most the same scalar factor. -/
theorem potential_centered_smul_le (x : State d) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    V.U (V.minimizer + a • (x - V.minimizer)) - V.U V.minimizer ≤
      a * (V.U x - V.U V.minimizer) := by
  have hseg := V.potential_segment_le V.minimizer x a ha0 ha1
  have hpoint :
      (1 - a) • V.minimizer + a • x =
        V.minimizer + a • (x - V.minimizer) := by module
  rw [hpoint] at hseg
  linarith

/-- The Boltzmann weight after subtracting the minimum of the potential. -/
def centeredBoltzmannWeight (x : State d) : ℝ :=
  Real.exp (-(V.U x - V.U V.minimizer))

lemma centeredBoltzmannWeight_eq (x : State d) :
    V.centeredBoltzmannWeight x =
      Real.exp (V.U V.minimizer) * V.boltzmannWeight x := by
  rw [centeredBoltzmannWeight, boltzmannWeight, ← Real.exp_add]
  congr 1
  ring

lemma continuous_centeredBoltzmannWeight :
    Continuous V.centeredBoltzmannWeight := by
  unfold centeredBoltzmannWeight
  exact Real.continuous_exp.comp
    (V.continuous_U.sub continuous_const).neg

lemma integrable_centeredBoltzmannWeight :
    Integrable V.centeredBoltzmannWeight := by
  apply (V.integrable_boltzmannWeight.const_mul
    (Real.exp (V.U V.minimizer))).congr
  exact ae_of_all _ fun x => (V.centeredBoltzmannWeight_eq x).symm

/-- Integrating against the normalized target is ordinary Lebesgue
integration against the normalized Boltzmann weight. -/
theorem integral_target_eq_normalized_boltzmann (f : State d → ℝ) :
    (∫ x, f x ∂(V.target : Measure (State d))) =
      (V.boltzmannFiniteMeasure.mass : ℝ)⁻¹ *
        ∫ x, V.boltzmannWeight x * f x ∂volume := by
  rw [V.target_toMeasure_eq_withDensity,
    integral_withDensity_eq_integral_toReal_smul
      V.measurable_targetDensity
        (ae_of_all _ fun x => (V.targetDensity_ne_top x).lt_top)]
  simp_rw [targetDensity, ENNReal.toReal_mul, boltzmannDensity,
    ENNReal.toReal_ofReal (V.boltzmannWeight_pos _).le,
    ENNReal.toReal_inv, ENNReal.coe_toReal, smul_eq_mul]
  rw [← integral_const_mul]
  congr 2
  ext x
  ring

/-- Every positive exponential tilt of the negative centered potential is
Lebesgue integrable. -/
theorem integrable_exp_neg_mul_potentialGap (a : ℝ) (ha : 0 < a) :
    Integrable (fun x : State d =>
      Real.exp (-a * (V.U x - V.U V.minimizer))) volume := by
  have hcoef : 0 < a * V.m / 2 := div_pos (mul_pos ha V.hm) (by norm_num)
  have hc := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := State d) (b := (a * V.m / 2 : ℂ)) (c := 0) (w := 0)
    (by exact_mod_cast hcoef)
  have hgauss : Integrable
      (fun z : State d => Real.exp (-(a * V.m / 2) * ‖z‖ ^ 2)) := by
    refine hc.norm.congr ?_
    filter_upwards with z
    rw [show (↑‖z‖ : ℂ) ^ 2 = ↑(‖z‖ ^ 2) by norm_cast]
    simp [Complex.norm_exp]
    left
    simp [pow_two, Complex.mul_re]
  have hmajor : Integrable
      (fun x : State d =>
        Real.exp (-(a * V.m / 2) * ‖x - V.minimizer‖ ^ 2)) :=
    hgauss.comp_sub_right V.minimizer
  apply hmajor.mono
    (Real.continuous_exp.comp
      (continuous_const.mul
        ((V.continuous_U.sub continuous_const)))).aestronglyMeasurable
  exact ae_of_all _ fun x => by
    change |Real.exp (-a * (V.U x - V.U V.minimizer))| ≤
      |Real.exp (-(a * V.m / 2) * ‖x - V.minimizer‖ ^ 2)|
    rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hcenter := V.centered_quadraticLowerBound x
    have hnonneg : 0 ≤ a := ha.le
    nlinarith

/-- The change-of-variables estimate behind the target exponential moment.
It is stated first at Lebesgue-integral level.  Translating to the minimizer
and scaling by `a` gives the exact Jacobian factor `a⁻ᵈ`. -/
theorem integral_exp_neg_mul_potentialGap_le
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    (∫ x : State d,
        Real.exp (-a * (V.U x - V.U V.minimizer)) ∂volume) ≤
      (a ^ d)⁻¹ *
        ∫ x : State d, V.centeredBoltzmannWeight x ∂volume := by
  let shifted : State d → ℝ := fun z =>
    V.centeredBoltzmannWeight (V.minimizer + z)
  have hshifted : Integrable shifted := by
    exact V.integrable_centeredBoltzmannWeight.comp_add_left V.minimizer
  have hright : Integrable (fun z : State d => shifted (a • z)) :=
    hshifted.comp_smul ha0.ne'
  have hleftMeas : AEStronglyMeasurable (fun z : State d =>
      Real.exp (-a *
        (V.U (V.minimizer + z) - V.U V.minimizer))) volume := by
    exact (Real.continuous_exp.comp
      (continuous_const.mul
        ((V.continuous_U.comp (continuous_const.add continuous_id)).sub
          continuous_const))).aestronglyMeasurable
  have hpoint : ∀ z : State d,
      Real.exp (-a *
          (V.U (V.minimizer + z) - V.U V.minimizer)) ≤
        shifted (a • z) := by
    intro z
    unfold shifted centeredBoltzmannWeight
    apply Real.exp_le_exp.mpr
    have hscale := V.potential_centered_smul_le
      (V.minimizer + z) a ha0.le ha1
    have hx :
        V.minimizer + a • ((V.minimizer + z) - V.minimizer) =
          V.minimizer + a • z := by module
    rw [hx] at hscale
    linarith
  have hleft : Integrable (fun z : State d =>
      Real.exp (-a *
        (V.U (V.minimizer + z) - V.U V.minimizer))) volume := by
    apply integrable_of_le_of_le hleftMeas
      (ae_of_all _ fun _ => (Real.exp_pos _).le)
      (ae_of_all _ hpoint) (integrable_zero _ _ volume) hright
  calc
    (∫ x : State d,
        Real.exp (-a * (V.U x - V.U V.minimizer)) ∂volume) =
        ∫ z : State d,
          Real.exp (-a *
            (V.U (V.minimizer + z) - V.U V.minimizer)) ∂volume := by
      simpa only using
        (MeasureTheory.integral_add_left_eq_self
          (fun x : State d =>
            Real.exp (-a * (V.U x - V.U V.minimizer))) V.minimizer).symm
    _ ≤ ∫ z : State d, shifted (a • z) ∂volume :=
      integral_mono hleft hright hpoint
    _ = (a ^ Module.finrank ℝ (State d))⁻¹ *
        ∫ z : State d, shifted z ∂volume := by
      simpa only [smul_eq_mul] using
        (Measure.integral_comp_smul_of_nonneg
          (volume : Measure (State d)) shifted a (hR := ha0.le))
    _ = (a ^ d)⁻¹ *
        ∫ x : State d, V.centeredBoltzmannWeight x ∂volume := by
      rw [MeasureTheory.integral_add_left_eq_self]
      rw [finrank_euclideanSpace_fin]

/-- Exponential moments of the potential gap under the normalized target.
This is the exact elementary estimate used in the discrete Euler energy
argument. -/
theorem integral_exp_potentialGap_le
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (∫ x : State d,
        Real.exp (s * (V.U x - V.U V.minimizer))
          ∂(V.target : Measure (State d))) ≤
      ((1 - s) ^ d)⁻¹ := by
  let a : ℝ := 1 - s
  let c : ℝ := (V.boltzmannFiniteMeasure.mass : ℝ)⁻¹ *
    Real.exp (-V.U V.minimizer)
  have ha0 : 0 < a := by dsimp [a]; linarith
  have ha1 : a ≤ 1 := by dsimp [a]; linarith
  have hc : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg (inv_nonneg.mpr NNReal.zero_le_coe) (Real.exp_pos _).le
  have hnumerator :
      (∫ x : State d,
          V.boltzmannWeight x *
            Real.exp (s * (V.U x - V.U V.minimizer)) ∂volume) =
        Real.exp (-V.U V.minimizer) *
          ∫ x : State d,
            Real.exp (-a * (V.U x - V.U V.minimizer)) ∂volume := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      change Real.exp (-V.U x) *
        Real.exp (s * (V.U x - V.U V.minimizer)) =
          Real.exp (-V.U V.minimizer) *
            Real.exp (-a * (V.U x - V.U V.minimizer))
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      dsimp [a]
      ring
  have hpartition :
      (∫ x : State d, V.boltzmannWeight x ∂volume) =
        Real.exp (-V.U V.minimizer) *
          ∫ x : State d, V.centeredBoltzmannWeight x ∂volume := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      change Real.exp (-V.U x) =
        Real.exp (-V.U V.minimizer) *
          Real.exp (-(V.U x - V.U V.minimizer))
      rw [← Real.exp_add]
      congr 1
      ring
  have hnormalization :
      c * (∫ x : State d, V.centeredBoltzmannWeight x ∂volume) = 1 := by
    have htargetOne := V.integral_target_eq_normalized_boltzmann
      (fun _ : State d => (1 : ℝ))
    have hprob :
        (∫ _x : State d, (1 : ℝ) ∂(V.target : Measure (State d))) = 1 := by simp
    rw [hprob] at htargetOne
    simp only [mul_one] at htargetOne
    rw [hpartition] at htargetOne
    dsimp [c]
    linarith
  rw [V.integral_target_eq_normalized_boltzmann,
    hnumerator]
  rw [← mul_assoc]
  change c *
      (∫ x : State d,
        Real.exp (-a * (V.U x - V.U V.minimizer)) ∂volume) ≤
    ((1 - s) ^ d)⁻¹
  change c *
      (∫ x : State d,
        Real.exp (-a * (V.U x - V.U V.minimizer)) ∂volume) ≤
    (a ^ d)⁻¹
  calc
    c * (∫ x : State d,
        Real.exp (-a * (V.U x - V.U V.minimizer)) ∂volume) ≤
        c * ((a ^ d)⁻¹ *
          ∫ x : State d, V.centeredBoltzmannWeight x ∂volume) :=
      mul_le_mul_of_nonneg_left
        (V.integral_exp_neg_mul_potentialGap_le a ha0 ha1) hc
    _ = (a ^ d)⁻¹ *
        (c * ∫ x : State d, V.centeredBoltzmannWeight x ∂volume) := by ring
    _ = (a ^ d)⁻¹ := by rw [hnormalization, mul_one]

/-- Every subcritical positive exponential tilt of the potential gap is
integrable under the normalized target.  This is the integrability companion
to `integral_exp_potentialGap_le`; it is useful when a later estimate needs
polynomial target moments rather than only a numerical integral bound. -/
theorem integrable_exp_potentialGap
    (s : ℝ) (hs : s < 1) :
    Integrable (fun x : State d =>
      Real.exp (s * (V.U x - V.U V.minimizer)))
      (V.target : Measure (State d)) := by
  rw [V.target_toMeasure_eq_withDensity,
    integrable_withDensity_iff V.measurable_targetDensity
      (ae_of_all _ fun x => (V.targetDensity_ne_top x).lt_top)]
  let c : ℝ := (V.boltzmannFiniteMeasure.mass : ℝ)⁻¹ *
    Real.exp (-V.U V.minimizer)
  have hbase := V.integrable_exp_neg_mul_potentialGap
    (1 - s) (sub_pos.mpr hs)
  apply (hbase.const_mul c).congr
  exact ae_of_all _ fun x => by
    simp only [targetDensity, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.coe_toReal, boltzmannDensity, boltzmannWeight]
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
    dsimp [c]
    have hexp :
        Real.exp (-V.U V.minimizer) *
            Real.exp (-(1 - s) * (V.U x - V.U V.minimizer)) =
          Real.exp (s * (V.U x - V.U V.minimizer)) *
            Real.exp (-V.U x) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc
      (↑V.boltzmannFiniteMeasure.mass)⁻¹ * Real.exp (-V.U V.minimizer) *
          Real.exp (-(1 - s) * (V.U x - V.U V.minimizer)) =
          (↑V.boltzmannFiniteMeasure.mass)⁻¹ *
            (Real.exp (-V.U V.minimizer) *
              Real.exp (-(1 - s) * (V.U x - V.U V.minimizer))) := by ring
      _ = (↑V.boltzmannFiniteMeasure.mass)⁻¹ *
          (Real.exp (s * (V.U x - V.U V.minimizer)) *
            Real.exp (-V.U x)) := by rw [hexp]
      _ = Real.exp (s * (V.U x - V.U V.minimizer)) *
          ((↑V.boltzmannFiniteMeasure.mass)⁻¹ * Real.exp (-V.U x)) := by ring

/-- The fourth gradient moment required by the stationary Euler/RWM coupling
is finite.  The proof is deliberately elementary: smooth descent controls
`‖grad U‖²` by the potential gap, and the second Taylor term of `exp` controls
the square of that gap by a half-exponential tilt. -/
theorem integrable_gradU_norm_fourth :
    Integrable (fun x : State d => ‖V.gradU x‖ ^ 4)
      (V.target : Measure (State d)) := by
  have hExp := V.integrable_exp_potentialGap (1 / 2) (by norm_num)
  have hMajor : Integrable (fun x : State d =>
      32 * V.L ^ 2 *
        Real.exp ((1 / 2) * (V.U x - V.U V.minimizer)))
      (V.target : Measure (State d)) := hExp.const_mul _
  apply hMajor.mono
  · exact (V.continuous_gradU.norm.pow 4).aestronglyMeasurable
  · exact ae_of_all _ fun x => by
      let u : ℝ := V.U x - V.U V.minimizer
      have hu : 0 ≤ u := V.minimizer_energy_nonneg x
      have hg := V.gradU_norm_sq_le_potentialGap x
      have hpow := Real.pow_div_factorial_le_exp
        (x := u / 2) (div_nonneg hu (by norm_num)) 2
      have huExp : u ^ 2 ≤ 8 * Real.exp (u / 2) := by
        norm_num [Nat.factorial] at hpow
        nlinarith
      have hsq : ‖V.gradU x‖ ^ 4 ≤ (2 * V.L * u) ^ 2 := by
        calc
          ‖V.gradU x‖ ^ 4 = (‖V.gradU x‖ ^ 2) ^ 2 := by ring
          _ ≤ (2 * V.L * u) ^ 2 := by
            exact (sq_le_sq₀ (sq_nonneg _) (mul_nonneg
              (mul_nonneg (by norm_num) V.hL.le) hu)).2 hg
      have hfinal : ‖V.gradU x‖ ^ 4 ≤
          32 * V.L ^ 2 * Real.exp (u / 2) := by
        calc
          ‖V.gradU x‖ ^ 4 ≤ (2 * V.L * u) ^ 2 := hsq
          _ = 4 * V.L ^ 2 * u ^ 2 := by ring
          _ ≤ 4 * V.L ^ 2 * (8 * Real.exp (u / 2)) := by gcongr
          _ = 32 * V.L ^ 2 * Real.exp (u / 2) := by ring
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _),
        Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      simpa [u, div_eq_mul_inv, mul_comm] using hfinal

/-- Exact exponential-moment input for the frozen-gradient part of the Euler
energy estimate. -/
theorem integral_exp_gradU_norm_sq_le
    (c : ℝ) (hc : 0 ≤ c) (hsmall : 2 * V.L * c < 1) :
    (∫ x : State d, Real.exp (c * ‖V.gradU x‖ ^ 2)
        ∂(V.target : Measure (State d))) ≤
      ((1 - 2 * V.L * c) ^ d)⁻¹ := by
  let s : ℝ := 2 * V.L * c
  have hs0 : 0 ≤ s := by
    dsimp [s]
    exact mul_nonneg (mul_nonneg (by norm_num) V.hL.le) hc
  have hs1 : s < 1 := by simpa [s] using hsmall
  have hMajor := V.integrable_exp_potentialGap s hs1
  have hpoint : ∀ x : State d,
      Real.exp (c * ‖V.gradU x‖ ^ 2) ≤
        Real.exp (s * (V.U x - V.U V.minimizer)) := by
    intro x
    apply Real.exp_le_exp.mpr
    have hg := V.gradU_norm_sq_le_potentialGap x
    have hcHg := mul_le_mul_of_nonneg_left hg hc
    dsimp [s]
    nlinarith
  have hLeft : Integrable (fun x : State d =>
      Real.exp (c * ‖V.gradU x‖ ^ 2))
      (V.target : Measure (State d)) := by
    apply hMajor.mono
    · exact (Real.continuous_exp.comp
        (continuous_const.mul (V.continuous_gradU.norm.pow 2))).aestronglyMeasurable
    · exact ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact hpoint x
  calc
    (∫ x : State d, Real.exp (c * ‖V.gradU x‖ ^ 2)
        ∂(V.target : Measure (State d))) ≤
        ∫ x : State d,
          Real.exp (s * (V.U x - V.U V.minimizer))
          ∂(V.target : Measure (State d)) :=
      integral_mono hLeft hMajor hpoint
    _ ≤ ((1 - s) ^ d)⁻¹ := V.integral_exp_potentialGap_le s hs0 hs1
    _ = ((1 - 2 * V.L * c) ^ d)⁻¹ := by rfl

end FirstOrderPotential

end Concrete

end

end UniformRandomMALA
