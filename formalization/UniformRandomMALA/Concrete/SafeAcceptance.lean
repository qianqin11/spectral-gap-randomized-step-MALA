import UniformRandomMALA.Concrete.MALA
import UniformRandomMALA.Concrete.Cocoercivity
import UniformRandomMALA.DiscreteTime.GaussianLawBridge
import UniformRandomMALA.DiscreteTime.GaussianMaximum

/-!
# A globally safe lower bound for one-step MALA acceptance

The proof is split into deterministic pieces.  In particular, the exact
Gaussian proposal log ratio is rewritten before any exponential or integral
is introduced.  This is the form needed by the discrete proof of Proposition
3.2.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

namespace Concrete
namespace FirstOrderPotential

variable {d : ℕ} (V : FirstOrderPotential d)

/-- Pure inner-product algebra used after substituting a Gaussian innovation
in the proposal.  Keeping it independent of the potential makes the exact
probabilistic identity reduce to a single rewrite. -/
theorem mala_innovation_algebra
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {h : ℝ} (hh : 0 < h) (gx gy z : E) :
    (1 / 2) * inner ℝ
          (-h • gx + Real.sqrt (2 * h) • z) (gx + gy) +
        (h / 4) * (‖gx‖ ^ 2 - ‖gy‖ ^ 2) =
      inner ℝ gy (-h • gx + Real.sqrt (2 * h) • z) -
        (h / 4) * ‖gy - gx‖ ^ 2 -
        Real.sqrt (h / 2) * inner ℝ z (gy - gx) := by
  have h2h : 0 ≤ 2 * h := by positivity
  have hh2 : 0 ≤ h / 2 := by positivity
  have hs2 : Real.sqrt (2 * h) ^ 2 = 2 * h := Real.sq_sqrt h2h
  have ht2 : Real.sqrt (h / 2) ^ 2 = h / 2 := Real.sq_sqrt hh2
  have hs : Real.sqrt (2 * h) = 2 * Real.sqrt (h / 2) := by
    have hs0 := Real.sqrt_nonneg (2 * h)
    have ht0 := Real.sqrt_nonneg (h / 2)
    nlinarith [sq_nonneg (Real.sqrt (2 * h) - 2 * Real.sqrt (h / 2)),
      sq_nonneg (Real.sqrt (2 * h) + 2 * Real.sqrt (h / 2))]
  have hnormdiff :
      ‖gy - gx‖ ^ 2 = ‖gy‖ ^ 2 - 2 * inner ℝ gx gy + ‖gx‖ ^ 2 := by
    calc
      ‖gy - gx‖ ^ 2 = inner ℝ (gy - gx) (gy - gx) :=
        (real_inner_self_eq_norm_sq (gy - gx)).symm
      _ = _ := by
        rw [inner_sub_left, inner_sub_right, inner_sub_right,
          real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
          real_inner_comm gy gx]
        ring
  rw [hnormdiff]
  simp only [inner_add_left, inner_add_right, inner_sub_right,
    inner_smul_left, inner_smul_right, starRingEnd_apply,
    star_trivial, neg_mul]
  rw [real_inner_comm gy gx, real_inner_comm z gy,
    real_inner_self_eq_norm_sq, hs]
  ring

/-- The real logarithm of the (unnormalized) reverse/forward MALA edge ratio.
The Gaussian and target normalizing constants have already cancelled. -/
def malaLogRatio (h : ℝ) (x y : State d) : ℝ :=
  V.U x - V.U y +
    (‖y - V.proposalMean h x‖ ^ 2 -
      ‖x - V.proposalMean h y‖ ^ 2) / (4 * h)

/-- Expanding the two Gaussian squares gives the symmetric-gradient form of
the MALA log ratio. -/
theorem malaLogRatio_eq_symmetric
    {h : ℝ} (hh : 0 < h) (x y : State d) :
    V.malaLogRatio h x y =
      V.U x - V.U y +
        (1 / 2) * inner ℝ (y - x) (V.gradU x + V.gradU y) +
        (h / 4) * (‖V.gradU x‖ ^ 2 - ‖V.gradU y‖ ^ 2) := by
  have hsx :
      y - V.proposalMean h x = (y - x) + h • V.gradU x := by
    simp only [proposalMean]
    module
  have hsy :
      x - V.proposalMean h y = -(y - x) + h • V.gradU y := by
    simp [proposalMean]
    module
  have hnorm (a b : State d) :
      ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + 2 * inner ℝ a b + ‖b‖ ^ 2 := by
    calc
      ‖a + b‖ ^ 2 = inner ℝ (a + b) (a + b) :=
        (real_inner_self_eq_norm_sq (a + b)).symm
      _ = _ := by
        rw [inner_add_left, inner_add_right, inner_add_right,
          real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
          real_inner_comm b a]
        ring
  rw [malaLogRatio, hsx, hsy, hnorm, hnorm]
  simp only [norm_neg, inner_neg_left, inner_smul_right, norm_smul,
    Real.norm_eq_abs, abs_of_pos hh, mul_pow]
  rw [inner_add_right]
  field_simp [ne_of_gt hh]
  ring

/-- Exact log-ratio identity at a proposal written as
`y = x - h grad U(x) + sqrt(2h) z`. -/
theorem malaLogRatio_at_innovation
    {h : ℝ} (hh : 0 < h) (x z : State d) :
    let y := V.proposalMean h x + Real.sqrt (2 * h) • z
    V.malaLogRatio h x y =
      V.U x - V.U y - inner ℝ (V.gradU y) (x - y) -
        (h / 4) * ‖V.gradU y - V.gradU x‖ ^ 2 -
        Real.sqrt (h / 2) *
          inner ℝ z (V.gradU y - V.gradU x) := by
  dsimp only
  let y : State d := V.proposalMean h x + Real.sqrt (2 * h) • z
  change V.malaLogRatio h x y =
    V.U x - V.U y - inner ℝ (V.gradU y) (x - y) -
      (h / 4) * ‖V.gradU y - V.gradU x‖ ^ 2 -
      Real.sqrt (h / 2) * inner ℝ z (V.gradU y - V.gradU x)
  have hs : y - x =
      -h • V.gradU x + Real.sqrt (2 * h) • z := by
    dsimp [y, proposalMean]
    module
  have hxs : x - y = -(y - x) := by module
  rw [V.malaLogRatio_eq_symmetric hh x y, hxs, inner_neg_right]
  simp only [hs, sub_neg_eq_add]
  linarith [mala_innovation_algebra hh (V.gradU x) (V.gradU y) z]

/-- Global pointwise lower bound for the log acceptance ratio.  It uses no
small-gradient or high-probability event: only `h ≤ 1/L`. -/
theorem malaLogRatio_at_innovation_lower
    {h : ℝ} (hh : 0 < h) (hhL : h ≤ 1 / V.L)
    (x z : State d) :
    let y := V.proposalMean h x + Real.sqrt (2 * h) • z
    (-(V.L * h / 2) * ‖z‖ ^ 2 ≤ V.malaLogRatio h x y) := by
  dsimp only
  let y : State d := V.proposalMean h x + Real.sqrt (2 * h) • z
  change -(V.L * h / 2) * ‖z‖ ^ 2 ≤ V.malaLogRatio h x y
  let dg : State d := V.gradU y - V.gradU x
  let breg : ℝ :=
    V.U x - V.U y - inner ℝ (V.gradU y) (x - y)
  have hbh : ‖dg‖ ^ 2 / (2 * V.L) ≤ breg := by
    dsimp [dg, breg]
    simpa only [norm_sub_rev] using V.gradDiff_sq_div_twoL_le_bregman x y
  have hsafe := one_sided_bh_safe_log_lower
    V.L h breg ‖dg‖ ‖z‖ (inner ℝ z dg)
    V.hL (le_of_lt hh) hhL (norm_nonneg _) (norm_nonneg _)
    hbh (real_inner_le_norm z dg)
  have hid := V.malaLogRatio_at_innovation hh x z
  change V.malaLogRatio h x y =
      breg - h / 4 * ‖dg‖ ^ 2 -
        Real.sqrt (h / 2) * inner ℝ z dg at hid
  rw [hid]
  exact hsafe

lemma toReal_targetDensity (x : State d) :
    (V.targetDensity x).toReal =
      ((V.boltzmannFiniteMeasure.mass⁻¹ : ℝ≥0∞).toReal) *
        Real.exp (-V.U x) := by
  rw [targetDensity, ENNReal.toReal_mul]
  simp [boltzmannDensity, boltzmannWeight,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]

lemma toReal_proposalDensity {h : ℝ} (hh : 0 < h)
    (x y : State d) :
    (V.proposalDensity h x y).toReal = V.proposalDensityReal h x y := by
  rw [proposalDensity, ENNReal.toReal_ofReal]
  exact V.proposalDensityReal_nonneg hh x y

/-- The extended-nonnegative edge ratio used by the concrete MH kernel is
exactly the exponential of the real log ratio. -/
theorem malaEdgeRatio_eq_ofReal_exp_malaLogRatio
    {h : ℝ} (hh : 0 < h) (x y : State d) :
    MetropolisHastings.edgeDensity V.targetDensity (V.proposalDensity h) y x /
        MetropolisHastings.edgeDensity V.targetDensity (V.proposalDensity h) x y =
      ENNReal.ofReal (Real.exp (V.malaLogRatio h x y)) := by
  let e : State d → State d → ℝ≥0∞ :=
    MetropolisHastings.edgeDensity V.targetDensity (V.proposalDensity h)
  have hnumtop : e y x ≠ ∞ := V.malaEdgeDensity_ne_top h y x
  have hdpos : e x y ≠ 0 := V.malaEdgeDensity_ne_zero hh x y
  have hratioTop : e y x / e x y ≠ ∞ :=
    ENNReal.div_ne_top hnumtop hdpos
  change e y x / e x y = _
  rw [← ENNReal.ofReal_toReal hratioTop]
  congr 1
  rw [ENNReal.toReal_div]
  simp only [e, MetropolisHastings.edgeDensity, ENNReal.toReal_mul,
    V.toReal_targetDensity, V.toReal_proposalDensity hh]
  unfold proposalDensityReal proposalBase malaLogRatio
  have hc :
      0 < (V.boltzmannFiniteMeasure.mass⁻¹ : ℝ≥0∞).toReal := by
    apply ENNReal.toReal_pos
    · exact ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top
    · exact ENNReal.inv_ne_top.mpr
        (ENNReal.coe_ne_zero.mpr
          (V.boltzmannFiniteMeasure.mass_nonzero_iff.mpr
            V.boltzmannFiniteMeasure_ne_zero))
  have hn : 0 < proposalNormalizer (d := d) h :=
    proposalNormalizer_pos (d := d) hh
  field_simp [ne_of_gt hc, ne_of_gt hn, ne_of_gt (Real.exp_pos (-V.U x)),
    ne_of_gt (Real.exp_pos (-V.U y))]
  let A : ℝ := ‖x - V.proposalMean h y‖ ^ 2 / (4 * h)
  let B : ℝ := ‖y - V.proposalMean h x‖ ^ 2 / (4 * h)
  let R : ℝ :=
    (4 * h * (V.U x - V.U y) +
      (‖y - V.proposalMean h x‖ ^ 2 -
        ‖x - V.proposalMean h y‖ ^ 2)) / (4 * h)
  change Real.exp (-V.U y) * Real.exp (-A) =
    Real.exp (-V.U x) * Real.exp (-B) * Real.exp R
  calc
    Real.exp (-V.U y) * Real.exp (-A) =
        Real.exp (-V.U y - A) := by
      simpa only [sub_eq_add_neg] using
        (Real.exp_add (-V.U y) (-A)).symm
    _ = Real.exp (-V.U x - B + R) := by
      congr 1
      dsimp [A, B, R]
      field_simp [ne_of_gt hh]
      ring
    _ = Real.exp (-V.U x) * Real.exp (-B) * Real.exp R := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_add]

/-- Real-valued presentation of the concrete MALA acceptance probability. -/
theorem malaAcceptance_eq_ofReal_min_exp_logRatio
    {h : ℝ} (hh : 0 < h) (x y : State d) :
    V.malaAcceptance h x y =
      ENNReal.ofReal (min (Real.exp (V.malaLogRatio h x y)) 1) := by
  rw [malaAcceptance, MetropolisHastings.acceptance,
    V.malaEdgeRatio_eq_ofReal_exp_malaLogRatio hh x y,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_min]

/-- Pointwise safe acceptance lower bound at an affine Gaussian proposal. -/
theorem malaAcceptance_at_innovation_lower
    {h : ℝ} (hh : 0 < h) (hhL : h ≤ 1 / V.L)
    (x z : State d) :
    let y := V.proposalMean h x + Real.sqrt (2 * h) • z
    ENNReal.ofReal (Real.exp (-(V.L * h / 2) * ‖z‖ ^ 2)) ≤
      V.malaAcceptance h x y := by
  dsimp only
  let y : State d := V.proposalMean h x + Real.sqrt (2 * h) • z
  change ENNReal.ofReal (Real.exp (-(V.L * h / 2) * ‖z‖ ^ 2)) ≤
    V.malaAcceptance h x y
  rw [V.malaAcceptance_eq_ofReal_min_exp_logRatio hh x y]
  rw [ENNReal.ofReal_le_ofReal_iff]
  · apply le_min
    · exact Real.exp_le_exp.mpr (V.malaLogRatio_at_innovation_lower hh hhL x z)
    · apply Real.exp_le_one_iff.mpr
      have hcoef : 0 ≤ V.L * h / 2 :=
        div_nonneg (mul_nonneg V.hL.le hh.le) (by norm_num)
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hcoef) (sq_nonneg _)
  · exact le_min (Real.exp_pos _).le zero_le_one

/-- The proposal-averaged acceptance dominates an explicit standard-Gaussian
quadratic Laplace transform. -/
theorem lintegral_malaAcceptance_ge_gaussianLaplace
    {h : ℝ} (hh : 0 < h) (hhL : h ≤ 1 / V.L) (x : State d) :
    (∫⁻ y, V.malaAcceptance h x y ∂V.gaussianDensityProposal h x) ≥
      ∫⁻ z : State d,
        ENNReal.ofReal (Real.exp (-(V.L * h / 2) * ‖z‖ ^ 2))
          ∂stdGaussian (State d) := by
  rw [DiscreteTime.gaussianDensityProposal_eq_map_stdGaussian V hh x]
  rw [MeasureTheory.lintegral_map]
  · exact MeasureTheory.lintegral_mono fun z =>
      V.malaAcceptance_at_innovation_lower hh hhL x z
  · exact Measurable.of_uncurry_left (V.measurable_uncurry_malaAcceptance h)
  · fun_prop

/-- Exact real-valued evaluation of the quadratic Gaussian Laplace transform
appearing in the safe acceptance bound. -/
theorem integral_gaussianLaplace (h : ℝ) (hh : 0 ≤ h) :
    (∫ z : State d,
        Real.exp (-(V.L * h / 2) * ‖z‖ ^ 2) ∂stdGaussian (State d)) =
      ((Real.sqrt (2 * Real.pi))⁻¹ *
        Real.sqrt (Real.pi / (1 / 2 + V.L * h / 2))) ^ d := by
  have ha : -(V.L * h / 2) < (1 / 2 : ℝ) := by
    have hprod : 0 ≤ V.L * h / 2 :=
      div_nonneg (mul_nonneg V.hL.le hh) (by norm_num)
    linarith
  simpa only [sub_neg_eq_add, finrank_euclideanSpace_fin] using
    (DiscreteTime.integral_exp_mul_norm_sq_stdGaussian
      (E := State d) (-(V.L * h / 2)) ha)

/-- The ENNReal Laplace transform is the coercion of the corresponding exact
real integral.  This lemma is the bridge used by kernel acceptance masses. -/
theorem lintegral_gaussianLaplace_eq_ofReal (h : ℝ) (hh : 0 ≤ h) :
    (∫⁻ z : State d,
        ENNReal.ofReal (Real.exp (-(V.L * h / 2) * ‖z‖ ^ 2))
          ∂stdGaussian (State d)) =
      ENNReal.ofReal
        (((Real.sqrt (2 * Real.pi))⁻¹ *
          Real.sqrt (Real.pi / (1 / 2 + V.L * h / 2))) ^ d) := by
  have ha : -(V.L * h / 2) < (1 / 2 : ℝ) := by
    have hprod : 0 ≤ V.L * h / 2 :=
      div_nonneg (mul_nonneg V.hL.le hh) (by norm_num)
    linarith
  have hint := DiscreteTime.integrable_exp_mul_norm_sq_stdGaussian
    (E := State d) (-(V.L * h / 2)) ha
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun _ => (Real.exp_pos _).le)]
  rw [V.integral_gaussianLaplace h hh]

/-- Elementary simplification of the one-coordinate Gaussian Laplace factor.
It is kept separate from the measure calculation. -/
theorem gaussianLaplace_base_eq_inv_sqrt
    (t : ℝ) (ht : 0 ≤ t) :
    (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.sqrt (Real.pi / (1 / 2 + t / 2)) =
      (Real.sqrt (1 + t))⁻¹ := by
  have hpi2 : 0 ≤ 2 * Real.pi := by positivity
  have hden : 0 < 1 / 2 + t / 2 := by linarith
  have hone : 0 < 1 + t := by linarith
  apply (sq_eq_sq₀ (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)) (inv_nonneg.mpr (Real.sqrt_nonneg _))).mp
  rw [mul_pow, inv_pow, Real.sq_sqrt hpi2,
    Real.sq_sqrt (div_nonneg Real.pi_pos.le hden.le), inv_pow,
    Real.sq_sqrt hone.le]
  field_simp [Real.pi_ne_zero, ne_of_gt hden, ne_of_gt hone]

/-- Elementary exponential lower bound on the inverse-square-root power. -/
theorem exp_neg_half_mul_nat_le_invSqrtPow
    (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    Real.exp (-(t * (n : ℝ) / 2)) ≤
      (Real.sqrt (1 + t))⁻¹ ^ n := by
  have hone : 0 < 1 + t := by linarith
  have hsqrt : 0 < Real.sqrt (1 + t) := Real.sqrt_pos.mpr hone
  have hlog : Real.log (1 + t) ≤ t := by
    have := Real.log_le_sub_one_of_pos hone
    linarith
  have hbase :
      Real.exp (-t / 2) ≤ (Real.sqrt (1 + t))⁻¹ := by
    calc
      Real.exp (-t / 2) ≤ Real.exp (-Real.log (1 + t) / 2) := by
        apply Real.exp_le_exp.mpr
        linarith
      _ = Real.exp (-Real.log (Real.sqrt (1 + t))) := by
        rw [Real.log_sqrt hone.le]
        congr 1
        ring
      _ = (Real.sqrt (1 + t))⁻¹ := by
        rw [Real.exp_neg, Real.exp_log hsqrt]
  calc
    Real.exp (-(t * (n : ℝ) / 2)) =
        Real.exp (-t / 2) ^ n := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ (Real.sqrt (1 + t))⁻¹ ^ n :=
      pow_le_pow_left₀ (Real.exp_pos _).le hbase n

/-- Closed-form safe lower bound for the proposal-averaged acceptance.  The
right side is `(1 + L h)^(-d/2)`, written as an ordinary natural power of an
inverse square root to avoid real-power infrastructure. -/
theorem lintegral_malaAcceptance_ge_invSqrtPow
    {h : ℝ} (hh : 0 < h) (hhL : h ≤ 1 / V.L) (x : State d) :
    (∫⁻ y, V.malaAcceptance h x y ∂V.gaussianDensityProposal h x) ≥
      ENNReal.ofReal ((Real.sqrt (1 + V.L * h))⁻¹ ^ d) := by
  calc
    ENNReal.ofReal ((Real.sqrt (1 + V.L * h))⁻¹ ^ d) =
        ∫⁻ z : State d,
          ENNReal.ofReal (Real.exp (-(V.L * h / 2) * ‖z‖ ^ 2))
            ∂stdGaussian (State d) := by
      rw [V.lintegral_gaussianLaplace_eq_ofReal h hh.le]
      congr 1
      rw [gaussianLaplace_base_eq_inv_sqrt (V.L * h)
        (mul_nonneg V.hL.le hh.le)]
    _ ≤ ∫⁻ y, V.malaAcceptance h x y
        ∂V.gaussianDensityProposal h x :=
      V.lintegral_malaAcceptance_ge_gaussianLaplace hh hhL x

/-- Same result packaged in the `acceptanceMass` vocabulary used by the
accept--reject kernel construction. -/
theorem malaAcceptanceMass_ge_invSqrtPow
    {h : ℝ} (hh : 0 < h) (hhL : h ≤ 1 / V.L) (x : State d) :
    ENNReal.ofReal ((Real.sqrt (1 + V.L * h))⁻¹ ^ d) ≤
      MetropolisHastings.acceptanceMass
        (V.gaussianDensityProposal h) (V.malaAcceptance h) x := by
  simpa only [MetropolisHastings.acceptanceMass] using
    V.lintegral_malaAcceptance_ge_invSqrtPow hh hhL x

/-- Exponential version of the safe acceptance-mass bound. -/
theorem malaAcceptanceMass_ge_exp
    {h : ℝ} (hh : 0 < h) (hhL : h ≤ 1 / V.L) (x : State d) :
    ENNReal.ofReal (Real.exp (-(V.L * h * (d : ℝ) / 2))) ≤
      MetropolisHastings.acceptanceMass
        (V.gaussianDensityProposal h) (V.malaAcceptance h) x := by
  calc
    ENNReal.ofReal (Real.exp (-(V.L * h * (d : ℝ) / 2))) ≤
        ENNReal.ofReal ((Real.sqrt (1 + V.L * h))⁻¹ ^ d) :=
      ENNReal.ofReal_le_ofReal
        (exp_neg_half_mul_nat_le_invSqrtPow (V.L * h)
          (mul_nonneg V.hL.le hh.le) d)
    _ ≤ MetropolisHastings.acceptanceMass
        (V.gaussianDensityProposal h) (V.malaAcceptance h) x :=
      V.malaAcceptanceMass_ge_invSqrtPow hh hhL x

end FirstOrderPotential
end Concrete

end
end UniformRandomMALA
