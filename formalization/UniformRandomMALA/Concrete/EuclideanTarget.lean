import UniformRandomMALA.Scales
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Euclidean target data

The algebraic layer of the project records the dimension as a real number.
Concrete kernels instead require a natural dimension and an actual Euclidean
state space.  This file introduces the latter and proves the adapter to the
existing `Parameters` record.

`FirstOrderPotential` records consequences of the paper's Hessian bounds that
are used by most of the proof.  The current public theorem takes this record
directly; the standard analytic construction of the record from the paper's
stated `C²` Hessian assumptions is not included in this package.
-/

namespace UniformRandomMALA

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace Concrete

/-- The state space `ℝ^d`, represented using mathlib's Euclidean space. -/
abbrev State (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- First-order consequences of the strongly convex, smooth potential
assumptions. -/
structure FirstOrderPotential (d : ℕ) where
  U : State d → ℝ
  gradU : State d → State d
  m : ℝ
  L : ℝ
  hd : 0 < d
  hm : 0 < m
  hmL : m ≤ L
  continuous_U : Continuous U
  continuous_gradU : Continuous gradU
  lowerTaylor : ∀ x y,
    U x + @inner ℝ (State d) _ (gradU x) (y - x) +
      (m / 2) * ‖y - x‖ ^ 2 ≤ U y
  upperTaylor : ∀ x y,
    U y ≤ U x + @inner ℝ (State d) _ (gradU x) (y - x) +
      (L / 2) * ‖y - x‖ ^ 2
  grad_lipschitz : LipschitzWith ⟨L, le_of_lt (lt_of_lt_of_le hm hmL)⟩ gradU

namespace FirstOrderPotential

variable {d : ℕ} (V : FirstOrderPotential d)

lemma hL : 0 < V.L := lt_of_lt_of_le V.hm V.hmL

lemma dimension_real_pos (V : FirstOrderPotential d) : 0 < (d : ℝ) := by
  exact_mod_cast FirstOrderPotential.hd V

lemma dimension_real_one (V : FirstOrderPotential d) : 1 ≤ (d : ℝ) := by
  exact_mod_cast FirstOrderPotential.hd V

lemma conditionNumber_one : 1 ≤ V.L / V.m := by
  exact (le_div_iff₀ V.hm).2 (by simpa using V.hmL)

/-- The unnormalized Boltzmann weight. -/
def boltzmannWeight (x : State d) : ℝ := Real.exp (-V.U x)

lemma continuous_boltzmannWeight : Continuous V.boltzmannWeight := by
  exact Real.continuous_exp.comp V.continuous_U.neg

lemma measurable_boltzmannWeight : Measurable V.boltzmannWeight :=
  (continuous_boltzmannWeight V).measurable

lemma boltzmannWeight_pos (x : State d) : 0 < V.boltzmannWeight x :=
  Real.exp_pos _

/-- Strong convexity gives a coercive quadratic lower bound even when the
origin is not the minimizer of `U`. -/
lemma quadraticLowerBound (x : State d) :
    V.U 0 - ‖V.gradU 0‖ ^ 2 / V.m + (V.m / 4) * ‖x‖ ^ 2 ≤ V.U x := by
  have hinner :
      -(‖V.gradU 0‖ * ‖x‖) ≤ @inner ℝ (State d) _ (V.gradU 0) x :=
    neg_le_of_abs_le (abs_real_inner_le_norm (V.gradU 0) x)
  have hyoung :
      ‖V.gradU 0‖ * ‖x‖ ≤ ‖V.gradU 0‖ ^ 2 / V.m + (V.m / 4) * ‖x‖ ^ 2 := by
    have haux :
        ‖V.gradU 0‖ * ‖x‖ - (V.m / 4) * ‖x‖ ^ 2 ≤ ‖V.gradU 0‖ ^ 2 / V.m := by
      apply (le_div_iff₀ V.hm).2
      nlinarith [sq_nonneg (‖V.gradU 0‖ - (V.m / 2) * ‖x‖)]
    linarith
  have htaylor := V.lowerTaylor (0 : State d) x
  simp only [sub_zero] at htaylor
  linarith

/-- The centered Gaussian that controls the Boltzmann tail is integrable.
The proof reduces the real integral to mathlib's finite-dimensional complex
Gaussian integrability theorem. -/
lemma integrable_gaussianTail :
    Integrable (fun x : State d ↦ Real.exp (-(V.m / 4) * ‖x‖ ^ 2)) := by
  have hc := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := State d) (b := (V.m / 4 : ℂ)) (c := 0) (w := 0)
    (by exact_mod_cast div_pos V.hm (by norm_num))
  refine hc.norm.congr ?_
  filter_upwards with x
  rw [show (↑‖x‖ : ℂ) ^ 2 = ↑(‖x‖ ^ 2) by norm_cast]
  simp [Complex.norm_exp]
  left
  simp [pow_two, Complex.mul_re]

/-- An explicit integrable Gaussian majorant for `exp (-U)`. -/
def gaussianMajorant (x : State d) : ℝ :=
  Real.exp (-V.U 0 + ‖V.gradU 0‖ ^ 2 / V.m) *
    Real.exp (-(V.m / 4) * ‖x‖ ^ 2)

lemma boltzmannWeight_le_gaussianMajorant (x : State d) :
    V.boltzmannWeight x ≤ V.gaussianMajorant x := by
  rw [gaussianMajorant, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by
    have h := V.quadraticLowerBound x
    linarith)

lemma integrable_gaussianMajorant : Integrable V.gaussianMajorant := by
  apply Integrable.const_mul
  exact V.integrable_gaussianTail

/-- Strong convexity makes the unnormalized Boltzmann weight integrable over
Lebesgue measure. -/
lemma integrable_boltzmannWeight : Integrable V.boltzmannWeight := by
  refine V.integrable_gaussianMajorant.mono
    V.continuous_boltzmannWeight.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_pos (V.boltzmannWeight_pos x)]
  rw [gaussianMajorant]
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
  exact V.boltzmannWeight_le_gaussianMajorant x

/-- Extended nonnegative density used by `Measure.withDensity`. -/
def boltzmannDensity (x : State d) : ℝ≥0∞ :=
  ENNReal.ofReal (V.boltzmannWeight x)

lemma measurable_boltzmannDensity : Measurable V.boltzmannDensity :=
  ENNReal.measurable_ofReal.comp V.measurable_boltzmannWeight

/-- The unnormalized Boltzmann measure `exp (-U(x)) dx`. -/
def boltzmannMeasure : Measure (State d) :=
  volume.withDensity V.boltzmannDensity

lemma isFiniteMeasure_boltzmannMeasure : IsFiniteMeasure V.boltzmannMeasure := by
  exact isFiniteMeasure_withDensity_ofReal V.integrable_boltzmannWeight.hasFiniteIntegral

lemma boltzmannMeasure_ne_zero : V.boltzmannMeasure ≠ 0 := by
  have hsupp : Function.support V.boltzmannDensity = Set.univ := by
    ext x
    simp only [Function.mem_support, boltzmannDensity, Set.mem_univ, iff_true]
    exact (ENNReal.ofReal_pos.mpr (V.boltzmannWeight_pos x)).ne'
  have hlin : 0 < ∫⁻ x, V.boltzmannDensity x ∂(volume : Measure (State d)) := by
    rw [lintegral_pos_iff_support V.measurable_boltzmannDensity, hsupp]
    exact (Measure.measure_univ_pos (μ := (volume : Measure (State d)))).mpr
      ((Measure.measure_univ_pos (μ := (volume : Measure (State d)))).mp
        (isOpen_univ.measure_pos volume Set.univ_nonempty))
  intro hzero
  have huniv := congrArg (fun μ : Measure (State d) ↦ μ Set.univ) hzero
  simp only [boltzmannMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] at huniv
  exact hlin.ne' huniv

/-- The unnormalized target bundled with its kernel-checked finiteness proof. -/
def boltzmannFiniteMeasure : FiniteMeasure (State d) :=
  ⟨V.boltzmannMeasure, V.isFiniteMeasure_boltzmannMeasure⟩

lemma boltzmannFiniteMeasure_ne_zero : V.boltzmannFiniteMeasure ≠ 0 := by
  intro hzero
  apply V.boltzmannMeasure_ne_zero
  exact congrArg (fun μ : FiniteMeasure (State d) ↦ (μ : Measure (State d))) hzero

/-- The normalized target probability measure proportional to `exp (-U)`. -/
def target : ProbabilityMeasure (State d) :=
  V.boltzmannFiniteMeasure.normalize

lemma target_apply (s : Set (State d)) :
    V.target s = V.boltzmannFiniteMeasure.mass⁻¹ * V.boltzmannFiniteMeasure s := by
  exact FiniteMeasure.normalize_eq_of_nonzero
    V.boltzmannFiniteMeasure V.boltzmannFiniteMeasure_ne_zero s

lemma target_apply_measurable {s : Set (State d)} (hs : MeasurableSet s) :
    (V.target s : ℝ≥0∞) = (V.boltzmannFiniteMeasure.mass⁻¹ : ℝ≥0∞) *
      ∫⁻ x in s, V.boltzmannDensity x ∂volume := by
  have hmass : V.boltzmannFiniteMeasure.mass ≠ 0 :=
    V.boltzmannFiniteMeasure.mass_nonzero_iff.mpr V.boltzmannFiniteMeasure_ne_zero
  rw [V.target_apply s, ENNReal.coe_mul, ENNReal.coe_inv hmass]
  congr 1
  rw [V.boltzmannFiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  change V.boltzmannMeasure s = ∫⁻ x in s, V.boltzmannDensity x ∂volume
  exact withDensity_apply _ hs

/-- Lebesgue density of the normalized target probability measure. -/
def targetDensity (x : State d) : ℝ≥0∞ :=
  (V.boltzmannFiniteMeasure.mass⁻¹ : ℝ≥0∞) * V.boltzmannDensity x

lemma measurable_targetDensity : Measurable V.targetDensity :=
  measurable_const.mul V.measurable_boltzmannDensity

lemma targetDensity_pos (x : State d) : 0 < V.targetDensity x := by
  have hmass : V.boltzmannFiniteMeasure.mass ≠ 0 :=
    V.boltzmannFiniteMeasure.mass_nonzero_iff.mpr V.boltzmannFiniteMeasure_ne_zero
  exact ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top)
    (ENNReal.ofReal_pos.mpr (V.boltzmannWeight_pos x)).ne'

lemma targetDensity_ne_top (x : State d) : V.targetDensity x ≠ ∞ := by
  have hmass : V.boltzmannFiniteMeasure.mass ≠ 0 :=
    V.boltzmannFiniteMeasure.mass_nonzero_iff.mpr V.boltzmannFiniteMeasure_ne_zero
  exact ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.mpr (ENNReal.coe_ne_zero.mpr hmass))
    (by simp [boltzmannDensity])

/-- The normalized target is exactly the with-density measure induced by
`targetDensity`; no normalization hypothesis remains abstract. -/
lemma target_toMeasure_eq_withDensity :
    (V.target : Measure (State d)) = volume.withDensity V.targetDensity := by
  ext s hs
  rw [withDensity_apply _ hs]
  rw [← V.target.ennreal_coeFn_eq_coeFn_toMeasure s]
  rw [V.target_apply_measurable hs]
  exact (lintegral_const_mul
    (V.boltzmannFiniteMeasure.mass⁻¹ : ℝ≥0∞)
    V.measurable_boltzmannDensity).symm

/-- Convert concrete problem data and fixed universal constants to the
real-valued parameter record used by the completed algebraic assembly. -/
def toParameters
    (H A₀ b₀ c₀ : ℝ)
    (hH : 0 < H) (hA₀ : 2 ≤ A₀)
    (hb₀ : 0 < b₀) (hb₀half : b₀ ≤ 1 / 2)
    (hc₀ : 0 < c₀) : Parameters where
  d := d
  m := V.m
  L := V.L
  kappa := V.L / V.m
  H := H
  A0 := A₀
  b0 := b₀
  c0 := c₀
  pStar := A₀ * (1 + Real.log ((d : ℝ) + 1) + Real.log (V.L / V.m))
  hd := dimension_real_pos V
  hd_one := dimension_real_one V
  hm := V.hm
  hL := V.hL
  hH := hH
  hA0 := hA₀
  hb0 := hb₀
  hb0_half := hb₀half
  hb0_lt_one := lt_of_le_of_lt hb₀half (by norm_num)
  hc0 := hc₀
  hkappa := rfl
  hkappa_one := V.conditionNumber_one
  hpStar := rfl
  hpStar_pos := by
    have hA₀pos : 0 < A₀ := lt_of_lt_of_le (by norm_num) hA₀
    have hdlog : 0 ≤ Real.log ((d : ℝ) + 1) := by
      apply Real.log_nonneg
      have hd0 : 0 ≤ (d : ℝ) := le_of_lt (dimension_real_pos V)
      linarith
    have hklog : 0 ≤ Real.log (V.L / V.m) :=
      Real.log_nonneg V.conditionNumber_one
    exact mul_pos hA₀pos (by linarith)

@[simp] lemma toParameters_dimension
    (H A₀ b₀ c₀ : ℝ)
    (hH : 0 < H) (hA₀ : 2 ≤ A₀)
    (hb₀ : 0 < b₀) (hb₀half : b₀ ≤ 1 / 2)
    (hc₀ : 0 < c₀) :
    (V.toParameters H A₀ b₀ c₀ hH hA₀ hb₀ hb₀half hc₀).d = d := rfl

end FirstOrderPotential

end Concrete

end

end UniformRandomMALA
