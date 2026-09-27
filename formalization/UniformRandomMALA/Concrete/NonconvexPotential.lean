import UniformRandomMALA.Concrete.C1ToFirstOrder
import UniformRandomMALA.Concrete.NonconvexGradientMoments

/-!
# The nonconvex Boltzmann setting

This interface states the assumptions preceding Proposition B.1
(`prop:stationary-rejection`): a continuously differentiable potential,
a globally Lipschitz actual gradient, and an integrable Boltzmann weight.
Positivity of the normalizing integral is proved. No strong convexity or
position-moment condition is included. The interface and gradient-moment
theorem are prerequisites for extending the rejection proof; they do not
assert that extension is complete.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory
open scoped Gradient RealInnerProductSpace ENNReal NNReal

noncomputable section

variable {d : ℕ}

local instance nonconvexRealNormedAddCommGroupIP : NormedAddCommGroup ℝ :=
  Real.normedAddCommGroup
local instance nonconvexRealNormedSpaceIP : NormedSpace ℝ ℝ :=
  RCLike.toInnerProductSpaceReal.toNormedSpace

private abbrev NonconvexIPHasDerivAt (f : ℝ → ℝ) (f' x : ℝ) : Prop :=
  @HasDerivAt ℝ _ ℝ nonconvexRealNormedAddCommGroupIP.toAddCommGroup
    nonconvexRealNormedSpaceIP.toModule _ _ f f' x

private lemma NonconvexIPHasDerivAt.toStandard {f : ℝ → ℝ} {f' x : ℝ}
    (h : NonconvexIPHasDerivAt f f' x) : HasDerivAt f f' x := by
  rw [NonconvexIPHasDerivAt, HasDerivAt, HasDerivAtFilter] at h
  rw [HasDerivAt, HasDerivAtFilter]
  constructor
  simpa [ContinuousLinearMap.toSpanSingleton] using h.isLittleOTVS

/-- The appendix's assumptions, allowing nonconvex potentials. -/
structure NonconvexPotential (d : ℕ) where
  U : State d → ℝ
  L : ℝ
  hd : 0 < d
  hL : 0 < L
  contDiff_U : ContDiff ℝ 1 U
  gradient_lipschitz : LipschitzWith ⟨L, hL.le⟩ (∇ U)
  integrable_boltzmann : Integrable (fun x => Real.exp (-U x))

namespace NonconvexPotential

variable (V : NonconvexPotential d)

/-- The actual gradient, not a separately specified drift. -/
def gradU : State d → State d := ∇ V.U

lemma continuous_U : Continuous V.U := V.contDiff_U.continuous

lemma continuous_gradU : Continuous V.gradU := V.gradient_lipschitz.continuous

lemma line_hasDerivAt (x v : State d) (s : ℝ) :
    HasDerivAt (fun r : ℝ => V.U (x + r • v))
      (fderiv ℝ V.U (x + s • v) v) s := by
  have ha : HasDerivAt (fun r : ℝ => x + r • v) v s := by
    simpa using ((hasDerivAt_id s).smul_const v).const_add x
  simpa [Function.comp_def] using
    (V.contDiff_U.differentiable (by norm_num) (x + s • v) |>.hasFDerivAt
      |>.comp s ha.hasFDerivAt |>.hasDerivAt)

lemma upperResidual_hasDerivAt (x v : State d) (s : ℝ) :
    HasDerivAt
      (fun r : ℝ => V.U x + r * fderiv ℝ V.U x v +
        (V.L / 2) * r ^ 2 * ‖v‖ ^ 2 - V.U (x + r • v))
      (fderiv ℝ V.U x v + V.L * s * ‖v‖ ^ 2 -
        fderiv ℝ V.U (x + s • v) v) s := by
  have hlin : HasDerivAt (fun r : ℝ => r * fderiv ℝ V.U x v)
      (fderiv ℝ V.U x v) s := by
    simpa using (hasDerivAt_id s).mul_const (fderiv ℝ V.U x v)
  have hquad : HasDerivAt (fun r : ℝ => (V.L / 2) * r ^ 2 * ‖v‖ ^ 2)
      (V.L * s * ‖v‖ ^ 2) s := by
    have hraw : HasDerivAt (fun r : ℝ => (V.L / 2) * r ^ 2 * ‖v‖ ^ 2)
        ((V.L / 2) * (2 * s) * ‖v‖ ^ 2) s := by
      simpa [id_eq] using
        (((hasDerivAt_id s).pow 2).const_mul (V.L / 2)).mul_const (‖v‖ ^ 2)
    exact hraw.congr_deriv (by ring)
  have h := ((hlin.const_add (V.U x)).add hquad).sub (V.line_hasDerivAt x v s)
  apply NonconvexIPHasDerivAt.toStandard
  convert h using 1
  funext r
  simp only [Pi.sub_apply, Pi.add_apply]

lemma upperResidual_deriv_nonneg (x v : State d) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ fderiv ℝ V.U x v + V.L * s * ‖v‖ ^ 2 -
      fderiv ℝ V.U (x + s • v) v := by
  have hnorm := V.gradient_lipschitz.norm_sub_le (x + s • v) x
  change ‖∇ V.U (x + s • v) - ∇ V.U x‖ ≤
    V.L * ‖(x + s • v) - x‖ at hnorm
  have hnorm' : ‖∇ V.U (x + s • v) - ∇ V.U x‖ ≤ V.L * s * ‖v‖ := by
    simpa [norm_smul, Real.norm_of_nonneg hs, mul_assoc] using hnorm
  have hinner :
      @inner ℝ (State d) _ (∇ V.U (x + s • v)) v -
          @inner ℝ (State d) _ (∇ V.U x) v ≤
        ‖∇ V.U (x + s • v) - ∇ V.U x‖ * ‖v‖ := by
    rw [← inner_sub_left]
    exact (le_abs_self _).trans (abs_real_inner_le_norm _ _)
  have hmul := mul_le_mul_of_nonneg_right hnorm' (norm_nonneg v)
  rw [inner_gradient_left, inner_gradient_left] at hinner
  nlinarith

/-- The descent lemma from a Lipschitz actual gradient, without using `C²`. -/
lemma upperTaylor (x y : State d) :
    V.U y ≤ V.U x + @inner ℝ (State d) _ (∇ V.U x) (y - x) +
      (V.L / 2) * ‖y - x‖ ^ 2 := by
  let v : State d := y - x
  let g : ℝ → ℝ := fun r => V.U x + r * fderiv ℝ V.U x v +
    (V.L / 2) * r ^ 2 * ‖v‖ ^ 2 - V.U (x + r • v)
  let g' : ℝ → ℝ := fun r => fderiv ℝ V.U x v + V.L * r * ‖v‖ ^ 2 -
    fderiv ℝ V.U (x + r • v) v
  have hg : ∀ s, HasDerivAt g (g' s) s :=
    fun s => V.upperResidual_hasDerivAt x v s
  have hcont : ContinuousOn g (Set.Icc (0 : ℝ) 1) :=
    (continuous_iff_continuousAt.mpr (fun s => (hg s).continuousAt)).continuousOn
  have hmono : MonotoneOn g (Set.Icc (0 : ℝ) 1) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hcont
      (fun s _ => (hg s).differentiableAt.differentiableWithinAt)
      (fun s hs => by
        rw [(hg s).deriv]
        have hs' : s ∈ Set.Ioo (0 : ℝ) 1 := by
          simpa only [interior_Icc] using hs
        exact V.upperResidual_deriv_nonneg x v hs'.1.le)
  have hendpoint := hmono
    (Set.left_mem_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1))
    (Set.right_mem_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1))
    (by norm_num : (0 : ℝ) ≤ 1)
  dsimp [g, v] at hendpoint
  rw [inner_gradient_left, map_sub]
  norm_num at hendpoint
  linarith

/-- The unnormalized Boltzmann weight. -/
def boltzmannWeight (x : State d) : ℝ := Real.exp (-V.U x)

lemma continuous_boltzmannWeight : Continuous V.boltzmannWeight := by
  exact Real.continuous_exp.comp V.continuous_U.neg

lemma measurable_boltzmannWeight : Measurable V.boltzmannWeight :=
  (continuous_boltzmannWeight V).measurable

lemma boltzmannWeight_pos (x : State d) : 0 < V.boltzmannWeight x :=
  Real.exp_pos _

lemma integrable_boltzmannWeight : Integrable V.boltzmannWeight := V.integrable_boltzmann

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

/-- Gradient exponential moments under the actual normalized target,
proved without a convexity assumption or a position-moment hypothesis. -/
theorem integrable_exp_gradU_norm_sq (a : ℝ) (ha : 0 < a) :
    Integrable (fun x => Real.exp (‖V.gradU x‖ ^ 2 / (4 * (a + V.L / 2))))
      (V.target : Measure (State d)) := by
  rw [V.target_toMeasure_eq_withDensity,
    integrable_withDensity_iff V.measurable_targetDensity
      (ae_of_all _ fun x => (V.targetDensity_ne_top x).lt_top)]
  have h := boltzmann_gradient_exponential_integrable V.U V.gradU
    V.continuous_U.measurable V.continuous_gradU.measurable V.L a V.hL ha
    V.integrable_boltzmann V.upperTaylor
  apply (h.const_mul (V.boltzmannFiniteMeasure.mass : ℝ)⁻¹).congr
  filter_upwards with x
  simp only [targetDensity, boltzmannDensity, boltzmannWeight,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.exp_add]
  ring

/-- Integration against the target is normalized Boltzmann integration. -/
theorem integral_target_eq_normalized_boltzmann (f : State d → ℝ) :
    (∫ x, f x ∂(V.target : Measure (State d))) =
      (V.boltzmannFiniteMeasure.mass : ℝ)⁻¹ *
        ∫ x, V.boltzmannWeight x * f x ∂volume := by
  rw [V.target_toMeasure_eq_withDensity,
    integral_withDensity_eq_integral_toReal_smul V.measurable_targetDensity
      (ae_of_all _ fun x => (V.targetDensity_ne_top x).lt_top)]
  simp_rw [targetDensity, ENNReal.toReal_mul, boltzmannDensity,
    ENNReal.toReal_ofReal (V.boltzmannWeight_pos _).le,
    ENNReal.toReal_inv, ENNReal.coe_toReal, smul_eq_mul]
  rw [← integral_const_mul]
  congr 2
  ext x
  ring

/-- The normalized Gaussian-convolution bound on gradient exponential
moments, valid for every potential in the nonconvex appendix class. -/
theorem integral_exp_gradU_norm_sq_le (a : ℝ) (ha : 0 < a) :
    (∫ x, Real.exp (‖V.gradU x‖ ^ 2 / (4 * (a + V.L / 2)))
      ∂(V.target : Measure (State d))) ≤
        (Real.pi / a) ^ ((d : ℝ) / 2) /
          (Real.pi / (a + V.L / 2)) ^ ((d : ℝ) / 2) := by
  let b := a + V.L / 2
  let Ca := (Real.pi / a) ^ ((d : ℝ) / 2)
  let Cb := (Real.pi / b) ^ ((d : ℝ) / 2)
  have hCa : 0 < Ca := Real.rpow_pos_of_pos (div_pos Real.pi_pos ha) _
  have hb : 0 < b := add_pos ha (half_pos V.hL)
  have hCb : 0 < Cb := Real.rpow_pos_of_pos (div_pos Real.pi_pos hb) _
  have hTilt := boltzmann_gradient_exponential_integrable V.U V.gradU
    V.continuous_U.measurable V.continuous_gradU.measurable V.L a V.hL ha
    V.integrable_boltzmann V.upperTaylor
  have hraw := boltzmann_gradient_exponential_lintegral_bound V.U V.gradU
    V.continuous_U.measurable V.continuous_gradU.measurable V.L a V.hL ha V.upperTaylor
  rw [← ofReal_integral_eq_lintegral_ofReal hTilt (ae_of_all _ fun _ => (Real.exp_pos _).le),
    ← ofReal_integral_eq_lintegral_ofReal V.integrable_boltzmann
      (ae_of_all _ fun _ => (Real.exp_pos _).le)] at hraw
  change ENNReal.ofReal Cb * ENNReal.ofReal
      (∫ x, Real.exp (-V.U x + ‖V.gradU x‖ ^ 2 / (4 * b))) ≤
    ENNReal.ofReal Ca * ENNReal.ofReal (∫ x, Real.exp (-V.U x)) at hraw
  have hreal : Cb * (∫ x, Real.exp (-V.U x + ‖V.gradU x‖ ^ 2 / (4 * b))) ≤
      Ca * (∫ x, Real.exp (-V.U x)) := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top) hraw
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCa.le,
      ENNReal.toReal_ofReal hCb.le,
      ENNReal.toReal_ofReal (integral_nonneg fun _ => (Real.exp_pos _).le)] using h
  let c := (V.boltzmannFiniteMeasure.mass : ℝ)⁻¹
  have hc : 0 ≤ c := inv_nonneg.mpr (NNReal.coe_nonneg _)
  have hnorm : c * (∫ x, Real.exp (-V.U x)) = 1 := by
    have := V.integral_target_eq_normalized_boltzmann (fun _ => 1)
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul, mul_one,
      boltzmannWeight] using this.symm
  change (∫ x, Real.exp (‖V.gradU x‖ ^ 2 / (4 * b))
    ∂(V.target : Measure (State d))) ≤ Ca / Cb
  apply (le_div_iff₀ hCb).mpr
  rw [V.integral_target_eq_normalized_boltzmann]
  simp_rw [boltzmannWeight, ← Real.exp_add]
  calc
    _ = c * (Cb * (∫ x, Real.exp (-V.U x + ‖V.gradU x‖ ^ 2 / (4 * b)))) := by ring
    _ ≤ c * (Ca * (∫ x, Real.exp (-V.U x))) := mul_le_mul_of_nonneg_left hreal hc
    _ = Ca := by rw [← mul_assoc, mul_comm c Ca, mul_assoc, hnorm, mul_one]

end NonconvexPotential

/-- Standing strongly convex targets are a special case of the appendix
interface; integrability is derived rather than added as an assumption. -/
def C1Potential.toNonconvexPotential (V : C1Potential d) : NonconvexPotential d where
  U := V.U
  L := V.L
  hd := V.hd
  hL := V.hL
  contDiff_U := V.contDiff_U
  gradient_lipschitz := V.gradient_lipschitz
  integrable_boltzmann := V.toFirstOrderPotential.integrable_boltzmannWeight

@[simp] theorem C1Potential.toNonconvexPotential_target (V : C1Potential d) :
    V.toNonconvexPotential.target = V.toFirstOrderPotential.target := rfl

end
end UniformRandomMALA.Concrete
