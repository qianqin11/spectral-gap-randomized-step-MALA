import UniformRandomMALA.Concrete.GaussianRampSmoothApproximation
import UniformRandomMALA.Concrete.GaussianOUCanonicalFields
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# Concrete smooth mollification of Gaussian distance ramps

This file constructs the localized approximation certificate required by
`GaussianRampSmoothApproximationProperty` using Mathlib's normalized smooth
bump convolution.  The ramp is first enlarged by the bump radius.  This makes
the convolution exactly one on the original closed set while retaining an
exact `1/h` Lipschitz bound and a shrinking outer support.
-/

namespace UniformRandomMALA

open Function Set Metric MeasureTheory Filter ContinuousLinearMap ProbabilityTheory
open scoped Convolution Topology NNReal ENNReal ProbabilityTheory

noncomputable section

namespace Concrete

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [SecondCountableTopology E]

local notation "volE" => (Measure.addHaar : Measure E)

/-- Convolution with a normalized nonnegative bump preserves a real-valued
Lipschitz constant exactly. -/
theorem lipschitzWith_normedBumpConvolution
    (φ : ContDiffBump (0 : E))
    (f : BoundedContinuousFunction E ℝ) {L : ℝ≥0}
    (hf : LipschitzWith L f) :
    LipschitzWith L
      (φ.normed volE ⋆[lsmul ℝ ℝ, volE] (⇑f) : E → ℝ) := by
  have hconv : ConvolutionExists (φ.normed volE) (⇑f)
      (lsmul ℝ ℝ) volE :=
    φ.hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ)
      φ.continuous_normed f.continuous.locallyIntegrable
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hxint : Integrable
      (fun z => φ.normed volE z * f (x - z)) volE := by
    simpa only [lsmul_apply, smul_eq_mul] using (hconv x).integrable
  have hyint : Integrable
      (fun z => φ.normed volE z * f (y - z)) volE := by
    simpa only [lsmul_apply, smul_eq_mul] using (hconv y).integrable
  rw [Real.dist_eq]
  change |(∫ z, φ.normed volE z * f (x - z) ∂volE) -
      (∫ z, φ.normed volE z * f (y - z) ∂volE)| ≤ _
  rw [← integral_sub hxint hyint]
  calc
    |∫ z, φ.normed volE z * f (x - z) -
        φ.normed volE z * f (y - z) ∂volE| =
        ‖∫ z, φ.normed volE z *
          (f (x - z) - f (y - z)) ∂volE‖ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with z
      ring
    _ ≤ ∫ z, ‖φ.normed volE z *
        (f (x - z) - f (y - z))‖ ∂volE :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z, φ.normed volE z * ((L : ℝ) * dist x y) ∂volE := by
      apply integral_mono_of_nonneg
      · exact ae_of_all _ fun z => norm_nonneg _
      · simpa [mul_comm] using
          (φ.integrable_normed.const_mul ((L : ℝ) * dist x y))
      · exact ae_of_all _ fun z => by
          change |φ.normed volE z * (f (x - z) - f (y - z))| ≤ _
          rw [abs_mul, abs_of_nonneg (φ.nonneg_normed z)]
          apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed z)
          have h := hf.dist_le_mul (x - z) (y - z)
          rw [Real.dist_eq] at h
          simpa [dist_eq_norm] using h
    _ = (L : ℝ) * dist x y := by
      rw [integral_mul_const, φ.integral_normed, one_mul]

/-- Convolution of a compact continuous vector-valued kernel against a
bounded scalar Lipschitz function is Lipschitz.  The operator `A` is the
continuous bilinear scalar action, written in curried form. -/
theorem lipschitzWith_convolution_left_smul
    {G F : Type*} [NormedAddCommGroup G] [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : G → F) (g : BoundedContinuousFunction G ℝ)
    (A : F →L[ℝ] ℝ →L[ℝ] F)
    (hA : ∀ v r, A v r = r • v)
    (hkcomp : HasCompactSupport k) (hkcont : Continuous k)
    {L : ℝ≥0} (hg : LipschitzWith L g)
    (μ : Measure G) [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    [IsFiniteMeasureOnCompacts μ] [IsLocallyFiniteMeasure μ] :
    LipschitzWith (L * Real.toNNReal (∫ z, ‖k z‖ ∂μ))
      (k ⋆[A, μ] (⇑g)) := by
  have hkint : Integrable (fun z => ‖k z‖) μ :=
    hkcont.norm.integrable_of_hasCompactSupport hkcomp.norm
  have hconv : ConvolutionExists k (⇑g) A μ :=
    hkcomp.convolutionExists_left A hkcont g.continuous.locallyIntegrable
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hxint := (hconv x).integrable
  have hyint := (hconv y).integrable
  change dist (∫ z, A (k z) (g (x - z)) ∂μ)
      (∫ z, A (k z) (g (y - z)) ∂μ) ≤ _
  rw [dist_eq_norm, ← integral_sub hxint hyint]
  calc
    ‖∫ z, A (k z) (g (x - z)) - A (k z) (g (y - z)) ∂μ‖ ≤
        ∫ z, ‖A (k z) (g (x - z)) - A (k z) (g (y - z))‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z, ‖k z‖ * ((L : ℝ) * dist x y) ∂μ := by
      apply integral_mono
      · exact (hxint.sub hyint).norm
      · exact (hkint.const_mul ((L : ℝ) * dist x y)).congr
          (ae_of_all _ fun z => by simp [mul_comm])
      · intro z
        change ‖A (k z) (g (x - z)) - A (k z) (g (y - z))‖ ≤ _
        rw [hA, hA]
        have heq : g (x - z) • k z - g (y - z) • k z =
            (g (x - z) - g (y - z)) • k z := by
          rw [sub_smul]
        rw [heq, norm_smul, Real.norm_eq_abs]
        have habs : |g (x - z) - g (y - z)| ≤ (L : ℝ) * dist x y := by
          have h := hg.dist_le_mul (x - z) (y - z)
          rw [Real.dist_eq] at h
          simpa [dist_eq_norm] using h
        calc
          |g (x - z) - g (y - z)| * ‖k z‖ ≤
              ((L : ℝ) * dist x y) * ‖k z‖ :=
            mul_le_mul_of_nonneg_right habs (norm_nonneg _)
          _ = ‖k z‖ * ((L : ℝ) * dist x y) := by ring
    _ = ((L * Real.toNNReal (∫ z, ‖k z‖ ∂μ) : ℝ≥0) : ℝ) * dist x y := by
      rw [integral_mul_const]
      rw [NNReal.coe_mul, Real.coe_toNNReal _
        (integral_nonneg fun _ => norm_nonneg _)]
      ring

/-- Enlarging the underlying set by a radius tending to zero does not change
the pointwise limit of a fixed-width Gaussian ramp. -/
theorem tendsto_gaussianRamp_cthickening
    {h : ℝ} (hh : 0 < h) {rho : ℕ → ℝ}
    (hrho : Tendsto rho atTop (nhds 0)) {A : Set E} (hA : A.Nonempty)
    (x : E) :
    Tendsto (fun n => gaussianRamp hh (cthickening (rho n) A) x)
      atTop (nhds (gaussianRamp hh A x)) := by
  have hinf : Tendsto
      (fun n => infEDist x (cthickening (rho n) A)) atTop
      (nhds (infEDist x A)) := by
    simp_rw [infEDist_cthickening]
    have hof := ENNReal.tendsto_ofReal hrho
    have hsub := (ENNReal.continuous_sub_left
      (infEDist_ne_top (x := x) hA)).tendsto (ENNReal.ofReal 0) |>.comp hof
    change Tendsto (fun n => infEDist x A - ENNReal.ofReal (rho n))
      atTop (nhds (infEDist x A - ENNReal.ofReal 0)) at hsub
    simpa only [ENNReal.ofReal_zero, tsub_zero] using hsub
  have hdiv : Tendsto
      (fun n => infEDist x (cthickening (rho n) A) /
        ENNReal.ofReal h) atTop
      (nhds (infEDist x A / ENNReal.ofReal h)) :=
    ((ENNReal.continuous_div_const _
      (ENNReal.ofReal_pos.mpr hh).ne').tendsto _).comp hinf
  have haux : Tendsto
      (fun n => thickenedIndicatorAux h (cthickening (rho n) A) x)
      atTop (nhds (thickenedIndicatorAux h A x)) :=
    (ENNReal.continuous_nnreal_sub.tendsto _).comp hdiv
  have hnn := (ENNReal.tendsto_toNNReal
    thickenedIndicatorAux_lt_top.ne).comp haux
  have hreal := NNReal.continuous_coe.continuousAt.tendsto.comp hnn
  change Tendsto (fun n => NNReal.toReal
      (thickenedIndicatorAux h (cthickening (rho n) A) x).toNNReal)
    atTop (nhds
      (NNReal.toReal (thickenedIndicatorAux h A x).toNNReal))
  convert hreal using 1 <;> rfl

/-- The explicit radius sequence used for ramp mollification. -/
def gaussianRampMollifierRadius (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem gaussianRampMollifierRadius_pos (n : ℕ) :
    0 < gaussianRampMollifierRadius n := by
  unfold gaussianRampMollifierRadius
  positivity

theorem gaussianRampMollifierRadius_tendsto_zero :
    Tendsto gaussianRampMollifierRadius atTop (nhds 0) := by
  change Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0)
  exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

/-- A normalized smooth bump whose outer support radius is `ρₙ`. -/
def gaussianRampMollifier (n : ℕ) : ContDiffBump (0 : E) :=
  ⟨gaussianRampMollifierRadius n / 2, gaussianRampMollifierRadius n,
    half_pos (gaussianRampMollifierRadius_pos n),
    half_lt_self (gaussianRampMollifierRadius_pos n)⟩

/-- The ramp is enlarged by one bump radius before convolution. -/
def gaussianRampExpanded {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) :
    BoundedContinuousFunction E ℝ :=
  gaussianRamp hh (cthickening (gaussianRampMollifierRadius n) A)

/-- The concrete smooth approximation before bundling. -/
def gaussianRampMollified {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) : E → ℝ :=
  (gaussianRampMollifier (E := E) n).normed volE ⋆[lsmul ℝ ℝ, volE]
    (⇑(gaussianRampExpanded hh A n))

theorem lipschitzWith_gaussianRampMollified
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) :
    LipschitzWith h.toNNReal⁻¹ (gaussianRampMollified hh A n) := by
  exact lipschitzWith_normedBumpConvolution
    (gaussianRampMollifier (E := E) n)
    (gaussianRampExpanded hh A n)
    (lipschitzWith_gaussianRamp hh _)

theorem contDiff_gaussianRampMollified
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (gaussianRampMollified hh A n) := by
  unfold gaussianRampMollified
  exact (gaussianRampMollifier (E := E) n).hasCompactSupport_normed
    |>.contDiff_convolution_left (lsmul ℝ ℝ)
      (gaussianRampMollifier (E := E) n).contDiff_normed
      (gaussianRampExpanded hh A n).continuous.locallyIntegrable

theorem gaussianRampMollified_mem_Icc
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) (x : E) :
    gaussianRampMollified hh A n x ∈ Icc (0 : ℝ) 1 := by
  let φ := gaussianRampMollifier (E := E) n
  let f := gaussianRampExpanded hh A n
  have hconv : ConvolutionExists (φ.normed volE) (⇑f)
      (lsmul ℝ ℝ) volE :=
    φ.hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ)
      φ.continuous_normed f.continuous.locallyIntegrable
  have hxint : Integrable (fun z => φ.normed volE z * f (x - z)) volE := by
    simpa only [lsmul_apply, smul_eq_mul] using (hconv x).integrable
  have honeint : Integrable (fun z => φ.normed volE z * (1 : ℝ)) volE := by
    simpa only [mul_one] using φ.integrable_normed
  change (∫ z, φ.normed volE z * f (x - z) ∂volE) ∈ Icc (0 : ℝ) 1
  constructor
  · apply integral_nonneg
    intro z
    exact mul_nonneg (φ.nonneg_normed z) (gaussianRamp_mem_Icc hh _ _).1
  · calc
      ∫ z, φ.normed volE z * f (x - z) ∂volE ≤
          ∫ z, φ.normed volE z * (1 : ℝ) ∂volE := by
        apply integral_mono hxint honeint
        intro z
        exact mul_le_mul_of_nonneg_left
          (gaussianRamp_mem_Icc hh _ _).2 (φ.nonneg_normed z)
      _ = 1 := by simp only [mul_one, φ.integral_normed]

/-- The smooth mollified ramp bundled as a bounded continuous function. -/
def gaussianRampMollifiedBCF {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) :
    BoundedContinuousFunction E ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨gaussianRampMollified hh A n,
      (contDiff_gaussianRampMollified hh A n).continuous⟩
    1 (by
      intro x y
      have hx := gaussianRampMollified_mem_Icc hh A n x
      have hy := gaussianRampMollified_mem_Icc hh A n y
      change dist (gaussianRampMollified hh A n x)
        (gaussianRampMollified hh A n y) ≤ 1
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2])

@[simp] theorem gaussianRampMollifiedBCF_apply
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) (x : E) :
    gaussianRampMollifiedBCF hh A n x = gaussianRampMollified hh A n x := rfl

theorem dist_gaussianRampMollified_expanded_le
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) (x : E) :
    dist (gaussianRampMollified hh A n x) (gaussianRampExpanded hh A n x) ≤
      (h.toNNReal⁻¹ : ℝ) * gaussianRampMollifierRadius n := by
  let φ := gaussianRampMollifier (E := E) n
  let f := gaussianRampExpanded hh A n
  have h := φ.dist_normed_convolution_le (μ := volE)
    f.continuous.aestronglyMeasurable
    (ε := (h.toNNReal⁻¹ : ℝ) * gaussianRampMollifierRadius n)
    (fun y hy => by
      have hlip := (lipschitzWith_gaussianRamp hh
        (cthickening (gaussianRampMollifierRadius n) A)).dist_le_mul y x
      exact hlip.trans (mul_le_mul_of_nonneg_left
        (mem_ball.mp hy).le (NNReal.coe_nonneg _)))
  exact h

theorem tendsto_gaussianRampExpanded
    {h : ℝ} (hh : 0 < h) (A : Set E) (x : E) :
    Tendsto (fun n => gaussianRampExpanded hh A n x) atTop
      (nhds (gaussianRamp hh A x)) := by
  by_cases hA : A.Nonempty
  · exact tendsto_gaussianRamp_cthickening hh
      gaussianRampMollifierRadius_tendsto_zero hA x
  · have hAempty : A = ∅ := not_nonempty_iff_eq_empty.mp hA
    subst A
    have hzero (n : ℕ) : gaussianRampExpanded hh (∅ : Set E) n x = 0 := by
      apply gaussianRamp_zero
      simp
    have htarget : gaussianRamp hh (∅ : Set E) x = 0 := by
      apply gaussianRamp_zero
      simp
    simpa only [hzero, htarget] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))

theorem tendsto_gaussianRampMollified
    {h : ℝ} (hh : 0 < h) (A : Set E) (x : E) :
    Tendsto (fun n => gaussianRampMollified hh A n x) atTop
      (nhds (gaussianRamp hh A x)) := by
  have hbase := tendsto_gaussianRampExpanded hh A x
  have hbound : Tendsto (fun n =>
      (h.toNNReal⁻¹ : ℝ) * gaussianRampMollifierRadius n) atTop (nhds 0) := by
    convert tendsto_const_nhds.mul gaussianRampMollifierRadius_tendsto_zero using 1
    ring
  have hdist : Tendsto (fun n => dist
      (gaussianRampExpanded hh A n x)
      (gaussianRampMollified hh A n x)) atTop (nhds 0) := by
    apply squeeze_zero'
      (g := fun n => (h.toNNReal⁻¹ : ℝ) * gaussianRampMollifierRadius n)
    · exact Filter.Eventually.of_forall fun _ => dist_nonneg
    · exact Filter.Eventually.of_forall fun n => by
        rw [dist_comm]
        exact dist_gaussianRampMollified_expanded_le hh A n x
    · exact hbound
  exact hbase.congr_dist hdist

theorem tendsto_integral_gaussianRampMollified
    {h : ℝ} (hh : 0 < h) (A : Set E) :
    Tendsto (fun n => ∫ x, gaussianRampMollifiedBCF hh A n x ∂stdGaussian E)
      atTop (nhds (∫ x, gaussianRamp hh A x ∂stdGaussian E)) := by
  apply tendsto_integral_filter_of_norm_le_const
  · exact Filter.Eventually.of_forall fun n =>
      (gaussianRampMollifiedBCF hh A n).continuous.aestronglyMeasurable
  · refine ⟨1, Filter.Eventually.of_forall fun n =>
      Filter.Eventually.of_forall fun x => ?_⟩
    rw [gaussianRampMollifiedBCF_apply, Real.norm_eq_abs,
      abs_of_nonneg (gaussianRampMollified_mem_Icc hh A n x).1]
    exact (gaussianRampMollified_mem_Icc hh A n x).2
  · exact Filter.Eventually.of_forall fun x =>
      tendsto_gaussianRampMollified hh A x

theorem norm_fderiv_gaussianRampMollified_le
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) (x : E) :
    ‖fderiv ℝ (gaussianRampMollified hh A n) x‖ ≤ h⁻¹ := by
  have hbound := norm_fderiv_le_of_lipschitz ℝ
    (lipschitzWith_gaussianRampMollified hh A n) (x₀ := x)
  simpa [NNReal.coe_inv, Real.toNNReal_of_nonneg hh.le] using hbound

/-- The bounded continuous derivative of the concrete smooth ramp. -/
def gaussianRampMollifiedDerivBCF
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) :
    BoundedContinuousFunction E (E →L[ℝ] ℝ) :=
  BoundedContinuousFunction.mkOfBound
    ⟨fderiv ℝ (gaussianRampMollified hh A n),
      (contDiff_gaussianRampMollified hh A n).continuous_fderiv (by simp)⟩
    (2 * h⁻¹) (by
      intro x y
      rw [dist_eq_norm]
      calc
        ‖fderiv ℝ (gaussianRampMollified hh A n) x -
            fderiv ℝ (gaussianRampMollified hh A n) y‖ ≤
            ‖fderiv ℝ (gaussianRampMollified hh A n) x‖ +
              ‖fderiv ℝ (gaussianRampMollified hh A n) y‖ := norm_sub_le _ _
        _ ≤ h⁻¹ + h⁻¹ := add_le_add
          (norm_fderiv_gaussianRampMollified_le hh A n x)
          (norm_fderiv_gaussianRampMollified_le hh A n y)
        _ = 2 * h⁻¹ := by ring)

@[simp] theorem gaussianRampMollifiedDerivBCF_apply
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) (x : E) :
    gaussianRampMollifiedDerivBCF hh A n x =
      fderiv ℝ (gaussianRampMollified hh A n) x := rfl

/-! ### A bounded Hessian for the mollified ramp

The canonical OU calculation needs a bounded continuous second derivative.
The nested operator space for a Hessian is a perfectly good normed space,
but a third nested continuous-linear-map action is not available in the
current Mathlib hierarchy.  We therefore avoid differentiating the
convolution a second time under the integral.  Instead, the explicit first
derivative convolution is globally Lipschitz (the ramp is `1/h`-Lipschitz),
and the mean-value bound controls its Fréchet derivative. -/

set_option maxHeartbeats 1200000

/-- Scalar multiplication lifted once, used for the explicit first
derivative convolution. -/
def firstDerivativeScalarAction :
    (E →L[ℝ] ℝ) →L[ℝ] ℝ →L[ℝ] (E →L[ℝ] ℝ) :=
  (lsmul ℝ ℝ).precompL E

@[simp] theorem firstDerivativeScalarAction_apply
    (D : E →L[ℝ] ℝ) (r : ℝ) :
    firstDerivativeScalarAction D r = r • D := by
  ext v
  simp [firstDerivativeScalarAction]
  ring

def gaussianRampMollifiedD1Explicit
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) :
    E → E →L[ℝ] ℝ :=
  fderiv ℝ ((gaussianRampMollifier (E := E) n).normed volE) ⋆[
      firstDerivativeScalarAction, volE] (⇑(gaussianRampExpanded hh A n))

theorem hasFDerivAt_gaussianRampMollified_explicitD1
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) (x : E) :
    HasFDerivAt (gaussianRampMollified hh A n)
      (gaussianRampMollifiedD1Explicit hh A n x) x := by
  have hk : ContDiff ℝ 1
      ((gaussianRampMollifier (E := E) n).normed volE) :=
    (gaussianRampMollifier (E := E) n).contDiff_normed (n := 1)
  exact (gaussianRampMollifier (E := E) n).hasCompactSupport_normed
    |>.hasFDerivAt_convolution_left (lsmul ℝ ℝ) hk
      (gaussianRampExpanded hh A n).continuous.locallyIntegrable x

theorem fderiv_gaussianRampMollified_eq_explicitD1
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) :
    fderiv ℝ (gaussianRampMollified hh A n) =
      gaussianRampMollifiedD1Explicit hh A n := by
  funext x
  exact (hasFDerivAt_gaussianRampMollified_explicitD1 hh A n x).fderiv

def gaussianRampMollifiedD1LipschitzConstant
    {h : ℝ} (hh : 0 < h) (n : ℕ) : ℝ≥0 :=
  ⟨h⁻¹ * ∫ z, ‖fderiv ℝ
      ((gaussianRampMollifier (E := E) n).normed volE) z‖ ∂volE,
    mul_nonneg (inv_nonneg.mpr hh.le) (integral_nonneg fun _ => norm_nonneg _)⟩

theorem lipschitzWith_gaussianRampMollifiedD1Explicit
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) :
    LipschitzWith (gaussianRampMollifiedD1LipschitzConstant
      (E := E) hh n) (gaussianRampMollifiedD1Explicit hh A n) := by
  let k := fderiv ℝ ((gaussianRampMollifier (E := E) n).normed volE)
  let g : BoundedContinuousFunction E ℝ := gaussianRampExpanded hh A n
  have hkcont : Continuous k :=
    (gaussianRampMollifier (E := E) n).contDiff_normed (n := 1)
      |>.continuous_fderiv (by norm_num)
  have hkcomp : HasCompactSupport k :=
    (gaussianRampMollifier (E := E) n).hasCompactSupport_normed.fderiv ℝ
  have hkint : Integrable (fun z => ‖k z‖) volE :=
    hkcont.norm.integrable_of_hasCompactSupport hkcomp.norm
  have hconv : ConvolutionExists k (⇑g)
      firstDerivativeScalarAction volE :=
    hkcomp.convolutionExists_left firstDerivativeScalarAction hkcont
      g.continuous.locallyIntegrable
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hxint := (hconv x).integrable
  have hyint := (hconv y).integrable
  change dist (∫ z, firstDerivativeScalarAction (k z) (g (x - z)) ∂volE)
      (∫ z, firstDerivativeScalarAction (k z) (g (y - z)) ∂volE) ≤ _
  rw [dist_eq_norm, ← integral_sub hxint hyint]
  calc
    ‖∫ z, firstDerivativeScalarAction (k z) (g (x - z)) -
        firstDerivativeScalarAction (k z) (g (y - z)) ∂volE‖ ≤
        ∫ z, ‖firstDerivativeScalarAction (k z) (g (x - z)) -
          firstDerivativeScalarAction (k z) (g (y - z))‖ ∂volE :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z, ‖k z‖ * (h⁻¹ * dist x y) ∂volE := by
      apply integral_mono
      · exact (hxint.sub hyint).norm
      · exact (hkint.const_mul (h⁻¹ * dist x y)).congr
          (ae_of_all _ fun z => by simp [mul_comm])
      · intro z
        change ‖firstDerivativeScalarAction (k z) (g (x - z)) -
          firstDerivativeScalarAction (k z) (g (y - z))‖ ≤ _
        simp only [firstDerivativeScalarAction_apply]
        have heq : g (x - z) • k z - g (y - z) • k z =
            (g (x - z) - g (y - z)) • k z := by
          ext v
          simp
          ring
        rw [heq]
        rw [norm_smul, Real.norm_eq_abs]
        have hgdist := (lipschitzWith_gaussianRamp hh
          (cthickening (gaussianRampMollifierRadius n) A)).dist_le_mul
            (x - z) (y - z)
        rw [Real.dist_eq] at hgdist
        have habs : |g (x - z) - g (y - z)| ≤ h⁻¹ * dist x y := by
          simpa [g, gaussianRampExpanded, dist_eq_norm, NNReal.coe_inv,
            Real.toNNReal_of_nonneg hh.le] using hgdist
        calc
          |g (x - z) - g (y - z)| * ‖k z‖ ≤
              (h⁻¹ * dist x y) * ‖k z‖ :=
            mul_le_mul_of_nonneg_right habs (norm_nonneg _)
          _ = ‖k z‖ * (h⁻¹ * dist x y) := by ring
    _ = (gaussianRampMollifiedD1LipschitzConstant
          (E := E) hh n : ℝ) * dist x y := by
      rw [integral_mul_const]
      simp only [gaussianRampMollifiedD1LipschitzConstant]
      change (∫ z, ‖k z‖ ∂volE) * (h⁻¹ * dist x y) =
        (h⁻¹ * ∫ z, ‖fderiv ℝ
          ((gaussianRampMollifier (E := E) n).normed volE) z‖ ∂volE)
          * dist x y
      change (∫ z, ‖fderiv ℝ
          ((gaussianRampMollifier (E := E) n).normed volE) z‖ ∂volE) *
        (h⁻¹ * dist x y) = _
      ring

/-- The Hessian is kept as the genuine iterated Fréchet derivative. -/
def gaussianRampMollifiedD2
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) (x : E) :
    E →L[ℝ] (E →L[ℝ] ℝ) :=
  fderiv ℝ (fderiv ℝ (gaussianRampMollified hh A n)) x

theorem continuous_gaussianRampMollifiedD2
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) :
    Continuous (gaussianRampMollifiedD2 hh A n) := by
  have hD1 : ContDiff ℝ 1
      (fderiv ℝ (gaussianRampMollified hh A n)) :=
    (contDiff_gaussianRampMollified hh A n).fderiv_right (m := 1)
      (WithTop.coe_le_coe.2 (OrderTop.le_top (2 : ℕ∞)))
  exact hD1.continuous_fderiv (by norm_num)

theorem hasFDerivAt_fderiv_gaussianRampMollified
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) (x : E) :
    HasFDerivAt (fderiv ℝ (gaussianRampMollified hh A n))
      (gaussianRampMollifiedD2 hh A n x) x := by
  have hD1 : ContDiff ℝ 1
      (fderiv ℝ (gaussianRampMollified hh A n)) :=
    (contDiff_gaussianRampMollified hh A n).fderiv_right (m := 1)
      (WithTop.coe_le_coe.2 (OrderTop.le_top (2 : ℕ∞)))
  exact (hD1.differentiable (by norm_num) x).hasFDerivAt

theorem norm_gaussianRampMollifiedD2_le
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) (x : E) :
    ‖gaussianRampMollifiedD2 hh A n x‖ ≤
      gaussianRampMollifiedD1LipschitzConstant (E := E) hh n := by
  unfold gaussianRampMollifiedD2
  apply norm_fderiv_le_of_lipschitz ℝ
  rw [fderiv_gaussianRampMollified_eq_explicitD1 hh A n]
  exact lipschitzWith_gaussianRampMollifiedD1Explicit hh A n

/-- The bounded continuous Hessian of the compact-kernel mollified ramp. -/
def gaussianRampMollifiedD2BCF
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) :
    BoundedContinuousFunction E (E →L[ℝ] (E →L[ℝ] ℝ)) :=
  let C : ℝ := gaussianRampMollifiedD1LipschitzConstant (E := E) hh n
  BoundedContinuousFunction.ofNormedAddCommGroup
    (gaussianRampMollifiedD2 hh A n)
    (continuous_gaussianRampMollifiedD2 hh A n) C
    (fun x => norm_gaussianRampMollifiedD2_le hh A n x)

@[simp] theorem gaussianRampMollifiedD2BCF_apply
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) (x : E) :
    gaussianRampMollifiedD2BCF hh A n x =
      gaussianRampMollifiedD2 hh A n x := rfl

theorem norm_gaussianRampMollifiedD2BCF_le
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) (x : E) :
    ‖gaussianRampMollifiedD2BCF hh A n x‖ ≤
      gaussianRampMollifiedD1LipschitzConstant (E := E) hh n :=
  norm_gaussianRampMollifiedD2_le hh A n x

theorem hasFDerivAt_gaussianRampMollifiedDerivBCF
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) (x : E) :
    HasFDerivAt (gaussianRampMollifiedDerivBCF hh A n)
      (gaussianRampMollifiedD2BCF hh A n x) x := by
  exact hasFDerivAt_fderiv_gaussianRampMollified hh A n x

theorem gaussianRampMollified_one_on
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ)
    {x : E} (hx : x ∈ A) : gaussianRampMollified hh A n x = 1 := by
  let ρ := gaussianRampMollifierRadius n
  let φ := gaussianRampMollifier (E := E) n
  let B := cthickening ρ A
  have hxB : x ∈ B := self_subset_cthickening A hx
  have hconst : ∀ y ∈ ball x φ.rOut,
      gaussianRampExpanded hh A n y = gaussianRampExpanded hh A n x := by
    intro y hy
    have hyB : y ∈ B := by
      exact mem_cthickening_of_dist_le y x ρ A hx (mem_ball.mp hy).le
    change gaussianRamp hh B y = gaussianRamp hh B x
    rw [gaussianRamp_one hh B hyB, gaussianRamp_one hh B hxB]
  change (φ.normed volE ⋆[lsmul ℝ ℝ, volE]
    (⇑(gaussianRampExpanded hh A n))) x = 1
  rw [φ.normed_convolution_eq_right (μ := volE) hconst]
  change gaussianRamp hh B x = 1
  exact gaussianRamp_one hh B hxB

theorem gaussianRampMollified_zero_off
    {h : ℝ} (hh : 0 < h) (A : Set E) (n : ℕ) {x : E}
    (hx : x ∉ cthickening
      (h + 2 * gaussianRampMollifierRadius n) A) :
    gaussianRampMollified hh A n x = 0 := by
  let ρ := gaussianRampMollifierRadius n
  let φ := gaussianRampMollifier (E := E) n
  let B := cthickening ρ A
  have hρ : 0 < ρ := gaussianRampMollifierRadius_pos n
  have hout (y : E) (hyx : dist y x ≤ ρ) : y ∉ thickening h B := by
    intro hy
    have hyA : y ∈ thickening (h + ρ) A := by
      have hy' : y ∈ thickening h (cthickening ρ A) := by
        simpa only [B] using hy
      rw [thickening_cthickening hh hρ.le A] at hy'
      exact hy'
    have hxy : dist x y ≤ ρ := by simpa [dist_comm] using hyx
    have hx' : x ∈ cthickening ρ (thickening (h + ρ) A) :=
      mem_cthickening_of_dist_le x y ρ (thickening (h + ρ) A) hyA hxy
    rw [cthickening_thickening hρ.le (by linarith [hh]) A] at hx'
    have hradius : ρ + (h + ρ) =
        h + 2 * gaussianRampMollifierRadius n := by
      dsimp [ρ]
      ring
    rw [hradius] at hx'
    exact hx hx'
  have hxout : x ∉ thickening h B := hout x (by simp [hρ.le])
  have hconst : ∀ y ∈ ball x φ.rOut,
      gaussianRampExpanded hh A n y = gaussianRampExpanded hh A n x := by
    intro y hy
    have hyout : y ∉ thickening h B := hout y (mem_ball.mp hy).le
    change gaussianRamp hh B y = gaussianRamp hh B x
    rw [gaussianRamp_zero hh B hyout, gaussianRamp_zero hh B hxout]
  change (φ.normed volE ⋆[lsmul ℝ ℝ, volE]
    (⇑(gaussianRampExpanded hh A n))) x = 0
  rw [φ.normed_convolution_eq_right (μ := volE) hconst]
  change gaussianRamp hh B x = 0
  exact gaussianRamp_zero hh B hxout

/-- The normalized bump construction, bundled as the exact smooth
approximation certificate consumed by the G4-to-G5 passage.  Two bump radii
account for the preliminary closed enlargement and the subsequent
convolution. -/
def concreteGaussianRampSmoothApproximation
    {h : ℝ} (hh : 0 < h) (A : Set E) :
    GaussianRampSmoothApproximation hh A where
  delta := fun n => 2 * gaussianRampMollifierRadius n
  approx := gaussianRampMollifiedBCF hh A
  Dapprox := gaussianRampMollifiedDerivBCF hh A
  delta_pos := fun n => mul_pos (by norm_num) (gaussianRampMollifierRadius_pos n)
  delta_tendsto_zero := by
    simpa using tendsto_const_nhds.mul
      gaussianRampMollifierRadius_tendsto_zero
  range := gaussianRampMollified_mem_Icc hh A
  smooth := fun n => contDiff_gaussianRampMollified hh A n
  fderiv_eq := fun _ _ => rfl
  mean_tendsto := tendsto_integral_gaussianRampMollified hh A
  one_on := fun n x hx => gaussianRampMollified_one_on hh A n hx
  zero_off := fun n x hx => gaussianRampMollified_zero_off hh A n hx
  norm_Dapprox_le := fun n x => norm_fderiv_gaussianRampMollified_le hh A n x

/-- Every finite-dimensional Gaussian distance ramp has the localized smooth
approximation needed by the closed-strip proof. -/
theorem gaussianRampSmoothApproximationProperty :
    GaussianRampSmoothApproximationProperty (E := E) := by
  intro h hh A _hA
  exact ⟨concreteGaussianRampSmoothApproximation hh A⟩

/-- With mollification now discharged concretely, the only analytic input in
the smooth G3--G5 Gaussian enlargement route is the canonical smooth OU
interpolation certificate. -/
theorem bakryLedouxEnlargement_of_smoothInterpolations
    (hflow : GaussianBobkovSmoothInterpolationProperty (X := E)) :
    BakryLedouxEnlargement (stdGaussian E) 1
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure) := by
  exact bakryLedouxEnlargement_of_smoothInterpolationsAndRampApproximation
    hflow gaussianRampSmoothApproximationProperty

/-- The sharp standard-Gaussian enlargement theorem from the single
remaining canonical-Q residual certificate. -/
theorem bakryLedouxEnlargement_of_canonicalInterpolations
    (hcanonical : CanonicalGaussianBobkovInterpolationProperty (E := E)) :
    BakryLedouxEnlargement (stdGaussian E) 1
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure) := by
  exact bakryLedouxEnlargement_of_smoothInterpolations
    (gaussianBobkovSmoothInterpolationProperty_of_canonical hcanonical)

end Concrete

end

end UniformRandomMALA
