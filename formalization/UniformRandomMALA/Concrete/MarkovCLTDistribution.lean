import UniformRandomMALA.Concrete.L2DensityTV
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# From characteristic limits to Gaussian convergence

The probability spaces may vary with the row index. The conversion uses
mathlib's Lévy theorem. A square-integrable error whose second moment tends
to zero does not change either the characteristic limit or the limiting law.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology ProbabilityTheory ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- The characteristic function of a push-forward law in the phase convention used here. -/
theorem charFun_map_eq_integral_characteristic
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X : Ω → ℝ} (hX : AEMeasurable X μ) (t : ℝ) :
    charFun (μ.map X) t = ∫ x, Complex.exp (Complex.I * (t * X x)) ∂μ := by
  rw [charFun_apply_real, integral_map hX]
  · congr 1
    funext x
    rw [mul_comm _ Complex.I]
  · exact (by fun_prop : AEStronglyMeasurable
      (fun x : ℝ => Complex.exp ((t : ℂ) * x * Complex.I)) (μ.map X))

/-- The centered Gaussian characteristic function, including zero variance. -/
theorem charFun_gaussianReal_zero_eq {v : ℝ} (hv : 0 ≤ v) (t : ℝ) :
    charFun (gaussianReal 0 ⟨v, hv⟩) t = (Real.exp (-(t ^ 2 * v / 2)) : ℂ) := by
  rw [charFun_gaussianReal, Complex.ofReal_exp]
  congr 1
  change (t : ℂ) * 0 * I - (v : ℂ) * (t : ℂ) ^ 2 / 2 = _
  push_cast
  ring

/-- Lévy's theorem for the exact characteristic-function normalization
used by the finite-row martingale argument. -/
theorem tendstoInDistribution_gaussian_of_characteristic
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : (n : ℕ) → Ω n → ℝ) (hX : ∀ n, AEMeasurable (X n) (μ n))
    {v : ℝ} (hv : 0 ≤ v)
    (hchar : ∀ t : ℝ, Tendsto
      (fun n => ∫ x, Complex.exp (Complex.I * (t * X n x)) ∂μ n) atTop
      (𝓝 (Real.exp (-(t ^ 2 * v / 2)) : ℂ))) :
    TendstoInDistribution X atTop (id : ℝ → ℝ) μ (gaussianReal 0 ⟨v, hv⟩) where
  forall_aemeasurable := hX
  tendsto := by
    apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
    intro t
    simpa only [ProbabilityMeasure.coe_mk, Measure.map_id,
      charFun_map_eq_integral_characteristic _ (hX _), charFun_gaussianReal_zero_eq hv]
      using hchar t

/-- Gaussian convergence in distribution implies convergence of the exact
characteristic expectations, on fixed or varying probability spaces. -/
theorem characteristic_tendsto_of_tendstoInDistribution_gaussian
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : (n : ℕ) → Ω n → ℝ) {v : ℝ} (hv : 0 ≤ v)
    (hX : TendstoInDistribution X atTop (id : ℝ → ℝ) μ (gaussianReal 0 ⟨v, hv⟩)) :
    ∀ t : ℝ, Tendsto
      (fun n => ∫ x, Complex.exp (Complex.I * (t * X n x)) ∂μ n) atTop
      (𝓝 (Real.exp (-(t ^ 2 * v / 2)) : ℂ)) := by
  intro t
  have h := (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hX.tendsto) t
  simpa only [ProbabilityMeasure.coe_mk, Measure.map_id,
    charFun_map_eq_integral_characteristic _ (hX.forall_aemeasurable _),
    charFun_gaussianReal_zero_eq hv] using h

theorem norm_characteristic_phase_sub_le (t x y : ℝ) :
    ‖Complex.exp (Complex.I * (t * x)) - Complex.exp (Complex.I * (t * y))‖ ≤
      |t| * |x - y| := by
  have heq : Complex.exp (Complex.I * (t * x)) - Complex.exp (Complex.I * (t * y)) =
      (Complex.exp (Complex.I * (t * (x - y))) - 1) *
        Complex.exp (Complex.I * (t * y)) := by
    rw [sub_mul, one_mul, ← Complex.exp_add]
    congr 2
    ring
  rw [heq, norm_mul]
  have hunit : ‖Complex.exp (Complex.I * (t * y))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hunit, mul_one]
  simpa only [Real.norm_eq_abs, abs_mul, Complex.ofReal_mul, Complex.ofReal_sub] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := t * (x - y)))

theorem characteristic_integrable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {X : Ω → ℝ} (hX : AEMeasurable X μ) (t : ℝ) :
    Integrable (fun x => Complex.exp (Complex.I * (t * X x))) μ := by
  apply Integrable.of_bound (by fun_prop) 1
  exact ae_of_all _ fun x => by
    rw [Complex.norm_exp]
    simp

/-- The characteristic-function error is controlled by the actual second
moment of the difference, on any probability space. -/
theorem norm_characteristic_integral_sub_le_sqrt
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hXY : MemLp (fun x => X x - Y x) 2 μ) (t : ℝ) :
    ‖(∫ x, Complex.exp (Complex.I * (t * X x)) ∂μ) -
      ∫ x, Complex.exp (Complex.I * (t * Y x)) ∂μ‖ ≤
      |t| * Real.sqrt (∫ x, (X x - Y x) ^ 2 ∂μ) := by
  have hiX := characteristic_integrable μ hX t
  have hiY := characteristic_integrable μ hY t
  have hsq := abs_integral_mul_le_sqrt_integral_sq hXY.norm
    (memLp_const (1 : ℝ) : MemLp (fun _ : Ω => (1 : ℝ)) 2 μ)
  have habs : (∫ x, |X x - Y x| ∂μ) ≤ Real.sqrt (∫ x, (X x - Y x) ^ 2 ∂μ) := by
    have hI0 : 0 ≤ ∫ x, |X x - Y x| ∂μ := integral_nonneg fun x => abs_nonneg _
    simpa [Real.norm_eq_abs, abs_of_nonneg hI0] using hsq
  rw [← integral_sub hiX hiY]
  calc
    _ ≤ ∫ x, ‖Complex.exp (Complex.I * (t * X x)) -
        Complex.exp (Complex.I * (t * Y x))‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, |t| * |X x - Y x| ∂μ := integral_mono
      (hiX.sub hiY).norm ((hXY.integrable (by norm_num)).norm.const_mul _)
      (fun x => norm_characteristic_phase_sub_le t (X x) (Y x))
    _ = |t| * ∫ x, |X x - Y x| ∂μ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left habs (abs_nonneg t)

/-- A vanishing square-integrable perturbation preserves a characteristic
limit even when the probability space varies with the row. -/
theorem characteristic_limit_of_sq_error
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X Y : (n : ℕ) → Ω n → ℝ)
    (hX : ∀ n, AEMeasurable (X n) (μ n)) (hY : ∀ n, AEMeasurable (Y n) (μ n))
    (hYX : ∀ n, MemLp (fun x => Y n x - X n x) 2 (μ n))
    (herror : Tendsto (fun n => ∫ x, (Y n x - X n x) ^ 2 ∂μ n) atTop (𝓝 0))
    {z : ℝ → ℂ}
    (hchar : ∀ t : ℝ, Tendsto
      (fun n => ∫ x, Complex.exp (Complex.I * (t * X n x)) ∂μ n) atTop (𝓝 (z t))) :
    ∀ t : ℝ, Tendsto
      (fun n => ∫ x, Complex.exp (Complex.I * (t * Y n x)) ∂μ n) atTop (𝓝 (z t)) := by
  intro t
  have hroot : Tendsto
      (fun n => |t| * Real.sqrt (∫ x, (Y n x - X n x) ^ 2 ∂μ n)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (Real.continuous_sqrt.tendsto 0 |>.comp herror)
  have hnorm : Tendsto (fun n =>
      ‖(∫ x, Complex.exp (Complex.I * (t * Y n x)) ∂μ n) -
        ∫ x, Complex.exp (Complex.I * (t * X n x)) ∂μ n‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (fun n =>
      norm_characteristic_integral_sub_le_sqrt (μ n) (hY n) (hX n) (hYX n) t) hroot
  have hdiff := (tendsto_zero_iff_norm_tendsto_zero).mpr hnorm
  simpa only [zero_add, sub_add_cancel] using hdiff.add (hchar t)

/-- The Gaussian conclusion is unchanged by an error whose actual second
moment vanishes; square integrability is explicit to avoid vacuous integrals. -/
theorem tendstoInDistribution_gaussian_of_characteristic_of_sq_error
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X Y : (n : ℕ) → Ω n → ℝ)
    (hX : ∀ n, AEMeasurable (X n) (μ n)) (hY : ∀ n, AEMeasurable (Y n) (μ n))
    (hYX : ∀ n, MemLp (fun x => Y n x - X n x) 2 (μ n))
    (herror : Tendsto (fun n => ∫ x, (Y n x - X n x) ^ 2 ∂μ n) atTop (𝓝 0))
    {v : ℝ} (hv : 0 ≤ v)
    (hchar : ∀ t : ℝ, Tendsto
      (fun n => ∫ x, Complex.exp (Complex.I * (t * X n x)) ∂μ n) atTop
      (𝓝 (Real.exp (-(t ^ 2 * v / 2)) : ℂ))) :
    TendstoInDistribution Y atTop (id : ℝ → ℝ) μ (gaussianReal 0 ⟨v, hv⟩) :=
  tendstoInDistribution_gaussian_of_characteristic μ Y hY hv
    (characteristic_limit_of_sq_error μ X Y hX hY hYX herror hchar)

end
end UniformRandomMALA.Concrete
