import UniformRandomMALA.Concrete.SetwiseTV
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Square-integrable densities and total variation

The centered Radon--Nikodym density controls expectation discrepancies by
Cauchy--Schwarz.  Centered indicators give the factor `1/2` in the paper's
total-variation convention.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- The centered Radon--Nikodym density of the initial distribution. -/
def centeredDensity (μ π : Measure α) (x : α) : ℝ :=
  (μ.rnDeriv π x).toReal - 1

/-- The paper's `‖dμ/dπ - 1‖_{L²(π)}`, written as a square-root integral. -/
def centeredDensityL2Norm (μ π : Measure α) : ℝ :=
  Real.sqrt (∫ x, centeredDensity μ π x ^ 2 ∂π)

theorem centeredDensityL2Norm_nonneg (μ π : Measure α) :
    0 ≤ centeredDensityL2Norm μ π := Real.sqrt_nonneg _

/-- Integral Cauchy--Schwarz in square-root-of-square-integral notation. -/
theorem abs_integral_mul_le_sqrt_integral_sq {π : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 π) (hg : MemLp g 2 π) :
    |∫ x, f x * g x ∂π| ≤
      Real.sqrt (∫ x, f x ^ 2 ∂π) * Real.sqrt (∫ x, g x ^ 2 ∂π) := by
  calc
    |∫ x, f x * g x ∂π| ≤ ∫ x, |f x * g x| ∂π :=
      abs_integral_le_integral_abs
    _ = ∫ x, ‖f x‖ * ‖g x‖ ∂π := by simp only [Real.norm_eq_abs, abs_mul]
    _ ≤ Real.sqrt (∫ x, f x ^ 2 ∂π) * Real.sqrt (∫ x, g x ^ 2 ∂π) := by
      have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
        (by simpa using hf) (by simpa using hg)
      simpa only [Real.norm_eq_abs, Real.rpow_two, sq_abs, Real.sqrt_eq_rpow] using h

/-- Every square-integrable test has discrepancy bounded by the centered
density norm times its `L²` norm. -/
theorem abs_integral_sub_le_centeredDensityL2Norm
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : μ ≪ π)
    (hDensity : MemLp (fun x => (μ.rnDeriv π x).toReal) 2 π)
    {f : α → ℝ} (hf : MemLp f 2 π) :
    |(∫ x, f x ∂μ) - ∫ x, f x ∂π| ≤
      centeredDensityL2Norm μ π * Real.sqrt (∫ x, f x ^ 2 ∂π) := by
  have hcenter : MemLp (centeredDensity μ π) 2 π :=
    hDensity.sub (memLp_const (1 : ℝ))
  have hfInt : Integrable f π := hf.integrable (by norm_num)
  have hdInt : Integrable (fun x => (μ.rnDeriv π x).toReal * f x) π :=
    hDensity.integrable_mul hf
  have hDifference : (∫ x, f x ∂μ) - ∫ x, f x ∂π =
      ∫ x, centeredDensity μ π x * f x ∂π := by
    rw [← integral_toReal_rnDeriv_mul hμ, ← integral_sub hdInt hfInt]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by dsimp [centeredDensity]; ring
  rw [hDifference]
  exact abs_integral_mul_le_sqrt_integral_sq hcenter hf

/-- A centered event indicator, whose variance is at most `1/4`. -/
def centeredIndicator (π : Measure α) (s : Set α) (x : α) : ℝ :=
  s.indicator (fun _ => (1 : ℝ)) x - π.real s

theorem centeredIndicator_memLp (π : Measure α) [IsFiniteMeasure π]
    {s : Set α} (hs : MeasurableSet s) :
    MemLp (centeredIndicator π s) 2 π :=
  ((memLp_const (1 : ℝ)).indicator hs).sub (memLp_const (π.real s))

theorem integral_centeredIndicator (π : Measure α) [IsProbabilityMeasure π]
    {s : Set α} (hs : MeasurableSet s) :
    ∫ x, centeredIndicator π s x ∂π = 0 := by
  have hi : Integrable (s.indicator (fun _ => (1 : ℝ))) π :=
    (integrable_const _).indicator hs
  simp [centeredIndicator, integral_sub hi (integrable_const _),
    integral_indicator_const _ hs]

theorem integral_centeredIndicator_sq (π : Measure α) [IsProbabilityMeasure π]
    {s : Set α} (hs : MeasurableSet s) :
    ∫ x, centeredIndicator π s x ^ 2 ∂π = π.real s * (1 - π.real s) := by
  have hi : Integrable (s.indicator (fun _ => (1 : ℝ))) π :=
    (integrable_const _).indicator hs
  have hfun : (fun x => centeredIndicator π s x ^ 2) =
      (fun x => (1 - 2 * π.real s) * s.indicator (fun _ => (1 : ℝ)) x +
        (π.real s) ^ 2) := by
    funext x
    by_cases hx : x ∈ s
    · simp only [centeredIndicator, Set.indicator_of_mem hx]
      ring
    · simp [centeredIndicator, hx]
  rw [hfun, integral_add (hi.const_mul _) (integrable_const _), integral_const_mul]
  simp only [integral_indicator_const _ hs, integral_const, measureReal_def,
    measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul, mul_one]
  ring

theorem integral_centeredIndicator_sq_le_quarter (π : Measure α)
    [IsProbabilityMeasure π] {s : Set α} (hs : MeasurableSet s) :
    (∫ x, centeredIndicator π s x ^ 2 ∂π) ≤ 1 / 4 := by
  rw [integral_centeredIndicator_sq π hs]
  nlinarith [sq_nonneg (π.real s - 1 / 2)]

theorem sqrt_integral_centeredIndicator_sq_le_half (π : Measure α)
    [IsProbabilityMeasure π] {s : Set α} (hs : MeasurableSet s) :
    Real.sqrt (∫ x, centeredIndicator π s x ^ 2 ∂π) ≤ 1 / 2 := by
  apply (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 1 / 2)).2
  convert integral_centeredIndicator_sq_le_quarter π hs using 1
  norm_num

/-- Integration of a centered indicator against another probability law
gives the measurable-event discrepancy. -/
theorem integral_centeredIndicator_eq_sub (μ π : Measure α)
    [IsProbabilityMeasure μ] {s : Set α} (hs : MeasurableSet s) :
    ∫ x, centeredIndicator π s x ∂μ = μ.real s - π.real s := by
  have hi : Integrable (s.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const _).indicator hs
  simp [centeredIndicator, integral_sub hi (integrable_const _),
    integral_indicator_const _ hs]

/-- The initial total-variation error is at most one half of the centered
Radon--Nikodym density's `L²` norm. -/
theorem setwiseTV_le_half_centeredDensityL2Norm
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : μ ≪ π)
    (hDensity : MemLp (fun x => (μ.rnDeriv π x).toReal) 2 π) :
    setwiseTV μ π ≤ centeredDensityL2Norm μ π / 2 := by
  apply setwiseTV_le_of_forall
  intro s hs
  have h := abs_integral_sub_le_centeredDensityL2Norm μ π hμ hDensity
    (centeredIndicator_memLp π hs)
  rw [integral_centeredIndicator_eq_sub μ π hs, integral_centeredIndicator π hs,
    sub_zero] at h
  calc
    |μ.real s - π.real s| ≤ centeredDensityL2Norm μ π *
        Real.sqrt (∫ x, centeredIndicator π s x ^ 2 ∂π) := h
    _ ≤ centeredDensityL2Norm μ π * (1 / 2) :=
      mul_le_mul_of_nonneg_left (sqrt_integral_centeredIndicator_sq_le_half π hs)
        (centeredDensityL2Norm_nonneg μ π)
    _ = centeredDensityL2Norm μ π / 2 := by ring

end

end UniformRandomMALA.Concrete
