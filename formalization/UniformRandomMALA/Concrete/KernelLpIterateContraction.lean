import UniformRandomMALA.Concrete.KernelLpInterpolation
import UniformRandomMALA.Concrete.StationaryVarianceKernel

/-! # `L²` and `L⁴` decay along the actual finite kernel iterates -/

namespace UniformRandomMALA.Concrete.KernelLp
open MeasureTheory ProbabilityTheory DiscreteTime
open scoped ENNReal ProbabilityTheory
noncomputable section
variable {α : Type*} [MeasurableSpace α]

theorem integral_sq_average_iterate_le (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : Kernel.Invariant K π)
    (a : ℝ)
    (hstep : ∀ h : α → ℝ, MemLp h 2 π → (∫ x, h x ∂π) = 0 →
      (∫ x, average K h x ^ 2 ∂π) ≤ a ^ 2 * ∫ x, h x ^ 2 ∂π)
    {f : α → ℝ} (hf : MemLp f 2 π) (hf0 : ∫ x, f x ∂π = 0) (n : ℕ) :
    (∫ x, average (finiteKernelIterate K n) f x ^ 2 ∂π) ≤
      (a ^ n) ^ 2 * ∫ x, f x ^ 2 ∂π := by
  induction n with
  | zero =>
    simpa only [finiteKernelIterate, pow_zero, one_pow, one_mul] using
      integral_sq_average_le π Kernel.id (kernelId_isReversible π).invariant hf
  | succ n ih =>
    have hKn := finiteKernelIterate_invariant K π hπ n
    have hfn := average_memLp_of_ne_top (finiteKernelIterate K n) π hKn
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hf
    have hfn0 : ∫ x, average (finiteKernelIterate K n) f x ∂π = 0 := by
      rw [integral_average_invariant _ π hKn (hf.integrable (by norm_num)), hf0]
    have hcomp := average_comp_ae K (finiteKernelIterate K n) π hπ hKn
      (hf.integrable (by norm_num))
    rw [finiteKernelIterate_comp_right] at hcomp
    have heq : (∫ x, average (finiteKernelIterate K (n + 1)) f x ^ 2 ∂π) =
        ∫ x, average K (average (finiteKernelIterate K n) f) x ^ 2 ∂π := by
      apply integral_congr_ae
      filter_upwards [hcomp] with x hx using congrArg (fun y : ℝ => y ^ 2) hx
    rw [heq]
    calc
      _ ≤ a ^ 2 * ∫ x, average (finiteKernelIterate K n) f x ^ 2 ∂π :=
        hstep _ hfn hfn0
      _ ≤ a ^ 2 * ((a ^ n) ^ 2 * ∫ x, f x ^ 2 ∂π) :=
        mul_le_mul_of_nonneg_left ih (sq_nonneg a)
      _ = _ := by rw [pow_succ a n, mul_pow]; ring

theorem sqrt_pow_of_nonneg {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    Real.sqrt (a ^ n) = Real.sqrt a ^ n := by
  have h : (Real.sqrt a ^ n) ^ 2 = a ^ n := by
    rw [← pow_mul, mul_comm n 2, pow_mul, Real.sq_sqrt ha]
  rw [← h, Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg a) n)]

/-- Every finite transition iterate has `L⁴` decay obtained from the
proved `L²` decay and elementary interpolation. -/
theorem lpNorm_average_iterate_le (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : Kernel.Invariant K π)
    {a : ℝ} (ha : 0 ≤ a)
    (hstep : ∀ h : α → ℝ, MemLp h 2 π → (∫ x, h x ∂π) = 0 →
      (∫ x, average K h x ^ 2 ∂π) ≤ a ^ 2 * ∫ x, h x ^ 2 ∂π)
    {f : α → ℝ} (hf : MemLp f 4 π) (hf0 : ∫ x, f x ∂π = 0) (n : ℕ) :
    lpNorm (average (finiteKernelIterate K n) f) 4 π ≤
      4 * (Real.sqrt a) ^ n * lpNorm f 4 π := by
  have hi := lpNorm_centeredAverage_le (finiteKernelIterate K n) π
    (finiteKernelIterate_invariant K π hπ n) (pow_nonneg ha n)
    (fun h hh hh0 => integral_sq_average_iterate_le K π hπ a hstep hh hh0 n) hf
  have heq : centeredAverage (finiteKernelIterate K n) π f =
      average (finiteKernelIterate K n) f := by
    funext x
    simp only [centeredAverage, hf0, sub_zero]
  simpa only [heq, sqrt_pow_of_nonneg ha n] using hi

theorem lpNorm_average_halfLazy_iterate_le
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hrev : Kernel.IsReversible K π)
    {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π (halfLazyKernel K))
    {f : α → ℝ} (hf : MemLp f 4 π) (hf0 : ∫ x, f x ∂π = 0) (n : ℕ) :
    lpNorm (average (finiteKernelIterate (halfLazyKernel K) n) f) 4 π ≤
      4 * (Real.sqrt (1 - g)) ^ n * lpNorm f 4 π :=
  lpNorm_average_iterate_le (halfLazyKernel K) π
    (halfLazyKernel_isReversible π K hrev).invariant (sub_nonneg.mpr hg1)
    (fun _ hh hh0 => integral_sq_average_halfLazy_le π K hrev hg0 hg1 hgap hh hh0)
    hf hf0 n

end
end UniformRandomMALA.Concrete.KernelLp
