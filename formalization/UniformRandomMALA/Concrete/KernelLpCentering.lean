import UniformRandomMALA.Concrete.KernelLpContraction

/-! # Centering and quadratic estimates for Markov integration -/

namespace UniformRandomMALA.Concrete.KernelLp
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
noncomputable section
variable {α : Type*} [MeasurableSpace α]

def center (π : Measure α) (f : α → ℝ) (x : α) : ℝ := f x - ∫ y, f y ∂π
def centeredAverage (K : Kernel α α) (π : Measure α) (f : α → ℝ) (x : α) : ℝ :=
  average K f x - ∫ y, f y ∂π

theorem center_memLp (π : Measure α) [IsProbabilityMeasure π]
    {p : ℝ≥0∞} {f : α → ℝ} (hf : MemLp f p π) : MemLp (center π f) p π :=
  hf.sub (memLp_const _)

theorem integral_center (π : Measure α) [IsProbabilityMeasure π]
    {f : α → ℝ} (hf : Integrable f π) : ∫ x, center π f x ∂π = 0 := by
  simp only [center]
  rw [integral_sub hf (integrable_const _)]
  simp

theorem integral_sq_center (π : Measure α) [IsProbabilityMeasure π]
    {f : α → ℝ} (hf : MemLp f 2 π) :
    (∫ x, center π f x ^ 2 ∂π) = (∫ x, f x ^ 2 ∂π) - (∫ x, f x ∂π) ^ 2 := by
  have hi := hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  simp_rw [center, sub_sq]
  have hprod : Integrable (fun x => 2 * f x * ∫ y, f y ∂π) π :=
    (hi.const_mul 2).mul_const _
  have hsub : Integrable (fun x => f x ^ 2 - 2 * f x * ∫ y, f y ∂π) π :=
    hf.integrable_sq.sub hprod
  rw [integral_add hsub (integrable_const _), integral_sub hf.integrable_sq hprod,
    integral_mul_const, integral_const_mul]
  simp
  ring

theorem integral_sq_center_le (π : Measure α) [IsProbabilityMeasure π]
    {f : α → ℝ} (hf : MemLp f 2 π) :
    (∫ x, center π f x ^ 2 ∂π) ≤ ∫ x, f x ^ 2 ∂π := by
  rw [integral_sq_center π hf]
  exact sub_le_self _ (sq_nonneg _)

theorem average_center_ae (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : Kernel.Invariant K π)
    {f : α → ℝ} (hf : Integrable f π) :
    average K (center π f) =ᵐ[π] centeredAverage K π f := by
  have hcomp : Integrable f (K ∘ₘ π) := by rwa [hπ]
  filter_upwards [Measure.ae_integrable_of_integrable_comp hcomp] with x hx
  simp only [average, center, centeredAverage]
  rw [integral_sub hx (integrable_const _)]
  simp

theorem centeredAverage_memLp (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : Kernel.Invariant K π)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) {f : α → ℝ} (hf : MemLp f p π) :
    MemLp (centeredAverage K π f) p π :=
  (average_memLp_of_ne_top K π hπ hp hpt hf).sub (memLp_const _)

theorem centeredAverage_add_ae (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : Kernel.Invariant K π)
    {f h : α → ℝ} (hf : Integrable f π) (hh : Integrable h π) :
    centeredAverage K π (f + h) =ᵐ[π]
      fun x => centeredAverage K π f x + centeredAverage K π h x := by
  filter_upwards [average_add_ae K π hπ hf hh] with x hx
  simp only [centeredAverage, integral_add hf hh, Pi.add_apply] at hx ⊢
  rw [hx]
  ring

theorem abs_centeredAverage_le (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] {f : α → ℝ} {B : ℝ}
    (hb : ∀ x, |f x| ≤ B) (x : α) : |centeredAverage K π f x| ≤ 2 * B := by
  have hK : |average K f x| ≤ B := by
    have hi := norm_integral_le_of_norm_le_const (μ := K x) (f := f)
      (Filter.Eventually.of_forall fun x => (Real.norm_eq_abs _).symm ▸ hb x)
    rw [Real.norm_eq_abs] at hi
    simpa [average] using hi
  have hπ : |∫ y, f y ∂π| ≤ B := by
    have hi := norm_integral_le_of_norm_le_const (μ := π) (f := f)
      (Filter.Eventually.of_forall fun x => (Real.norm_eq_abs _).symm ▸ hb x)
    rw [Real.norm_eq_abs] at hi
    simpa using hi
  exact (abs_sub _ _).trans (by linarith)

theorem integral_sq_centeredAverage_le (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : Kernel.Invariant K π)
    (a : ℝ)
    (hdecay : ∀ h : α → ℝ, MemLp h 2 π → (∫ x, h x ∂π) = 0 →
      (∫ x, average K h x ^ 2 ∂π) ≤ a ^ 2 * ∫ x, h x ^ 2 ∂π)
    {f : α → ℝ} (hf : MemLp f 2 π) :
    (∫ x, centeredAverage K π f x ^ 2 ∂π) ≤ a ^ 2 * ∫ x, f x ^ 2 ∂π := by
  have h := hdecay (center π f) (center_memLp π hf)
    (integral_center π (hf.integrable (by norm_num)))
  have heq : (∫ x, average K (center π f) x ^ 2 ∂π) =
      ∫ x, centeredAverage K π f x ^ 2 ∂π := by
    apply integral_congr_ae
    filter_upwards [average_center_ae K π hπ (hf.integrable (by norm_num))] with x hx
    rw [hx]
  rw [heq] at h
  exact h.trans (mul_le_mul_of_nonneg_left (integral_sq_center_le π hf) (sq_nonneg a))

end
end UniformRandomMALA.Concrete.KernelLp
