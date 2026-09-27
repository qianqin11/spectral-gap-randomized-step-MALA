import UniformRandomMALA.Concrete.StationaryVarianceCentered
import UniformRandomMALA.Concrete.StationaryPathMoments

/-! # Powers of the `L²` Markov operator and actual transition iterates -/

namespace UniformRandomMALA.Concrete.KernelLp

open MeasureTheory ProbabilityTheory DiscreteTime
open scoped ENNReal ProbabilityTheory RealInnerProductSpace

noncomputable section
variable {α : Type*} [MeasurableSpace α]

theorem average_comp_ae (K J : Kernel α α) [IsMarkovKernel K] [IsMarkovKernel J]
    (π : Measure α) [IsProbabilityMeasure π]
    (hK : Kernel.Invariant K π) (hJ : Kernel.Invariant J π)
    {f : α → ℝ} (hf : Integrable f π) :
    average (J ∘ₖ K) f =ᵐ[π] average K (average J f) := by
  have hi : Integrable f ((J ∘ₖ K) ∘ₘ π) := by
    rw [← Measure.comp_assoc, hK, hJ]
    exact hf
  filter_upwards [Measure.ae_integrable_of_integrable_comp hi] with x hx
  exact Kernel.integral_comp hx

theorem operator_pow_coeFn (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : Kernel.Invariant K π)
    (f : Lp ℝ 2 π) (n : ℕ) :
    ((operator K π hπ 2 (by norm_num)) ^ n) f =ᵐ[π]
      average (finiteKernelIterate K n) f := by
  induction n with
  | zero =>
    apply Filter.Eventually.of_forall
    intro x
    simp only [pow_zero, one_apply_eq_self, finiteKernelIterate, average, Kernel.id_apply]
    exact (integral_dirac' f x (Lp.stronglyMeasurable f)).symm
  | succ n ih =>
    have havg := average_congr_ae K π hπ ih
    have hcomp := average_comp_ae K (finiteKernelIterate K n) π hπ
      (finiteKernelIterate_invariant K π hπ n) ((Lp.memLp f).integrable (by norm_num))
    rw [finiteKernelIterate_comp_right] at hcomp
    rw [pow_succ']
    exact (operator_coeFn K π hπ 2 (by norm_num)
      (((operator K π hπ 2 (by norm_num)) ^ n) f)).trans (havg.trans hcomp.symm)

theorem centeredOperator_pow_coe (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : Kernel.Invariant K π)
    (f : centeredL2 π) (n : ℕ) :
    (((centeredOperator K π hπ) ^ n) f : Lp ℝ 2 π) =
      ((operator K π hπ 2 (by norm_num)) ^ n) (f : Lp ℝ 2 π) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ']
    change (centeredOperator K π hπ (((centeredOperator K π hπ) ^ n) f) : Lp ℝ 2 π) = _
    rw [centeredOperator_coe, ih]
    rfl

theorem inner_centeredOperator_pow (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : Kernel.Invariant K π)
    (f : centeredL2 π) (n : ℕ) :
    ⟪f, ((centeredOperator K π hπ) ^ n) f⟫ =
      ∫ x, (f : Lp ℝ 2 π) x * average (finiteKernelIterate K n) (f : Lp ℝ 2 π) x ∂π := by
  change ⟪(f : Lp ℝ 2 π), (((centeredOperator K π hπ) ^ n) f : Lp ℝ 2 π)⟫ = _
  rw [centeredOperator_pow_coe, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [operator_pow_coeFn K π hπ (f : Lp ℝ 2 π) n] with x hx
  change (((operator K π hπ 2 (by norm_num)) ^ n) (f : Lp ℝ 2 π)) x * (f : Lp ℝ 2 π) x = _
  rw [hx, mul_comm]

end
end UniformRandomMALA.Concrete.KernelLp
