import UniformRandomMALA.Concrete.KernelLpL2
import UniformRandomMALA.Concrete.StationaryVarianceResolvent
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-! # The Markov operator on the complete space of centered `L²` functions -/

namespace UniformRandomMALA.Concrete.KernelLp

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory RealInnerProductSpace

noncomputable section
variable {α : Type*} [MeasurableSpace α]

def oneL2 (π : Measure α) [IsProbabilityMeasure π] : Lp ℝ 2 π :=
  (memLp_const (1 : ℝ)).toLp (fun _ => 1)

theorem inner_oneL2 (π : Measure α) [IsProbabilityMeasure π] (f : Lp ℝ 2 π) :
    ⟪oneL2 π, f⟫ = ∫ x, f x ∂π := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (memLp_const (1 : ℝ))] with x hx
  change f x * oneL2 π x = f x
  change oneL2 π x = 1 at hx
  rw [hx, mul_one]

/-- The closed subspace of mean-zero square-integrable real functions. -/
def centeredL2 (π : Measure α) [IsProbabilityMeasure π] : Submodule ℝ (Lp ℝ 2 π) :=
  (innerSL ℝ (oneL2 π)).ker

theorem mem_centeredL2_iff (π : Measure α) [IsProbabilityMeasure π] (f : Lp ℝ 2 π) :
    f ∈ centeredL2 π ↔ ∫ x, f x ∂π = 0 := by
  change ⟪oneL2 π, f⟫ = 0 ↔ _
  rw [inner_oneL2]

instance centeredL2_completeSpace (π : Measure α) [IsProbabilityMeasure π] :
    CompleteSpace (centeredL2 π) :=
  (ContinuousLinearMap.isClosed_ker (innerSL ℝ (oneL2 π))).completeSpace_coe

theorem centeredL2_integral (π : Measure α) [IsProbabilityMeasure π]
    (f : centeredL2 π) : ∫ x, (f : Lp ℝ 2 π) x ∂π = 0 :=
  (mem_centeredL2_iff π f).1 f.property

def centeredOperator (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : Kernel.Invariant K π) :
    centeredL2 π →L[ℝ] centeredL2 π :=
  (operator K π hπ 2 (by norm_num)).restrict fun f hf => by
    rw [mem_centeredL2_iff, integral_operator]
    exact (mem_centeredL2_iff π f).1 hf

@[simp] theorem centeredOperator_coe (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : Kernel.Invariant K π)
    (f : centeredL2 π) :
    (centeredOperator K π hπ f : Lp ℝ 2 π) = operator K π hπ 2 (by norm_num) f := rfl

theorem norm_centeredOperator_le (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : Kernel.Invariant K π) :
    ‖centeredOperator K π hπ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖operator K π hπ 2 (by norm_num) (f : Lp ℝ 2 π)‖ ≤ 1 * ‖(f : Lp ℝ 2 π)‖
  simpa using norm_toLp_le K π hπ 2 (by norm_num) (f : Lp ℝ 2 π)

theorem centeredOperator_rightGap (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : Kernel.Invariant K π)
    {g : ℝ} (hg : 0 ≤ g) (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π K)
    (f : centeredL2 π) :
    g * ‖f‖ ^ 2 ≤ ⟪f, f - centeredOperator K π hπ f⟫ := by
  have hi := inner_operator_le_gap K π hπ hg hgap (f : Lp ℝ 2 π)
    (centeredL2_integral π f)
  change g * ‖(f : Lp ℝ 2 π)‖ ^ 2 ≤
    ⟪(f : Lp ℝ 2 π), (f : Lp ℝ 2 π) - operator K π hπ 2 (by norm_num) f⟫
  rw [inner_sub_right, real_inner_self_eq_norm_sq]
  linarith

end
end UniformRandomMALA.Concrete.KernelLp
