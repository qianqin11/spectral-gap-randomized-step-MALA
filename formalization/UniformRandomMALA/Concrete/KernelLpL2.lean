import UniformRandomMALA.Concrete.KernelLpOperator
import UniformRandomMALA.Concrete.RayleighSpectralGap
import UniformRandomMALA.Concrete.Conductance
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Reversible Markov integration on the full `L²` space -/

namespace UniformRandomMALA.Concrete.KernelLp

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory InnerProductSpace

noncomputable section
variable {α : Type*} [MeasurableSpace α]

theorem measurePreserving_edge_fst (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] :
    MeasurePreserving Prod.fst (π ⊗ₘ K) π :=
  ⟨measurable_fst, Measure.fst_compProd π K⟩

theorem measurePreserving_edge_snd (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π) :
    MeasurePreserving Prod.snd (π ⊗ₘ K) π :=
  ⟨measurable_snd, by change (π ⊗ₘ K).snd = π; rw [Measure.snd_compProd, hπ]⟩

theorem integral_edge_product (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {f g : α → ℝ} (hf : MemLp f 2 π) (hg : MemLp g 2 π) :
    (∫ z, f z.1 * g z.2 ∂(π ⊗ₘ K)) = ∫ x, f x * average K g x ∂π := by
  have hF := hf.comp_measurePreserving (measurePreserving_edge_fst π K)
  have hG := hg.comp_measurePreserving (measurePreserving_edge_snd π K hπ)
  simpa only [Function.comp_def, Pi.mul_apply, average, integral_const_mul] using
    Measure.integral_compProd (hF.integrable_mul hG)

/-- Reversibility gives adjoint symmetry for all square-integrable functions,
including unbounded densities. -/
theorem integral_mul_average_symm (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hrev : Kernel.IsReversible K π)
    {f g : α → ℝ} (hf : MemLp f 2 π) (hg : MemLp g 2 π) :
    (∫ x, f x * average K g x ∂π) = ∫ x, average K f x * g x ∂π := by
  rw [← integral_edge_product π K hrev.invariant hf hg]
  have hs := edgeMeasure_map_swap π K hrev
  change (π ⊗ₘ K).map Prod.swap = π ⊗ₘ K at hs
  have hF := hf.comp_measurePreserving (measurePreserving_edge_fst π K)
  have hG := hg.comp_measurePreserving (measurePreserving_edge_snd π K hrev.invariant)
  have hm : AEStronglyMeasurable (fun z : α × α => f z.1 * g z.2)
      ((π ⊗ₘ K).map Prod.swap) := by
    rw [hs]
    exact hF.1.mul hG.1
  have hi := integral_map measurable_swap.aemeasurable hm
  rw [hs] at hi
  rw [hi]
  change (∫ z : α × α, f z.2 * g z.1 ∂(π ⊗ₘ K)) = _
  simp_rw [mul_comm (f _) (g _)]
  rw [integral_edge_product π K hrev.invariant hg hf]
  simp_rw [mul_comm (g _) (average K f _)]

theorem inner_operator (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : Kernel.Invariant K π)
    (f g : Lp ℝ 2 π) :
    ⟪f, operator K π hπ 2 (by norm_num) g⟫_ℝ =
      ∫ x, f x * average K g x ∂π := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [operator_coeFn K π hπ 2 (by norm_num) g] with x hx
  change (operator K π hπ 2 (by norm_num) g x) * f x = _
  rw [hx, mul_comm]

theorem operator_isSymmetric (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hrev : Kernel.IsReversible K π) :
    (operator K π hrev.invariant 2 (by norm_num)).toLinearMap.IsSymmetric := by
  intro f g
  change ⟪operator K π hrev.invariant 2 (by norm_num) f, g⟫_ℝ =
    ⟪f, operator K π hrev.invariant 2 (by norm_num) g⟫_ℝ
  rw [real_inner_comm, inner_operator, integral_mul_average_symm π K hrev
    (Lp.memLp g) (Lp.memLp f), inner_operator]
  simp_rw [mul_comm (average K g _) (f _)]

theorem integral_sq_eq_norm_sq (π : Measure α) (f : Lp ℝ 2 π) :
    (∫ x, f x ^ 2 ∂π) = ‖f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext x
  simp [pow_two]

theorem integral_sq_average_le (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {f : α → ℝ} (hf : MemLp f 2 π) :
    (∫ x, average K f x ^ 2 ∂π) ≤ ∫ x, f x ^ 2 ∂π := by
  have hi := (integral_norm_average_rpow_le K π hπ (p := 2) (by norm_num)
    (by simpa using hf)).2
  simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using hi

/-- The usual Dirichlet identity, with only an `L²` hypothesis. -/
theorem energy_eq_ofReal (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {f : α → ℝ} (hm : Measurable f) (hf : MemLp f 2 π) :
    Dirichlet.energy π K f = ENNReal.ofReal
      ((∫ x, f x ^ 2 ∂π) - ∫ x, f x * average K f x ∂π) := by
  have hF := hf.comp_measurePreserving (measurePreserving_edge_fst π K)
  have hG := hf.comp_measurePreserving (measurePreserving_edge_snd π K hπ)
  have hsq : Integrable (fun z : α × α => (f z.1 - f z.2) ^ 2) (π ⊗ₘ K) :=
    (hF.sub hG).integrable_sq
  have hF2 := hF.integrable_sq
  have hG2 := hG.integrable_sq
  have hFG := hF.integrable_mul hG
  simp only [Function.comp_def] at hF2 hG2
  change Integrable (fun z : α × α => f z.1 * f z.2) (π ⊗ₘ K) at hFG
  have hdiff : Integrable (fun z : α × α => f z.1 ^ 2 - 2 * (f z.1 * f z.2))
      (π ⊗ₘ K) := hF2.sub (hFG.const_mul 2)
  have hfst : (∫ z : α × α, f z.1 ^ 2 ∂(π ⊗ₘ K)) = ∫ x, f x ^ 2 ∂π := by
    rw [← integral_map measurable_fst.aemeasurable (hm.pow_const 2).aestronglyMeasurable]
    change (∫ x, f x ^ 2 ∂(π ⊗ₘ K).fst) = _
    rw [Measure.fst_compProd]
  have hsnd : (∫ z : α × α, f z.2 ^ 2 ∂(π ⊗ₘ K)) = ∫ x, f x ^ 2 ∂π := by
    rw [← integral_map measurable_snd.aemeasurable (hm.pow_const 2).aestronglyMeasurable]
    change (∫ x, f x ^ 2 ∂(π ⊗ₘ K).snd) = _
    rw [Measure.snd_compProd, hπ]
  have heq : (∫ z : α × α, (f z.1 - f z.2) ^ 2 ∂(π ⊗ₘ K)) =
      2 * ((∫ x, f x ^ 2 ∂π) - ∫ x, f x * average K f x ∂π) := by
    simp_rw [sub_sq, mul_assoc]
    rw [integral_add hdiff hG2,
      integral_sub hF2 (hFG.const_mul 2), integral_const_mul,
      hfst, hsnd, integral_edge_product π K hπ hf hf]
    ring
  rw [energy_eq_edgeMeasure_lintegral π K f hm]
  change (2 : ℝ≥0∞)⁻¹ * (∫⁻ z : α × α, ENNReal.ofReal ((f z.1 - f z.2) ^ 2)
    ∂(π ⊗ₘ K)) = _
  rw [← ofReal_integral_eq_lintegral_ofReal hsq
    (Filter.Eventually.of_forall fun _ => sq_nonneg _), heq,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num [← mul_assoc]
  rw [ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num), one_mul]

theorem inner_operator_le_norm_sq (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : Kernel.Invariant K π)
    (f : Lp ℝ 2 π) :
    ⟪f, operator K π hπ 2 (by norm_num) f⟫_ℝ ≤ ‖f‖ ^ 2 := by
  calc
    _ ≤ ‖f‖ * ‖operator K π hπ 2 (by norm_num) f‖ := real_inner_le_norm _ _
    _ ≤ ‖f‖ * ‖f‖ := mul_le_mul_of_nonneg_left (norm_toLp_le K π hπ 2
      (by norm_num) f) (norm_nonneg f)
    _ = _ := (pow_two _).symm

/-- The variational gap controls the full `L²` Markov quadratic form. -/
theorem inner_operator_le_gap (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : Kernel.Invariant K π)
    {g : ℝ} (hg : 0 ≤ g) (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π K)
    (f : Lp ℝ 2 π) (hf : ∫ x, f x ∂π = 0) :
    ⟪f, operator K π hπ 2 (by norm_num) f⟫_ℝ ≤ (1 - g) * ‖f‖ ^ 2 := by
  have hp := (l2PoincareLower_iff_le_rayleighSpectralGap K (ENNReal.ofReal g)).2 hgap
    f (Lp.stronglyMeasurable f).measurable (Lp.memLp f)
  have hv : evariance f π = ENNReal.ofReal (‖f‖ ^ 2) := by
    rw [← (Lp.memLp f).ofReal_variance_eq, variance_eq_sub (Lp.memLp f), hf]
    simp [integral_sq_eq_norm_sq]
  rw [hv, energy_eq_ofReal π K hπ (Lp.stronglyMeasurable f).measurable (Lp.memLp f),
    integral_sq_eq_norm_sq, ← inner_operator K π hπ, ← ENNReal.ofReal_mul hg] at hp
  have hi := (ENNReal.ofReal_le_ofReal_iff
    (sub_nonneg.mpr (inner_operator_le_norm_sq K π hπ f))).1 hp
  nlinarith

end
end UniformRandomMALA.Concrete.KernelLp
