import UniformRandomMALA.Concrete.StationaryPath
import UniformRandomMALA.Concrete.L2DensityEvolution
import Mathlib.Probability.Kernel.Composition.RadonNikodym

/-!
# Nonstationary pair moments and density discrepancies

Pair-coordinate laws are the actual finite Markov laws. An initial L²
density and L⁴ observables make their products integrable. Conditioning the
second coordinate then gives the covariance-error bound needed for
Corollary 2.8 (`cor:nonstationary-variance`).
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory DiscreteTime
open scoped ENNReal ProbabilityTheory

noncomputable section

variable {α : Type*} [MeasurableSpace α]

private theorem holderTriple_four_four_two : ENNReal.HolderTriple 4 4 2 := by
  constructor
  apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by norm_num)).mp
  norm_num [ENNReal.toReal_add (by norm_num : (4 : ℝ≥0∞)⁻¹ ≠ ∞)
    (by norm_num : (4 : ℝ≥0∞)⁻¹ ≠ ∞)]

lemma lpNorm_two_eq_sqrt_integral_sq {π : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f π) :
    lpNorm f 2 π = Real.sqrt (∫ x, f x ^ 2 ∂π) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hf]
  simp [Real.sqrt_eq_rpow, Real.norm_eq_abs, sq_abs]

lemma lpNorm_mul_le_L4 {π : Measure α} {f g : α → ℝ}
    (hf : MemLp f 4 π) (hg : MemLp g 4 π) :
    lpNorm (fun x => f x * g x) 2 π ≤ lpNorm f 4 π * lpNorm g 4 π := by
  let := holderTriple_four_four_two
  have h := eLpNorm_smul_le_mul_eLpNorm (p := 4) (q := 4) (r := 2) hg.1 hf.1
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top) h
  change (eLpNorm (fun x => f x * g x) 2 π).toReal ≤
    (eLpNorm f 4 π * eLpNorm g 4 π).toReal at hr
  simpa only [ENNReal.toReal_mul, toReal_eLpNorm hf.1, toReal_eLpNorm hg.1,
    toReal_eLpNorm (show AEStronglyMeasurable (fun x => f x * g x) π from hf.1.mul hg.1)] using hr

/-- L² densities and two L⁴ marginal observables suffice for genuine
integrability on the nonstationary edge law. -/
theorem integrable_edge_product_of_density
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : μ ≪ π) (hDensity : MemLp (fun x => (μ.rnDeriv π x).toReal) 2 π)
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {f g : α → ℝ} (hf : MemLp f 4 π) (hg : MemLp g 4 π) :
    Integrable (fun z : α × α => f z.1 * g z.2) (μ ⊗ₘ K) := by
  let := holderTriple_four_four_two
  have hF := hf.comp_measurePreserving (KernelLp.measurePreserving_edge_fst π K)
  have hG := hg.comp_measurePreserving (KernelLp.measurePreserving_edge_snd π K hπ)
  have hFG : MemLp (fun z : α × α => f z.1 * g z.2) 2 (π ⊗ₘ K) := hG.mul' hF
  have hD := hDensity.comp_measurePreserving (KernelLp.measurePreserving_edge_fst π K)
  have hD' : MemLp (fun z => ((μ ⊗ₘ K).rnDeriv (π ⊗ₘ K) z).toReal) 2 (π ⊗ₘ K) := by
    apply MemLp.ae_eq ?_ hD
    filter_upwards [rnDeriv_measure_compProd_left μ π K] with z hz
    exact congrArg ENNReal.toReal hz.symm
  exact (integrable_toReal_rnDeriv_mul_iff (hμ.compProd_left K)).mp
    (hD'.integrable_mul hFG)

theorem integral_edge_product_of_density
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : μ ≪ π) (hDensity : MemLp (fun x => (μ.rnDeriv π x).toReal) 2 π)
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {f g : α → ℝ} (hf : MemLp f 4 π) (hg : MemLp g 4 π) :
    (∫ z : α × α, f z.1 * g z.2 ∂(μ ⊗ₘ K)) =
      ∫ x, f x * KernelLp.average K g x ∂μ := by
  simpa only [KernelLp.average, integral_const_mul] using
    Measure.integral_compProd (integrable_edge_product_of_density μ π hμ hDensity K hπ hf hg)

/-- Conditioning exposes the decay of the lagged observable, rather than
discarding it in a bound on the product-space norm. -/
theorem abs_edge_product_sub_le_density_L4
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : μ ≪ π) (hDensity : MemLp (fun x => (μ.rnDeriv π x).toReal) 2 π)
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {f g : α → ℝ} (hf : MemLp f 4 π) (hg : MemLp g 4 π) :
    |(∫ z : α × α, f z.1 * g z.2 ∂(μ ⊗ₘ K)) -
      ∫ z : α × α, f z.1 * g z.2 ∂(π ⊗ₘ K)| ≤
      centeredDensityL2Norm μ π * lpNorm f 4 π * lpNorm (KernelLp.average K g) 4 π := by
  let := holderTriple_four_four_two
  have hKg : MemLp (KernelLp.average K g) 4 π :=
    KernelLp.average_memLp_of_ne_top K π hπ (by norm_num) (by norm_num) hg
  have hprod : MemLp (fun x => f x * KernelLp.average K g x) 2 π := hKg.mul' hf
  rw [integral_edge_product_of_density μ π hμ hDensity K hπ hf hg,
    KernelLp.integral_edge_product π K hπ
      (hf.mono_exponent (by norm_num)) (hg.mono_exponent (by norm_num))]
  have h := abs_integral_sub_le_centeredDensityL2Norm μ π hμ hDensity hprod
  rw [← lpNorm_two_eq_sqrt_integral_sq hprod.1] at h
  calc
    _ ≤ centeredDensityL2Norm μ π * lpNorm (fun x => f x * KernelLp.average K g x) 2 π := h
    _ ≤ centeredDensityL2Norm μ π * (lpNorm f 4 π * lpNorm (KernelLp.average K g) 4 π) :=
      mul_le_mul_of_nonneg_left (lpNorm_mul_le_L4 hf hKg) (centeredDensityL2Norm_nonneg μ π)
    _ = _ := by ring

theorem integral_finitePath_pair_eq_edge
    (μ : Measure α) [IsProbabilityMeasure μ]
    (K : Kernel α α) [IsMarkovKernel K] (n : ℕ) (i j : Fin n) (hij : i ≤ j)
    {f g : α → ℝ}
    (hI : Integrable (fun z : α × α => f z.1 * g z.2)
      ((finiteKernelIterate K i.val ∘ₘ μ) ⊗ₘ finiteKernelIterate K (j.val - i.val))) :
    (∫ path, f (path i) * g (path j) ∂finiteMarkovPathLaw μ K n) =
      ∫ z : α × α, f z.1 * g z.2
        ∂((finiteKernelIterate K i.val ∘ₘ μ) ⊗ₘ finiteKernelIterate K (j.val - i.val)) := by
  have hmap := finiteMarkovPathLaw_map_pair μ K n i j hij
  have hm : Measurable (fun path : Fin n → α => (path i, path j)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have hIa : AEStronglyMeasurable (fun z : α × α => f z.1 * g z.2)
      ((finiteMarkovPathLaw μ K n).map (fun path => (path i, path j))) := by
    rw [hmap]
    exact hI.1
  have h := integral_map hm.aemeasurable hIa
  rw [hmap] at h
  exact h.symm

/-- The finite path covariance discrepancy, including its integrability,
uses the evolved law at the earlier time and the actual lag iterate. -/
theorem finitePath_pair_discrepancy_le_density_L4
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : μ ≪ π) (hDensity : MemLp (fun x => (μ.rnDeriv π x).toReal) 2 π)
    (K : Kernel α α) [IsMarkovKernel K] (hrev : Kernel.IsReversible K π)
    {f g : α → ℝ} (hf : MemLp f 4 π) (hg : MemLp g 4 π)
    (n : ℕ) (i j : Fin n) (hij : i ≤ j) :
    Integrable (fun path => f (path i) * g (path j)) (finiteMarkovPathLaw μ K n) ∧
    |(∫ path, f (path i) * g (path j) ∂finiteMarkovPathLaw μ K n) -
      ∫ path, f (path i) * g (path j) ∂finiteMarkovPathLaw π K n| ≤
      centeredDensityL2Norm (finiteKernelIterate K i.val ∘ₘ μ) π * lpNorm f 4 π *
        lpNorm (KernelLp.average (finiteKernelIterate K (j.val - i.val)) g) 4 π := by
  let ν := finiteKernelIterate K i.val ∘ₘ μ
  let Q := finiteKernelIterate K (j.val - i.val)
  have hiRev := finiteKernelIterate_isReversible K π hrev i.val
  have hQπ : Kernel.Invariant Q π := finiteKernelIterate_invariant K π hrev.invariant _
  have hν : ν ≪ π := absolutelyContinuous_comp_of_invariant μ π
    (finiteKernelIterate K i.val) hiRev.invariant hμ
  have hνLp : MemLp (fun x => (ν.rnDeriv π x).toReal) 2 π :=
    rnDeriv_comp_memLp μ π hμ hDensity (finiteKernelIterate K i.val) hiRev
  have hI := integrable_edge_product_of_density ν π hν hνLp Q hQπ hf hg
  have hIπ : Integrable (fun z : α × α => f z.1 * g z.2) (π ⊗ₘ Q) :=
    ((hf.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)).comp_measurePreserving
      (KernelLp.measurePreserving_edge_fst π Q)).integrable_mul
    ((hg.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)).comp_measurePreserving
      (KernelLp.measurePreserving_edge_snd π Q hQπ))
  have hπi : finiteKernelIterate K i.val ∘ₘ π = π :=
    finiteKernelIterate_invariant K π hrev.invariant _
  have hIπ' : Integrable (fun z : α × α => f z.1 * g z.2)
      ((finiteKernelIterate K i.val ∘ₘ π) ⊗ₘ finiteKernelIterate K (j.val - i.val)) := by
    rw [hπi]
    exact hIπ
  refine ⟨?_, ?_⟩
  · have hmp : MeasurePreserving (fun path : Fin n → α => (path i, path j))
        (finiteMarkovPathLaw μ K n) (ν ⊗ₘ Q) :=
      ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j),
        finiteMarkovPathLaw_map_pair μ K n i j hij⟩
    exact hmp.integrable_comp_of_integrable hI
  · rw [integral_finitePath_pair_eq_edge μ K n i j hij hI,
      integral_finitePath_pair_eq_edge π K n i j hij hIπ', hπi]
    exact abs_edge_product_sub_le_density_L4 ν π hν hνLp Q hQπ hf hg

end
end UniformRandomMALA.Concrete
