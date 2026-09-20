import UniformRandomMALA.Concrete.L2MixingBase
import UniformRandomMALA.Concrete.RayleighSpectralGap
import UniformRandomMALA.Concrete.Conductance

/-! # Stationary and reversible integral identities for bounded observables -/

namespace UniformRandomMALA.Concrete
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
noncomputable section
variable {α : Type*} [MeasurableSpace α]
namespace BoundedObservable

theorem inner_average_symm (π : Measure α) [IsFiniteMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hrev : Kernel.IsReversible K π)
    (f g : BoundedObservable α) :
    inner π f (g.average K) = inner π g (f.average K) := by
  rw [← integral_edge_product, ← integral_edge_product]
  have hs := edgeMeasure_map_swap π K hrev
  have hm : Measurable (fun z : α × α => f z.1 * g z.2) :=
    (f.measurable_toFun.comp measurable_fst).mul (g.measurable_toFun.comp measurable_snd)
  have hi := integral_map (μ := π ⊗ₘ K) measurable_swap.aemeasurable hm.aestronglyMeasurable
  rw [show (π ⊗ₘ K).map Prod.swap = π ⊗ₘ K from hs] at hi
  simpa [mul_comm] using hi

theorem integral_edge_fst (π : Measure α) [IsFiniteMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (f : BoundedObservable α) :
    (∫ z, f z.1 ∂(π ⊗ₘ K)) = ∫ x, f x ∂π := by
  rw [← integral_map measurable_fst.aemeasurable f.measurable_toFun.aestronglyMeasurable]
  change ∫ x, f x ∂(π ⊗ₘ K).fst = _
  rw [Measure.fst_compProd]

theorem integral_edge_snd (π : Measure α) [IsFiniteMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    (f : BoundedObservable α) :
    (∫ z, f z.2 ∂(π ⊗ₘ K)) = ∫ x, f x ∂π := by
  rw [← integral_map measurable_snd.aemeasurable f.measurable_toFun.aestronglyMeasurable]
  change ∫ x, f x ∂(π ⊗ₘ K).snd = _
  rw [Measure.snd_compProd, hπ]

/-- Dirichlet energy as a difference of an `L²` norm and a kernel inner
product; the proof is the stationary edge-measure square expansion. -/
theorem energy_eq_ofReal (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    (f : BoundedObservable α) :
    Dirichlet.energy π K f = ENNReal.ofReal (f.sqNorm π - inner π f (f.average K)) := by
  let F : BoundedObservable (α × α) := f.comp Prod.fst measurable_fst
  let G : BoundedObservable (α × α) := f.comp Prod.snd measurable_snd
  have hsq : Integrable (fun z : α × α => (f z.1 - f z.2) ^ 2) (π ⊗ₘ K) := by
    simpa [add, smul, comp, F, G, sub_eq_add_neg] using
      ((F.add (G.smul (-1))).memLp (π ⊗ₘ K) 2).integrable_sq
  have heq : (∫ z : α × α, (f z.1 - f z.2) ^ 2 ∂(π ⊗ₘ K)) =
      2 * (f.sqNorm π - inner π f (f.average K)) := by
    have hF2 : Integrable (fun z => F z ^ 2) (π ⊗ₘ K) := (F.memLp (π ⊗ₘ K) 2).integrable_sq
    have hG2 : Integrable (fun z => G z ^ 2) (π ⊗ₘ K) := (G.memLp (π ⊗ₘ K) 2).integrable_sq
    have hFG : Integrable (fun z => F z * G z) (π ⊗ₘ K) := (F.mul G).integrable (π ⊗ₘ K)
    have hdiff : Integrable (fun z => F z ^ 2 - 2 * (F z * G z)) (π ⊗ₘ K) :=
      hF2.sub (hFG.const_mul 2)
    simp_rw [sub_sq, mul_assoc]
    change (∫ z : α × α, F z ^ 2 - 2 * (F z * G z) + G z ^ 2 ∂(π ⊗ₘ K)) = _
    rw [integral_add hdiff hG2,
      integral_sub hF2 (hFG.const_mul 2)]
    change ((∫ z : α × α, f z.1 ^ 2 ∂(π ⊗ₘ K)) -
      (∫ z : α × α, 2 * (f z.1 * f z.2) ∂(π ⊗ₘ K))) +
      (∫ z : α × α, f z.2 ^ 2 ∂(π ⊗ₘ K)) = _
    rw [integral_const_mul]
    have hfst := integral_edge_fst π K (f.mul f)
    have hsnd := integral_edge_snd π K hπ (f.mul f)
    simp only [mul, ← pow_two] at hfst hsnd
    rw [hfst, hsnd, integral_edge_product]
    unfold sqNorm
    ring
  rw [energy_eq_edgeMeasure_lintegral π K f f.measurable_toFun]
  change (2 : ℝ≥0∞)⁻¹ * (∫⁻ z : α × α, ENNReal.ofReal ((f z.1 - f z.2) ^ 2)
    ∂(π ⊗ₘ K)) = _
  rw [← ofReal_integral_eq_lintegral_ofReal hsq
    (Filter.Eventually.of_forall fun _ => sq_nonneg _), heq,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num [← mul_assoc]
  rw [ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num), one_mul]

theorem inner_average_le_sqNorm (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    (f : BoundedObservable α) :
    inner π f (f.average K) ≤ f.sqNorm π := by
  have hn := (f.add ((f.average K).smul (-1))).sqNorm_nonneg π
  rw [sqNorm_add, inner_smul_right] at hn
  have heq : ((f.average K).smul (-1)).sqNorm π = (f.average K).sqNorm π := by
    simp [sqNorm, smul]
  rw [heq] at hn
  have hc := f.integral_sq_average_le K π hπ
  change (f.average K).sqNorm π ≤ f.sqNorm π at hc
  nlinarith

/-- A stationary Markov kernel has Rayleigh gap at most two whenever the
state space admits a nonzero centered bounded observable.  The explicit
witness excludes the empty Rayleigh-test family on a one-point space. -/
theorem rayleighSpectralGap_le_two (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    (f : BoundedObservable α) (hf : ∫ x, f x ∂π = 0)
    (hpos : 0 < f.sqNorm π) : rayleighSpectralGap π K ≤ 2 := by
  have hv : evariance f π = ENNReal.ofReal (f.sqNorm π) := by
    rw [← (f.memLp π 2).ofReal_variance_eq, variance_eq_sub (f.memLp π 2), hf]
    simp [sqNorm]
  have hv0 : evariance f π ≠ 0 := by
    rw [hv]
    exact ENNReal.ofReal_ne_zero_iff.mpr hpos
  let test : L2RayleighTest π := ⟨f, f.measurable_toFun, f.memLp π 2, hv0⟩
  have hi : rayleighSpectralGap π K ≤ rayleighQuotient π K test :=
    iInf_le (fun t : L2RayleighTest π => rayleighQuotient π K t) test
  have hn := (f.add (f.average K)).sqNorm_nonneg π
  rw [sqNorm_add] at hn
  have hc := f.integral_sq_average_le K π hπ
  change (f.average K).sqNorm π ≤ f.sqNorm π at hc
  have hcross : -f.sqNorm π ≤ inner π f (f.average K) := by nlinarith
  apply hi.trans
  change Dirichlet.energy π K f / evariance f π ≤ 2
  apply (ENNReal.div_le_iff hv0 (f.memLp π 2).evariance_ne_top).2
  rw [energy_eq_ofReal π K hπ, hv]
  have hreal : f.sqNorm π - inner π f (f.average K) ≤ 2 * f.sqNorm π := by linarith
  simpa [ENNReal.ofReal_mul] using ENNReal.ofReal_le_ofReal hreal


end BoundedObservable
end
end UniformRandomMALA.Concrete
