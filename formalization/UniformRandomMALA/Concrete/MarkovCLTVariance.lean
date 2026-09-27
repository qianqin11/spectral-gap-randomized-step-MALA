import UniformRandomMALA.Concrete.MarkovCLTPoisson

/-! # Identification of the actual Poisson-increment variance -/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory KernelLp
open scoped ENNReal ProbabilityTheory RealInnerProductSpace

noncomputable section
variable {α : Type*} [MeasurableSpace α]

theorem resolvent_poissonEquation_ae
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    (f : centeredL2 π) {g : ℝ} (hg : 0 < g) (hg2 : g ≤ 2)
    (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π K) :
    let u := poissonResolvent (centeredOperator K π hπ) f
    (fun x => (u : Lp ℝ 2 π) x - KernelLp.average K (u : Lp ℝ 2 π) x)
      =ᵐ[π] (f : Lp ℝ 2 π) := by
  intro u
  have h := poissonResolvent_sub (centeredOperator K π hπ)
    (norm_halfLazyOperator_lt_one _ (norm_centeredOperator_le K π hπ) hg hg2
      (centeredOperator_rightGap K π hπ hg.le hgap)) f
  have heq : (u : Lp ℝ 2 π) - operator K π hπ 2 (by norm_num) (u : Lp ℝ 2 π) =
      (f : Lp ℝ 2 π) := congrArg (fun v : centeredL2 π => (v : Lp ℝ 2 π)) h
  filter_upwards [Lp.coeFn_sub (u : Lp ℝ 2 π)
    (operator K π hπ 2 (by norm_num) (u : Lp ℝ 2 π)),
    operator_coeFn K π hπ 2 (by norm_num) (u : Lp ℝ 2 π)] with x hx hop
  rw [heq] at hx
  simpa only [Pi.sub_apply, hop] using hx.symm

theorem poissonIncrement_secondMoment
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    (u : Lp ℝ 2 π) :
    (∫ z : α × α, poissonIncrement K u z.1 z.2 ^ 2 ∂(π ⊗ₘ K)) =
      ‖u‖ ^ 2 - ‖operator K π hπ 2 (by norm_num) u‖ ^ 2 := by
  have hu := Lp.memLp u
  have hv : MemLp (KernelLp.average K u) 2 π :=
    average_memLp_of_ne_top K π hπ (by norm_num) (by norm_num) hu
  have hU := hu.comp_measurePreserving (measurePreserving_edge_snd π K hπ)
  have hV := hv.comp_measurePreserving (measurePreserving_edge_fst π K)
  have hU2 : Integrable (fun z : α × α => u z.2 ^ 2) (π ⊗ₘ K) := hU.integrable_sq
  have hV2 : Integrable (fun z : α × α => KernelLp.average K u z.1 ^ 2) (π ⊗ₘ K) :=
    hV.integrable_sq
  have hUV : Integrable (fun z : α × α => KernelLp.average K u z.1 * u z.2)
      (π ⊗ₘ K) := hV.integrable_mul hU
  have hfirst : (∫ z : α × α, u z.2 ^ 2 ∂(π ⊗ₘ K)) = ‖u‖ ^ 2 := by
    have hm : AEStronglyMeasurable (fun x => u x ^ 2) ((π ⊗ₘ K).map Prod.snd) := by
      change AEStronglyMeasurable _ (π ⊗ₘ K).snd
      rw [Measure.snd_compProd, hπ]
      exact hu.integrable_sq.1
    rw [← integral_map measurable_snd.aemeasurable hm]
    change (∫ x, u x ^ 2 ∂(π ⊗ₘ K).snd) = _
    rw [Measure.snd_compProd, hπ, integral_sq_eq_norm_sq]
  have hlast : (∫ z : α × α, KernelLp.average K u z.1 ^ 2 ∂(π ⊗ₘ K)) =
      ∫ x, KernelLp.average K u x ^ 2 ∂π := by
    have hm : AEStronglyMeasurable (fun x => KernelLp.average K u x ^ 2)
        ((π ⊗ₘ K).map Prod.fst) := by
      change AEStronglyMeasurable _ (π ⊗ₘ K).fst
      rw [Measure.fst_compProd]
      exact hv.integrable_sq.1
    rw [← integral_map measurable_fst.aemeasurable hm]
    change (∫ x, KernelLp.average K u x ^ 2 ∂(π ⊗ₘ K).fst) = _
    rw [Measure.fst_compProd]
  have hcross : (∫ z : α × α, KernelLp.average K u z.1 * u z.2 ∂(π ⊗ₘ K)) =
      ∫ x, KernelLp.average K u x ^ 2 ∂π := by
    rw [integral_edge_product π K hπ hv hu]
    simp only [pow_two]
  have hop : (∫ x, KernelLp.average K u x ^ 2 ∂π) =
      ‖operator K π hπ 2 (by norm_num) u‖ ^ 2 := by
    rw [← integral_sq_eq_norm_sq]
    apply integral_congr_ae
    filter_upwards [operator_coeFn K π hπ 2 (by norm_num) u] with x hx
    rw [hx]
  have heq (z : α × α) : poissonIncrement K u z.1 z.2 ^ 2 =
      (u z.2 ^ 2 - 2 * (KernelLp.average K u z.1 * u z.2)) +
        KernelLp.average K u z.1 ^ 2 := by
    simp only [poissonIncrement]
    ring
  have hdiff : Integrable (fun z : α × α =>
      u z.2 ^ 2 - 2 * (KernelLp.average K u z.1 * u z.2)) (π ⊗ₘ K) :=
    hU2.sub (hUV.const_mul 2)
  simp_rw [heq]
  rw [integral_add hdiff hV2,
    integral_sub hU2 (hUV.const_mul 2), integral_const_mul,
    hfirst, hlast, hcross, hop]
  ring

theorem norm_sub_poisson_variance {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u p f : E} (h : u - p = f) :
    ‖u‖ ^ 2 - ‖p‖ ^ 2 = 2 * ⟪f, u⟫ - ‖f‖ ^ 2 := by
  rw [← h, inner_sub_left, real_inner_self_eq_norm_sq, norm_sub_sq_real,
    real_inner_comm p u]
  ring

/-- The conditional-increment variance equals the actual asymptotic
variance, so a subsequent martingale CLT has exactly the paper's variance. -/
theorem resolvent_increment_variance_eq_asymptoticVariance
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    (f : centeredL2 π) {g : ℝ} (hg : 0 < g) (hg2 : g ≤ 2)
    (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π K) :
    let u := poissonResolvent (centeredOperator K π hπ) f
    (∫ z : α × α, poissonIncrement K (u : Lp ℝ 2 π) z.1 z.2 ^ 2 ∂(π ⊗ₘ K)) =
      stationaryAsymptoticVariance π K (f : Lp ℝ 2 π) := by
  intro u
  rw [poissonIncrement_secondMoment π K hπ,
    stationaryAsymptoticVariance_centered_eq π K hπ f hg hg2 hgap]
  have h := poissonResolvent_sub (centeredOperator K π hπ)
    (norm_halfLazyOperator_lt_one _ (norm_centeredOperator_le K π hπ) hg hg2
      (centeredOperator_rightGap K π hπ hg.le hgap)) f
  change ‖u‖ ^ 2 - ‖centeredOperator K π hπ u‖ ^ 2 = _
  exact norm_sub_poisson_variance h

theorem poissonIncrement_memLp
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {u : α → ℝ} (hu : MemLp u 2 π) :
    MemLp (fun z : α × α => poissonIncrement K u z.1 z.2) 2 (π ⊗ₘ K) := by
  have hv : MemLp (KernelLp.average K u) 2 π :=
    average_memLp_of_ne_top K π hπ (by norm_num) (by norm_num) hu
  exact (hu.comp_measurePreserving (measurePreserving_edge_snd π K hπ)).sub
    (hv.comp_measurePreserving (measurePreserving_edge_fst π K))

/-- Conditional variance of the actual centered transition increment. -/
def poissonConditionalVariance (K : Kernel α α) (u : α → ℝ) (x : α) : ℝ :=
  ∫ y, poissonIncrement K u x y ^ 2 ∂K x

theorem poissonConditionalVariance_nonneg (K : Kernel α α) (u : α → ℝ) (x : α) :
    0 ≤ poissonConditionalVariance K u x := integral_nonneg fun _ => sq_nonneg _

theorem poissonConditionalVariance_integrable
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {u : α → ℝ} (hu : MemLp u 2 π) : Integrable (poissonConditionalVariance K u) π := by
  have hi := (poissonIncrement_memLp π K hπ hu).integrable_sq
  have hq := ((Measure.integrable_compProd_iff hi.1).1 hi).2
  change Integrable (fun x => ∫ y, poissonIncrement K u x y ^ 2 ∂K x) π
  simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using hq

theorem integral_poissonConditionalVariance
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {u : α → ℝ} (hu : MemLp u 2 π) :
    ∫ x, poissonConditionalVariance K u x ∂π =
      ∫ z : α × α, poissonIncrement K u z.1 z.2 ^ 2 ∂(π ⊗ₘ K) :=
  (Measure.integral_compProd (poissonIncrement_memLp π K hπ hu).integrable_sq).symm

end
end UniformRandomMALA.Concrete
