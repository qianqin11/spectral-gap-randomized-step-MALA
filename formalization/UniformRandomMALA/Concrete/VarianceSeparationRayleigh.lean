import UniformRandomMALA.Concrete.VarianceSeparationExtended

/-!
# Unit-variance witnesses near the Rayleigh infimum

The witnesses come from the actual definition of the spectral gap and are
centered and rescaled inside the genuine `L²` space.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory KernelLp
open scoped ENNReal ProbabilityTheory RealInnerProductSpace

noncomputable section
variable {α : Type*} [MeasurableSpace α]

private theorem inner_smul_dirichlet {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (P : E →L[ℝ] E) (r : ℝ) (f : E) :
    ⟪r • f, r • f - P (r • f)⟫ = r ^ 2 * ⟪f, f - P f⟫ := by
  rw [map_smul, ← smul_sub, real_inner_smul_left, real_inner_smul_right]
  ring

theorem centeredL2_variance_eq_norm_sq (π : Measure α) [IsProbabilityMeasure π]
    (f : centeredL2 π) : variance (f : Lp ℝ 2 π) π = ‖f‖ ^ 2 := by
  rw [variance_eq_sub (Lp.memLp (f : Lp ℝ 2 π)), centeredL2_integral]
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero]
  change (∫ x, (f : Lp ℝ 2 π) x ^ 2 ∂π) = ‖(f : Lp ℝ 2 π)‖ ^ 2
  exact integral_sq_eq_norm_sq π _

theorem centeredObservableL2_energy_eq (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {f : α → ℝ} (hm : Measurable f) (hf : MemLp f 2 π) :
    Dirichlet.energy π K (centeredObservableL2 π f hf : Lp ℝ 2 π) = Dirichlet.energy π K f := by
  let F := centeredObservableL2 π f hf
  have hF := centeredObservableL2_coeFn π f hf
  rw [energy_eq_edgeMeasure_lintegral π K _ (Lp.stronglyMeasurable (F : Lp ℝ 2 π)).measurable,
    energy_eq_edgeMeasure_lintegral π K f hm]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [(measurePreserving_edge_fst π K).quasiMeasurePreserving.ae hF,
    (measurePreserving_edge_snd π K hπ).quasiMeasurePreserving.ae hF] with z hz1 hz2
  rw [hz1, hz2]
  congr 2
  ring

theorem centeredObservableL2_ofReal_energy (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {f : α → ℝ} (hm : Measurable f) (hf : MemLp f 2 π) :
    ENNReal.ofReal ⟪centeredObservableL2 π f hf,
      centeredObservableL2 π f hf - centeredOperator K π hπ (centeredObservableL2 π f hf)⟫ =
        Dirichlet.energy π K f := by
  let F := centeredObservableL2 π f hf
  change ENNReal.ofReal ⟪(F : Lp ℝ 2 π),
    (F : Lp ℝ 2 π) - operator K π hπ 2 (by norm_num) (F : Lp ℝ 2 π)⟫ = _
  rw [inner_sub_right, real_inner_self_eq_norm_sq, inner_operator,
    ← integral_sq_eq_norm_sq π (F : Lp ℝ 2 π),
    ← KernelLp.energy_eq_ofReal π K hπ (Lp.stronglyMeasurable (F : Lp ℝ 2 π)).measurable
      (Lp.memLp (F : Lp ℝ 2 π))]
  exact centeredObservableL2_energy_eq π K hπ hm hf

/-- Any strict upper threshold for the Rayleigh infimum has a centered,
unit-variance witness below that threshold. -/
theorem exists_centered_unit_energy_lt (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {β : ℝ} (hβ : 0 < β) (hlt : rayleighSpectralGap π K < ENNReal.ofReal β) :
    ∃ f : centeredL2 π, ‖f‖ = 1 ∧ ⟪f, f - centeredOperator K π hπ f⟫ < β := by
  obtain ⟨t, ht⟩ := iInf_lt_iff.mp hlt
  let F := centeredObservableL2 π t t.memLp_toFun
  have hv : 0 < variance t π := ENNReal.ofReal_ne_zero_iff.mp (by
    rw [t.memLp_toFun.ofReal_variance_eq]
    exact t.evariance_ne_zero)
  have hn2 : ‖F‖ ^ 2 = variance t π := centeredObservableL2_norm_sq π t t.memLp_toFun
  have hn : 0 < ‖F‖ := by nlinarith [norm_nonneg F]
  have he := centeredObservableL2_ofReal_energy π K hπ t.measurable_toFun t.memLp_toFun
  have hv' : evariance t π = ENNReal.ofReal (‖F‖ ^ 2) := by
    rw [hn2, t.memLp_toFun.ofReal_variance_eq]
  change Dirichlet.energy π K t / evariance t π < ENNReal.ofReal β at ht
  rw [← he, hv', ← ENNReal.ofReal_div_of_pos (sq_pos_of_pos hn)] at ht
  have henergy : ⟪F, F - centeredOperator K π hπ F⟫ / ‖F‖ ^ 2 < β :=
    (ENNReal.ofReal_lt_ofReal_iff hβ).mp ht
  let G : centeredL2 π := ‖F‖⁻¹ • F
  refine ⟨G, ?_, ?_⟩
  · simp only [G, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
    exact inv_mul_cancel₀ hn.ne'
  · have heq : ⟪G, G - centeredOperator K π hπ G⟫ =
        ⟪F, F - centeredOperator K π hπ F⟫ / ‖F‖ ^ 2 := by
      calc
        ⟪G, G - centeredOperator K π hπ G⟫ =
            (‖F‖⁻¹) ^ 2 * ⟪F, F - centeredOperator K π hπ F⟫ :=
          inner_smul_dirichlet (centeredOperator K π hπ) ‖F‖⁻¹ F
        _ = _ := by ring
    rwa [heq]

end
end UniformRandomMALA.Concrete
