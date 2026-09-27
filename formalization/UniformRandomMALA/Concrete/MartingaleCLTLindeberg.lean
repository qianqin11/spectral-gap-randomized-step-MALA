import UniformRandomMALA.Concrete.MartingaleCLTConditional

/-! # Conditional Lindeberg tails control the stopped variance clock -/

namespace UniformRandomMALA.Concrete.MartingaleDifferenceRow

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ProbabilityTheory ENNReal

noncomputable section
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

def tailTerm (D : MartingaleDifferenceRow μ) (δ : ℝ) (k : ℕ) (x : Ω) : ℝ :=
  if δ < |D.increment k x| then D.increment k x ^ 2 else 0

omit [IsProbabilityMeasure μ] in
theorem tailTerm_nonneg (D : MartingaleDifferenceRow μ) (δ : ℝ) (k : ℕ) (x : Ω) :
    0 ≤ D.tailTerm δ k x := by unfold tailTerm; split_ifs <;> positivity

omit [IsProbabilityMeasure μ] in
theorem tailTerm_le_sq (D : MartingaleDifferenceRow μ) (δ : ℝ) (k : ℕ) (x : Ω) :
    D.tailTerm δ k x ≤ D.increment k x ^ 2 := by
  unfold tailTerm
  split_ifs <;> simp [sq_nonneg]

omit [IsProbabilityMeasure μ] in
theorem tailTerm_measurable (D : MartingaleDifferenceRow μ) (δ : ℝ) (k : ℕ) :
    Measurable (D.tailTerm δ k) := by
  have hm : Measurable (D.increment k) :=
    ((D.measurable k).mono (D.filtration.le (k + 1))).measurable
  have ha : Measurable (fun x => |D.increment k x|) := continuous_abs.measurable.comp hm
  exact (hm.pow_const 2).ite (measurableSet_lt measurable_const ha) measurable_const

omit [IsProbabilityMeasure μ] in
theorem tailTerm_integrable (D : MartingaleDifferenceRow μ) (δ : ℝ) (k : ℕ) :
    Integrable (D.tailTerm δ k) μ :=
  (D.memLp k).integrable_sq.mono_nonneg (D.tailTerm_measurable δ k).aestronglyMeasurable
    (Filter.Eventually.of_forall (D.tailTerm_nonneg δ k))
    (Filter.Eventually.of_forall (D.tailTerm_le_sq δ k))

def conditionalTail (D : MartingaleDifferenceRow μ) (δ : ℝ) (k : ℕ) (x : Ω) : ℝ :=
  max 0 (μ[D.tailTerm δ k | D.filtration k] x)

omit [IsProbabilityMeasure μ] in
theorem conditionalTail_nonneg (D : MartingaleDifferenceRow μ) (δ : ℝ) (k : ℕ) (x : Ω) :
    0 ≤ D.conditionalTail δ k x := le_max_left _ _

omit [IsProbabilityMeasure μ] in
theorem conditionalTail_eq_condExp (D : MartingaleDifferenceRow μ) (δ : ℝ) (k : ℕ) :
    D.conditionalTail δ k =ᵐ[μ] μ[D.tailTerm δ k | D.filtration k] := by
  filter_upwards [condExp_nonneg (m := D.filtration k)
    (Filter.Eventually.of_forall (D.tailTerm_nonneg δ k))] with x hx
  exact max_eq_right hx

omit [IsProbabilityMeasure μ] in
theorem conditionalTail_integrable (D : MartingaleDifferenceRow μ) (δ : ℝ) (k : ℕ) :
    Integrable (D.conditionalTail δ k) μ :=
  integrable_condExp.congr (D.conditionalTail_eq_condExp δ k).symm

theorem integral_conditionalTail (D : MartingaleDifferenceRow μ) (δ : ℝ) (k : ℕ) :
    ∫ x, D.conditionalTail δ k x ∂μ = ∫ x, D.tailTerm δ k x ∂μ := by
  rw [integral_congr_ae (D.conditionalTail_eq_condExp δ k)]
  exact integral_condExp (D.filtration.le k)

theorem conditionalVariance_le_sq_add_tail (D : MartingaleDifferenceRow μ)
    {δ : ℝ} (hδ : 0 ≤ δ) (k : ℕ) :
    ∀ᵐ x ∂μ, D.conditionalVariance k x ≤ δ ^ 2 + D.conditionalTail δ k x := by
  have hp (x : Ω) : D.increment k x ^ 2 ≤ δ ^ 2 + D.tailTerm δ k x := by
    unfold tailTerm
    split_ifs with h
    · nlinarith [sq_nonneg δ]
    · have hs : |D.increment k x| ≤ δ := le_of_not_gt h
      have hsq := (sq_le_sq₀ (abs_nonneg (D.increment k x)) hδ).2 hs
      simpa only [sq_abs, add_zero] using hsq
  have hmono := condExp_mono (m := D.filtration k) (D.memLp k).integrable_sq
    ((integrable_const (δ ^ 2)).add (D.tailTerm_integrable δ k)) (Filter.Eventually.of_forall hp)
  have hadd := condExp_add (m := D.filtration k) (integrable_const (δ ^ 2))
    (D.tailTerm_integrable δ k)
  rw [condExp_const (D.filtration.le k)] at hadd
  filter_upwards [hmono, hadd, D.conditionalVariance_eq_condExp k,
    D.conditionalTail_eq_condExp δ k] with x hle heq hv ht
  rw [hv, ht]
  simpa only [Pi.add_apply, heq] using hle

omit [IsProbabilityMeasure μ] in
theorem stoppedVariance_measurable (D : MartingaleDifferenceRow μ) (C : ℝ) (k : ℕ) :
    StronglyMeasurable[D.filtration k]
      (fun x => stoppedVariance (fun j => D.conditionalVariance j x) C k) := by
  have heq : (fun x => stoppedVariance (fun j => D.conditionalVariance j x) C k) =
      (D.beforeVarianceCap C k).indicator (D.conditionalVariance k) := by
    funext x
    rfl
  rw [heq]
  exact (D.conditionalVariance_measurable k).indicator (D.beforeVarianceCap_measurable C k)

theorem stoppedVariance_memLp (D : MartingaleDifferenceRow μ) {C : ℝ} (hC : 0 ≤ C)
    (k : ℕ) (p : ℝ≥0∞) :
    MemLp (fun x => stoppedVariance (fun j => D.conditionalVariance j x) C k) p μ := by
  apply MemLp.of_bound ((D.stoppedVariance_measurable C k).mono (D.filtration.le k)).aestronglyMeasurable C
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg
    (stoppedVariance_nonneg (fun j => D.conditionalVariance_nonneg j x) C k)]
  exact stoppedVariance_le_cap (fun j => D.conditionalVariance_nonneg j x) hC k

theorem integral_sum_sq_stoppedVariance_le (D : MartingaleDifferenceRow μ)
    {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ) (n : ℕ) :
    (∫ x, ∑ k ∈ range n, stoppedVariance (fun j => D.conditionalVariance j x) C k ^ 2 ∂μ) ≤
      δ ^ 2 * C + C * ∑ k ∈ range n, ∫ x, D.tailTerm δ k x ∂μ := by
  have hleft : Integrable (fun x => ∑ k ∈ range n,
      stoppedVariance (fun j => D.conditionalVariance j x) C k ^ 2) μ :=
    integrable_finsetSum (range n) fun k _ => (D.stoppedVariance_memLp hC k 2).integrable_sq
  have hsum : Integrable (fun x => ∑ k ∈ range n, D.conditionalTail δ k x) μ :=
    integrable_finsetSum (range n) fun k _ => D.conditionalTail_integrable δ k
  have hright : Integrable (fun x => δ ^ 2 * C + C *
      ∑ k ∈ range n, D.conditionalTail δ k x) μ := (integrable_const _).add (hsum.const_mul C)
  have hp : ∀ᵐ x ∂μ, (∑ k ∈ range n,
      stoppedVariance (fun j => D.conditionalVariance j x) C k ^ 2) ≤
      δ ^ 2 * C + C * ∑ k ∈ range n, D.conditionalTail δ k x := by
    filter_upwards [ae_all_iff.2 (fun k => D.conditionalVariance_le_sq_add_tail hδ k)] with x hx
    exact sum_sq_stoppedVariance_le (fun k => D.conditionalVariance_nonneg k x)
      (fun k => D.conditionalTail_nonneg δ k x) hC δ n (fun k _ => hx k)
  have h := integral_mono_ae hleft hright hp
  rw [integral_add (integrable_const _) (hsum.const_mul C), integral_const,
    integral_const_mul, integral_finsetSum (range n) (fun k _ => D.conditionalTail_integrable δ k)] at h
  simpa only [probReal_univ, smul_eq_mul, one_mul, integral_conditionalTail] using h

end
end UniformRandomMALA.Concrete.MartingaleDifferenceRow
