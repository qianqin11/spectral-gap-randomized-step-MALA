import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Tactic

/-!
# Markov integration on `Lᵖ`

Kernel averaging is defined by the actual Bochner integral. Jensen's
inequality and invariance show contraction on every finite `Lᵖ`, `p ≥ 1`.
The inputs need only be almost-everywhere strongly measurable; boundedness
and pointwise integrability at exceptional initial states are not assumed.
-/

namespace UniformRandomMALA.Concrete.KernelLp

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The Markov operator acting on real-valued functions. -/
def average (K : Kernel α β) (f : β → ℝ) (x : α) : ℝ := ∫ y, f y ∂K x

theorem aestronglyMeasurable_average (K : Kernel α β) [IsSFiniteKernel K]
    (μ : Measure α) [SFinite μ] {f : β → ℝ}
    (hf : AEStronglyMeasurable f (K ∘ₘ μ)) :
    AEStronglyMeasurable (average K f) μ := by
  rw [Measure.comp_eq_comp_const_apply] at hf
  change AEStronglyMeasurable (fun x => ∫ y, f y ∂K x) μ
  simpa only [Kernel.const_apply] using hf.integral_kernel_comp

theorem ae_aestronglyMeasurable (K : Kernel α β) [IsSFiniteKernel K]
    (μ : Measure α) [SFinite μ] {f : β → ℝ}
    (hf : AEStronglyMeasurable f (K ∘ₘ μ)) :
    ∀ᵐ x ∂μ, AEStronglyMeasurable f (K x) := by
  rw [Measure.comp_eq_comp_const_apply] at hf
  simpa using hf.comp

theorem integrable_average (K : Kernel α β) [IsSFiniteKernel K]
    (μ : Measure α) [SFinite μ] {f : β → ℝ}
    (hf : Integrable f (K ∘ₘ μ)) : Integrable (average K f) μ := by
  rw [Measure.comp_eq_comp_const_apply] at hf
  change Integrable (fun x => ∫ y, f y ∂K x) μ
  simpa only [Kernel.const_apply] using hf.integral_comp

theorem integral_average (K : Kernel α β) [IsSFiniteKernel K]
    (μ : Measure α) [SFinite μ] {f : β → ℝ}
    (hf : Integrable f (K ∘ₘ μ)) :
    ∫ x, average K f x ∂μ = ∫ y, f y ∂(K ∘ₘ μ) := by
  rw [Measure.comp_eq_comp_const_apply] at hf ⊢
  simpa [average] using (Kernel.integral_comp hf).symm

theorem integral_average_invariant (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : Kernel.Invariant K π)
    {f : α → ℝ} (hf : Integrable f π) :
    ∫ x, average K f x ∂π = ∫ x, f x ∂π := by
  have hcomp : Integrable f (K ∘ₘ π) := by rwa [hπ]
  rw [integral_average K π hcomp, hπ]

/-- Invariance makes averaging independent of the chosen almost-everywhere
representative of an `Lᵖ` function. -/
theorem average_congr_ae (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : Kernel.Invariant K π)
    {f g : α → ℝ} (hfg : f =ᵐ[π] g) : average K f =ᵐ[π] average K g := by
  have hcomp : f =ᵐ[K ∘ₘ π] g := by rwa [hπ]
  filter_upwards [Measure.ae_ae_of_ae_comp hcomp] with x hx
  exact integral_congr_ae hx

theorem average_add_ae (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : Kernel.Invariant K π)
    {f g : α → ℝ} (hf : Integrable f π) (hg : Integrable g π) :
    average K (f + g) =ᵐ[π] average K f + average K g := by
  have hfcomp : Integrable f (K ∘ₘ π) := by rwa [hπ]
  have hgcomp : Integrable g (K ∘ₘ π) := by rwa [hπ]
  filter_upwards [Measure.ae_integrable_of_integrable_comp hfcomp,
    Measure.ae_integrable_of_integrable_comp hgcomp] with x hfx hgx
  exact integral_add hfx hgx

theorem average_smul (K : Kernel α β) (c : ℝ) (f : β → ℝ) :
    average K (c • f) = c • average K f := by
  funext x
  exact integral_const_mul c f

/-- Jensen's inequality for a finite real `Lᵖ` exponent on a probability law. -/
theorem norm_integral_rpow_le {ν : Measure β} [IsProbabilityMeasure ν]
    {p : ℝ} (hp : 1 ≤ p) {f : β → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) ν) :
    ‖∫ x, f x ∂ν‖ ^ p ≤ ∫ x, ‖f x‖ ^ p ∂ν := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp
  have hfi : Integrable f ν := hf.integrable hpE
  have hpow : Integrable (fun x => ‖f x‖ ^ p) ν := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using
      hf.integrable_norm_rpow (by positivity) ENNReal.ofReal_ne_top
  calc
    ‖∫ x, f x ∂ν‖ ^ p ≤ (∫ x, ‖f x‖ ∂ν) ^ p :=
      Real.rpow_le_rpow (norm_nonneg _) (norm_integral_le_integral_norm _) hp0.le
    _ ≤ ∫ x, ‖f x‖ ^ p ∂ν :=
      (convexOn_rpow hp).map_integral_le
        (Real.continuous_rpow_const hp0.le).continuousOn isClosed_Ici
        (Filter.Eventually.of_forall fun x => norm_nonneg (f x)) hfi.norm hpow

theorem ae_memLp_of_invariant (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : Kernel.Invariant K π)
    {p : ℝ} (hp : 1 ≤ p) {f : α → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) π) :
    ∀ᵐ x ∂π, MemLp f (ENNReal.ofReal p) (K x) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpow : Integrable (fun x => ‖f x‖ ^ p) (K ∘ₘ π) := by
    rw [hπ]
    simpa only [ENNReal.toReal_ofReal hp0.le] using
      hf.integrable_norm_rpow (by positivity) ENNReal.ofReal_ne_top
  have hmeas : AEStronglyMeasurable f (K ∘ₘ π) := by rw [hπ]; exact hf.1
  filter_upwards [ae_aestronglyMeasurable K π hmeas,
    Measure.ae_integrable_of_integrable_comp hpow] with x hx hxp
  rw [← integrable_norm_rpow_iff hx (by positivity : ENNReal.ofReal p ≠ 0)
    ENNReal.ofReal_ne_top]
  simpa only [ENNReal.toReal_ofReal hp0.le] using hxp

/-- Invariance turns pointwise Jensen into a global `p`th-moment bound. -/
theorem integral_norm_average_rpow_le (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : Kernel.Invariant K π)
    {p : ℝ} (hp : 1 ≤ p) {f : α → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) π) :
    Integrable (fun x => ‖average K f x‖ ^ p) π ∧
      (∫ x, ‖average K f x‖ ^ p ∂π) ≤ ∫ x, ‖f x‖ ^ p ∂π := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpow : Integrable (fun x => ‖f x‖ ^ p) π := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using
      hf.integrable_norm_rpow (by positivity) ENNReal.ofReal_ne_top
  have hpowComp : Integrable (fun x => ‖f x‖ ^ p) (K ∘ₘ π) := by rwa [hπ]
  have hmajor := integrable_average K π hpowComp
  have hmeas : AEStronglyMeasurable (average K f) π :=
    aestronglyMeasurable_average K π (by rw [hπ]; exact hf.1)
  have hle : ∀ᵐ x ∂π, ‖average K f x‖ ^ p ≤ average K (fun y => ‖f y‖ ^ p) x := by
    filter_upwards [ae_memLp_of_invariant K π hπ hp hf] with x hx
    exact norm_integral_rpow_le hp hx
  have hInt : Integrable (fun x => ‖average K f x‖ ^ p) π :=
    hmajor.mono_nonneg
      ((Real.continuous_rpow_const hp0.le).comp_aestronglyMeasurable hmeas.norm)
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _) hle
  refine ⟨hInt, (integral_mono_ae hInt hmajor hle).trans_eq ?_⟩
  exact integral_average_invariant K π hπ hpow

/-- Markov averaging preserves each finite `Lᵖ`, including `L²` and `L⁴`. -/
theorem average_memLp (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : Kernel.Invariant K π)
    {p : ℝ} (hp : 1 ≤ p) {f : α → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) π) :
    MemLp (average K f) (ENNReal.ofReal p) π := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  rw [← integrable_norm_rpow_iff
    (aestronglyMeasurable_average K π (by rw [hπ]; exact hf.1))
    (by positivity : ENNReal.ofReal p ≠ 0) ENNReal.ofReal_ne_top]
  simpa only [ENNReal.toReal_ofReal hp0.le] using
    (integral_norm_average_rpow_le K π hπ hp hf).1

/-- Every finite `Lᵖ` norm contracts under an invariant Markov kernel. -/
theorem lpNorm_average_le (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : Kernel.Invariant K π)
    {p : ℝ} (hp : 1 ≤ p) {f : α → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) π) :
    lpNorm (average K f) (ENNReal.ofReal p) π ≤ lpNorm f (ENNReal.ofReal p) π := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) ENNReal.ofReal_ne_top
    (average_memLp K π hπ hp hf).1,
    lpNorm_eq_integral_norm_rpow_toReal (by positivity) ENNReal.ofReal_ne_top hf.1,
    ENNReal.toReal_ofReal hp0.le]
  exact Real.rpow_le_rpow (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _)
    (integral_norm_average_rpow_le K π hπ hp hf).2 (inv_nonneg.mpr hp0.le)

theorem average_memLp_of_ne_top (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : Kernel.Invariant K π)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hpt : p ≠ ∞) {f : α → ℝ}
    (hf : MemLp f p π) : MemLp (average K f) p π := by
  have hp : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_le_toReal ENNReal.one_ne_top hpt).2 hp1
  simpa only [ENNReal.ofReal_toReal hpt] using
    average_memLp K π hπ hp (by simpa only [ENNReal.ofReal_toReal hpt] using hf)

theorem lpNorm_average_le_of_ne_top (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : Kernel.Invariant K π)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hpt : p ≠ ∞) {f : α → ℝ}
    (hf : MemLp f p π) : lpNorm (average K f) p π ≤ lpNorm f p π := by
  have hp : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_le_toReal ENNReal.one_ne_top hpt).2 hp1
  simpa only [ENNReal.ofReal_toReal hpt] using
    lpNorm_average_le K π hπ hp (by simpa only [ENNReal.ofReal_toReal hpt] using hf)

end
end UniformRandomMALA.Concrete.KernelLp
