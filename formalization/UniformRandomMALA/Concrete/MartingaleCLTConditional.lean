import UniformRandomMALA.Concrete.MartingaleCLTStopping
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.Analysis.Complex.Exponential

/-! # Conditional identities for a genuine triangular martingale CLT -/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ProbabilityTheory ENNReal

noncomputable section
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- One row of martingale differences, with the ordinary conditional
expectation formulation. The array theorem will allow this probability
space and filtration to depend on the row. -/
structure MartingaleDifferenceRow (μ : Measure Ω) where
  length : ℕ
  filtration : Filtration ℕ mΩ
  increment : ℕ → Ω → ℝ
  memLp : ∀ k, MemLp (increment k) 2 μ
  measurable : ∀ k, StronglyMeasurable[filtration (k + 1)] (increment k)
  mean_zero : ∀ k, μ[increment k | filtration k] =ᵐ[μ] 0

namespace MartingaleDifferenceRow

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A everywhere nonnegative version of the conditional variance. -/
def conditionalVariance (D : MartingaleDifferenceRow μ) (k : ℕ) (ω : Ω) : ℝ :=
  max 0 (μ[fun x => D.increment k x ^ 2 | D.filtration k] ω)

omit [IsProbabilityMeasure μ] in
theorem conditionalVariance_nonneg (D : MartingaleDifferenceRow μ) (k : ℕ) (ω : Ω) :
    0 ≤ D.conditionalVariance k ω := le_max_left _ _

omit [IsProbabilityMeasure μ] in
theorem conditionalVariance_eq_condExp (D : MartingaleDifferenceRow μ) (k : ℕ) :
    D.conditionalVariance k =ᵐ[μ] μ[fun x => D.increment k x ^ 2 | D.filtration k] := by
  filter_upwards [condExp_nonneg (m := D.filtration k)
    (Filter.Eventually.of_forall fun x => sq_nonneg (D.increment k x))] with x hx
  exact max_eq_right hx

omit [IsProbabilityMeasure μ] in
theorem conditionalVariance_measurable (D : MartingaleDifferenceRow μ) (k : ℕ) :
    StronglyMeasurable[D.filtration k] (D.conditionalVariance k) := by
  have hm : Measurable[D.filtration k] (D.conditionalVariance k) :=
    measurable_const.max stronglyMeasurable_condExp.measurable
  exact hm.stronglyMeasurable

omit [IsProbabilityMeasure μ] in
theorem conditionalVariance_integrable (D : MartingaleDifferenceRow μ) (k : ℕ) :
    Integrable (D.conditionalVariance k) μ :=
  integrable_condExp.congr (D.conditionalVariance_eq_condExp k).symm

theorem integral_conditionalVariance (D : MartingaleDifferenceRow μ) (k : ℕ) :
    ∫ x, D.conditionalVariance k x ∂μ = ∫ x, D.increment k x ^ 2 ∂μ := by
  rw [integral_congr_ae (D.conditionalVariance_eq_condExp k)]
  exact integral_condExp (D.filtration.le k)

/-- Predictable event on which the next variance-clock step fits under
the cap. Stopping before the crossing keeps the entire clock bounded. -/
def beforeVarianceCap (D : MartingaleDifferenceRow μ) (C : ℝ) (k : ℕ) : Set Ω :=
  {ω | varianceClock (fun j => D.conditionalVariance j ω) (k + 1) ≤ C}

omit [IsProbabilityMeasure μ] in
theorem beforeVarianceCap_measurable (D : MartingaleDifferenceRow μ) (C : ℝ) (k : ℕ) :
    MeasurableSet[D.filtration k] (D.beforeVarianceCap C k) := by
  apply measurableSet_le _ measurable_const
  apply Finset.measurable_sum
  intro j hj
  exact ((D.conditionalVariance_measurable j).mono
    (D.filtration.mono (by simpa using Finset.mem_range.mp hj))).measurable

def stoppedIncrement (D : MartingaleDifferenceRow μ) (C : ℝ) (k : ℕ) : Ω → ℝ :=
  (D.beforeVarianceCap C k).indicator (D.increment k)

omit [IsProbabilityMeasure μ] in
theorem stoppedIncrement_memLp (D : MartingaleDifferenceRow μ) (C : ℝ) (k : ℕ) :
    MemLp (D.stoppedIncrement C k) 2 μ :=
  (D.memLp k).indicator ((D.filtration.le k) _ (D.beforeVarianceCap_measurable C k))

theorem stoppedIncrement_mean_zero (D : MartingaleDifferenceRow μ) (C : ℝ) (k : ℕ) :
    μ[D.stoppedIncrement C k | D.filtration k] =ᵐ[μ] 0 := by
  have h := condExp_indicator ((D.memLp k).integrable (by norm_num))
    (D.beforeVarianceCap_measurable C k)
  refine h.trans ?_
  filter_upwards [D.mean_zero k] with x hx
  by_cases hs : x ∈ D.beforeVarianceCap C k <;> simp [hs, hx]

omit [IsProbabilityMeasure μ] in
theorem stoppedIncrement_conditionalVariance
    (D : MartingaleDifferenceRow μ) (C : ℝ) (k : ℕ) :
    μ[fun x => D.stoppedIncrement C k x ^ 2 | D.filtration k] =ᵐ[μ]
      fun x => stoppedVariance (fun j => D.conditionalVariance j x) C k := by
  have heq : (fun x => D.stoppedIncrement C k x ^ 2) =
      (D.beforeVarianceCap C k).indicator (fun x => D.increment k x ^ 2) := by
    funext x
    by_cases hs : x ∈ D.beforeVarianceCap C k <;> simp [stoppedIncrement, hs]
  rw [heq]
  have h := condExp_indicator (D.memLp k).integrable_sq (D.beforeVarianceCap_measurable C k)
  refine h.trans ?_
  filter_upwards [D.conditionalVariance_eq_condExp k] with x hx
  unfold stoppedVariance
  by_cases hs : varianceClock (fun j => D.conditionalVariance j x) (k + 1) ≤ C
  · simp only [if_pos hs]
    rw [Set.indicator_of_mem (show x ∈ D.beforeVarianceCap C k from hs)]
    exact hx.symm
  · simp [beforeVarianceCap, hs]

end MartingaleDifferenceRow

/-- Pulling an adapted complex weight through a real conditional
expectation, in the integral form used by characteristic functions. -/
theorem integral_smul_condExp (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {X : Ω → ℝ} {W : Ω → ℂ}
    (hX : Integrable X μ) (hW : AEStronglyMeasurable[m] W μ)
    (hXW : Integrable (X • W) μ) :
    ∫ x, X x • W x ∂μ = ∫ x, μ[X | m] x • W x ∂μ := by
  calc
    _ = ∫ x, μ[X • W | m] x ∂μ := (integral_condExp hm).symm
    _ = _ := integral_congr_ae (condExp_smul_of_aestronglyMeasurable_right hX hXW hW)

theorem integral_weighted_martingale_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {X : Ω → ℝ} {W : Ω → ℂ}
    (hX : Integrable X μ) (hmean : μ[X | m] =ᵐ[μ] 0)
    (hW : AEStronglyMeasurable[m] W μ) (hXW : Integrable (X • W) μ) :
    ∫ x, X x • W x ∂μ = 0 := by
  rw [@integral_smul_condExp Ω mΩ μ _ m hm X W hX hW hXW]
  have hz : (fun x => μ[X | m] x • W x) =ᵐ[μ] 0 := by
    filter_upwards [hmean] with x hx
    simp only [hx, Pi.zero_apply, zero_smul]
  rw [integral_congr_ae hz]
  simp only [Pi.zero_apply, integral_zero]

end
end UniformRandomMALA.Concrete
