import UniformRandomMALA.DiscreteTime.KernelAveraging
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Good sets from averaged rejection moments

This file isolates the Jensen--Markov step used for the dyadic local-overlap
clause.  A nonnegative rejection function is first averaged over a probability
law of step sizes.  Scalar Jensen transfers its product-space `p`-moment to
the averaged function, and the good set is then obtained by the elementary
Markov inequality.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace DiscreteTime

/-- Average a rejection function over a probability law of step sizes. -/
def averagedRejection
    {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (rho : Measure A) (r : X × A → ℝ) (x : X) : ℝ :=
  kernelAverage (Kernel.const X rho) r x

/-- Measurability of the step-size averaged rejection function. -/
theorem measurable_averagedRejection
    {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (rho : Measure A) [SFinite rho]
    {r : X × A → ℝ} (hr : Measurable r) :
    Measurable (averagedRejection rho r) := by
  exact hr.stronglyMeasurable.integral_kernel_prod_right'.measurable

/-- Jensen followed by Markov's inequality.  The conclusion is deliberately
stated with an arbitrary moment upper bound `M`; this avoids taking an
`L^p` root in applications.

The good set is measurable, every point in it has averaged rejection at most
`threshold`, and its complement has mass at most
`M / threshold^p`. -/
theorem exists_averagedRejection_goodSet_of_moment_le
    {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    {mu : Measure X} {rho : Measure A}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure rho]
    {r : X × A → ℝ} {p threshold M : ℝ}
    (hp : 1 ≤ p) (hthreshold : 0 < threshold)
    (hr : Measurable r) (hr0 : ∀ z, 0 ≤ r z)
    (hrpInt : Integrable (fun z => (r z) ^ p) (mu.prod rho))
    (hmoment : (∫ z, (r z) ^ p ∂(mu.prod rho)) ≤ M) :
    ∃ G : Set X,
      MeasurableSet G ∧
      mu Gᶜ ≤ ENNReal.ofReal (M / threshold ^ p) ∧
      ∀ x ∈ G, averagedRejection rho r x ≤ threshold := by
  let kappa : Kernel X A := Kernel.const X rho
  let _ : IsMarkovKernel kappa := by
    dsimp [kappa]
    infer_instance
  have hrIntProd : Integrable r (mu.prod rho) :=
    integrable_of_nonneg_rpow_integrable hp hr hr0 hrpInt
  have hrInt : Integrable r (mu ⊗ₘ kappa) := by
    simpa only [kappa, Measure.compProd_const] using hrIntProd
  have hrpInt' : Integrable (fun z => (r z) ^ p) (mu ⊗ₘ kappa) := by
    simpa only [kappa, Measure.compProd_const] using hrpInt
  have hAvg := integral_kernelAverage_rpow_le hp hr hr0 hrInt hrpInt'
  have hAvgMeas : Measurable (averagedRejection rho r) :=
    measurable_averagedRejection rho hr
  have hAvgEq :
      averagedRejection rho r = kernelAverage kappa r := by
    rfl
  have hAvg0 (x : X) : 0 ≤ averagedRejection rho r x := by
    exact integral_nonneg_of_ae (ae_of_all _ fun a => hr0 (x, a))
  let G : Set X := {x | averagedRejection rho r x ≤ threshold}
  have hG : MeasurableSet G :=
    hAvgMeas measurableSet_Iic
  have hq : 0 < threshold ^ p :=
    Real.rpow_pos_of_pos hthreshold p
  let F : X → ℝ := fun x =>
    (averagedRejection rho r x) ^ p / threshold ^ p
  have hAvgPowInt :
      Integrable (fun x => (averagedRejection rho r x) ^ p) mu := by
    rw [hAvgEq]
    exact hAvg.1
  have hFInt : Integrable F mu := by
    exact hAvgPowInt.div_const _
  have hF0 : ∀ x, 0 ≤ F x := by
    intro x
    exact div_nonneg (Real.rpow_nonneg (hAvg0 x) p) hq.le
  have htail : mu Gᶜ ≤ ENNReal.ofReal (∫ x, F x ∂mu) := by
    apply hFInt.measure_le_integral (ae_of_all _ hF0)
    intro x hx
    have hx' : threshold < averagedRejection rho r x := by
      simpa only [G, mem_compl_iff, mem_ofPred_eq, not_le] using hx
    have hpow : threshold ^ p ≤ (averagedRejection rho r x) ^ p :=
      (Real.rpow_le_rpow_iff hthreshold.le (hAvg0 x)
        (lt_of_lt_of_le zero_lt_one hp)).2 hx'.le
    exact (le_div_iff₀ hq).2 (by simpa using hpow)
  refine ⟨G, hG, ?_, fun x hx => hx⟩
  calc
    mu Gᶜ ≤ ENNReal.ofReal (∫ x, F x ∂mu) := htail
    _ = ENNReal.ofReal
        ((∫ x, (averagedRejection rho r x) ^ p ∂mu) /
          threshold ^ p) := by
      congr 1
      change (∫ x, (averagedRejection rho r x) ^ p / threshold ^ p ∂mu) = _
      exact integral_div (μ := mu) (threshold ^ p)
        (fun x => (averagedRejection rho r x) ^ p)
    _ ≤ ENNReal.ofReal (M / threshold ^ p) := by
      apply ENNReal.ofReal_le_ofReal
      apply div_le_div_of_nonneg_right _ hq.le
      calc
        (∫ x, (averagedRejection rho r x) ^ p ∂mu) ≤
            ∫ z, (r z) ^ p ∂(mu.prod rho) := by
          simpa only [hAvgEq, kappa, Measure.compProd_const] using hAvg.2
        _ ≤ M := hmoment

/-- Root-form corollary.  If the product-space `p`-moment is bounded by
`B^p`, the exceptional mass is at most `(B / threshold)^p`. -/
theorem exists_averagedRejection_goodSet_of_rpow_moment_le
    {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    {mu : Measure X} {rho : Measure A}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure rho]
    {r : X × A → ℝ} {p threshold B : ℝ}
    (hp : 1 ≤ p) (hthreshold : 0 < threshold) (hB : 0 ≤ B)
    (hr : Measurable r) (hr0 : ∀ z, 0 ≤ r z)
    (hrpInt : Integrable (fun z => (r z) ^ p) (mu.prod rho))
    (hmoment : (∫ z, (r z) ^ p ∂(mu.prod rho)) ≤ B ^ p) :
    ∃ G : Set X,
      MeasurableSet G ∧
      mu Gᶜ ≤ ENNReal.ofReal ((B / threshold) ^ p) ∧
      ∀ x ∈ G, averagedRejection rho r x ≤ threshold := by
  obtain ⟨G, hG, hmass, hgood⟩ :=
    exists_averagedRejection_goodSet_of_moment_le
      hp hthreshold hr hr0 hrpInt hmoment
  refine ⟨G, hG, ?_, hgood⟩
  simpa only [Real.div_rpow hB hthreshold.le p] using hmass

/-- The threshold used by the local MALA/RWM overlap argument. -/
theorem exists_averagedRejection_goodSet_one_third
    {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    {mu : Measure X} {rho : Measure A}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure rho]
    {r : X × A → ℝ} {p B : ℝ}
    (hp : 1 ≤ p) (hB : 0 ≤ B)
    (hr : Measurable r) (hr0 : ∀ z, 0 ≤ r z)
    (hrpInt : Integrable (fun z => (r z) ^ p) (mu.prod rho))
    (hmoment : (∫ z, (r z) ^ p ∂(mu.prod rho)) ≤ B ^ p) :
    ∃ G : Set X,
      MeasurableSet G ∧
      mu Gᶜ ≤ ENNReal.ofReal ((3 * B) ^ p) ∧
      ∀ x ∈ G, averagedRejection rho r x ≤ 1 / 3 := by
  obtain ⟨G, hG, hmass, hgood⟩ :=
    exists_averagedRejection_goodSet_of_rpow_moment_le
      hp (by norm_num : (0 : ℝ) < 1 / 3) hB hr hr0 hrpInt hmoment
  refine ⟨G, hG, ?_, hgood⟩
  have hscale : B / (1 / 3 : ℝ) = 3 * B := by ring
  simpa only [hscale] using hmass

end DiscreteTime

end
end UniformRandomMALA
