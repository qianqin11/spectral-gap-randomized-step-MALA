import UniformRandomMALA.DiscreteTime.Averaging
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Elementary averaging along a probability kernel

This is the finite-kernel form of conditional Jensen used twice in the
discrete-time proof: first to forget intermediate path coordinates and then
to pass from a rejected endpoint-flow density to its first marginal.

The theorem is stated only for scalar nonnegative functions.  It is proved
by applying the scalar Jensen theorem fiber by fiber and then using the
composition-product integral formula.  No conditional-expectation API is
used.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

namespace DiscreteTime

/-- Averaging a scalar function against the probability kernel `kappa`. -/
def kernelAverage {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (kappa : Kernel X Y) (f : X × Y → ℝ) (x : X) : ℝ :=
  ∫ y, f (x, y) ∂kappa x

/-- On a finite measure space, an integrable `p`-th power of a nonnegative
function, with `p >= 1`, implies integrability of the function itself.  This
small lemma avoids routing the rejection argument through the general
`MemLp` monotonicity API. -/
theorem integrable_of_nonneg_rpow_integrable
    {X : Type*} [MeasurableSpace X] {mu : Measure X} [IsFiniteMeasure mu]
    {f : X → ℝ} {p : ℝ} (hp : 1 ≤ p) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x)
    (hfp : Integrable (fun x => (f x) ^ p) mu) :
    Integrable f mu := by
  have hdom : ∀ x, f x ≤ 1 + (f x) ^ p := by
    intro x
    by_cases hx : f x ≤ 1
    · exact hx.trans (le_add_of_nonneg_right (Real.rpow_nonneg (hf0 x) p))
    · have hx1 : 1 ≤ f x := le_of_not_ge hx
      have hpow : f x ≤ (f x) ^ p := by
        calc
          f x = (f x) ^ (1 : ℝ) := (Real.rpow_one (f x)).symm
          _ ≤ (f x) ^ p := Real.rpow_le_rpow_of_exponent_le hx1 hp
      exact hpow.trans (le_add_of_nonneg_left zero_le_one)
  apply integrable_of_le_of_le hf.aestronglyMeasurable
    (ae_of_all _ hf0) (ae_of_all _ hdom)
    (integrable_const 0) ((integrable_const 1).add hfp)

section Kernel

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Probability-kernel averaging contracts a nonnegative scalar `p`-moment.
All integrability statements needed for fiberwise Jensen are derived from
the two corresponding composition-product assumptions. -/
theorem integral_kernelAverage_rpow_le
    {mu : Measure X} [IsProbabilityMeasure mu]
    {kappa : Kernel X Y} [IsMarkovKernel kappa]
    {f : X × Y → ℝ} {p : ℝ}
    (hp : 1 ≤ p) (hf : Measurable f) (hf0 : ∀ z, 0 ≤ f z)
    (hfInt : Integrable f (mu ⊗ₘ kappa))
    (hfpInt : Integrable (fun z => (f z) ^ p) (mu ⊗ₘ kappa)) :
    Integrable (fun x => (kernelAverage kappa f x) ^ p) mu ∧
      (∫ x, (kernelAverage kappa f x) ^ p ∂mu) ≤
        ∫ z, (f z) ^ p ∂(mu ⊗ₘ kappa) := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hAvgStrong : StronglyMeasurable (kernelAverage kappa f) := by
    exact hf.stronglyMeasurable.integral_kernel_prod_right'
  have hAvgPowMeas : Measurable
      (fun x => (kernelAverage kappa f x) ^ p) :=
    (Real.continuous_rpow_const hp0).measurable.comp hAvgStrong.measurable
  have hOuterInt : Integrable
      (fun x => ∫ y, (f (x, y)) ^ p ∂kappa x) mu :=
    hfpInt.integral_compProd
  have hFiber : ∀ᵐ x ∂mu,
      Integrable (fun y => f (x, y)) (kappa x) ∧
        Integrable (fun y => (f (x, y)) ^ p) (kappa x) :=
    hfInt.ae_of_compProd.and hfpInt.ae_of_compProd
  have hJensen : ∀ᵐ x ∂mu,
      (kernelAverage kappa f x) ^ p ≤
        ∫ y, (f (x, y)) ^ p ∂kappa x := by
    filter_upwards [hFiber] with x hx
    exact rpow_integral_le_integral_rpow hp
      (ae_of_all _ fun y => hf0 (x, y)) hx.1 hx.2
  have hAvgPowInt : Integrable
      (fun x => (kernelAverage kappa f x) ^ p) mu := by
    apply integrable_of_le_of_le hAvgPowMeas.aestronglyMeasurable
      (ae_of_all _ fun x => Real.rpow_nonneg
        (integral_nonneg_of_ae (ae_of_all _ fun y => hf0 (x, y))) p)
      hJensen (integrable_zero X ℝ mu) hOuterInt
  refine ⟨hAvgPowInt, ?_⟩
  calc
    (∫ x, (kernelAverage kappa f x) ^ p ∂mu) ≤
        ∫ x, ∫ y, (f (x, y)) ^ p ∂kappa x ∂mu :=
      integral_mono_ae hAvgPowInt hOuterInt hJensen
    _ = ∫ z, (f z) ^ p ∂(mu ⊗ₘ kappa) :=
      (Measure.integral_compProd hfpInt).symm

end Kernel

end DiscreteTime

end

end UniformRandomMALA
