import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Elementary averaging inequalities

The discrete-time proof repeatedly conditions or averages finite-product
random variables.  This file gives the scalar Jensen step in the exact form
needed there.  Stating it for ordinary real integrals avoids importing a
specialized Minkowski or conditional-expectation API when convexity alone is
enough.
-/

namespace UniformRandomMALA

open Filter MeasureTheory Set

noncomputable section

namespace DiscreteTime

/-- Probability averaging contracts the real `L^p` moment of a nonnegative
integrand.  This is the pointwise ingredient behind both finite-mixture
averaging and endpoint conditional-density contraction. -/
theorem rpow_integral_le_integral_rpow
    {Alpha : Type*} [MeasurableSpace Alpha]
    {rho : Measure Alpha} [IsProbabilityMeasure rho]
    {f : Alpha → ℝ} {p : ℝ}
    (hp : 1 ≤ p)
    (hf_nonneg : ∀ᵐ x ∂rho, 0 ≤ f x)
    (hf : Integrable f rho)
    (hfp : Integrable (fun x => (f x) ^ p) rho) :
    (∫ x, f x ∂rho) ^ p ≤ ∫ x, (f x) ^ p ∂rho := by
  exact (convexOn_rpow hp).map_integral_le
    (Real.continuous_rpow_const (le_trans zero_le_one hp)).continuousOn
    isClosed_Ici
    hf_nonneg
    hf
    (by simpa only [Function.comp_def] using hfp)

end DiscreteTime

end

end UniformRandomMALA
