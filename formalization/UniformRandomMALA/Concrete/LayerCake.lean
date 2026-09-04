import UniformRandomMALA.Concrete.Conductance
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Layer cake for squared superlevels

Mathlib's layer-cake theorem integrates strict superlevels over `(0,∞)`.
The coarea module uses `[0,∞)`.  Lebesgue measure has no atom at zero, so the
two restricted measures agree.  This file records the exact bridge once,
with the project's `sqSuperlevel` notation.
-/

namespace UniformRandomMALA

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Concrete

variable {α : Type*} [MeasurableSpace α]

/-- The stationary second moment is the integral of the masses of the
strict squared superlevel sets. -/
theorem lintegral_sq_eq_lintegral_measure_sqSuperlevel
    (π : Measure α) (g : α → ℝ) (hg : Measurable g) :
    (∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂π) =
      ∫⁻ r in Ici (0 : ℝ), π (sqSuperlevel g r) ∂volume := by
  have h := lintegral_eq_lintegral_meas_lt π
    (f := fun x => g x ^ 2)
    (by filter_upwards with x; exact sq_nonneg (g x))
    (hg.pow_const 2).aemeasurable
  simpa only [sqSuperlevel, restrict_Ioi_eq_restrict_Ici] using h

end Concrete

end

end UniformRandomMALA
