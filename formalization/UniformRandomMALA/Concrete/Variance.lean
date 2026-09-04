import Mathlib.Probability.Moments.Variance

/-!
# Extended variance around an arbitrary center

The median decomposition used by the conductance proof naturally controls
`∫ (f - b)² dπ`, whereas the concrete spectral gap is stated with Mathlib's
extended variance.  The lemmas below provide that bridge without assuming
`f ∈ L²` in the theorem statement.

The proof treats the non-`L²` case explicitly.  This is important for a
Poincaré lower bound, whose quantifier ranges over every measurable real
function: silently assuming square-integrability at this point would make
the final variational theorem weaker than `Concrete.PoincareLower`.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace Concrete

variable {α : Type*} [MeasurableSpace α]

/-- Extended variance is unchanged by subtracting a real constant. -/
theorem evariance_sub_const
    (π : Measure α) [IsProbabilityMeasure π]
    (f : α → ℝ) (hf : Measurable f) (b : ℝ) :
    evariance (fun x => f x - b) π = evariance f π := by
  by_cases hLp : MemLp f 2 π
  · have hSub : MemLp (fun x => f x - b) 2 π :=
      hLp.sub (memLp_const b)
    rw [← hSub.ofReal_variance_eq, ← hLp.ofReal_variance_eq,
      variance_sub_const hf.aestronglyMeasurable b]
  · have hSub : ¬ MemLp (fun x => f x - b) 2 π := by
      intro h
      apply hLp
      have hConst : MemLp (fun _ : α => b) 2 π := memLp_const b
      convert h.add hConst using 1
      ext x
      simp
    change evariance (f - fun _ => b) π = evariance f π
    rw [evariance_eq_top (hf.sub measurable_const).aestronglyMeasurable hSub,
      evariance_eq_top hf.aestronglyMeasurable hLp]

/-- Extended variance is at most the extended second moment. -/
theorem evariance_le_lintegral_sq
    (π : Measure α) [IsProbabilityMeasure π]
    (f : α → ℝ) (hf : Measurable f) :
    evariance f π ≤ ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂π := by
  rw [evariance_def' hf.aestronglyMeasurable]
  calc
    (∫⁻ x, ‖f x‖ₑ ^ 2 ∂π) - ENNReal.ofReal (π[f] ^ 2) ≤
        ∫⁻ x, ‖f x‖ₑ ^ 2 ∂π := tsub_le_self
    _ = ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂π := by
      apply lintegral_congr
      intro x
      rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg (f x))]

/-- The center-free bound needed for the median split.  It remains valid
when either side is infinite. -/
theorem evariance_le_lintegral_sq_sub
    (π : Measure α) [IsProbabilityMeasure π]
    (f : α → ℝ) (hf : Measurable f) (b : ℝ) :
    evariance f π ≤ ∫⁻ x, ENNReal.ofReal ((f x - b) ^ 2) ∂π := by
  rw [← evariance_sub_const π f hf b]
  exact evariance_le_lintegral_sq π (fun x => f x - b)
    (hf.sub measurable_const)

end Concrete

end

end UniformRandomMALA
