import UniformRandomMALA.DiscreteTime.MovingReference
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# From density moments to Hölder bounds on tests

This file records the finite-measure step that precedes the moving-reference
weak-limit argument.  If `mu` has density `F` with respect to `nu`, then the
difference of expectations of a test `f` is the integral of `(F - 1) * f`.
Hölder's inequality therefore turns an `L^p(nu)` bound on `F - 1` into the
test-function inequality consumed by `centeredRNDeriv_memLp_of_weakLimit`.

The moment-integrability hypothesis in the final theorem is intentional:
the Bochner integral of a non-integrable real-valued function is defined to
be zero, so a bare inequality between integral values would not by itself
assert an `L^p` bound.
-/

namespace UniformRandomMALA

open MeasureTheory

noncomputable section

namespace DiscreteTime

variable {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]

/-- A density whose centered part has bounded `L^p` norm satisfies the
corresponding Hölder estimate on bounded continuous tests. -/
theorem boundedContinuous_holder_of_withDensity_memLp
    (mu nu : ProbabilityMeasure E)
    {F : E → ℝ} {p q C : ℝ}
    (hpq : p.HolderConjugate q)
    (hF : Measurable F) (hF_nonneg : ∀ x, 0 ≤ F x)
    (hmu : (mu : Measure E) =
      (nu : Measure E).withDensity (fun x => ENNReal.ofReal (F x)))
    (hcenter : MemLp (fun x => F x - 1) (ENNReal.ofReal p) (nu : Measure E))
    (hroot :
      (∫ x, |F x - 1| ^ p ∂(nu : Measure E)) ^ (1 / p) ≤ C)
    (f : BoundedContinuousFunction E ℝ) :
    |(∫ x, f x ∂(mu : Measure E)) -
        ∫ x, f x ∂(nu : Measure E)| ≤
      C * (∫ x, |f x| ^ q ∂(nu : Measure E)) ^ (1 / q) := by
  let u : E → ℝ := fun x => F x - 1
  have hfMem : MemLp (fun x => f x) (ENNReal.ofReal q) (nu : Measure E) := by
    apply MemLp.of_bound f.continuous.measurable.aestronglyMeasurable ‖f‖
    exact Filter.Eventually.of_forall fun x => f.norm_coe_le_norm x
  let _ : (ENNReal.ofReal p).HolderTriple (ENNReal.ofReal q) 1 := by
    simpa using hpq.ennrealOfReal
  have hufMem : MemLp (fun x => u x * f x) 1 (nu : Measure E) :=
    hfMem.mul' hcenter
  have hufInt : Integrable (fun x => u x * f x) (nu : Measure E) :=
    memLp_one_iff_integrable.mp hufMem
  have hfInt : Integrable (fun x => f x) (nu : Measure E) := f.integrable _
  have hFfInt : Integrable (fun x => F x * f x) (nu : Measure E) := by
    apply (hufInt.add hfInt).congr
    exact Filter.Eventually.of_forall fun x => by
      change (F x - 1) * f x + f x = F x * f x
      ring
  have hDensityIntegral :
      ∫ x, f x ∂(mu : Measure E) = ∫ x, F x * f x ∂(nu : Measure E) := by
    rw [hmu, integral_withDensity_eq_integral_toReal_smul
      hF.ennreal_ofReal (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top) f]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change (ENNReal.ofReal (F x)).toReal * f x = F x * f x
      rw [ENNReal.toReal_ofReal (hF_nonneg x)]
  have hDifference :
      (∫ x, f x ∂(mu : Measure E)) - ∫ x, f x ∂(nu : Measure E) =
        ∫ x, u x * f x ∂(nu : Measure E) := by
    rw [hDensityIntegral, ← integral_sub hFfInt hfInt]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      simp only [u]
      ring
  rw [hDifference]
  calc
    |∫ x, u x * f x ∂(nu : Measure E)|
        ≤ ∫ x, |u x * f x| ∂(nu : Measure E) := abs_integral_le_integral_abs
    _ = ∫ x, ‖u x‖ * ‖f x‖ ∂(nu : Measure E) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by simp [abs_mul]
    _ ≤ (∫ x, ‖u x‖ ^ p ∂(nu : Measure E)) ^ (1 / p) *
        (∫ x, ‖f x‖ ^ q ∂(nu : Measure E)) ^ (1 / q) :=
      integral_mul_norm_le_Lp_mul_Lq hpq hcenter hfMem
    _ ≤ C * (∫ x, |f x| ^ q ∂(nu : Measure E)) ^ (1 / q) := by
      simp only [u, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hroot
        (Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _) _)

/-- Integral-moment version of
`boundedContinuous_holder_of_withDensity_memLp`.  Explicit integrability of
the `p`-moment converts the paper's real-integral hypothesis into `MemLp`. -/
theorem boundedContinuous_holder_of_withDensity_moment
    (mu nu : ProbabilityMeasure E)
    {F : E → ℝ} {p q C : ℝ}
    (hpq : p.HolderConjugate q)
    (hF : Measurable F) (hF_nonneg : ∀ x, 0 ≤ F x)
    (hmu : (mu : Measure E) =
      (nu : Measure E).withDensity (fun x => ENNReal.ofReal (F x)))
    (hmoment : Integrable (fun x => |F x - 1| ^ p) (nu : Measure E))
    (hroot :
      (∫ x, |F x - 1| ^ p ∂(nu : Measure E)) ^ (1 / p) ≤ C)
    (f : BoundedContinuousFunction E ℝ) :
    |(∫ x, f x ∂(mu : Measure E)) -
        ∫ x, f x ∂(nu : Measure E)| ≤
      C * (∫ x, |f x| ^ q ∂(nu : Measure E)) ^ (1 / q) := by
  apply boundedContinuous_holder_of_withDensity_memLp mu nu hpq hF hF_nonneg hmu
  · let u : E → ℝ := fun x => F x - 1
    change MemLp u (ENNReal.ofReal p) (nu : Measure E)
    have hu : AEStronglyMeasurable u (nu : Measure E) :=
      (hF.sub measurable_const).aestronglyMeasurable
    rw [← integrable_norm_rpow_iff hu]
    · simpa only [ENNReal.toReal_ofReal hpq.pos.le, Real.norm_eq_abs] using hmoment
    · simpa using hpq.pos
    · exact ENNReal.ofReal_ne_top
  · exact hroot

end DiscreteTime

end

end UniformRandomMALA
