import UniformRandomMALA.Concrete.L2MixingEnergy
import UniformRandomMALA.Concrete.LazyKernel
import UniformRandomMALA.Concrete.PositiveContraction

/-! # Exact spectral-gap contraction for lazy reversible kernels -/

namespace UniformRandomMALA.Concrete
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
noncomputable section
variable {α : Type*} [MeasurableSpace α]
namespace BoundedObservable

theorem average_halfLazy (K : Kernel α α) [IsMarkovKernel K]
    (f : BoundedObservable α) :
    f.average (halfLazyKernel K) = (f.add (f.average K)).smul (1 / 2) := by
  ext x
  have heq : halfLazyKernel K x = (2 : ℝ≥0∞)⁻¹ • (Measure.dirac x + K x) := by
    ext s hs
    rw [halfLazyKernel_apply K x s hs, Measure.smul_apply, Measure.add_apply]
    rfl
  change (∫ y, f y ∂halfLazyKernel K x) = (1 / 2 : ℝ) * (f x + ∫ y, f y ∂K x)
  rw [heq, integral_smul_measure,
    integral_add_measure (f.integrable (Measure.dirac x)) (f.integrable (K x)),
    integral_dirac' _ _ f.measurable_toFun.stronglyMeasurable]
  norm_num

theorem inner_halfLazy_nonneg (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    (f : BoundedObservable α) :
    0 ≤ inner π f (f.average (halfLazyKernel K)) := by
  rw [average_halfLazy, inner_smul_right, inner_add_right, inner_self]
  have hn := (f.add (f.average K)).sqNorm_nonneg π
  rw [sqNorm_add] at hn
  have hc := f.integral_sq_average_le K π hπ
  change (f.average K).sqNorm π ≤ f.sqNorm π at hc
  nlinarith

theorem inner_average_le_gap (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {g : ℝ} (hg : 0 ≤ g) (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π K)
    (f : BoundedObservable α) (hf : ∫ x, f x ∂π = 0) :
    inner π f (f.average K) ≤ (1 - g) * f.sqNorm π := by
  have hp := (l2PoincareLower_iff_le_rayleighSpectralGap K (ENNReal.ofReal g)).2 hgap
    f f.measurable_toFun (f.memLp π 2)
  have hv : evariance f π = ENNReal.ofReal (f.sqNorm π) := by
    rw [← (f.memLp π 2).ofReal_variance_eq, variance_eq_sub (f.memLp π 2), hf]
    simp [sqNorm]
  rw [hv, energy_eq_ofReal π K hπ, ← ENNReal.ofReal_mul hg] at hp
  have hi := (ENNReal.ofReal_le_ofReal_iff
    (sub_nonneg.mpr (inner_average_le_sqNorm π K hπ f))).1 hp
  nlinarith

/-- Exact one-step squared `L²` contraction for a fair-lazy reversible
kernel, obtained from positivity and the variational spectral gap. -/
theorem sqNorm_halfLazy_contraction (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hrev : Kernel.IsReversible K π)
    {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π (halfLazyKernel K))
    (f : BoundedObservable α) (hf : ∫ x, f x ∂π = 0) :
    (f.average (halfLazyKernel K)).sqNorm π ≤ (1 - g) ^ 2 * f.sqNorm π := by
  let M := halfLazyKernel K
  let u := f.average M
  have hMrev : Kernel.IsReversible M π := halfLazyKernel_isReversible π K hrev
  have hu : ∫ x, u x ∂π = 0 := by
    rw [show u = f.average M from rfl, integral_average_invariant M π hMrev.invariant, hf]
  have hcross : inner π f (u.average M) = u.sqNorm π := by
    rw [inner_average_symm π M hMrev, show f.average M = u from rfl, inner_self]
  have hCS : (u.sqNorm π) ^ 2 ≤
      inner π f (f.average M) * inner π u (u.average M) := by
    apply bilinear_cauchy_schwarz_of_quadratic_nonneg
    intro t
    have hn := inner_halfLazy_nonneg π K hrev.invariant (f.add (u.smul t))
    rw [average_add_eq, average_smul_eq, inner_add_left, inner_add_right,
      inner_add_right, inner_smul_left, inner_smul_left,
      inner_smul_right, inner_smul_right, hcross,
      show f.average M = u from rfl, inner_self] at hn
    nlinarith
  exact sq_norm_contraction_of_positive_form (f.sqNorm_nonneg π) (u.sqNorm_nonneg π)
    (sub_nonneg.mpr hg1) (inner_halfLazy_nonneg π K hrev.invariant f)
    (inner_halfLazy_nonneg π K hrev.invariant u) hCS
    (inner_average_le_gap π M hMrev.invariant hg0 hgap f hf)
    (inner_average_le_gap π M hMrev.invariant hg0 hgap u hu)

theorem sqNorm_iterate_halfLazy_le (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hrev : Kernel.IsReversible K π)
    {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π (halfLazyKernel K))
    (f : BoundedObservable α) (hf : ∫ x, f x ∂π = 0) (n : ℕ) :
    (f.iterateAverage (halfLazyKernel K) n).sqNorm π ≤
      (1 - g) ^ (2 * n) * f.sqNorm π := by
  induction n with
  | zero => simp [iterateAverage]
  | succ n ih =>
    have hz : ∫ x, f.iterateAverage (halfLazyKernel K) n x ∂π = 0 := by
      rw [integral_iterateAverage _ π (halfLazyKernel_isReversible π K hrev).invariant, hf]
    have hc := sqNorm_halfLazy_contraction π K hrev hg0 hg1 hgap
      (f.iterateAverage (halfLazyKernel K) n) hz
    have hmul := mul_le_mul_of_nonneg_left ih (sq_nonneg (1 - g))
    calc
      (f.iterateAverage (halfLazyKernel K) (n + 1)).sqNorm π =
          ((f.iterateAverage (halfLazyKernel K) n).average (halfLazyKernel K)).sqNorm π := by
        simp only [iterateAverage, Function.iterate_succ_apply']
      _ ≤ (1 - g) ^ 2 * (f.iterateAverage (halfLazyKernel K) n).sqNorm π := hc
      _ ≤ (1 - g) ^ 2 * ((1 - g) ^ (2 * n) * f.sqNorm π) := hmul
      _ = (1 - g) ^ (2 * (n + 1)) * f.sqNorm π := by
        rw [← mul_assoc, ← pow_add]
        congr 2
        omega

end BoundedObservable

end
end UniformRandomMALA.Concrete
