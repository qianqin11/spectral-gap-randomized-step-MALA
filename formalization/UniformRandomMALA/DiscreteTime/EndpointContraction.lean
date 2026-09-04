import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Disintegration.Integral
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# Endpoint contraction by finite-measure disintegration

This file proves the data-processing step needed in the discrete-time proof.
The argument concerns two finite measures on a product space.  It
disintegrates each measure over the first coordinate, applies scalar Jensen
to the resulting probability kernels, and integrates the pointwise
inequality.  There is no conditional-expectation object and no path-space
limit in the statement or proof.

In the application, the first coordinate is the pair of endpoints and the
second coordinate contains the finitely many intermediate Gaussian
innovations.  Thus this theorem turns a centered moment bound for the full
finite likelihood product into the same bound for the endpoint likelihood.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace DiscreteTime

/-- For `p >= 1`, the centered power `t |-> |t - 1|^p` is convex.  We state
the result on `[0, infinity)` because Radon--Nikodym derivatives are
nonnegative, although the same function is convex on all of `R`. -/
theorem convexOn_centered_abs_rpow {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ (Ici 0) (fun t : ℝ => |t - 1| ^ p) := by
  have hrange : (fun t : ℝ => dist t 1) '' (univ : Set ℝ) = Ici 0 := by
    ext r
    constructor
    · rintro ⟨t, -, rfl⟩
      exact dist_nonneg
    · intro hr
      change 0 ≤ r at hr
      refine ⟨r + 1, Set.mem_univ _, ?_⟩
      change |(r + 1) - 1| = r
      simpa [abs_of_nonneg hr]
  have hdist : ConvexOn ℝ (univ : Set ℝ) (fun t : ℝ => dist t 1) :=
    convexOn_univ_dist 1
  have hcomp : ConvexOn ℝ (univ : Set ℝ)
      ((fun r : ℝ => r ^ p) ∘ fun t : ℝ => dist t 1) := by
    apply ConvexOn.comp
    · simpa [hrange] using convexOn_rpow hp
    · exact hdist
    · rw [hrange]
      exact Real.monotoneOn_rpow_Ici_of_exponent_nonneg (zero_le_one.trans hp)
  exact hcomp.subset (subset_univ _) (convex_Ici 0) |>.congr fun t _ => by
    simp only [Function.comp_apply, Real.dist_eq]

section FstContraction

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [TopologicalSpace Y] [OpensMeasurableSpace Y] [StandardBorelSpace Y]
  [Nonempty Y] [MeasurableSpace.CountableOrCountablyGenerated X Y]

/-- Projection to the first coordinate contracts the centered `p`-moment of
a Radon--Nikodym derivative.  This is the endpoint-likelihood contraction in
the exact form needed for a finite path law.

The only structural assumption is that the forgotten coordinate is standard
Borel, which supplies a probability disintegration kernel in Mathlib. -/
theorem integral_centered_rnDeriv_fst_rpow_le
    {rho sigma : Measure (X × Y)} [IsFiniteMeasure rho]
    [IsFiniteMeasure sigma] {p : ℝ}
    (hp : 1 ≤ p) (hρσ : rho ≪ sigma)
    (hInt : Integrable
      (fun z => |(rho.rnDeriv sigma z).toReal - 1| ^ p) sigma) :
    Integrable
        (fun x => |(rho.fst.rnDeriv sigma.fst x).toReal - 1| ^ p)
        sigma.fst ∧
      (∫ x, |(rho.fst.rnDeriv sigma.fst x).toReal - 1| ^ p ∂sigma.fst) ≤
        ∫ z, |(rho.rnDeriv sigma z).toReal - 1| ^ p ∂sigma := by
  let phi : ℝ → ℝ := fun t => |t - 1| ^ p
  have hphiStrong : StronglyMeasurable phi := by
    exact ((continuous_abs.comp (continuous_id.sub continuous_const)).rpow_const
      (fun _ => Or.inr (zero_le_one.trans hp))).stronglyMeasurable
  have hphiConvex : ConvexOn ℝ (Ici 0) phi := by
    simpa [phi] using convexOn_centered_abs_rpow hp
  have hphiCont : ContinuousWithinAt phi (Ici 0) 0 := by
    exact ((continuous_abs.comp (continuous_id.sub continuous_const)).rpow_const
      (fun _ => Or.inr (zero_le_one.trans hp))).continuousWithinAt
  have hcomp :
      rho.fst ⊗ₘ rho.condKernel ≪ sigma.fst ⊗ₘ sigma.condKernel := by
    rw [rho.disintegrate rho.condKernel, sigma.disintegrate sigma.condKernel]
    exact hρσ
  have hconditional :
      rho.fst ⊗ₘ rho.condKernel ≪ rho.fst ⊗ₘ sigma.condKernel :=
    Measure.AbsolutelyContinuous.compProd_right hcomp.kernel_of_compProd
  have hIntComp : Integrable
      (fun z => phi
        (((rho.fst ⊗ₘ rho.condKernel).rnDeriv
          (sigma.fst ⊗ₘ sigma.condKernel) z).toReal))
      (sigma.fst ⊗ₘ sigma.condKernel) := by
    simpa only [rho.disintegrate rho.condKernel,
      sigma.disintegrate sigma.condKernel, phi] using hInt
  have hMarginal : Integrable
      (fun x => phi ((rho.fst.rnDeriv sigma.fst x).toReal)) sigma.fst :=
    hphiConvex.integrable_apply_rnDeriv_of_integrable_compProd
      hphiStrong hphiCont hIntComp hconditional
  refine ⟨by simpa [phi] using hMarginal, ?_⟩
  have hPointwise :
      (fun x => phi ((rho.fst.rnDeriv sigma.fst x).toReal)) ≤ᵐ[sigma.fst]
        fun x => ∫ y, phi
          (((rho.fst ⊗ₘ rho.condKernel).rnDeriv
            (sigma.fst ⊗ₘ sigma.condKernel) (x, y)).toReal)
          ∂sigma.condKernel x :=
    hphiConvex.apply_rnDeriv_ae_le_integral
      hphiStrong hphiCont hIntComp hconditional
  calc
    (∫ x, |(rho.fst.rnDeriv sigma.fst x).toReal - 1| ^ p ∂sigma.fst) =
        ∫ x, phi ((rho.fst.rnDeriv sigma.fst x).toReal) ∂sigma.fst := by
          rfl
    _ ≤ ∫ x, ∫ y, phi
          (((rho.fst ⊗ₘ rho.condKernel).rnDeriv
            (sigma.fst ⊗ₘ sigma.condKernel) (x, y)).toReal)
          ∂sigma.condKernel x ∂sigma.fst :=
      integral_mono_ae hMarginal hIntComp.integral_compProd hPointwise
    _ = ∫ z, phi
          (((rho.fst ⊗ₘ rho.condKernel).rnDeriv
            (sigma.fst ⊗ₘ sigma.condKernel) z).toReal)
          ∂(sigma.fst ⊗ₘ sigma.condKernel) :=
      (Measure.integral_compProd hIntComp).symm
    _ = ∫ z, |(rho.rnDeriv sigma z).toReal - 1| ^ p ∂sigma := by
      simp only [rho.disintegrate rho.condKernel,
        sigma.disintegrate sigma.condKernel, phi]

end FstContraction

end DiscreteTime

end

end UniformRandomMALA
