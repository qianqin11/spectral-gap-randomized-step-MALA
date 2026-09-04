import UniformRandomMALA.Concrete.HessianToFirstOrder
import UniformRandomMALA.Concrete.RayleighSpectralGap
import UniformRandomMALA.Concrete.GaussianRampCanonicalInterpolation

/-!
# The randomized-MALA master bound from the paper's Hessian assumptions

This file joins the calculus bridge, the existing concrete lower-bound chain,
and the manuscript's `L²` Rayleigh definition of the spectral gap.  No
analytic certificate or independently supplied gradient remains in the
public endpoint.
-/

namespace UniformRandomMALA.Concrete.HessianBoundedPotential

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory Gradient

noncomputable section

variable {d : ℕ}

/-- The non-lazy master lower bound under the paper's `C²` Hessian
assumptions, stated with the package's original all-measurable Poincaré gap. -/
theorem universal_masterRHS_spectralGap_lower
    (V : HessianBoundedPotential d) (H : ℝ) (hH : 0 < H) :
    let W := V.toFirstOrderPotential
    let p := W.universalParameters H hH
    ENNReal.ofReal p.masterRHS ≤
      spectralGap (W.target : Measure (State d))
        (W.uniformMALA p.H p.hH) := by
  exact V.toFirstOrderPotential.universal_masterRHS_spectralGap_lower H hH

/-- Exact paper-form non-lazy endpoint: the hypotheses are `C²` regularity
and quadratic-form bounds on the actual Hessian, the MALA drift is the Riesz
gradient of `U`, all universal constants are the explicit package constants,
and the conclusion uses the manuscript's `L²` Rayleigh spectral gap. -/
theorem universal_masterRHS_rayleighSpectralGap_lower
    (V : HessianBoundedPotential d) (H : ℝ) (hH : 0 < H) :
    let W := V.toFirstOrderPotential
    let p := W.universalParameters H hH
    ENNReal.ofReal p.masterRHS ≤
      rayleighSpectralGap (W.target : Measure (State d))
        (W.uniformMALA p.H p.hH) := by
  let W := V.toFirstOrderPotential
  let p := W.universalParameters H hH
  exact (W.universal_masterRHS_spectralGap_lower H hH).trans
    (spectralGap_le_rayleighSpectralGap (W.uniformMALA p.H p.hH))

end

end UniformRandomMALA.Concrete.HessianBoundedPotential

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory Gradient

noncomputable section

/-- The manuscript's displayed definition of `p⋆`, separated from the
internal positive-parameter record. -/
def paperMomentThreshold {d : ℕ} (V : HessianBoundedPotential d) (A₀ : ℝ) : ℝ :=
  A₀ * (1 + Real.log ((d : ℝ) + 1) + Real.log (V.L / V.m))

/-- The right-hand side displayed in the non-lazy clause of Theorem 2.1. -/
def paperMasterRHS {d : ℕ} (V : HessianBoundedPotential d)
    (A₀ b₀ c₀ H : ℝ) : ℝ :=
  let pStar := paperMomentThreshold V A₀
  c₀ * (V.m / H) *
    (min H (b₀ / V.L *
      max (1 / Real.sqrt (pStar * ((d : ℝ) + pStar)))
        (1 / (d : ℝ)))) ^ 2

/-- Theorem 2.1 in its displayed existential-constant form.  The witnesses
are explicit universal constants, are chosen before the dimension and
potential, and the conclusion uses the paper's `L²` Rayleigh quotient gap. -/
theorem exists_universal_nonlazy_paperMasterRHS_lower :
    ∃ A₀ b₀ c₀ : ℝ,
      2 ≤ A₀ ∧ 0 < b₀ ∧ b₀ ≤ 1 / 2 ∧ 0 < c₀ ∧
      ∀ {d : ℕ} (V : HessianBoundedPotential d) (H : ℝ) (hH : 0 < H),
        ENNReal.ofReal (paperMasterRHS V A₀ b₀ c₀ H) ≤
          rayleighSpectralGap
            (V.toFirstOrderPotential.target : Measure (State d))
            (V.toFirstOrderPotential.uniformMALA H hH) := by
  refine ⟨FirstOrderPotential.concreteA0,
    FirstOrderPotential.concreteB0, concreteGapConstant,
    FirstOrderPotential.concreteA0_ge_two,
    FirstOrderPotential.concreteB0_pos,
    FirstOrderPotential.concreteB0_le_half,
    concreteGapConstant_pos, ?_⟩
  intro d V H hH
  have hmain := V.universal_masterRHS_rayleighSpectralGap_lower H hH
  simpa [paperMasterRHS, paperMomentThreshold,
    HessianBoundedPotential.toFirstOrderPotential,
    FirstOrderPotential.universalParameters,
    FirstOrderPotential.toParameters,
    Parameters.masterRHS, Parameters.certifiedScale,
    Parameters.baseFactor, Parameters.certifiedShape,
    Parameters.rejectionShape, Parameters.safeShape] using hmain

end

end UniformRandomMALA.Concrete
