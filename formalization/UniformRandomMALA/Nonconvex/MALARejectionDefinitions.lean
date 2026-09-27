import UniformRandomMALA.Concrete.NonconvexMALA
import UniformRandomMALA.Concrete.NonconvexBasic

/-!
# Stationary MALA rejection for the nonconvex Boltzmann setting

The rejection probability is the actual missing mass of the accepted
Gaussian proposal. The moment interface below is the intermediate `p ≥ 2`
estimate used to prove Proposition B.1 (`prop:stationary-rejection`).
-/

namespace UniformRandomMALA.Concrete.NonconvexPotential

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

variable {d : ℕ} (V : NonconvexPotential d)

/-- The pointwise rejection probability of the fixed-step MALA algorithm. -/
def malaRejectionMassReal (h : ℝ) (x : State d) : ℝ :=
  (1 - MetropolisHastings.acceptanceMass
    (V.gaussianDensityProposal h) (V.malaAcceptance h) x).toReal

lemma measurable_malaRejectionMassReal (h : ℝ) :
    Measurable (V.malaRejectionMassReal h) := by
  exact ENNReal.measurable_toReal.comp (measurable_const.sub
    (MetropolisHastings.measurable_acceptanceMass _ _
      (V.measurable_uncurry_malaAcceptance h)))

lemma malaRejectionMassReal_nonneg (h : ℝ) (x : State d) :
    0 ≤ V.malaRejectionMassReal h x := ENNReal.toReal_nonneg

lemma malaRejectionMassReal_le_one (h : ℝ) (x : State d) :
    V.malaRejectionMassReal h x ≤ 1 := by
  exact (ENNReal.toReal_mono ENNReal.one_ne_top tsub_le_self).trans_eq
    ENNReal.toReal_one

lemma malaRejectionMassReal_eq_fixed {h : ℝ} (_hh : 0 < h) (x : State d) :
    V.malaRejectionMassReal h x =
      (1 - MetropolisHastings.acceptanceMass
        (V.gaussianDensityProposal h) (V.malaAcceptance h) x).toReal := rfl

/-- The intermediate rejection moment estimate, before interpolation to `p ≥ 1`. -/
def StationaryMALARejectionMomentBound (cr Cr : ℝ) : Prop :=
  ∀ p h : ℝ, 2 ≤ p → 0 < h →
    h ≤ cr / (V.L * Real.sqrt (p * ((d : ℝ) + p))) →
    (∫ x : State d,
      ((1 - MetropolisHastings.acceptanceMass
        (V.gaussianDensityProposal h) (V.malaAcceptance h) x).toReal) ^ p
        ∂(V.target : Measure (State d))) ≤
      ((Cr / 3) * V.L * h * Real.sqrt (p * ((d : ℝ) + p))) ^ p

end
end UniformRandomMALA.Concrete.NonconvexPotential
