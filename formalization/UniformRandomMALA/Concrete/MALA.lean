import UniformRandomMALA.Concrete.GaussianProposal
import UniformRandomMALA.Concrete.MetropolisHastings

/-!
# The concrete fixed-step MALA kernel

This file combines the normalized Boltzmann target, the Gaussian proposal
density, and the generic accept--reject construction.  For every positive
step size it produces an actual mathlib Markov kernel and proves detailed
balance with the target probability measure.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace Concrete

namespace FirstOrderPotential

variable {d : ℕ} (V : FirstOrderPotential d)

/-- The Metropolis acceptance probability for the MALA proposal. -/
def malaAcceptance (h : ℝ) (x y : State d) : ℝ≥0∞ :=
  MetropolisHastings.acceptance V.targetDensity (V.proposalDensity h) x y

lemma measurable_uncurry_malaAcceptance (h : ℝ) :
    Measurable (Function.uncurry (V.malaAcceptance h)) := by
  exact MetropolisHastings.measurable_uncurry_acceptance
    V.targetDensity (V.proposalDensity h)
    V.measurable_targetDensity (V.measurable_uncurry_proposalDensity h)

lemma malaAcceptance_le_one (h : ℝ) (x y : State d) :
    V.malaAcceptance h x y ≤ 1 :=
  MetropolisHastings.acceptance_le_one _ _ x y

/-- A fixed-step MALA transition.  The positivity proof is included because
the Gaussian density is a probability density exactly when `h > 0`. -/
def malaKernel (h : ℝ) (_hh : 0 < h) : Kernel (State d) (State d) := by
  exact MetropolisHastings.kernel
    (V.gaussianDensityProposal h) (V.malaAcceptance h)

theorem malaKernel_isMarkovKernel (h : ℝ) (hh : 0 < h) :
    IsMarkovKernel (V.malaKernel h hh) := by
  letI : Fact (0 < h) := ⟨hh⟩
  letI : Fact (Measurable (Function.uncurry (V.malaAcceptance h))) :=
    ⟨V.measurable_uncurry_malaAcceptance h⟩
  letI : Fact (∀ x y, V.malaAcceptance h x y ≤ 1) :=
    ⟨V.malaAcceptance_le_one h⟩
  unfold malaKernel
  infer_instance

lemma malaEdgeDensity_ne_zero {h : ℝ} (hh : 0 < h) (x y : State d) :
    MetropolisHastings.edgeDensity V.targetDensity (V.proposalDensity h) x y ≠ 0 := by
  exact (ENNReal.mul_pos (V.targetDensity_pos x).ne'
    (V.proposalDensity_pos hh x y).ne').ne'

lemma malaEdgeDensity_ne_top (h : ℝ) (x y : State d) :
    MetropolisHastings.edgeDensity V.targetDensity (V.proposalDensity h) x y ≠ ∞ := by
  exact ENNReal.mul_ne_top (V.targetDensity_ne_top x)
    (V.proposalDensity_ne_top h x y)

/-- Every positive-step MALA kernel satisfies detailed balance with the
normalized target. -/
theorem malaKernel_isReversible (h : ℝ) (hh : 0 < h) :
    Kernel.IsReversible (V.malaKernel h hh) (V.target : Measure (State d)) := by
  letI : Fact (0 < h) := ⟨hh⟩
  letI : IsSFiniteKernel
      (MetropolisHastings.densityKernel (volume : Measure (State d))
        (V.proposalDensity h)) := by
    unfold MetropolisHastings.densityKernel
    exact Kernel.IsSFiniteKernel.withDensity _ (V.proposalDensity_ne_top h)
  have hacceptedDensity := @MetropolisHastings.accepted_densityKernel_isReversible
    (State d) (WithLp.measurableSpace 2 (Fin d → ℝ))
    (volume : Measure (State d)) (by infer_instance)
    V.targetDensity (V.proposalDensity h) (by infer_instance)
    V.measurable_targetDensity (V.measurable_uncurry_proposalDensity h)
    (V.malaEdgeDensity_ne_zero hh) (V.malaEdgeDensity_ne_top h)
  have haccepted : Kernel.IsReversible
      (MetropolisHastings.accepted (V.gaussianDensityProposal h)
        (V.malaAcceptance h))
      (V.target : Measure (State d)) := by
    change Kernel.IsReversible
      (MetropolisHastings.accepted (V.gaussianDensityProposal h)
        (MetropolisHastings.acceptance V.targetDensity (V.proposalDensity h)))
      (V.target : Measure (State d))
    rw [V.target_toMeasure_eq_withDensity]
    simpa [gaussianDensityProposal, MetropolisHastings.densityKernel,
      malaAcceptance] using hacceptedDensity
  unfold malaKernel
  exact MetropolisHastings.kernel_isReversible
    (V.target : Measure (State d)) (V.gaussianDensityProposal h)
    (V.malaAcceptance h) (V.measurable_uncurry_malaAcceptance h) haccepted

theorem malaKernel_invariant (h : ℝ) (hh : 0 < h) :
    Kernel.Invariant (V.malaKernel h hh) (V.target : Measure (State d)) := by
  letI : IsMarkovKernel (V.malaKernel h hh) := V.malaKernel_isMarkovKernel h hh
  exact (V.malaKernel_isReversible h hh).invariant

end FirstOrderPotential

end Concrete

end

end UniformRandomMALA
