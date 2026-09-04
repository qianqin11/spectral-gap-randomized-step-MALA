import UniformRandomMALA.KernelMixture
import Mathlib.Probability.Moments.Variance

/-!
# Concrete extended-valued Poincaré gap

The paper uses the right spectral gap through its variational/Poincaré
characterization.  Working first in `ℝ≥0∞` avoids imposing integrability merely
to state Tonelli and monotone-convergence arguments.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace Concrete

variable {α : Type*} [MeasurableSpace α]

/-- `c` is a Poincaré lower bound for `K` with stationary measure `π`. -/
def PoincareLower (π : Measure α) (K : Kernel α α) (c : ℝ≥0∞) : Prop :=
  ∀ f : α → ℝ, Measurable f →
    c * evariance f π ≤ Dirichlet.energy π K f

/-- The extended-valued right spectral gap, defined as the supremum of all
Poincaré lower bounds. -/
def spectralGap (π : Measure α) (K : Kernel α α) : ℝ≥0∞ :=
  sSup {c : ℝ≥0∞ | PoincareLower π K c}

lemma poincareLower_zero (π : Measure α) (K : Kernel α α) :
    PoincareLower π K 0 := by
  intro f hf
  simp

lemma spectralGap_nonneg (π : Measure α) (K : Kernel α α) :
    0 ≤ spectralGap π K := bot_le

/-- Every proved Poincaré constant lies below the concrete spectral gap. -/
theorem le_spectralGap
    (π : Measure α) (K : Kernel α α) {c : ℝ≥0∞}
    (hc : PoincareLower π K c) :
    c ≤ spectralGap π K := by
  exact le_sSup hc

/-- Reversibility of a Markov kernel gives the stationarity needed later for
the `L²` finiteness and coarea arguments. -/
theorem invariant_of_reversible
    (π : Measure α) (K : Kernel α α) [IsMarkovKernel K]
    (hrev : Kernel.IsReversible K π) :
    Kernel.Invariant K π :=
  hrev.invariant

end Concrete

end

end UniformRandomMALA
