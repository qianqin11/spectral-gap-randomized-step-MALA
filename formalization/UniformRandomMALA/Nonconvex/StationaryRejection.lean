import UniformRandomMALA.Nonconvex.MALAFullPathAssembly
import UniformRandomMALA.Nonconvex.RejectionMomentsOne

/-!
# The nonconvex stationary rejection theorem

Proposition B.1 (`prop:stationary-rejection`) holds for the actual MALA
rejection probability for every real `p ≥ 1`. Its only potential assumptions
are the appendix's continuously differentiable, globally Lipschitz-gradient,
normalizable Boltzmann setting. Finite Gaussian likelihood estimates,
Euler/RWM weak limits, endpoint density identification, Metropolis meets,
and moment interpolation discharge every analytic input internally.
-/

namespace UniformRandomMALA.Concrete.NonconvexPotential

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

/-- A universal step constant for the stationary rejection theorem. -/
def rejectionStepConstant : ℝ := 1 / (32 * Real.exp 1)

/-- A universal norm constant for the stationary rejection theorem. -/
def rejectionNormConstant : ℝ := 4096 * (Real.exp 1) ^ 3

lemma rejectionStepConstant_pos : 0 < rejectionStepConstant := by
  unfold rejectionStepConstant
  positivity

lemma rejectionNormConstant_pos : 0 < rejectionNormConstant := by
  unfold rejectionNormConstant
  positivity

variable {d : ℕ} (V : NonconvexPotential d)

/-- The full exponent range of Proposition B.1 (`prop:stationary-rejection`)
as an unconditional power-moment bound. -/
theorem stationaryMALARejectionMomentBoundOne_paper :
    V.StationaryMALARejectionMomentBoundOne
      rejectionStepConstant (3 * rejectionNormConstant) := by
  have h := V.stationaryMALARejectionMomentBoundOne_of_two
    (by positivity : 0 < 1 / (16 * Real.exp 1))
    (by positivity : 0 ≤ 6144 * (Real.exp 1) ^ 3)
    V.stationaryMALARejectionMomentBound_paperScale
  convert h using 1 <;> simp only [rejectionStepConstant, rejectionNormConstant] <;> ring

/-- Proposition B.1 (`prop:stationary-rejection`), with the paper's literal
`L^p(π)` norm and the actual Gaussian Metropolis rejection probability. -/
theorem stationary_rejection_moments
    {p h : ℝ} (hp : 1 ≤ p) (hh : 0 < h)
    (hstep : h ≤ rejectionStepConstant /
      (V.L * Real.sqrt (p * ((d : ℝ) + p)))) :
    MemLp (V.malaRejectionMassReal h) (ENNReal.ofReal p)
      (V.target : Measure (State d)) ∧
    lpNorm (V.malaRejectionMassReal h) (ENNReal.ofReal p)
      (V.target : Measure (State d)) ≤
        rejectionNormConstant * V.L * h * Real.sqrt (p * ((d : ℝ) + p)) := by
  refine ⟨V.memLp_malaRejectionMassReal h _, ?_⟩
  have h := V.stationaryMALARejection_lpNorm_le_of_moments
    (mul_nonneg (by norm_num) rejectionNormConstant_pos.le)
    V.stationaryMALARejectionMomentBoundOne_paper hp hh hstep
  simpa only [mul_div_cancel_left₀ _ (by norm_num : (3 : ℝ) ≠ 0)] using h

/-- The same stationary rejection estimate in the extended norm, making
finiteness explicit in the inequality itself. -/
theorem stationary_rejection_eLpNorm_le
    {p h : ℝ} (hp : 1 ≤ p) (hh : 0 < h)
    (hstep : h ≤ rejectionStepConstant /
      (V.L * Real.sqrt (p * ((d : ℝ) + p)))) :
    eLpNorm (V.malaRejectionMassReal h) (ENNReal.ofReal p)
      (V.target : Measure (State d)) ≤
        ENNReal.ofReal (rejectionNormConstant * V.L * h *
          Real.sqrt (p * ((d : ℝ) + p))) := by
  obtain ⟨hm, hb⟩ := V.stationary_rejection_moments hp hh hstep
  rw [← ofReal_lpNorm hm]
  exact ENNReal.ofReal_mono hb

/-- Universal constants precede every dimension, nonconvex potential,
exponent and step in Proposition B.1 (`prop:stationary-rejection`). -/
theorem exists_universal_stationary_rejection_moments :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {d : ℕ} (V : NonconvexPotential d) {p h : ℝ}, 1 ≤ p → 0 < h →
        h ≤ c / (V.L * Real.sqrt (p * ((d : ℝ) + p))) →
        MemLp (V.malaRejectionMassReal h) (ENNReal.ofReal p)
          (V.target : Measure (State d)) ∧
        lpNorm (V.malaRejectionMassReal h) (ENNReal.ofReal p)
          (V.target : Measure (State d)) ≤
            C * V.L * h * Real.sqrt (p * ((d : ℝ) + p)) := by
  refine ⟨rejectionStepConstant, rejectionNormConstant, rejectionStepConstant_pos,
    rejectionNormConstant_pos, ?_⟩
  intro d V p h hp hh hs
  exact V.stationary_rejection_moments hp hh hs

end
end UniformRandomMALA.Concrete.NonconvexPotential
