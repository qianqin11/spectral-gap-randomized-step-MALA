import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Bernoulli decisions from one unit-interval coordinate

The finite Euler/RWM coupling uses independent unit uniforms to implement
Metropolis decisions.  These lemmas reduce the only required integrals to
the volume of an initial interval.  Thus later proofs can integrate out the
uniform coordinate immediately and work only with the rejection profile.
-/

namespace UniformRandomMALA

open MeasureTheory Set
open scoped unitInterval

noncomputable section

namespace DiscreteTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

/-- Return `c` when the unit uniform lies below `ρ`, and zero otherwise. -/
def thresholdConst (ρ : ℝ) (c : E) (u : Set.Icc (0 : ℝ) 1) : E :=
  if (u : ℝ) ≤ ρ then c else 0

theorem measurable_thresholdConst (ρ : ℝ) (c : E) :
    Measurable (thresholdConst ρ c) := by
  unfold thresholdConst
  exact Measurable.ite
    (measurableSet_le measurable_subtype_coe measurable_const)
    measurable_const measurable_const

theorem integrable_thresholdConst (ρ : ℝ) (c : E) :
    Integrable (thresholdConst ρ c) := by
  exact (integrable_const c).indicator
    (measurableSet_le measurable_subtype_coe measurable_const)

/-- A unit uniform realizes a Bernoulli variable with mean `ρ`. -/
theorem integral_thresholdConst
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (c : E) :
    (∫ u : Set.Icc (0 : ℝ) 1, thresholdConst ρ c u) = ρ • c := by
  let ρI : Set.Icc (0 : ℝ) 1 := ⟨ρ, hρ0, hρ1⟩
  have heq : thresholdConst ρ c =
      (Set.Iic ρI).indicator (fun _ : Set.Icc (0 : ℝ) 1 => c) := by
    funext u
    by_cases hu : (u : ℝ) ≤ ρ
    · have huI : u ≤ ρI := hu
      simp [thresholdConst, Set.indicator, hu, huI]
    · have huI : u ∉ Set.Iic ρI := hu
      simp [thresholdConst, Set.indicator, hu, huI]
  rw [heq, integral_indicator measurableSet_Iic, setIntegral_const]
  change ((volume (Set.Iic ρI)).toReal) • c = ρ • c
  rw [unitInterval.volume_Iic]
  simp [ρI, ENNReal.toReal_ofReal hρ0]

/-- The second moment of the Bernoulli displacement is `ρ ‖c‖²`. -/
theorem integral_norm_thresholdConst_sq
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (c : E) :
    (∫ u : Set.Icc (0 : ℝ) 1, ‖thresholdConst ρ c u‖ ^ 2) =
      ρ * ‖c‖ ^ 2 := by
  have h := integral_thresholdConst (E := ℝ) ρ hρ0 hρ1 (‖c‖ ^ 2)
  convert h using 1
  · apply integral_congr_ae
    exact ae_of_all _ fun u => by
      by_cases hu : (u : ℝ) ≤ ρ <;>
        simp [thresholdConst, hu]
  · simp [smul_eq_mul]

/-- Centering the Bernoulli displacement gives mean zero. -/
theorem integral_thresholdConst_sub_mean
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (c : E) :
    (∫ u : Set.Icc (0 : ℝ) 1, thresholdConst ρ c u - ρ • c) = 0 := by
  rw [integral_sub (integrable_thresholdConst ρ c) (integrable_const _),
    integral_thresholdConst ρ hρ0 hρ1, integral_const]
  simp

end DiscreteTime

end

end UniformRandomMALA
