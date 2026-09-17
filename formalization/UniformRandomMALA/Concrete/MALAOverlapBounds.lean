import UniformRandomMALA.Concrete.MALAFullPathAssembly
import UniformRandomMALA.Concrete.MALAOverlapFromRejection

/-!
# Certificate-free `p >= 2` MALA local-overlap core

The finite path estimate has constant `1024 e^3`.  Endpoint contraction and
the Metropolis meet cost a factor six, giving `Cr = 6144 e^3`; its scalar
smallness condition is exactly `cr = 1 / (16 e)`.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace Concrete
namespace FirstOrderPotential

open DiscreteTime

variable {d : ℕ} (V : FirstOrderPotential d)

/-- Small-step constant in the elementary Proposition 3.2 (`prop:overlap`) proof. -/
def proposition32CrSmall : ℝ := 1 / (16 * Real.exp 1)

/-- Exceptional-set constant in the elementary Proposition 3.2 (`prop:overlap`) proof. -/
def proposition32CrLarge : ℝ := 6144 * (Real.exp 1) ^ 3

lemma proposition32CrSmall_pos : 0 < proposition32CrSmall := by
  unfold proposition32CrSmall
  positivity

lemma proposition32CrSmall_le_one : proposition32CrSmall ≤ 1 := by
  unfold proposition32CrSmall
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  rw [div_le_one (by positivity : 0 < 16 * Real.exp 1)]
  nlinarith

lemma proposition32CrLarge_pos : 0 < proposition32CrLarge := by
  unfold proposition32CrLarge
  positivity

/-- Certificate-free stationary rejection estimate with the sharper core
constants, under `FirstOrderPotential`. -/
theorem stationaryMALARejectionMomentBound_proposition32 :
    V.StationaryMALARejectionMomentBound
      proposition32CrSmall proposition32CrLarge := by
  simpa only [proposition32CrSmall, proposition32CrLarge] using
    V.stationaryMALARejectionMomentBound_paperScale

/-- Sharper `p >= 2` core of Proposition 3.2 (`prop:overlap`), with explicit elementary
constants `cr = 1 / (16e)` and `Cr = 6144 e^3`. The revised `p >= 1`
paper-facing wrapper is in `Concrete/C1MainTheorem.lean`. -/
theorem proposition32_discreteTime :
    (∀ p t : ℝ, 2 ≤ p → ∀ ht : 0 < t,
      t ≤ proposition32CrSmall /
        (V.L * Real.sqrt (p * ((d : ℝ) + p))) →
      ∃ G : Set (State d),
        MeasurableSet G ∧
        (V.target : Measure (State d)) Gᶜ ≤
          ENNReal.ofReal
            ((proposition32CrLarge * V.L * t *
              Real.sqrt (p * ((d : ℝ) + p))) ^ p) ∧
        ∀ x ∈ G, ∀ y ∈ G,
          ‖x - y‖ ≤ Real.sqrt t / 16 →
          setwiseTV (V.dyadicMALA t ht x)
            (V.dyadicMALA t ht y) ≤ 3 / 4) ∧
    (∀ t : ℝ, ∀ ht : 0 < t,
      t ≤ 1 / (2 * V.L * (d : ℝ)) →
      ∀ x y : State d,
        ‖x - y‖ ≤ Real.sqrt t / 16 →
        setwiseTV (V.dyadicMALA t ht x)
          (V.dyadicMALA t ht y) ≤ 3 / 4) :=
  V.proposition32_of_stationaryMALARejectionMomentBound
    proposition32CrSmall_pos proposition32CrSmall_le_one
    proposition32CrLarge_pos
    V.stationaryMALARejectionMomentBound_proposition32

end FirstOrderPotential
end Concrete

end
end UniformRandomMALA
