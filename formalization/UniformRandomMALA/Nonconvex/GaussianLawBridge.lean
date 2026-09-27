import UniformRandomMALA.Concrete.NonconvexMALA
import UniformRandomMALA.DiscreteTime.GaussianLawBridge

/-!
# The Gaussian proposal law in the nonconvex setting

The existing Gaussian density-to-sampling theorem is indexed by a
strongly convex potential even though its random-walk proposal does not
depend on that potential. A quadratic reference supplies that unused
index. The density is identified exactly with the nonconvex MALA proposal
at its actual Euler mean, so no convexity is imposed on the target.
-/

namespace UniformRandomMALA.Nonconvex.DiscreteTime

open MeasureTheory ProbabilityTheory
open UniformRandomMALA.Concrete
open scoped RealInnerProductSpace ENNReal
noncomputable section

private def gaussianReferencePotential (d : ℕ) (hd : 0 < d) : FirstOrderPotential d where
  U x := ‖x‖ ^ 2 / 2
  gradU x := x
  m := 1
  L := 1
  hd := hd
  hm := by norm_num
  hmL := le_rfl
  continuous_U := (continuous_norm.pow 2).div_const 2
  continuous_gradU := continuous_id
  lowerTaylor x y := by
    have h := norm_add_sq_real x (y - x)
    rw [show x + (y - x) = y by abel] at h
    nlinarith
  upperTaylor x y := by
    have h := norm_add_sq_real x (y - x)
    rw [show x + (y - x) = y by abel] at h
    nlinarith
  grad_lipschitz := by
    intro x y
    change edist x y ≤ (1 : ℝ≥0∞) * edist x y
    simp

/-- The nonconvex MALA proposal uses exactly the paper's Gaussian draw. -/
theorem gaussianDensityProposal_eq_map_stdGaussian {d : ℕ}
    (V : NonconvexPotential d) {h : ℝ} (hh : 0 < h) (x : State d) :
    V.gaussianDensityProposal h x =
      (stdGaussian (State d)).map
        (fun z : State d => V.proposalMean h x + Real.sqrt (2 * h) • z) := by
  let Q := gaussianReferencePotential d V.hd
  calc
    _ = Q.randomWalkProposal h (V.proposalMean h x) := by
      rw [NonconvexPotential.gaussianDensityProposal, Kernel.withDensity_apply _
        (V.measurable_uncurry_proposalDensity h) x,
        FirstOrderPotential.randomWalkProposal, Kernel.withDensity_apply _
        (Q.measurable_uncurry_randomWalkDensity h) (V.proposalMean h x)]
      congr 1
    _ = _ := UniformRandomMALA.DiscreteTime.randomWalkProposal_eq_map_stdGaussian Q hh _

end
end UniformRandomMALA.Nonconvex.DiscreteTime
