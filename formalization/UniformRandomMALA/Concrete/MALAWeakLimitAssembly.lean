import UniformRandomMALA.Concrete.MALAMetropolisMeet
import UniformRandomMALA.DiscreteTime.MovingDensityClosure

/-!
# Weak-limit assembly for the stationary MALA rejection estimate

This module joins the two generic halves of the elementary argument.  The
input is a sequence of finite-dimensional reference probability laws against
which the fixed MALA proposal edge has explicit densities with a uniform
centered `L^p` bound.  Weak convergence to a symmetric law with target
marginals gives the canonical RN derivative at the limit; the meet argument
then turns its centered moment bound into the stationary rejection estimate.
-/

namespace UniformRandomMALA

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

namespace Concrete
namespace FirstOrderPotential

variable {d : ℕ} (V : FirstOrderPotential d)

/-- Assemble the stationary MALA rejection estimate directly from a family
of elementary moving-reference approximations.

For each admissible `(p,h)`, `nu n` is the finite reference law, `F n` is the
exact density of the fixed oriented MALA proposal edge relative to `nu n`, and
`sigma` is their weak limit.  Only the limit is required to be swap invariant
and to have both target marginals.  The conjugate exponent needed by the
moving-density closure is chosen canonically as `Real.conjExponent p`. -/
theorem stationaryMALARejectionMomentBound_of_moving_reference_family
    {cr Cr : ℝ} (hCr : 0 ≤ Cr)
    (hfamily : ∀ p h : ℝ, 2 ≤ p → 0 < h →
      h ≤ cr / (V.L * Real.sqrt (p * ((d : ℝ) + p))) →
      ∃ (sigma : ProbabilityMeasure (State d × State d))
        (nu : ℕ → ProbabilityMeasure (State d × State d))
        (F : ℕ → State d × State d → ℝ),
        Tendsto nu atTop (nhds sigma) ∧
        (∀ n, Measurable (F n)) ∧
        (∀ n z, 0 ≤ F n z) ∧
        (∀ n, ((V.target : Measure (State d)) ⊗ₘ
            V.gaussianDensityProposal h) =
          (nu n : Measure (State d × State d)).withDensity
            (fun z => ENNReal.ofReal (F n z))) ∧
        (∀ n, Integrable (fun z => |F n z - 1| ^ p)
          (nu n : Measure (State d × State d))) ∧
        (∀ n, ((∫ z, |F n z - 1| ^ p
            ∂(nu n : Measure (State d × State d))) ^ (1 / p) ≤
          (Cr / 6) * V.L * h * Real.sqrt (p * ((d : ℝ) + p)))) ∧
        Measure.map Prod.swap (sigma : Measure (State d × State d)) = sigma ∧
        (sigma : Measure (State d × State d)).fst =
          (V.target : Measure (State d)) ∧
        (sigma : Measure (State d × State d)).snd =
          (V.target : Measure (State d))) :
    V.StationaryMALARejectionMomentBound cr Cr := by
  apply V.stationaryMALARejectionMomentBound_of_rnDeriv_memLp_family hCr
  intro p h hp hh hstep
  obtain ⟨sigma, nu, F, hnu, hFmeas, hFnonneg, hDensity, hInt, hRoot,
    hsymm, hfst, hsnd⟩ := hfamily p h hp hh hstep
  letI : Fact (0 < h) := ⟨hh⟩
  let proposalEdge : ProbabilityMeasure (State d × State d) :=
    ⟨(V.target : Measure (State d)) ⊗ₘ V.gaussianDensityProposal h, by
      infer_instance⟩
  let C : ℝ :=
    (Cr / 6) * V.L * h * Real.sqrt (p * ((d : ℝ) + p))
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (div_nonneg hCr (by norm_num)) V.hL.le) hh.le)
      (Real.sqrt_nonneg _)
  have hp_one : 1 < p := lt_of_lt_of_le (by norm_num) hp
  have hpq : p.HolderConjugate (Real.conjExponent p) :=
    Real.HolderConjugate.conjExponent hp_one
  have hLimit := DiscreteTime.rnDeriv_memLp_of_moving_withDensity
    proposalEdge sigma nu F hp hpq hC hnu hFmeas hFnonneg
      (fun n => by
        change ((V.target : Measure (State d)) ⊗ₘ
            V.gaussianDensityProposal h) =
          (nu n : Measure (State d × State d)).withDensity
            (fun z => ENNReal.ofReal (F n z))
        exact hDensity n)
      hInt (fun n => by simpa only [C] using hRoot n)
  refine ⟨(sigma : Measure (State d × State d)), inferInstance,
    hsymm, hfst, hsnd, ?_, ?_, ?_⟩
  · change ((V.target : Measure (State d)) ⊗ₘ
      V.gaussianDensityProposal h) ≪
        (sigma : Measure (State d × State d))
    exact hLimit.1
  · change MemLp (fun z =>
      ((((V.target : Measure (State d)) ⊗ₘ
        V.gaussianDensityProposal h).rnDeriv
          (sigma : Measure (State d × State d))) z).toReal - 1)
        (ENNReal.ofReal p) (sigma : Measure (State d × State d))
    exact hLimit.2.2.1
  · change ((∫ z,
      |((((V.target : Measure (State d)) ⊗ₘ
        V.gaussianDensityProposal h).rnDeriv
          (sigma : Measure (State d × State d))) z).toReal - 1| ^ p
          ∂(sigma : Measure (State d × State d))) ^ (1 / p) ≤ C)
    exact hLimit.2.2.2

end FirstOrderPotential
end Concrete

end
end UniformRandomMALA
