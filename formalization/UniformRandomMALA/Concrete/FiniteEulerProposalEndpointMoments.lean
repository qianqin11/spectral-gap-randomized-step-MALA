import UniformRandomMALA.DiscreteTime.FiniteEulerEdgeBridge

/-!
# Concrete proposal endpoint moments

This module rewrites the endpoint contraction in the exact edge-law
vocabulary used by MALA: the finite Euler edge is the reference law and
`target ⊗ Q_h` is the Gaussian proposal edge.  The proof remains a finite
deterministic data-processing argument; no conditional expectation is used.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory

noncomputable section

namespace DiscreteTime

open Concrete

variable {d n : ℕ} (V : FirstOrderPotential d)

/-- Under `n * delta = h`, the explicit frozen-over-Euler density is exactly
the concrete stationary Gaussian-proposal-over-finite-Euler density. -/
theorem finiteFrozenLikelihoodEdge_rnDeriv_eq_concreteProposal
    (delta h : ℝ) (hdelta : 0 ≤ delta) (hh : 0 < h)
    (htime : (n : ℝ) * delta = h) :
    (finiteFrozenLikelihoodEdgeLaw V n delta).rnDeriv
        (finiteEulerLikelihoodEdgeLaw V n delta) =
      ((V.target : Measure (State d)) ⊗ₘ V.gaussianDensityProposal h).rnDeriv
        (finiteEulerEdgeMeasure V delta n) := by
  rw [← finiteEulerLikelihoodTiltedEdgeLaw_eq_finiteFrozenLikelihoodEdgeLaw
    V delta hdelta]
  rw [finiteEulerLikelihoodTiltedEdgeLaw_eq_compProd_gaussianDensityProposal
      V delta h n hdelta hh htime,
    finiteEulerLikelihoodEdgeLaw_eq_finiteEulerEdgeMeasure]

/-- A full finite-likelihood root estimate transfers verbatim to the
concrete stationary proposal edge relative to the finite Euler edge. -/
theorem finiteGaussianProposalEdge_rnDeriv_centered_rpow_integrable_and_root_le
    (delta h p B : ℝ) (hdelta : 0 ≤ delta) (hh : 0 < h)
    (hp : 1 ≤ p) (htime : (n : ℝ) * delta = h)
    (hLikelihoodInt : Integrable
      (fun q : State d × (Fin n → State d) =>
        |finiteGaussianDRec V 1 delta q.1 q.1 q.2 - 1| ^ p)
      (finiteEulerBaseJointMeasure V))
    (hLikelihoodRoot :
      ((∫ q : State d × (Fin n → State d),
        |finiteGaussianDRec V 1 delta q.1 q.1 q.2 - 1| ^ p
        ∂finiteEulerBaseJointMeasure V) ^ (1 / p)) ≤ B) :
    Integrable
        (fun e : State d × State d =>
          |(((V.target : Measure (State d)) ⊗ₘ V.gaussianDensityProposal h).rnDeriv
            (finiteEulerEdgeMeasure V delta n) e).toReal - 1| ^ p)
        (finiteEulerEdgeMeasure V delta n) ∧
      ((∫ e : State d × State d,
        |(((V.target : Measure (State d)) ⊗ₘ V.gaussianDensityProposal h).rnDeriv
          (finiteEulerEdgeMeasure V delta n) e).toReal - 1| ^ p
        ∂finiteEulerEdgeMeasure V delta n) ^ (1 / p)) ≤ B := by
  have hEndpoint :=
    finiteFrozenLikelihoodEdge_rnDeriv_centered_rpow_integrable_and_root_le
      V delta p B hdelta hp hLikelihoodInt hLikelihoodRoot
  rw [finiteFrozenLikelihoodEdge_rnDeriv_eq_concreteProposal
      V delta h hdelta hh htime,
    finiteEulerLikelihoodEdgeLaw_eq_finiteEulerEdgeMeasure] at hEndpoint
  exact hEndpoint

end DiscreteTime

end

end UniformRandomMALA
