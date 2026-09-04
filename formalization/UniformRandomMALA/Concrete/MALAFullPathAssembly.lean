import UniformRandomMALA.Concrete.MALAWeakLimitAssembly
import UniformRandomMALA.Concrete.FiniteEulerRealMoments
import UniformRandomMALA.DiscreteTime.EulerRWMEdgeVanishing
import UniformRandomMALA.DiscreteTime.FiniteEulerEdgeBridge

/-!
# From finite full-path moments to stationary MALA rejection

This module is the concrete assembly layer immediately below the numerical
finite-Gaussian likelihood estimate.  It chooses the offset fixed-horizon
Euler schedule, extracts the structured common Euler/RWM edge-law limit,
contracts the assumed full-path moment to the endpoint, and invokes the
generic moving-reference MALA assembly.
-/

namespace UniformRandomMALA

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

namespace Concrete
namespace FirstOrderPotential

open DiscreteTime

variable {d : ℕ} (V : FirstOrderPotential d)

/-- The sole quantitative input required from the finite full-path
likelihood analysis.  It is stated uniformly along every positive offset of
the fixed-horizon schedule, so an estimate depending only on the horizon can
instantiate it without knowing which compactness subsequence will be chosen.
-/
def FixedHorizonOffsetFullPathMomentBound (cr Cr : ℝ) : Prop :=
  ∀ p h : ℝ, 2 ≤ p → 0 < h →
    h ≤ cr / (V.L * Real.sqrt (p * ((d : ℝ) + p))) →
    ∀ N : ℕ, 1 ≤ N → ∀ n : ℕ,
      Integrable (fun q : State d ×
          (Fin (fixedHorizonOffsetSteps N n) → State d) =>
        |finiteGaussianDRec V 1 (fixedHorizonOffsetStep h N n)
          q.1 q.1 q.2 - 1| ^ p)
        (finiteEulerBaseJointMeasure V) ∧
      ((∫ q : State d ×
          (Fin (fixedHorizonOffsetSteps N n) → State d),
        |finiteGaussianDRec V 1 (fixedHorizonOffsetStep h N n)
          q.1 q.1 q.2 - 1| ^ p
          ∂finiteEulerBaseJointMeasure V) ^ (1 / p)) ≤
        (Cr / 6) * V.L * h * Real.sqrt (p * ((d : ℝ) + p))

/-- A uniform centered full-path moment bound along the elementary offset
schedule implies the fixed-step stationary MALA rejection estimate.

All compactness, endpoint data processing, density identification, and
Metropolis-meet steps are discharged internally. -/
theorem stationaryMALARejectionMomentBound_of_fixedHorizonOffsetFullPath
    {cr Cr : ℝ} (hCr : 0 ≤ Cr)
    (hPath : V.FixedHorizonOffsetFullPathMomentBound cr Cr) :
    V.StationaryMALARejectionMomentBound cr Cr := by
  apply V.stationaryMALARejectionMomentBound_of_moving_reference_family hCr
  intro p h hp hh hstep
  obtain ⟨N, _epsilon, hN, _hepsilonPos, _hepsilonZero, _hcost,
      sigma, _hsigmaClosure, subseq, _hsubseq, _hrwm, heuler,
      hsymm, hfst, hsnd⟩ :=
    exists_common_tendsto_subseq_fixedHorizonEulerRWMEdgeLaws_with_structure
      V h hh
  let delta : ℕ → ℝ := fun k =>
    fixedHorizonOffsetStep h N (subseq k)
  let steps : ℕ → ℕ := fun k =>
    fixedHorizonOffsetSteps N (subseq k)
  let nu : ℕ → ProbabilityMeasure (State d × State d) := fun k =>
    finiteEulerEdgeLaw V (delta k) (steps k)
  let F : ℕ → State d × State d → ℝ := fun k z =>
    (finiteEulerLikelihoodEndpointRNDensity V (steps k) (delta k) z).toReal
  have hdeltaPos (k : ℕ) : 0 < delta k := by
    exact fixedHorizonOffsetStep_pos h N (subseq k) hh hN
  have htime (k : ℕ) : (steps k : ℝ) * delta k = h := by
    exact fixedHorizonOffset_horizon h N (subseq k) hN
  have hEndpoint (k : ℕ) :
      Integrable (fun z : State d × State d => |F k z - 1| ^ p)
          (nu k : Measure (State d × State d)) ∧
        ((∫ z : State d × State d, |F k z - 1| ^ p
            ∂(nu k : Measure (State d × State d))) ^ (1 / p)) ≤
          (Cr / 6) * V.L * h * Real.sqrt (p * ((d : ℝ) + p)) := by
    change
      Integrable (fun z : State d × State d =>
        |(finiteEulerLikelihoodEndpointRNDensity V
          (steps k) (delta k) z).toReal - 1| ^ p)
        (finiteEulerEdgeMeasure V (delta k) (steps k)) ∧
      ((∫ z : State d × State d,
        |(finiteEulerLikelihoodEndpointRNDensity V
          (steps k) (delta k) z).toReal - 1| ^ p
          ∂finiteEulerEdgeMeasure V (delta k) (steps k)) ^ (1 / p)) ≤
        (Cr / 6) * V.L * h * Real.sqrt (p * ((d : ℝ) + p))
    have hFull := hPath p h hp hh hstep N hN (subseq k)
    have hFrozen :=
      finiteFrozenLikelihoodEdge_rnDeriv_centered_rpow_integrable_and_root_le
        (n := steps k) V (delta k) p
        ((Cr / 6) * V.L * h * Real.sqrt (p * ((d : ℝ) + p)))
        (hdeltaPos k).le (by linarith) hFull.1 hFull.2
    simpa only [
      finiteEulerLikelihoodEndpointRNDensity_eq_frozen_rnDeriv
        V (delta k) (hdeltaPos k).le,
      finiteEulerLikelihoodEdgeLaw_eq_finiteEulerEdgeMeasure] using hFrozen
  refine ⟨sigma, nu, F, ?_, ?_, ?_, ?_, ?_, ?_, hsymm, hfst, hsnd⟩
  · change Tendsto
      ((fun n => finiteEulerEdgeLaw V
        (fixedHorizonOffsetStep h N n)
        (fixedHorizonOffsetSteps N n)) ∘ subseq)
      atTop (nhds sigma)
    exact heuler
  · intro k
    dsimp only [F]
    exact ENNReal.measurable_toReal.comp
      ((finiteEulerLikelihoodTiltedEdgeLaw V (steps k) (delta k)).measurable_rnDeriv
        (finiteEulerLikelihoodEdgeLaw V (steps k) (delta k)))
  · intro k z
    exact ENNReal.toReal_nonneg
  · intro k
    change ((V.target : Measure (State d)) ⊗ₘ
        V.gaussianDensityProposal h) =
      (finiteEulerEdgeMeasure V (delta k) (steps k)).withDensity
        (fun z => ENNReal.ofReal
          ((finiteEulerLikelihoodEndpointRNDensity V
            (steps k) (delta k) z).toReal))
    exact
      compProd_gaussianDensityProposal_eq_finiteEulerEdgeMeasure_withDensity_toReal_endpointRNDensity
        V (delta k) h (steps k) (hdeltaPos k).le hh (htime k)
  · exact fun k => (hEndpoint k).1
  · exact fun k => (hEndpoint k).2

/-- The paper-scale finite likelihood theorem supplies the offset-schedule
full-path hypothesis with `cr = 1/(16e)` and `Cr = 6144 e^3`. -/
theorem fixedHorizonOffsetFullPathMomentBound_paperScale :
    V.FixedHorizonOffsetFullPathMomentBound
      (1 / (16 * Real.exp 1)) (6144 * (Real.exp 1) ^ 3) := by
  intro p h hp hh hstep N hN n
  let m : ℕ := fixedHorizonOffsetSteps N n
  let delta : ℝ := fixedHorizonOffsetStep h N n
  let s : ℝ := Real.sqrt (p * ((d : ℝ) + p))
  have hm : 0 < m := by
    dsimp [m, fixedHorizonOffsetSteps]
    omega
  have hdelta : 0 < delta := by
    exact fixedHorizonOffsetStep_pos h N n hh hN
  have htime : (m : ℝ) * delta = h := by
    exact fixedHorizonOffset_horizon h N n hN
  have hp0 : 0 < p := by linarith
  have hd0 : 0 < (d : ℝ) := V.dimension_real_pos
  have harg : 0 < p * ((d : ℝ) + p) := by positivity
  have hspos : 0 < s := by
    exact Real.sqrt_pos.2 harg
  have hsquare : s ^ 2 = p * ((d : ℝ) + p) := by
    exact Real.sq_sqrt harg.le
  have hscaled : V.L * h * s ≤ 1 / (16 * Real.exp 1) := by
    have hmul := (le_div_iff₀ (mul_pos V.hL hspos)).mp hstep
    dsimp [s] at hmul ⊢
    nlinarith
  have hsone : 1 ≤ s := by
    rw [Real.le_sqrt (by norm_num) harg.le]
    have hd1 : 1 ≤ (d : ℝ) := V.dimension_real_one
    nlinarith
  have hEuler : V.L * h ≤ 1 := by
    have hLh0 : 0 ≤ V.L * h := mul_nonneg V.hL.le hh.le
    have htoS : V.L * h ≤ V.L * h * s := by
      nlinarith [mul_nonneg hLh0 (sub_nonneg.mpr hsone)]
    have hcrone : 1 / (16 * Real.exp 1) ≤ 1 := by
      apply (div_le_one (by positivity : 0 < 16 * Real.exp 1)).2
      have heone : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      nlinarith
    exact htoS.trans (hscaled.trans hcrone)
  have hscaledOne : 16 * Real.exp 1 * V.L * h * s ≤ 1 := by
    calc
      16 * Real.exp 1 * V.L * h * s =
          (16 * Real.exp 1) * (V.L * h * s) := by ring
      _ ≤ (16 * Real.exp 1) * (1 / (16 * Real.exp 1)) :=
        mul_le_mul_of_nonneg_left hscaled (by positivity)
      _ = 1 := by field_simp [Real.exp_ne_zero]
  have hsmall :
      256 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 *
        (p * ((d : ℝ) + p)) ≤ 1 := by
    have hscaledNonneg : 0 ≤ 16 * Real.exp 1 * V.L * h * s :=
      (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) (Real.exp_pos 1))
        V.hL) hh) hspos).le
    calc
      256 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 *
          (p * ((d : ℝ) + p)) =
          (16 * Real.exp 1 * V.L * h * s) ^ 2 := by
        rw [← hsquare]
        ring
      _ ≤ 1 := by nlinarith
  have hPaper := finiteGaussianDRec_centered_rpow_root_le_paper_scale
    (n := m) V hm V.hd delta h p hdelta.le hh (by linarith)
      htime hEuler hsmall
  change
    Integrable (fun q : State d × (Fin m → State d) =>
      |finiteGaussianDRec V 1 delta q.1 q.1 q.2 - 1| ^ p)
      (finiteEulerBaseJointMeasure V) ∧
    ((∫ q : State d × (Fin m → State d),
      |finiteGaussianDRec V 1 delta q.1 q.1 q.2 - 1| ^ p
        ∂finiteEulerBaseJointMeasure V) ^ (1 / p)) ≤
      ((6144 * (Real.exp 1) ^ 3) / 6) * V.L * h *
        Real.sqrt (p * ((d : ℝ) + p))
  have hscale :
      ((6144 * (Real.exp 1) ^ 3) / 6) * V.L * h *
          Real.sqrt (p * ((d : ℝ) + p)) =
        1024 * (Real.exp 1) ^ 3 * V.L * h *
          Real.sqrt (p * ((d : ℝ) + p)) := by ring
  rw [hscale]
  simpa only [finiteEulerBaseJointMeasure] using hPaper

/-- Unconditional paper-scale stationary rejection estimate obtained by the
finite Euler weak-limit route. -/
theorem stationaryMALARejectionMomentBound_paperScale :
    V.StationaryMALARejectionMomentBound
      (1 / (16 * Real.exp 1)) (6144 * (Real.exp 1) ^ 3) := by
  apply V.stationaryMALARejectionMomentBound_of_fixedHorizonOffsetFullPath
    (by positivity)
  exact V.fixedHorizonOffsetFullPathMomentBound_paperScale

end FirstOrderPotential
end Concrete

end
end UniformRandomMALA
