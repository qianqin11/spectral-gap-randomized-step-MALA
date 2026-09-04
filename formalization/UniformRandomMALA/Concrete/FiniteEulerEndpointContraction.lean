import UniformRandomMALA.Concrete.FiniteEulerLikelihoodBounds
import UniformRandomMALA.DiscreteTime.EndpointContraction

/-!
# Endpoint contraction for the finite Euler likelihood

The endpoint edge is a deterministic measurable image of the finite initial
state/innovation pair.  We retain that pair as an auxiliary coordinate,
apply `EndpointContraction` to the first projection, and then erase the
auxiliary coordinate.  This realizes data processing without a conditional
expectation object.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace DiscreteTime

open Concrete

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 800000

section Definitions

variable {d n : ℕ} (V : FirstOrderPotential d)

/-- Stationary initial state together with `n` independent standard
Gaussian innovations. -/
def finiteEulerBaseJointMeasure :
    Measure (State d × (Fin n → State d)) :=
  (V.target : Measure (State d)).prod
    (Measure.pi (fun _ : Fin n => stdGaussian (State d)))

/-- The finite likelihood as an `ENNReal` density on the base joint space. -/
def finiteEulerJointDensity (delta : ℝ) :
    State d × (Fin n → State d) → ℝ≥0∞ := fun p =>
  ENNReal.ofReal (finiteGaussianDRec V 1 delta p.1 p.1 p.2)

/-- Joint law tilted by the finite Gaussian likelihood. -/
def finiteEulerTiltedJointMeasure (delta : ℝ) :
    Measure (State d × (Fin n → State d)) :=
  (finiteEulerBaseJointMeasure V).withDensity
    (finiteEulerJointDensity V delta)

/-- Initial state and ordinary Euler endpoint. -/
def finiteEulerLikelihoodEdgeMap (delta : ℝ) :
    State d × (Fin n → State d) → State d × State d := fun p =>
  (p.1, finiteEulerEndpointRec V delta p.1 p.2)

/-- Initial state and frozen-drift endpoint. -/
def finiteFrozenLikelihoodEdgeMap (delta : ℝ) :
    State d × (Fin n → State d) → State d × State d := fun p =>
  (p.1, finiteFrozenEndpointRec V delta p.1 p.1 p.2)

/-- Ordinary Euler endpoint edge law under the un-tilted joint law. -/
def finiteEulerLikelihoodEdgeLaw (n : ℕ) (delta : ℝ) : Measure (State d × State d) :=
  Measure.map (finiteEulerLikelihoodEdgeMap (n := n) V delta)
    (finiteEulerBaseJointMeasure (n := n) V)

/-- Ordinary Euler endpoint edge law under the likelihood-tilted joint law. -/
def finiteEulerLikelihoodTiltedEdgeLaw (n : ℕ) (delta : ℝ) : Measure (State d × State d) :=
  Measure.map (finiteEulerLikelihoodEdgeMap (n := n) V delta)
    (finiteEulerTiltedJointMeasure (n := n) V delta)

/-- Frozen-drift proposal edge law under the un-tilted joint law. -/
def finiteFrozenLikelihoodEdgeLaw (n : ℕ) (delta : ℝ) : Measure (State d × State d) :=
  Measure.map (finiteFrozenLikelihoodEdgeMap (n := n) V delta)
    (finiteEulerBaseJointMeasure (n := n) V)

/-- Endpoint Radon--Nikodym density of the tilted/frozen edge law relative
to the ordinary Euler edge law. -/
def finiteEulerLikelihoodEndpointRNDensity (n : ℕ) (delta : ℝ) :
    State d × State d → ℝ≥0∞ :=
  (finiteEulerLikelihoodTiltedEdgeLaw V n delta).rnDeriv
    (finiteEulerLikelihoodEdgeLaw V n delta)

lemma measurable_finiteEulerJointDensity (delta : ℝ) (hdelta : 0 ≤ delta) :
    Measurable (finiteEulerJointDensity V delta :
      State d × (Fin n → State d) → ℝ≥0∞) :=
  ENNReal.measurable_ofReal.comp
    (measurable_finiteGaussianDRec_initial V 1 delta hdelta n)

lemma measurable_finiteEulerLikelihoodEdgeMap (delta : ℝ) :
    Measurable (finiteEulerLikelihoodEdgeMap V delta :
      State d × (Fin n → State d) → State d × State d) :=
  measurable_fst.prodMk (measurable_finiteEulerEndpointRec_joint V delta n)

lemma measurable_finiteFrozenLikelihoodEdgeMap (delta : ℝ) :
    Measurable (finiteFrozenLikelihoodEdgeMap V delta :
      State d × (Fin n → State d) → State d × State d) := by
  have hall : ∀ m : ℕ, Measurable
      (fun p : (State d × State d) × (Fin m → State d) =>
        finiteFrozenEndpointRec V delta p.1.1 p.1.2 p.2) := by
    intro m
    induction m with
    | zero => exact measurable_snd.comp measurable_fst
    | succ m ih =>
        have hz0 : Measurable
            (fun p : (State d × State d) × (Fin (m + 1) → State d) =>
              p.2 0) :=
          (measurable_pi_apply (0 : Fin (m + 1))).comp measurable_snd
        have hstep : Measurable
            (fun p : (State d × State d) × (Fin (m + 1) → State d) =>
              finiteFrozenEulerStep V delta p.1.1 p.1.2 (p.2 0)) := by
          unfold finiteFrozenEulerStep
          exact ((measurable_snd.comp measurable_fst).sub
            ((measurable_const : Measurable fun _ :
              (State d × State d) × (Fin (m + 1) → State d) => delta).smul
              (V.continuous_gradU.measurable.comp
                (measurable_fst.comp measurable_fst)))).add
            ((measurable_const : Measurable fun _ :
              (State d × State d) × (Fin (m + 1) → State d) =>
                Real.sqrt (2 * delta)).smul hz0)
        have htail : Measurable
            (fun p : (State d × State d) × (Fin (m + 1) → State d) =>
              Fin.tail p.2) := by
          apply measurable_pi_iff.mpr
          intro k
          exact (measurable_pi_apply k.succ).comp measurable_snd
        change Measurable
          (fun p : (State d × State d) × (Fin (m + 1) → State d) =>
            finiteFrozenEndpointRec V delta p.1.1
              (finiteFrozenEulerStep V delta p.1.1 p.1.2 (p.2 0))
              (Fin.tail p.2))
        exact ih.comp
          (((measurable_fst.comp measurable_fst).prodMk hstep).prodMk htail)
  exact measurable_fst.prodMk
    (hall n |>.comp ((measurable_fst.prodMk measurable_fst).prodMk measurable_snd))

end Definitions

section TiltedEdgeLaw

variable {d n : ℕ} (V : FirstOrderPotential d)

/-- The likelihood-tilted ordinary Euler edge law is exactly the
frozen-drift proposal edge law.  The fixed-initial-state change of variables
is integrated over the stationary initial law by Tonelli. -/
theorem finiteEulerLikelihoodTiltedEdgeLaw_eq_finiteFrozenLikelihoodEdgeLaw
    (delta : ℝ) (hdelta : 0 ≤ delta) :
    finiteEulerLikelihoodTiltedEdgeLaw V n delta =
      finiteFrozenLikelihoodEdgeLaw V n delta := by
  let γ : Measure (Fin n → State d) :=
    Measure.pi (fun _ : Fin n => stdGaussian (State d))
  let μ : Measure (State d) := V.target
  let P : Measure (State d × (Fin n → State d)) := μ.prod γ
  let density : State d × (Fin n → State d) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (finiteGaussianDRec V 1 delta p.1 p.1 p.2)
  let edge : State d × (Fin n → State d) → State d × State d :=
    finiteEulerLikelihoodEdgeMap V delta
  let frozen : State d × (Fin n → State d) → State d × State d :=
    finiteFrozenLikelihoodEdgeMap V delta
  have hdensity : Measurable density :=
    ENNReal.measurable_ofReal.comp
      (measurable_finiteGaussianDRec_initial V 1 delta hdelta n)
  have hedge : Measurable edge := measurable_finiteEulerLikelihoodEdgeMap V delta
  have hfrozen : Measurable frozen :=
    measurable_finiteFrozenLikelihoodEdgeMap V delta
  change Measure.map edge (P.withDensity density) = Measure.map frozen P
  ext s hs
  rw [Measure.map_apply hedge hs, Measure.map_apply hfrozen hs]
  rw [withDensity_apply _ (hs.preimage hedge)]
  let H : State d × (Fin n → State d) → ℝ≥0∞ :=
    (edge ⁻¹' s).indicator density
  have hH : Measurable H :=
    Measurable.indicator hdensity (hs.preimage hedge)
  rw [← lintegral_indicator (hs.preimage hedge) density]
  rw [lintegral_prod H hH.aemeasurable]
  rw [Measure.prod_apply (hs.preimage hfrozen)]
  apply lintegral_congr
  intro x
  let sx : Set (State d) := {y | (x, y) ∈ s}
  have hsx : MeasurableSet sx := by
    exact hs.preimage (measurable_const.prodMk measurable_id)
  let endpoint : (Fin n → State d) → State d :=
    finiteEulerEndpointRec V delta x
  let frozenEndpoint : (Fin n → State d) → State d :=
    finiteFrozenEndpointRec V delta x x
  let densityx : (Fin n → State d) → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (finiteGaussianDRec V 1 delta x x z)
  have hendpoint : Measurable endpoint :=
    measurable_finiteEulerEndpointRec V delta x n
  have hfrozenEndpoint : Measurable frozenEndpoint :=
    measurable_finiteFrozenEndpointRec V delta x x n
  have hdensityx : Measurable densityx :=
    ENNReal.measurable_ofReal.comp
      (measurable_finiteGaussianDRec V 1 delta hdelta x n x)
  have hlaw := map_finiteEulerEndpointRec_DRec_withDensity
    V delta hdelta x x n
  have hlawSet := congrArg (fun ν : Measure (State d) => ν sx) hlaw
  rw [Measure.map_apply hendpoint hsx,
    Measure.map_apply hfrozenEndpoint hsx] at hlawSet
  rw [withDensity_apply _ (hsx.preimage hendpoint)] at hlawSet
  calc
    (∫⁻ y, H (x, y) ∂γ) =
        ∫⁻ z in endpoint ⁻¹' sx, densityx z ∂γ := by
      rw [← lintegral_indicator (hsx.preimage hendpoint) densityx]
      apply lintegral_congr
      intro z
      rfl
    _ = γ (frozenEndpoint ⁻¹' sx) := by
      simpa only [γ, endpoint, frozenEndpoint, densityx] using hlawSet
    _ = γ (Prod.mk x ⁻¹' (frozen ⁻¹' s)) := by
      congr 1

end TiltedEdgeLaw

section Contraction

variable {d n : ℕ} (V : FirstOrderPotential d)

/-- The centered real `p`-moment of the endpoint Radon--Nikodym density is
bounded by the corresponding centered moment of the full finite likelihood.

The proof embeds each joint sample as `(edge, sample)`.  This embedding keeps
the full likelihood as its RN derivative, while `EndpointContraction` erases
the sample coordinate. -/
theorem finiteEulerLikelihoodEndpointRNDensity_centered_rpow_integrable_and_integral_le
    (delta p : ℝ) (hdelta : 0 ≤ delta) (hp : 1 ≤ p)
    (hLikelihoodInt : Integrable
      (fun q : State d × (Fin n → State d) =>
        |finiteGaussianDRec V 1 delta q.1 q.1 q.2 - 1| ^ p)
      (finiteEulerBaseJointMeasure V)) :
    Integrable
        (fun e : State d × State d =>
          |(finiteEulerLikelihoodEndpointRNDensity V n delta e).toReal - 1| ^ p)
        (finiteEulerLikelihoodEdgeLaw V n delta) ∧
      (∫ e : State d × State d,
        |(finiteEulerLikelihoodEndpointRNDensity V n delta e).toReal - 1| ^ p
        ∂finiteEulerLikelihoodEdgeLaw V n delta) ≤
      ∫ q : State d × (Fin n → State d),
        |finiteGaussianDRec V 1 delta q.1 q.1 q.2 - 1| ^ p
        ∂finiteEulerBaseJointMeasure V := by
  let P : Measure (State d × (Fin n → State d)) :=
    finiteEulerBaseJointMeasure V
  let D : State d × (Fin n → State d) → ℝ := fun q =>
    finiteGaussianDRec V 1 delta q.1 q.1 q.2
  let density : State d × (Fin n → State d) → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (D q)
  let Ptilt : Measure (State d × (Fin n → State d)) :=
    P.withDensity density
  let edge : State d × (Fin n → State d) → State d × State d :=
    finiteEulerLikelihoodEdgeMap V delta
  let graph : State d × (Fin n → State d) →
      (State d × State d) × (State d × (Fin n → State d)) := fun q =>
    (edge q, q)
  let sigma : Measure
      ((State d × State d) × (State d × (Fin n → State d))) :=
    Measure.map graph P
  let rho : Measure
      ((State d × State d) × (State d × (Fin n → State d))) :=
    Measure.map graph Ptilt
  have hDMeas : Measurable D :=
    measurable_finiteGaussianDRec_initial V 1 delta hdelta n
  have hdensity : Measurable density :=
    ENNReal.measurable_ofReal.comp hDMeas
  have hedge : Measurable edge := measurable_finiteEulerLikelihoodEdgeMap V delta
  have hgraph : Measurable graph := hedge.prodMk measurable_id
  have hgraphInj : Function.Injective graph := by
    intro a b hab
    exact congrArg Prod.snd hab
  letI hStateSB : StandardBorelSpace (State d) := inferInstance
  letI hInnovSB : StandardBorelSpace (Fin n → State d) := inferInstance
  letI hJointSB : StandardBorelSpace
      (State d × (Fin n → State d)) := inferInstance
  letI hEdgeSB : StandardBorelSpace (State d × State d) := inferInstance
  letI hGraphSB : StandardBorelSpace
      ((State d × State d) × (State d × (Fin n → State d))) := inferInstance
  letI hGraphCS : MeasurableSpace.CountablySeparated
      ((State d × State d) × (State d × (Fin n → State d))) := inferInstance
  have hgraphEmb : MeasurableEmbedding graph :=
    hgraph.measurableEmbedding hgraphInj
  letI : IsProbabilityMeasure P := by
    dsimp only [P, finiteEulerBaseJointMeasure]
    infer_instance
  have hDInt : Integrable D P := by
    simpa only [D, P, finiteEulerBaseJointMeasure] using
      integrable_finiteGaussianDRec_initial V 1 delta hdelta n
  letI : IsFiniteMeasure Ptilt := by
    exact isFiniteMeasure_withDensity_ofReal hDInt.hasFiniteIntegral
  letI : IsFiniteMeasure sigma := by
    dsimp only [sigma]
    infer_instance
  letI : IsFiniteMeasure rho := by
    dsimp only [rho]
    infer_instance
  have hPtiltP : Ptilt ≪ P := by
    exact withDensity_absolutelyContinuous P density
  have hrhosigma : rho ≪ sigma := by
    exact hgraphEmb.absolutelyContinuous_map hPtiltP
  have hrnTilt :
      (fun q => (Ptilt.rnDeriv P q).toReal) =ᵐ[P] D := by
    have hrn := Measure.rnDeriv_withDensity P hdensity
    change Ptilt.rnDeriv P =ᵐ[P] density at hrn
    filter_upwards [hrn] with q hq
    rw [hq]
    exact ENNReal.toReal_ofReal (by
      dsimp only [D]
      exact (Real.exp_pos _).le)
  have hrnGraph := hgraphEmb.rnDeriv_map Ptilt P
  have hpullEq :
      (fun q => |(rho.rnDeriv sigma (graph q)).toReal - 1| ^ p) =ᵐ[P]
        fun q => |D q - 1| ^ p := by
    filter_upwards [hrnGraph, hrnTilt] with q hgraphq htiltq
    rw [hgraphq, htiltq]
  have hpullInt : Integrable
      (fun q => |(rho.rnDeriv sigma (graph q)).toReal - 1| ^ p) P := by
    have hIntP : Integrable (fun q => |D q - 1| ^ p) P := by
      simpa only [D, P] using hLikelihoodInt
    exact hIntP.congr hpullEq.symm
  let F : ((State d × State d) ×
      (State d × (Fin n → State d))) → ℝ := fun z =>
    |(rho.rnDeriv sigma z).toReal - 1| ^ p
  have hFMeas : Measurable F := by
    dsimp only [F]
    fun_prop
  have hFInt : Integrable F sigma := by
    apply (integrable_map_measure hFMeas.aestronglyMeasurable
      hgraph.aemeasurable).2
    change Integrable
      (fun q => |(rho.rnDeriv sigma (graph q)).toReal - 1| ^ p) P
    exact hpullInt
  have hcontract := integral_centered_rnDeriv_fst_rpow_le
    (rho := rho) (sigma := sigma) hp hrhosigma hFInt
  have hsigmaFst : sigma.fst = finiteEulerLikelihoodEdgeLaw V n delta := by
    dsimp only [sigma, graph, edge, finiteEulerLikelihoodEdgeLaw, P,
      finiteEulerBaseJointMeasure]
    exact Measure.fst_map_prodMk measurable_id
  have hrhoFst : rho.fst = finiteEulerLikelihoodTiltedEdgeLaw V n delta := by
    dsimp only [rho, graph, edge, finiteEulerLikelihoodTiltedEdgeLaw, Ptilt,
      finiteEulerTiltedJointMeasure, P, density, finiteEulerJointDensity,
      finiteEulerBaseJointMeasure, D]
    exact Measure.fst_map_prodMk measurable_id
  have hfullIntegral :
      (∫ z, F z ∂sigma) =
        ∫ q : State d × (Fin n → State d), |D q - 1| ^ p ∂P := by
    dsimp only [sigma]
    rw [integral_map hgraph.aemeasurable hFMeas.aestronglyMeasurable]
    exact integral_congr_ae hpullEq
  rw [hsigmaFst, hrhoFst] at hcontract
  constructor
  · simpa only [finiteEulerLikelihoodEndpointRNDensity] using hcontract.1
  · calc
      (∫ e : State d × State d,
        |(finiteEulerLikelihoodEndpointRNDensity V n delta e).toReal - 1| ^ p
        ∂finiteEulerLikelihoodEdgeLaw V n delta) ≤ ∫ z, F z ∂sigma := by
          simpa only [finiteEulerLikelihoodEndpointRNDensity, F] using hcontract.2
      _ = ∫ q : State d × (Fin n → State d),
          |finiteGaussianDRec V 1 delta q.1 q.1 q.2 - 1| ^ p
          ∂finiteEulerBaseJointMeasure V := by
        simpa only [D, P] using hfullIntegral

end Contraction

section ConcreteBounds

variable {d n : ℕ} (V : FirstOrderPotential d)

/-- After identifying the tilted edge law with the frozen-drift proposal,
the endpoint density is literally the proposal-over-Euler Radon--Nikodym
density. -/
theorem finiteEulerLikelihoodEndpointRNDensity_eq_frozen_rnDeriv
    (delta : ℝ) (hdelta : 0 ≤ delta) :
    finiteEulerLikelihoodEndpointRNDensity V n delta =
      (finiteFrozenLikelihoodEdgeLaw V n delta).rnDeriv
        (finiteEulerLikelihoodEdgeLaw V n delta) := by
  unfold finiteEulerLikelihoodEndpointRNDensity
  rw [finiteEulerLikelihoodTiltedEdgeLaw_eq_finiteFrozenLikelihoodEdgeLaw
    V delta hdelta]

/-- Dimension-explicit centered `L²` contraction from the full finite
Gaussian likelihood to the endpoint density. -/
theorem
    finiteEulerLikelihoodEndpointRNDensity_centered_sq_integrable_and_integral_le_linear
    (hd : 0 < d) (hn : 0 < n) (delta h : ℝ)
    (hdelta : 0 ≤ delta)
    (hhorizon : (n : ℝ) * delta = h)
    (hsmallDim :
      192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 * d ≤ 1) :
    Integrable
        (fun e : State d × State d =>
          ((finiteEulerLikelihoodEndpointRNDensity V n delta e).toReal - 1) ^ 2)
        (finiteEulerLikelihoodEdgeLaw V n delta) ∧
      (∫ e : State d × State d,
        ((finiteEulerLikelihoodEndpointRNDensity V n delta e).toReal - 1) ^ 2
        ∂finiteEulerLikelihoodEdgeLaw V n delta) ≤
      96 * (Real.exp 1) ^ 3 * V.L ^ 2 * h ^ 2 * d := by
  obtain ⟨hLikelihoodInt, hLikelihoodBound⟩ :=
    finiteEulerLikelihood_centered_sq_integrable_and_integral_le_linear
      V hd hn delta h hdelta hhorizon hsmallDim
  have hLikelihoodRpowInt : Integrable
      (fun q : State d × (Fin n → State d) =>
        |finiteGaussianDRec V 1 delta q.1 q.1 q.2 - 1| ^ (2 : ℝ))
      (finiteEulerBaseJointMeasure V) := by
    simpa only [Real.rpow_two, sq_abs, finiteEulerBaseJointMeasure] using
      hLikelihoodInt
  obtain ⟨hEndpointInt, hEndpointBound⟩ :=
    finiteEulerLikelihoodEndpointRNDensity_centered_rpow_integrable_and_integral_le
      V delta (2 : ℝ) hdelta (by norm_num) hLikelihoodRpowInt
  constructor
  · simpa only [Real.rpow_two, sq_abs] using hEndpointInt
  · calc
      (∫ e : State d × State d,
        ((finiteEulerLikelihoodEndpointRNDensity V n delta e).toReal - 1) ^ 2
        ∂finiteEulerLikelihoodEdgeLaw V n delta) ≤
          ∫ q : State d × (Fin n → State d),
            |finiteGaussianDRec V 1 delta q.1 q.1 q.2 - 1| ^ (2 : ℝ)
            ∂finiteEulerBaseJointMeasure V := by
        simpa only [Real.rpow_two, sq_abs] using hEndpointBound
      _ ≤ 96 * (Real.exp 1) ^ 3 * V.L ^ 2 * h ^ 2 * d := by
        simpa only [Real.rpow_two, sq_abs, finiteEulerBaseJointMeasure] using
          hLikelihoodBound

/-- Paper-facing form: the frozen-drift proposal edge density relative to
the ordinary Euler edge law has centered `L²` norm controlled by the full
finite likelihood, with no conditional expectation construction. -/
theorem finiteFrozenLikelihoodEdge_rnDeriv_centered_sq_integrable_and_integral_le_linear
    (hd : 0 < d) (hn : 0 < n) (delta h : ℝ)
    (hdelta : 0 ≤ delta)
    (hhorizon : (n : ℝ) * delta = h)
    (hsmallDim :
      192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 * d ≤ 1) :
    Integrable
        (fun e : State d × State d =>
          (((finiteFrozenLikelihoodEdgeLaw V n delta).rnDeriv
            (finiteEulerLikelihoodEdgeLaw V n delta) e).toReal - 1) ^ 2)
        (finiteEulerLikelihoodEdgeLaw V n delta) ∧
      (∫ e : State d × State d,
        (((finiteFrozenLikelihoodEdgeLaw V n delta).rnDeriv
          (finiteEulerLikelihoodEdgeLaw V n delta) e).toReal - 1) ^ 2
        ∂finiteEulerLikelihoodEdgeLaw V n delta) ≤
      96 * (Real.exp 1) ^ 3 * V.L ^ 2 * h ^ 2 * d := by
  simpa only [finiteEulerLikelihoodEndpointRNDensity_eq_frozen_rnDeriv
    V delta hdelta] using
    finiteEulerLikelihoodEndpointRNDensity_centered_sq_integrable_and_integral_le_linear
      V hd hn delta h hdelta hhorizon hsmallDim

/-- Endpoint data processing in root-moment form.  The right side is the
full path likelihood root moment, so any path-level estimate can be passed
through without changing its constant. -/
theorem
    finiteFrozenLikelihoodEdge_rnDeriv_centered_rpow_integrable_and_root_le_full
    (delta p : ℝ) (hdelta : 0 ≤ delta) (hp : 1 ≤ p)
    (hLikelihoodInt : Integrable
      (fun q : State d × (Fin n → State d) =>
        |finiteGaussianDRec V 1 delta q.1 q.1 q.2 - 1| ^ p)
      (finiteEulerBaseJointMeasure V)) :
    Integrable
        (fun e : State d × State d =>
          |((finiteFrozenLikelihoodEdgeLaw V n delta).rnDeriv
            (finiteEulerLikelihoodEdgeLaw V n delta) e).toReal - 1| ^ p)
        (finiteEulerLikelihoodEdgeLaw V n delta) ∧
      ((∫ e : State d × State d,
        |((finiteFrozenLikelihoodEdgeLaw V n delta).rnDeriv
          (finiteEulerLikelihoodEdgeLaw V n delta) e).toReal - 1| ^ p
        ∂finiteEulerLikelihoodEdgeLaw V n delta) ^ (1 / p)) ≤
      ((∫ q : State d × (Fin n → State d),
        |finiteGaussianDRec V 1 delta q.1 q.1 q.2 - 1| ^ p
        ∂finiteEulerBaseJointMeasure V) ^ (1 / p)) := by
  obtain ⟨hEndpointInt, hEndpointMoment⟩ :=
    finiteEulerLikelihoodEndpointRNDensity_centered_rpow_integrable_and_integral_le
      V delta p hdelta hp hLikelihoodInt
  have hEndpointNonneg : 0 ≤
      ∫ e : State d × State d,
        |(finiteEulerLikelihoodEndpointRNDensity V n delta e).toReal - 1| ^ p
        ∂finiteEulerLikelihoodEdgeLaw V n delta :=
    integral_nonneg_of_ae (ae_of_all _ fun e =>
      Real.rpow_nonneg (abs_nonneg _) p)
  have hRoot := Real.rpow_le_rpow hEndpointNonneg hEndpointMoment
    (by positivity : 0 ≤ 1 / p)
  rw [finiteEulerLikelihoodEndpointRNDensity_eq_frozen_rnDeriv
    V delta hdelta] at hEndpointInt hRoot
  exact ⟨hEndpointInt, hRoot⟩

/-- A numerical full-likelihood root bound is inherited verbatim by the
frozen-proposal endpoint density. -/
theorem finiteFrozenLikelihoodEdge_rnDeriv_centered_rpow_integrable_and_root_le
    (delta p B : ℝ) (hdelta : 0 ≤ delta) (hp : 1 ≤ p)
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
          |((finiteFrozenLikelihoodEdgeLaw V n delta).rnDeriv
            (finiteEulerLikelihoodEdgeLaw V n delta) e).toReal - 1| ^ p)
        (finiteEulerLikelihoodEdgeLaw V n delta) ∧
      ((∫ e : State d × State d,
        |((finiteFrozenLikelihoodEdgeLaw V n delta).rnDeriv
          (finiteEulerLikelihoodEdgeLaw V n delta) e).toReal - 1| ^ p
        ∂finiteEulerLikelihoodEdgeLaw V n delta) ^ (1 / p)) ≤ B := by
  obtain ⟨hEndpointInt, hEndpointRoot⟩ :=
    finiteFrozenLikelihoodEdge_rnDeriv_centered_rpow_integrable_and_root_le_full
      V delta p hdelta hp hLikelihoodInt
  exact ⟨hEndpointInt, hEndpointRoot.trans hLikelihoodRoot⟩

end ConcreteBounds

end DiscreteTime

end

end UniformRandomMALA
