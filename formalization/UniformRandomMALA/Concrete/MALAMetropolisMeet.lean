import UniformRandomMALA.Concrete.MALAOverlapFromRejection
import UniformRandomMALA.Concrete.MALAAcceptedMeet
import UniformRandomMALA.DiscreteTime.MetropolisMeet
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub

/-!
# Identifying the limiting Metropolis meet with stationary MALA rejection

This file packages the final step after construction of the symmetric weak
endpoint limit.  A certificate records only the Radon--Nikodym description of
the oriented MALA proposal edge law and the centered likelihood moment bound.
The accepted-meet and rejected-marginal identifications are derived below.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace Concrete
namespace FirstOrderPotential

variable {d : ℕ} (V : FirstOrderPotential d)

/-- Data identifying a symmetric endpoint reference law with a concrete
fixed-step MALA proposal and rejection marginal.

`proposalRN` states that `F` is the real RN density of the oriented proposal
edge law relative to `sigma`.  Both endpoint marginals are recorded
explicitly. -/
structure MALAProposalMeetCertificate (h p M : ℝ) where
  step_pos : 0 < h
  moment_one : 1 ≤ p
  scale_nonneg : 0 ≤ M
  sigma : Measure (State d × State d)
  F : State d × State d → ℝ
  isProbability : IsProbabilityMeasure sigma
  measurable_F : Measurable F
  F_nonneg : ∀ z, 0 ≤ F z
  swap_invariant : Measure.map Prod.swap sigma = sigma
  fst_eq_target : sigma.fst = (V.target : Measure (State d))
  snd_eq_target : sigma.snd = (V.target : Measure (State d))
  proposalRN :
    ((V.target : Measure (State d)) ⊗ₘ V.gaussianDensityProposal h) =
      sigma.withDensity (fun z => ENNReal.ofReal (F z))
  centered_integrable : Integrable (fun z => |F z - 1| ^ p) sigma
  centered_moment_le : (∫ z, |F z - 1| ^ p ∂sigma) ≤ M ^ p

/-- Build a meet certificate from the canonical RN derivative of the MALA
proposal edge law.  Finiteness of the probability edge law ensures that
`ofReal (rnDeriv.toReal)` agrees a.e. with the ENNReal RN derivative. -/
def MALAProposalMeetCertificate.ofRNDeriv
    {h p M : ℝ} (hh : 0 < h) (hp : 1 ≤ p) (hM : 0 ≤ M)
    {sigma : Measure (State d × State d)} [IsProbabilityMeasure sigma]
    (hsymm : Measure.map Prod.swap sigma = sigma)
    (hfst : sigma.fst = (V.target : Measure (State d)))
    (hsnd : sigma.snd = (V.target : Measure (State d)))
    (hac : ((V.target : Measure (State d)) ⊗ₘ
      V.gaussianDensityProposal h) ≪ sigma)
    (hInt : Integrable (fun z =>
      |((((V.target : Measure (State d)) ⊗ₘ
        V.gaussianDensityProposal h).rnDeriv sigma) z).toReal - 1| ^ p) sigma)
    (hMoment : (∫ z,
      |((((V.target : Measure (State d)) ⊗ₘ
        V.gaussianDensityProposal h).rnDeriv sigma) z).toReal - 1| ^ p ∂sigma) ≤
        M ^ p) :
    V.MALAProposalMeetCertificate h p M := by
  letI : Fact (0 < h) := ⟨hh⟩
  let edge : Measure (State d × State d) :=
    (V.target : Measure (State d)) ⊗ₘ V.gaussianDensityProposal h
  letI : IsProbabilityMeasure edge := by
    dsimp [edge]
    infer_instance
  let F : State d × State d → ℝ := fun z =>
    ((edge.rnDeriv sigma) z).toReal
  have hFmeas : Measurable F := by
    exact ENNReal.measurable_toReal.comp (edge.measurable_rnDeriv sigma)
  have hRN : edge = sigma.withDensity (fun z => ENNReal.ofReal (F z)) := by
    calc
      edge = sigma.withDensity (edge.rnDeriv sigma) :=
        (edge.withDensity_rnDeriv_eq sigma hac).symm
      _ = sigma.withDensity (fun z => ENNReal.ofReal (F z)) := by
        apply withDensity_congr_ae
        filter_upwards [edge.rnDeriv_ne_top sigma] with z hz
        exact (ENNReal.ofReal_toReal hz).symm
  refine
    { step_pos := hh
      moment_one := hp
      scale_nonneg := hM
      sigma := sigma
      F := F
      isProbability := inferInstance
      measurable_F := hFmeas
      F_nonneg := fun z => ENNReal.toReal_nonneg
      swap_invariant := hsymm
      fst_eq_target := hfst
      snd_eq_target := hsnd
      proposalRN := by simpa only [edge] using hRN
      centered_integrable := by simpa only [F, edge] using hInt
      centered_moment_le := by simpa only [F, edge] using hMoment }

/-- Rejected meet marginal with the certificate's probability instance made
explicit internally. -/
def MALAProposalMeetCertificate.meetRejectionMarginal
    {h p M : ℝ} (c : V.MALAProposalMeetCertificate h p M) : State d → ℝ := by
  letI : IsProbabilityMeasure c.sigma := c.isProbability
  exact DiscreteTime.rejectionMarginal c.sigma c.F

private theorem kernel_apply_univ_ae_eq_of_compProd_eq
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {mu : Measure X} [SigmaFinite mu]
    {kappa eta : Kernel X Y} [IsSFiniteKernel kappa] [IsSFiniteKernel eta]
    (h : mu ⊗ₘ kappa = mu ⊗ₘ eta) :
    (fun x => kappa x Set.univ) =ᵐ[mu] (fun x => eta x Set.univ) := by
  apply ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
    (kappa.measurable_coe MeasurableSet.univ)
    (eta.measurable_coe MeasurableSet.univ)
  intro s hs _hsfin
  rw [← Measure.compProd_apply_prod hs MeasurableSet.univ, h,
    Measure.compProd_apply_prod hs MeasurableSet.univ]

/-- The RN proposal identity and the accepted-flow meet identity imply the
target-a.e. identification of the concrete rejection probability with the
rejected meet marginal. -/
theorem malaRejection_eq_rejectionMarginal
    {h p M : ℝ} (c : V.MALAProposalMeetCertificate h p M) :
    (fun x : State d =>
      (1 - MetropolisHastings.acceptanceMass
        (V.gaussianDensityProposal h) (V.malaAcceptance h) x).toReal) =ᵐ[
      (V.target : Measure (State d))]
        c.meetRejectionMarginal := by
  letI : IsProbabilityMeasure c.sigma := c.isProbability
  letI : Fact (0 < h) := ⟨c.step_pos⟩
  let kF : Kernel (State d) (State d) :=
    Kernel.withDensity c.sigma.condKernel
      (fun x y => ENNReal.ofReal (c.F (x, y)))
  let kMin : Kernel (State d) (State d) :=
    Kernel.withDensity c.sigma.condKernel
      (fun x y => ENNReal.ofReal (min (c.F (x, y)) (c.F (y, x))))
  letI : IsSFiniteKernel kF := by
    dsimp [kF]
    exact Kernel.IsSFiniteKernel.withDensity _ fun _ _ => ENNReal.ofReal_ne_top
  letI : IsSFiniteKernel kMin := by
    dsimp [kMin]
    exact Kernel.IsSFiniteKernel.withDensity _ fun _ _ => ENNReal.ofReal_ne_top
  letI : IsSFiniteKernel (MetropolisHastings.accepted
      (V.gaussianDensityProposal h) (V.malaAcceptance h)) := by
    unfold MetropolisHastings.accepted
    exact Kernel.IsSFiniteKernel.withDensity _ fun x y =>
      ne_top_of_le_ne_top ENNReal.one_ne_top (V.malaAcceptance_le_one h x y)
  have hFpair : Measurable (Function.uncurry
      (fun x y => ENNReal.ofReal (c.F (x, y)))) :=
    ENNReal.measurable_ofReal.comp c.measurable_F
  have hMinReal : Measurable (fun z => min (c.F z) (c.F (Prod.swap z))) :=
    c.measurable_F.min (c.measurable_F.comp measurable_swap)
  have hMinPair : Measurable (Function.uncurry
      (fun x y => ENNReal.ofReal (min (c.F (x, y)) (c.F (y, x))))) := by
    exact ENNReal.measurable_ofReal.comp hMinReal
  have hsigma :
      (V.target : Measure (State d)) ⊗ₘ c.sigma.condKernel = c.sigma := by
    rw [← c.fst_eq_target]
    exact c.sigma.disintegrate c.sigma.condKernel
  have hproposalComp :
      (V.target : Measure (State d)) ⊗ₘ V.gaussianDensityProposal h =
        (V.target : Measure (State d)) ⊗ₘ kF := by
    calc
      (V.target : Measure (State d)) ⊗ₘ V.gaussianDensityProposal h =
          c.sigma.withDensity (fun z => ENNReal.ofReal (c.F z)) := c.proposalRN
      _ = ((V.target : Measure (State d)) ⊗ₘ c.sigma.condKernel).withDensity
          (fun z => ENNReal.ofReal (c.F z)) := by rw [hsigma]
      _ = (V.target : Measure (State d)) ⊗ₘ kF := by
        symm
        exact Measure.compProd_withDensity hFpair
  have hacceptedComp :
      (V.target : Measure (State d)) ⊗ₘ
          MetropolisHastings.accepted
            (V.gaussianDensityProposal h) (V.malaAcceptance h) =
        (V.target : Measure (State d)) ⊗ₘ kMin := by
    calc
      (V.target : Measure (State d)) ⊗ₘ
          MetropolisHastings.accepted
            (V.gaussianDensityProposal h) (V.malaAcceptance h) =
          c.sigma.withDensity (fun z =>
            ENNReal.ofReal (min (c.F z) (c.F (Prod.swap z)))) :=
        V.malaAcceptedEdge_eq_rnMeet c.step_pos c.measurable_F
          c.swap_invariant c.proposalRN
      _ = ((V.target : Measure (State d)) ⊗ₘ c.sigma.condKernel).withDensity
          (fun z => ENNReal.ofReal (min (c.F z) (c.F (Prod.swap z)))) := by rw [hsigma]
      _ = (V.target : Measure (State d)) ⊗ₘ kMin := by
        symm
        exact Measure.compProd_withDensity hMinPair
  have hproposalUniv := kernel_apply_univ_ae_eq_of_compProd_eq hproposalComp
  have hacceptedUniv := kernel_apply_univ_ae_eq_of_compProd_eq hacceptedComp
  have hmeetPow := DiscreteTime.integral_rejectedMeetDensity_rpow_le
    c.moment_one c.measurable_F c.swap_invariant c.centered_integrable
  have hRejectedMeas : Measurable (DiscreteTime.rejectedMeetDensity c.F) := by
    unfold DiscreteTime.rejectedMeetDensity
    exact c.measurable_F.sub
      (c.measurable_F.min (c.measurable_F.comp measurable_swap))
  have hRejectedInt : Integrable (DiscreteTime.rejectedMeetDensity c.F) c.sigma :=
    DiscreteTime.integrable_of_nonneg_rpow_integrable c.moment_one
      hRejectedMeas (DiscreteTime.rejectedMeetDensity_nonneg c.F) hmeetPow.1
  have hRejectedIntComp : Integrable (DiscreteTime.rejectedMeetDensity c.F)
      ((V.target : Measure (State d)) ⊗ₘ c.sigma.condKernel) := by
    rwa [hsigma]
  have hFiberInt : ∀ᵐ x ∂(V.target : Measure (State d)),
      Integrable (fun y => DiscreteTime.rejectedMeetDensity c.F (x, y))
        (c.sigma.condKernel x) := hRejectedIntComp.ae_of_compProd
  filter_upwards [hproposalUniv, hacceptedUniv, hFiberInt] with x hxQ hxA hxInt
  have hQone : V.gaussianDensityProposal h x Set.univ = 1 := by simp
  have hkFone : kF x Set.univ = 1 := hxQ ▸ hQone
  have hFIntegral :
      ∫⁻ y, ENNReal.ofReal (c.F (x, y)) ∂c.sigma.condKernel x = 1 := by
    simpa [kF, Kernel.withDensity_apply' c.sigma.condKernel hFpair] using hkFone
  have hAccepted :
      MetropolisHastings.accepted
          (V.gaussianDensityProposal h) (V.malaAcceptance h) x Set.univ =
        MetropolisHastings.acceptanceMass
          (V.gaussianDensityProposal h) (V.malaAcceptance h) x :=
    MetropolisHastings.accepted_apply_univ _ _
      (V.measurable_uncurry_malaAcceptance h) x
  have hMinIntegral :
      ∫⁻ y, ENNReal.ofReal (min (c.F (x, y)) (c.F (y, x)))
          ∂c.sigma.condKernel x =
        MetropolisHastings.acceptanceMass
          (V.gaussianDensityProposal h) (V.malaAcceptance h) x := by
    calc
      (∫⁻ y, ENNReal.ofReal (min (c.F (x, y)) (c.F (y, x)))
          ∂c.sigma.condKernel x) = kMin x Set.univ := by
        change _ = (Kernel.withDensity c.sigma.condKernel
          (fun x y => ENNReal.ofReal (min (c.F (x, y)) (c.F (y, x))))) x Set.univ
        rw [Kernel.withDensity_apply' c.sigma.condKernel hMinPair]
        simp only [Measure.restrict_univ]
      _ = MetropolisHastings.accepted
          (V.gaussianDensityProposal h) (V.malaAcceptance h) x Set.univ := hxA.symm
      _ = _ := hAccepted
  have hMin0 (y : State d) : 0 ≤ min (c.F (x, y)) (c.F (y, x)) :=
    le_min (c.F_nonneg (x, y)) (c.F_nonneg (y, x))
  have hMinMeas : Measurable
      (fun y => ENNReal.ofReal (min (c.F (x, y)) (c.F (y, x)))) :=
    Measurable.of_uncurry_left hMinPair
  have hMinFin :
      (∫⁻ y, ENNReal.ofReal (min (c.F (x, y)) (c.F (y, x)))
          ∂c.sigma.condKernel x) ≠ ∞ := by
    rw [hMinIntegral]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top
      (MetropolisHastings.acceptanceMass_le_one
        (V.gaussianDensityProposal h) (V.malaAcceptance h)
        (V.malaAcceptance_le_one h) x)
  have hlin :
      (∫⁻ y, ENNReal.ofReal (DiscreteTime.rejectedMeetDensity c.F (x, y))
          ∂c.sigma.condKernel x) =
        1 - MetropolisHastings.acceptanceMass
          (V.gaussianDensityProposal h) (V.malaAcceptance h) x := by
    calc
      (∫⁻ y, ENNReal.ofReal (DiscreteTime.rejectedMeetDensity c.F (x, y))
          ∂c.sigma.condKernel x) =
          ∫⁻ y, ENNReal.ofReal (c.F (x, y)) -
            ENNReal.ofReal (min (c.F (x, y)) (c.F (y, x)))
              ∂c.sigma.condKernel x := by
        apply lintegral_congr
        intro y
        exact ENNReal.ofReal_sub _ (hMin0 y)
      _ = (∫⁻ y, ENNReal.ofReal (c.F (x, y)) ∂c.sigma.condKernel x) -
          ∫⁻ y, ENNReal.ofReal (min (c.F (x, y)) (c.F (y, x)))
            ∂c.sigma.condKernel x := lintegral_sub hMinMeas hMinFin
              (ae_of_all _ fun y => ENNReal.ofReal_mono (min_le_left _ _))
      _ = _ := by rw [hFIntegral, hMinIntegral]
  have hIntegralToReal :
      ∫ y, DiscreteTime.rejectedMeetDensity c.F (x, y) ∂c.sigma.condKernel x =
        (∫⁻ y, ENNReal.ofReal (DiscreteTime.rejectedMeetDensity c.F (x, y))
          ∂c.sigma.condKernel x).toReal := by
    calc
      (∫ y, DiscreteTime.rejectedMeetDensity c.F (x, y)
          ∂c.sigma.condKernel x) =
          ∫ y, (ENNReal.ofReal
            (DiscreteTime.rejectedMeetDensity c.F (x, y))).toReal
              ∂c.sigma.condKernel x := by
        apply integral_congr_ae
        exact ae_of_all _ fun y => by
          exact (ENNReal.toReal_ofReal
            (DiscreteTime.rejectedMeetDensity_nonneg c.F (x, y))).symm
      _ = _ := integral_toReal
        ((ENNReal.measurable_ofReal.comp
          (hRejectedMeas.comp (measurable_const.prodMk measurable_id))).aemeasurable)
        (ae_of_all _ fun y => ENNReal.ofReal_lt_top)
  change _ = ∫ y, DiscreteTime.rejectedMeetDensity c.F (x, y)
    ∂c.sigma.condKernel x
  rw [hIntegralToReal, hlin]

/-- The existing symmetric-meet theorem, transferred to the concrete MALA
rejection probability through the derived marginal identity. Before inserting a
numerical centered-likelihood bound, this retains the exact factor produced
by the elementary two-term power inequality. -/
theorem integral_malaRejection_rpow_le_of_meetCertificate
    {h p M : ℝ} (c : V.MALAProposalMeetCertificate h p M) :
    Integrable (fun x : State d =>
      ((1 - MetropolisHastings.acceptanceMass
        (V.gaussianDensityProposal h) (V.malaAcceptance h) x).toReal) ^ p)
      (V.target : Measure (State d)) ∧
    (∫ x : State d,
      ((1 - MetropolisHastings.acceptanceMass
        (V.gaussianDensityProposal h) (V.malaAcceptance h) x).toReal) ^ p
        ∂(V.target : Measure (State d))) ≤
      2 ^ (p - 1) *
        ((∫ z, |c.F z - 1| ^ p ∂c.sigma) +
          ∫ z, |c.F z - 1| ^ p ∂c.sigma) := by
  letI : IsProbabilityMeasure c.sigma := c.isProbability
  have hmeet := DiscreteTime.integral_rejectionMarginal_rpow_le
    c.moment_one c.measurable_F c.swap_invariant c.centered_integrable
  rw [c.fst_eq_target] at hmeet
  have hrejection := V.malaRejection_eq_rejectionMarginal c
  have heqpow :
      (fun x : State d =>
        ((1 - MetropolisHastings.acceptanceMass
          (V.gaussianDensityProposal h) (V.malaAcceptance h) x).toReal) ^ p) =ᵐ[
        (V.target : Measure (State d))]
      (fun x => (DiscreteTime.rejectionMarginal c.sigma c.F x) ^ p) := by
    filter_upwards [hrejection] with x hx
    calc
      ((1 - MetropolisHastings.acceptanceMass
        (V.gaussianDensityProposal h) (V.malaAcceptance h) x).toReal) ^ p =
          (MALAProposalMeetCertificate.meetRejectionMarginal V c x) ^ p :=
        congrArg (fun u : ℝ => u ^ p) hx
      _ = (DiscreteTime.rejectionMarginal c.sigma c.F x) ^ p := by rfl
  refine ⟨(integrable_congr heqpow).mpr hmeet.1, ?_⟩
  calc
    (∫ x : State d,
      ((1 - MetropolisHastings.acceptanceMass
        (V.gaussianDensityProposal h) (V.malaAcceptance h) x).toReal) ^ p
        ∂(V.target : Measure (State d))) =
        ∫ x : State d,
          (DiscreteTime.rejectionMarginal c.sigma c.F x) ^ p
            ∂(V.target : Measure (State d)) := integral_congr_ae heqpow
    _ ≤ 2 ^ (p - 1) *
        ((∫ z, |c.F z - 1| ^ p ∂c.sigma) +
          ∫ z, |c.F z - 1| ^ p ∂c.sigma) := hmeet.2

/-- A centered endpoint-likelihood bound `M` gives the concrete stationary
MALA rejection bound `2 M`. -/
theorem integral_malaRejection_rpow_le_two_mul
    {h p M : ℝ} (c : V.MALAProposalMeetCertificate h p M) :
    (∫ x : State d,
      ((1 - MetropolisHastings.acceptanceMass
        (V.gaussianDensityProposal h) (V.malaAcceptance h) x).toReal) ^ p
        ∂(V.target : Measure (State d))) ≤ (2 * M) ^ p := by
  have hmeet := (V.integral_malaRejection_rpow_le_of_meetCertificate c).2
  calc
    (∫ x : State d,
      ((1 - MetropolisHastings.acceptanceMass
        (V.gaussianDensityProposal h) (V.malaAcceptance h) x).toReal) ^ p
        ∂(V.target : Measure (State d))) ≤
        2 ^ (p - 1) * (M ^ p + M ^ p) :=
      hmeet.trans (mul_le_mul_of_nonneg_left
        (add_le_add c.centered_moment_le c.centered_moment_le)
        (Real.rpow_nonneg (by norm_num) _))
    _ = 2 ^ p * M ^ p := by
      rw [Real.rpow_sub_one (by norm_num : (2 : ℝ) ≠ 0)]
      ring
    _ = (2 * M) ^ p :=
      (Real.mul_rpow (by norm_num) c.scale_nonneg).symm

/-- Family form of the post-weak-limit step.  Certificates with centered
likelihood scale `(Cr/6) L h sqrt(p(d+p))` imply exactly the rejection moment
hypothesis used by `Concrete.MALAOverlapFromRejection`; the meet inequality contributes
the factor two, changing `Cr/6` to `Cr/3`. -/
theorem stationaryMALARejectionMomentBound_of_meetCertificates
    {cr Cr : ℝ}
    (hcert : ∀ p h : ℝ, 2 ≤ p → 0 < h →
      h ≤ cr / (V.L * Real.sqrt (p * ((d : ℝ) + p))) →
      V.MALAProposalMeetCertificate h p
        ((Cr / 6) * V.L * h * Real.sqrt (p * ((d : ℝ) + p)))) :
    V.StationaryMALARejectionMomentBound cr Cr := by
  intro p h hp hh hstep
  let M : ℝ := (Cr / 6) * V.L * h * Real.sqrt (p * ((d : ℝ) + p))
  let c := hcert p h hp hh hstep
  have hbound := V.integral_malaRejection_rpow_le_two_mul c
  have hscale : 2 * M =
      (Cr / 3) * V.L * h * Real.sqrt (p * ((d : ℝ) + p)) := by
    dsimp [M]
    ring
  rwa [hscale] at hbound

/-- Direct family form for the output of an endpoint weak-limit argument.
For every admissible exponent and step, it is enough to produce a symmetric
probability reference law with target marginals, domination of the oriented
MALA proposal edge, and the displayed centered RN-derivative root bound.

The RN derivative itself supplies the density, measurability, and
nonnegativity fields of `MALAProposalMeetCertificate`; the elementary meet
argument then supplies the stationary rejection estimate. -/
theorem stationaryMALARejectionMomentBound_of_rnDeriv_family
    {cr Cr : ℝ} (hCr : 0 ≤ Cr)
    (hRN : ∀ p h : ℝ, 2 ≤ p → 0 < h →
      h ≤ cr / (V.L * Real.sqrt (p * ((d : ℝ) + p))) →
      ∃ sigma : Measure (State d × State d),
        IsProbabilityMeasure sigma ∧
        Measure.map Prod.swap sigma = sigma ∧
        sigma.fst = (V.target : Measure (State d)) ∧
        sigma.snd = (V.target : Measure (State d)) ∧
        ((V.target : Measure (State d)) ⊗ₘ
          V.gaussianDensityProposal h) ≪ sigma ∧
        Integrable (fun z =>
          |((((V.target : Measure (State d)) ⊗ₘ
            V.gaussianDensityProposal h).rnDeriv sigma) z).toReal - 1| ^ p)
          sigma ∧
        ((∫ z,
          |((((V.target : Measure (State d)) ⊗ₘ
            V.gaussianDensityProposal h).rnDeriv sigma) z).toReal - 1| ^ p
              ∂sigma) ^ (1 / p) ≤
          (Cr / 6) * V.L * h * Real.sqrt (p * ((d : ℝ) + p)))) :
    V.StationaryMALARejectionMomentBound cr Cr := by
  apply V.stationaryMALARejectionMomentBound_of_meetCertificates
  intro p h hp hh hstep
  let hex := hRN p h hp hh hstep
  let sigma : Measure (State d × State d) := Classical.choose hex
  have hdata := Classical.choose_spec hex
  letI : IsProbabilityMeasure sigma := hdata.1
  have hsymm := hdata.2.1
  have hfst := hdata.2.2.1
  have hsnd := hdata.2.2.2.1
  have hac := hdata.2.2.2.2.1
  have hInt := hdata.2.2.2.2.2.1
  have hRoot := hdata.2.2.2.2.2.2
  let M : ℝ := (Cr / 6) * V.L * h * Real.sqrt (p * ((d : ℝ) + p))
  have hp_pos : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  have hM : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (div_nonneg hCr (by norm_num)) V.hL.le) hh.le)
      (Real.sqrt_nonneg _)
  have hMomentNonneg : 0 ≤
      ∫ z,
        |((((V.target : Measure (State d)) ⊗ₘ
          V.gaussianDensityProposal h).rnDeriv sigma) z).toReal - 1| ^ p
            ∂sigma := by
    apply integral_nonneg
    intro z
    exact Real.rpow_nonneg (abs_nonneg _) _
  have hMoment :
      (∫ z,
        |((((V.target : Measure (State d)) ⊗ₘ
          V.gaussianDensityProposal h).rnDeriv sigma) z).toReal - 1| ^ p
            ∂sigma) ≤ M ^ p := by
    have hpow := (Real.rpow_le_rpow_iff
      (Real.rpow_nonneg hMomentNonneg (1 / p)) hM hp_pos).2 (by
        simpa only [M] using hRoot)
    rw [← Real.rpow_mul hMomentNonneg, one_div, inv_mul_cancel₀ hp_ne,
      Real.rpow_one] at hpow
    exact hpow
  exact MALAProposalMeetCertificate.ofRNDeriv V hh (by linarith) hM
    hsymm hfst hsnd hac hInt hMoment

/-- Variant of `stationaryMALARejectionMomentBound_of_rnDeriv_family` whose
integrability input is the `MemLp` conclusion produced directly by
`DiscreteTime.rnDeriv_memLp_of_moving_withDensity`.  Since `sigma` is a
probability measure and `p > 0`, membership in `L^p` implies integrability of
the explicit real `p`-th power used by the meet certificate. -/
theorem stationaryMALARejectionMomentBound_of_rnDeriv_memLp_family
    {cr Cr : ℝ} (hCr : 0 ≤ Cr)
    (hRN : ∀ p h : ℝ, 2 ≤ p → 0 < h →
      h ≤ cr / (V.L * Real.sqrt (p * ((d : ℝ) + p))) →
      ∃ sigma : Measure (State d × State d),
        IsProbabilityMeasure sigma ∧
        Measure.map Prod.swap sigma = sigma ∧
        sigma.fst = (V.target : Measure (State d)) ∧
        sigma.snd = (V.target : Measure (State d)) ∧
        ((V.target : Measure (State d)) ⊗ₘ
          V.gaussianDensityProposal h) ≪ sigma ∧
        MemLp (fun z =>
          ((((V.target : Measure (State d)) ⊗ₘ
            V.gaussianDensityProposal h).rnDeriv sigma) z).toReal - 1)
          (ENNReal.ofReal p) sigma ∧
        ((∫ z,
          |((((V.target : Measure (State d)) ⊗ₘ
            V.gaussianDensityProposal h).rnDeriv sigma) z).toReal - 1| ^ p
              ∂sigma) ^ (1 / p) ≤
          (Cr / 6) * V.L * h * Real.sqrt (p * ((d : ℝ) + p)))) :
    V.StationaryMALARejectionMomentBound cr Cr := by
  apply V.stationaryMALARejectionMomentBound_of_rnDeriv_family hCr
  intro p h hp hh hstep
  obtain ⟨sigma, hsigma, hsymm, hfst, hsnd, hac, hMem, hRoot⟩ :=
    hRN p h hp hh hstep
  letI : IsProbabilityMeasure sigma := hsigma
  have hp_pos : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hInt : Integrable (fun z =>
      |((((V.target : Measure (State d)) ⊗ₘ
        V.gaussianDensityProposal h).rnDeriv sigma) z).toReal - 1| ^ p)
      sigma := by
    have hPower := hMem.integrable_norm_rpow'
    simpa only [ENNReal.toReal_ofReal hp_pos.le, Real.norm_eq_abs] using hPower
  exact ⟨sigma, inferInstance, hsymm, hfst, hsnd, hac, hInt, hRoot⟩

end FirstOrderPotential
end Concrete

end
end UniformRandomMALA
