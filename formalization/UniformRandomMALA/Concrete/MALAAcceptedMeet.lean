import UniformRandomMALA.Concrete.MALA
import UniformRandomMALA.DiscreteTime.MeasureMeet
import Mathlib.Probability.Kernel.CompProdEqIff

/-!
# The concrete MALA accepted edge flow is the RN-density meet

The proof first writes proposal and accepted edge laws relative to product
Lebesgue measure.  The accepted density is the pointwise minimum of the two
oriented edge densities by the elementary MH identity.  The reference-change
lemma in `DiscreteTime.MeasureMeet` then transports this minimum to any
swap-invariant RN reference law.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace Concrete
namespace FirstOrderPotential

variable {d : ℕ} (V : FirstOrderPotential d)

/-- The stationary Gaussian proposal edge law has its expected product
Lebesgue density. -/
theorem malaProposalEdge_eq_withDensity (h : ℝ) :
    ((V.target : Measure (State d)) ⊗ₘ V.gaussianDensityProposal h) =
      ((volume : Measure (State d)).prod volume).withDensity
        (fun z => MetropolisHastings.edgeDensity V.targetDensity
          (V.proposalDensity h) z.1 z.2) := by
  letI : IsSFiniteKernel
      ((Kernel.const (State d) (volume : Measure (State d))).withDensity
        (V.proposalDensity h)) :=
    Kernel.IsSFiniteKernel.withDensity _ (V.proposalDensity_ne_top h)
  rw [V.target_toMeasure_eq_withDensity]
  unfold gaussianDensityProposal MetropolisHastings.edgeDensity
  rw [Measure.compProd_withDensity (V.measurable_uncurry_proposalDensity h)]
  rw [Measure.compProd_const]
  rw [prod_withDensity_left V.measurable_targetDensity]
  rw [← withDensity_mul]
  · rfl
  · exact V.measurable_targetDensity.comp measurable_fst
  · exact V.measurable_uncurry_proposalDensity h

/-- Relative to product Lebesgue measure, the accepted MALA edge density is
the pointwise minimum of the forward and reversed proposal edge densities. -/
theorem malaAcceptedEdge_eq_withDensity_min
    {h : ℝ} (hh : 0 < h) :
    ((V.target : Measure (State d)) ⊗ₘ
      MetropolisHastings.accepted
        (V.gaussianDensityProposal h) (V.malaAcceptance h)) =
      ((volume : Measure (State d)).prod volume).withDensity
        (fun z => min
          (MetropolisHastings.edgeDensity V.targetDensity
            (V.proposalDensity h) z.1 z.2)
          (MetropolisHastings.edgeDensity V.targetDensity
            (V.proposalDensity h) z.2 z.1)) := by
  letI : Fact (0 < h) := ⟨hh⟩
  letI : IsSFiniteKernel (Kernel.withDensity
      (V.gaussianDensityProposal h) (V.malaAcceptance h)) :=
    Kernel.IsSFiniteKernel.withDensity _ fun x y =>
      ne_top_of_le_ne_top ENNReal.one_ne_top (V.malaAcceptance_le_one h x y)
  change ((V.target : Measure (State d)) ⊗ₘ Kernel.withDensity
    (V.gaussianDensityProposal h) (V.malaAcceptance h)) = _
  rw [Measure.compProd_withDensity (V.measurable_uncurry_malaAcceptance h)]
  rw [V.malaProposalEdge_eq_withDensity h]
  rw [← withDensity_mul]
  · congr 1
    funext z
    exact MetropolisHastings.edgeDensity_mul_acceptance
      V.targetDensity (V.proposalDensity h)
      (V.malaEdgeDensity_ne_zero hh) (V.malaEdgeDensity_ne_top h) z.1 z.2
  · exact (V.measurable_targetDensity.comp measurable_fst).mul
      (V.measurable_uncurry_proposalDensity h)
  · exact V.measurable_uncurry_malaAcceptance h

/-- Reference-free accepted-meet identity.  An RN representation of the
oriented proposal edge law relative to a swap-invariant measure automatically
identifies the concrete accepted MALA edge flow with density
`min(F, F ∘ swap)` relative to that measure. -/
theorem malaAcceptedEdge_eq_rnMeet
    {h : ℝ} (hh : 0 < h)
    {sigma : Measure (State d × State d)}
    {F : State d × State d → ℝ}
    (hF : Measurable F)
    (hsymm : Measure.map Prod.swap sigma = sigma)
    (hRN : ((V.target : Measure (State d)) ⊗ₘ
      V.gaussianDensityProposal h) =
        sigma.withDensity (fun z => ENNReal.ofReal (F z))) :
    ((V.target : Measure (State d)) ⊗ₘ
      MetropolisHastings.accepted
        (V.gaussianDensityProposal h) (V.malaAcceptance h)) =
      sigma.withDensity (fun z =>
        ENNReal.ofReal (min (F z) (F (Prod.swap z)))) := by
  let base : Measure (State d × State d) :=
    (volume : Measure (State d)).prod volume
  let e : State d × State d → ℝ≥0∞ := fun z =>
    MetropolisHastings.edgeDensity V.targetDensity
      (V.proposalDensity h) z.1 z.2
  have hFenn : Measurable (fun z => ENNReal.ofReal (F z)) :=
    ENNReal.measurable_ofReal.comp hF
  have he : Measurable e := by
    exact (V.measurable_targetDensity.comp measurable_fst).mul
      (V.measurable_uncurry_proposalDensity h)
  have hbaseSymm : Measure.map Prod.swap base = base := by
    dsimp [base]
    exact Measure.prod_swap
  have hforward :
      sigma.withDensity (fun z => ENNReal.ofReal (F z)) =
        base.withDensity e := by
    rw [← hRN]
    exact V.malaProposalEdge_eq_withDensity h
  have hreverse :
      sigma.withDensity (fun z => ENNReal.ofReal (F (Prod.swap z))) =
        base.withDensity (fun z => e (Prod.swap z)) := by
    calc
      sigma.withDensity (fun z => ENNReal.ofReal (F (Prod.swap z))) =
          Measure.map Prod.swap
            (sigma.withDensity (fun z => ENNReal.ofReal (F z))) :=
        (DiscreteTime.map_swap_withDensity_of_swapInvariant hFenn hsymm).symm
      _ = Measure.map Prod.swap (base.withDensity e) := by rw [hforward]
      _ = base.withDensity (fun z => e (Prod.swap z)) :=
        DiscreteTime.map_swap_withDensity_of_swapInvariant he hbaseSymm
  have hmeet := DiscreteTime.withDensity_min_invariant
    hFenn (hFenn.comp measurable_swap) he (he.comp measurable_swap)
    hforward hreverse
  calc
    ((V.target : Measure (State d)) ⊗ₘ
      MetropolisHastings.accepted
        (V.gaussianDensityProposal h) (V.malaAcceptance h)) =
        base.withDensity (fun z => min (e z) (e (Prod.swap z))) := by
      simpa only [base, e, Prod.fst_swap, Prod.snd_swap] using
        V.malaAcceptedEdge_eq_withDensity_min hh
    _ = sigma.withDensity (fun z =>
        min (ENNReal.ofReal (F z)) (ENNReal.ofReal (F (Prod.swap z)))) := hmeet.symm
    _ = sigma.withDensity (fun z =>
        ENNReal.ofReal (min (F z) (F (Prod.swap z)))) := by
      congr 1
      funext z
      exact (ENNReal.ofReal_min _ _).symm

end FirstOrderPotential
end Concrete

end
end UniformRandomMALA
