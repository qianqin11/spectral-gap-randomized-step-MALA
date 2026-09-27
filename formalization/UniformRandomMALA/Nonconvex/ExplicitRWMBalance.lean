import UniformRandomMALA.DiscreteTime.ExplicitRWMBalance
import UniformRandomMALA.Nonconvex.RWMBasic

/-! # Explicit random-walk balance for the nonconvex target -/
namespace UniformRandomMALA
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
noncomputable section
namespace Nonconvex.DiscreteTime
open Concrete UniformRandomMALA.DiscreteTime
variable {d : ℕ}
/-- Metropolis acceptance probability for the explicit proposal.  The
auxiliary proposal density in `MetropolisHastings.acceptance` is the constant
one: the actual Gaussian proposal is symmetric because its innovation is
invariant under negation. -/
def explicitRWMAcceptance (V : Concrete.NonconvexPotential d) (δ : ℝ)
    (x z : State d) : ℝ≥0∞ :=
  MetropolisHastings.acceptance V.targetDensity (fun _ _ => 1)
    x (explicitRWMEndpoint δ x z)

lemma measurable_uncurry_explicitRWMAcceptance
    (V : Concrete.NonconvexPotential d) (δ : ℝ) :
    Measurable (Function.uncurry (explicitRWMAcceptance V δ)) := by
  unfold explicitRWMAcceptance MetropolisHastings.acceptance
    MetropolisHastings.edgeDensity Function.uncurry
  simp only [mul_one]
  exact (((V.measurable_targetDensity.comp
    (measurable_uncurry_explicitRWMEndpoint δ)).div
      (V.measurable_targetDensity.comp measurable_fst)).inf measurable_const)

lemma explicitRWMAcceptance_le_one
    (V : Concrete.NonconvexPotential d) (δ : ℝ) (x z : State d) :
    explicitRWMAcceptance V δ x z ≤ 1 :=
  MetropolisHastings.acceptance_le_one _ _ _ _

/-- The same acceptance probability as a function of the current and proposed
positions. -/
def explicitRWMAcceptanceAt (V : Concrete.NonconvexPotential d)
    (x y : State d) : ℝ≥0∞ :=
  MetropolisHastings.acceptance V.targetDensity (fun _ _ => 1) x y

lemma explicitRWMAcceptanceAt_eq_targetRatio
    (V : Concrete.NonconvexPotential d) (x y : State d) :
    explicitRWMAcceptanceAt V x y =
      (V.targetDensity y / V.targetDensity x) ⊓ 1 := by
  simp [explicitRWMAcceptanceAt, MetropolisHastings.acceptance,
    MetropolisHastings.edgeDensity]

lemma explicitRWMAcceptanceAt_eq_boltzmann
    (V : Concrete.NonconvexPotential d) (x y : State d) :
    explicitRWMAcceptanceAt V x y =
      ENNReal.ofReal (Real.exp (V.U x - V.U y)) ⊓ 1 := by
  rw [explicitRWMAcceptanceAt_eq_targetRatio, V.targetDensity_ratio]

lemma explicitRWMAcceptance_eq_boltzmann
    (V : Concrete.NonconvexPotential d) (δ : ℝ) (x z : State d) :
    explicitRWMAcceptance V δ x z =
      ENNReal.ofReal
        (Real.exp (V.U x - V.U (explicitRWMEndpoint δ x z))) ⊓ 1 := by
  exact explicitRWMAcceptanceAt_eq_boltzmann V x
    (explicitRWMEndpoint δ x z)

lemma measurable_uncurry_explicitRWMAcceptanceAt
    (V : Concrete.NonconvexPotential d) :
    Measurable (Function.uncurry (explicitRWMAcceptanceAt V)) := by
  exact MetropolisHastings.measurable_uncurry_acceptance
    V.targetDensity (fun _ _ => 1) V.measurable_targetDensity measurable_const

@[simp] lemma explicitRWMAcceptanceAt_endpoint
    (V : Concrete.NonconvexPotential d) (δ : ℝ) (x z : State d) :
    explicitRWMAcceptanceAt V x (explicitRWMEndpoint δ x z) =
      explicitRWMAcceptance V δ x z := rfl

/-- Accepted part of the explicit Gaussian RWM transition. -/
def explicitRWMAcceptedKernel
    (V : Concrete.NonconvexPotential d) (δ : ℝ) :
    Kernel (State d) (State d) :=
  MetropolisHastings.accepted (explicitRWMProposal δ)
    (explicitRWMAcceptanceAt V)

lemma explicitRWMAcceptedKernel_apply
    (V : Concrete.NonconvexPotential d) (δ : ℝ)
    (x : State d) {s : Set (State d)} (hs : MeasurableSet s) :
    explicitRWMAcceptedKernel V δ x s =
      ∫⁻ z, s.indicator
        (fun y => explicitRWMAcceptanceAt V x y)
        (explicitRWMEndpoint δ x z) ∂stdGaussian (State d) := by
  have hax : Measurable (explicitRWMAcceptanceAt V x) :=
    Measurable.of_uncurry_left (measurable_uncurry_explicitRWMAcceptanceAt V)
  rw [explicitRWMAcceptedKernel, MetropolisHastings.accepted,
    Kernel.withDensity_apply'
      (explicitRWMProposal δ)
      (measurable_uncurry_explicitRWMAcceptanceAt V) x s]
  rw [← lintegral_indicator hs]
  exact lintegral_explicitRWMProposal δ x (hax.indicator hs)

/-- Pointwise balance of the accepted explicit proposal.  This is acceptance
algebra only; it does not use a Gaussian density or a change of variables. -/
lemma targetDensity_mul_explicitRWMAcceptance_balance
    (V : Concrete.NonconvexPotential d) (δ : ℝ) (x z : State d) :
    V.targetDensity x * explicitRWMAcceptance V δ x z =
      V.targetDensity (explicitRWMEndpoint δ x z) *
        explicitRWMAcceptance V δ (explicitRWMEndpoint δ x z) (-z) := by
  let q : State d → State d → ℝ≥0∞ := fun _ _ => 1
  have hpos : ∀ x y,
      MetropolisHastings.edgeDensity V.targetDensity q x y ≠ 0 := by
    intro x y
    simpa [MetropolisHastings.edgeDensity, q] using
      (V.targetDensity_pos x).ne'
  have htop : ∀ x y,
      MetropolisHastings.edgeDensity V.targetDensity q x y ≠ ∞ := by
    intro x y
    simpa [MetropolisHastings.edgeDensity, q] using
      V.targetDensity_ne_top x
  have hbalance := MetropolisHastings.acceptedDensity_balance
    V.targetDensity q hpos htop x (explicitRWMEndpoint δ x z)
  simpa [explicitRWMAcceptance, q, explicitRWMEndpoint_reverse] using hbalance

/-- Target-weighted accepted edge integrand for a nonnegative test function
of the old and proposed positions. -/
def explicitRWMAcceptedEdgeIntegrand
    (V : Concrete.NonconvexPotential d) (δ : ℝ)
    (F : State d × State d → ℝ≥0∞) (p : State d × State d) : ℝ≥0∞ :=
  V.targetDensity p.1 * explicitRWMAcceptance V δ p.1 p.2 *
    F (p.1, explicitRWMEndpoint δ p.1 p.2)

lemma measurable_explicitRWMAcceptedEdgeIntegrand
    (V : Concrete.NonconvexPotential d) (δ : ℝ)
    {F : State d × State d → ℝ≥0∞} (hF : Measurable F) :
    Measurable (explicitRWMAcceptedEdgeIntegrand V δ F) := by
  have hendpoint : Measurable (fun p : State d × State d =>
      (p.1, explicitRWMEndpoint δ p.1 p.2)) :=
    measurable_fst.prodMk (measurable_uncurry_explicitRWMEndpoint δ)
  exact ((V.measurable_targetDensity.comp measurable_fst).mul
    (measurable_uncurry_explicitRWMAcceptance V δ)).mul
      (hF.comp hendpoint)

lemma measurable_explicitRWMAcceptedTestIntegrand
    (V : Concrete.NonconvexPotential d) (δ : ℝ)
    {F : State d × State d → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun p : State d × State d =>
      explicitRWMAcceptance V δ p.1 p.2 *
        F (p.1, explicitRWMEndpoint δ p.1 p.2)) := by
  have hendpoint : Measurable (fun p : State d × State d =>
      (p.1, explicitRWMEndpoint δ p.1 p.2)) :=
    measurable_fst.prodMk (measurable_uncurry_explicitRWMEndpoint δ)
  exact (measurable_uncurry_explicitRWMAcceptance V δ).mul
    (hF.comp hendpoint)

/-- Expanding the target as its Lebesgue density and applying Tonelli turns
the target-first accepted integral into the product-coordinate integral used
by the direct change of variables. -/
lemma lintegral_target_explicitRWMAccepted_eq_productCoordinates
    (V : Concrete.NonconvexPotential d) (δ : ℝ)
    {F : State d × State d → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ x, ∫⁻ z,
        explicitRWMAcceptance V δ x z *
          F (x, explicitRWMEndpoint δ x z)
        ∂stdGaussian (State d) ∂(V.target : Measure (State d))) =
      ∫⁻ z, ∫⁻ x,
        explicitRWMAcceptedEdgeIntegrand V δ F (x, z)
        ∂volume ∂stdGaussian (State d) := by
  let G : State d × State d → ℝ≥0∞ := fun p =>
    explicitRWMAcceptance V δ p.1 p.2 *
      F (p.1, explicitRWMEndpoint δ p.1 p.2)
  have hG : Measurable G :=
    measurable_explicitRWMAcceptedTestIntegrand V δ hF
  have houter : Measurable (fun x : State d =>
      ∫⁻ z, G (x, z) ∂stdGaussian (State d)) :=
    hG.lintegral_prod_right'
  rw [V.target_toMeasure_eq_withDensity]
  rw [lintegral_withDensity_eq_lintegral_mul volume
    V.measurable_targetDensity houter]
  change (∫⁻ x, V.targetDensity x *
      (∫⁻ z, G (x, z) ∂stdGaussian (State d)) ∂volume) = _
  calc
    (∫⁻ x, V.targetDensity x *
        (∫⁻ z, G (x, z) ∂stdGaussian (State d)) ∂volume) =
        ∫⁻ x, ∫⁻ z, V.targetDensity x * G (x, z)
          ∂stdGaussian (State d) ∂volume := by
      apply lintegral_congr
      intro x
      exact (lintegral_const_mul (V.targetDensity x)
        (hG.comp (measurable_const.prodMk measurable_id))).symm
    _ = ∫⁻ z, ∫⁻ x, V.targetDensity x * G (x, z)
          ∂volume ∂stdGaussian (State d) := by
      let E : State d × State d → ℝ≥0∞ := fun p =>
        V.targetDensity p.1 * G p
      have hE : Measurable E :=
        (V.measurable_targetDensity.comp measurable_fst).mul hG
      rw [← lintegral_prod E hE.aemeasurable]
      exact lintegral_prod_symm E hE.aemeasurable
    _ = ∫⁻ z, ∫⁻ x,
          explicitRWMAcceptedEdgeIntegrand V δ F (x, z)
          ∂volume ∂stdGaussian (State d) := by
      apply lintegral_congr
      intro z
      apply lintegral_congr
      intro x
      simp only [G, explicitRWMAcceptedEdgeIntegrand,
        mul_assoc]

/-- Direct symmetry of the accepted edge flow, in the product coordinates
`(x,z)`.  It is proved solely from the shear--negation integral identity and
the pointwise Metropolis minimum identity. -/
theorem lintegral_explicitRWMAcceptedEdgeIntegrand_swap
    (V : Concrete.NonconvexPotential d) (δ : ℝ)
    {F : State d × State d → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z, ∫⁻ x, explicitRWMAcceptedEdgeIntegrand V δ F (x, z)
        ∂volume ∂stdGaussian (State d)) =
      ∫⁻ z, ∫⁻ x,
        V.targetDensity x * explicitRWMAcceptance V δ x z *
          F (explicitRWMEndpoint δ x z, x)
        ∂volume ∂stdGaussian (State d) := by
  rw [lintegral_stdGaussian_volume_reverseRWMCoordinates
    (Real.sqrt (2 * δ))
    (measurable_explicitRWMAcceptedEdgeIntegrand V δ hF)]
  apply lintegral_congr
  intro z
  apply lintegral_congr
  intro x
  rw [show x + Real.sqrt (2 * δ) • z =
      explicitRWMEndpoint δ x z by rfl]
  unfold explicitRWMAcceptedEdgeIntegrand
  rw [explicitRWMEndpoint_reverse]
  rw [← targetDensity_mul_explicitRWMAcceptance_balance V δ x z]

/-- Detailed balance for the accepted part of the explicit Gaussian RWM
proposal, stated directly against the normalized target measure.  No
identification of the pushforward Gaussian proposal with a Lebesgue-density
kernel occurs in the proof. -/
theorem lintegral_target_explicitRWMAccepted_swap
    (V : Concrete.NonconvexPotential d) (δ : ℝ)
    {F : State d × State d → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ x, ∫⁻ z,
        explicitRWMAcceptance V δ x z *
          F (x, explicitRWMEndpoint δ x z)
        ∂stdGaussian (State d) ∂(V.target : Measure (State d))) =
      ∫⁻ x, ∫⁻ z,
        explicitRWMAcceptance V δ x z *
          F (explicitRWMEndpoint δ x z, x)
        ∂stdGaussian (State d) ∂(V.target : Measure (State d)) := by
  let Fswap : State d × State d → ℝ≥0∞ := fun p => F (p.2, p.1)
  have hFswap : Measurable Fswap := hF.comp measurable_swap
  rw [lintegral_target_explicitRWMAccepted_eq_productCoordinates V δ hF]
  rw [show (∫⁻ x, ∫⁻ z,
        explicitRWMAcceptance V δ x z *
          F (explicitRWMEndpoint δ x z, x)
        ∂stdGaussian (State d) ∂(V.target : Measure (State d))) =
      ∫⁻ x, ∫⁻ z,
        explicitRWMAcceptance V δ x z *
          Fswap (x, explicitRWMEndpoint δ x z)
        ∂stdGaussian (State d) ∂(V.target : Measure (State d)) by rfl]
  rw [lintegral_target_explicitRWMAccepted_eq_productCoordinates
    V δ hFswap]
  exact lintegral_explicitRWMAcceptedEdgeIntegrand_swap V δ hF

/-- The accepted pushforward kernel is reversible with respect to the target.
This is the setwise kernel form of
`lintegral_target_explicitRWMAccepted_swap`. -/
theorem explicitRWMAcceptedKernel_isReversible
    (V : Concrete.NonconvexPotential d) (δ : ℝ) :
    Kernel.IsReversible (explicitRWMAcceptedKernel V δ)
      (V.target : Measure (State d)) := by
  intro A B hA hB
  simp_rw [explicitRWMAcceptedKernel_apply V δ _ hB]
  simp_rw [explicitRWMAcceptedKernel_apply V δ _ hA]
  rw [← lintegral_indicator hA, ← lintegral_indicator hB]
  let F : State d × State d → ℝ≥0∞ :=
    (A ×ˢ B).indicator (fun _ => 1)
  have hF : Measurable F := measurable_const.indicator (hA.prod hB)
  have hbalance := lintegral_target_explicitRWMAccepted_swap V δ hF
  have hleft :
      (∫⁻ x, A.indicator
          (fun x => ∫⁻ z, B.indicator
            (fun y => explicitRWMAcceptanceAt V x y)
            (explicitRWMEndpoint δ x z) ∂stdGaussian (State d)) x
          ∂(V.target : Measure (State d))) =
        ∫⁻ x, ∫⁻ z,
          explicitRWMAcceptance V δ x z *
            F (x, explicitRWMEndpoint δ x z)
          ∂stdGaussian (State d) ∂(V.target : Measure (State d)) := by
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      apply lintegral_congr
      intro z
      by_cases hy : explicitRWMEndpoint δ x z ∈ B
      · simp [F, hx, hy, explicitRWMAcceptanceAt_endpoint]
      · simp [F, hx, hy]
    · rw [Set.indicator_of_notMem hx]
      simp [F, hx]
  have hright :
      (∫⁻ x, B.indicator
          (fun x => ∫⁻ z, A.indicator
            (fun y => explicitRWMAcceptanceAt V x y)
            (explicitRWMEndpoint δ x z) ∂stdGaussian (State d)) x
          ∂(V.target : Measure (State d))) =
        ∫⁻ x, ∫⁻ z,
          explicitRWMAcceptance V δ x z *
            F (explicitRWMEndpoint δ x z, x)
          ∂stdGaussian (State d) ∂(V.target : Measure (State d)) := by
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]
      apply lintegral_congr
      intro z
      by_cases hy : explicitRWMEndpoint δ x z ∈ A
      · simp [F, hx, hy, explicitRWMAcceptanceAt_endpoint]
      · simp [F, hx, hy]
    · rw [Set.indicator_of_notMem hx]
      simp [F, hx]
  rw [hleft, hright]
  exact hbalance

/-- Full explicit RWM kernel, obtained by adding the diagonal rejection mass
to the accepted pushforward kernel. -/
def explicitRWMKernel
    (V : Concrete.NonconvexPotential d) (δ : ℝ) :
    Kernel (State d) (State d) :=
  MetropolisHastings.kernel (explicitRWMProposal δ)
    (explicitRWMAcceptanceAt V)

theorem explicitRWMKernel_isReversible
    (V : Concrete.NonconvexPotential d) (δ : ℝ) :
    Kernel.IsReversible (explicitRWMKernel V δ)
      (V.target : Measure (State d)) := by
  unfold explicitRWMKernel
  exact MetropolisHastings.kernel_isReversible
    (V.target : Measure (State d)) (explicitRWMProposal δ)
    (explicitRWMAcceptanceAt V)
    (measurable_uncurry_explicitRWMAcceptanceAt V)
    (explicitRWMAcceptedKernel_isReversible V δ)

theorem explicitRWMKernel_isMarkovKernel
    (V : Concrete.NonconvexPotential d) (δ : ℝ) :
    IsMarkovKernel (explicitRWMKernel V δ) := by
  let : Fact (Measurable
      (Function.uncurry (explicitRWMAcceptanceAt V))) :=
    ⟨measurable_uncurry_explicitRWMAcceptanceAt V⟩
  let : Fact (∀ x y, explicitRWMAcceptanceAt V x y ≤ 1) :=
    ⟨fun x y => MetropolisHastings.acceptance_le_one _ _ x y⟩
  unfold explicitRWMKernel
  infer_instance

theorem explicitRWMKernel_invariant
    (V : Concrete.NonconvexPotential d) (δ : ℝ) :
    Kernel.Invariant (explicitRWMKernel V δ)
      (V.target : Measure (State d)) := by
  let : IsMarkovKernel (explicitRWMKernel V δ) :=
    explicitRWMKernel_isMarkovKernel V δ
  exact (explicitRWMKernel_isReversible V δ).invariant

end Nonconvex.DiscreteTime

end

end UniformRandomMALA
