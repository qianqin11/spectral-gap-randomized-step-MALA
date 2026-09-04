import UniformRandomMALA.Concrete.MetropolisHastings
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub

/-!
# Elementary setwise bounds for accept--reject kernels

This file proves the proposal-versus-Metropolis comparison directly on a
measurable set.  It uses only decomposition of a finite `ENNReal` integral
into accepted and rejected parts.  No signed measure or total-variation norm
is introduced.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace DiscreteTime

variable {α : Type*} [MeasurableSpace α]

/-- Proposal mass rejected inside a measurable set. -/
def proposalRejectionOn (q : Kernel α α) (a : α → α → ℝ≥0∞)
    (x : α) (B : Set α) : ℝ≥0∞ :=
  ∫⁻ y in B, 1 - a x y ∂q x

lemma proposalRejectionOn_le_total
    (q : Kernel α α) (a : α → α → ℝ≥0∞)
    (x : α) (B : Set α) :
    proposalRejectionOn q a x B ≤ proposalRejectionOn q a x Set.univ := by
  exact lintegral_mono_set (Set.subset_univ B)

lemma proposalRejectionOn_univ
    (q : Kernel α α) [IsMarkovKernel q]
    (a : α → α → ℝ≥0∞)
    (ha : Measurable (Function.uncurry a))
    (ha1 : ∀ x y, a x y ≤ 1) (x : α) :
    proposalRejectionOn q a x Set.univ =
      1 - MetropolisHastings.acceptanceMass q a x := by
  have hax : Measurable (a x) := Measurable.of_uncurry_left ha
  rw [proposalRejectionOn, Measure.restrict_univ,
    lintegral_sub hax
      (by
        have hle : (∫⁻ y, a x y ∂q x) ≤ (∫⁻ _y, (1 : ℝ≥0∞) ∂q x) :=
          lintegral_mono (ha1 x)
        exact ne_top_of_le_ne_top ENNReal.one_ne_top (by simpa using hle))
      (ae_of_all _ (ha1 x))]
  simp [MetropolisHastings.acceptanceMass]

lemma proposal_apply_eq_accepted_add_rejectionOn
    (q : Kernel α α) [IsMarkovKernel q]
    (a : α → α → ℝ≥0∞)
    (ha : Measurable (Function.uncurry a))
    (ha1 : ∀ x y, a x y ≤ 1) (x : α)
    (B : Set α) (hB : MeasurableSet B) :
    q x B = MetropolisHastings.accepted q a x B +
      proposalRejectionOn q a x B := by
  have hax : Measurable (a x) := Measurable.of_uncurry_left ha
  rw [MetropolisHastings.accepted,
    Kernel.withDensity_apply' q ha x B]
  unfold proposalRejectionOn
  calc
    q x B = ∫⁻ _y in B, (1 : ℝ≥0∞) ∂q x := by simp
    _ = ∫⁻ y in B, a x y + (1 - a x y) ∂q x := by
      apply setLIntegral_congr_fun hB
      intro y _hy
      exact (add_tsub_cancel_of_le (ha1 x y)).symm
    _ = (∫⁻ y in B, a x y ∂q x) +
        ∫⁻ y in B, 1 - a x y ∂q x :=
      lintegral_add_left (μ := (q x).restrict B) hax
        (fun y => 1 - a x y)

/-- Every measurable-set discrepancy between a proposal and its
accept--reject correction is bounded by the total rejection probability.
The result is stated with real-valued masses, exactly as needed before taking
the supremum that defines total variation. -/
theorem abs_metropolisKernel_apply_toReal_sub_proposal_le_rejection
    (q : Kernel α α) [IsMarkovKernel q]
    (a : α → α → ℝ≥0∞)
    (ha : Measurable (Function.uncurry a))
    (ha1 : ∀ x y, a x y ≤ 1) (x : α)
    (B : Set α) (hB : MeasurableSet B) :
    |(MetropolisHastings.kernel q a x B).toReal - (q x B).toReal| ≤
      (1 - MetropolisHastings.acceptanceMass q a x).toReal := by
  let A := MetropolisHastings.accepted q a x B
  let M := proposalRejectionOn q a x B
  let R := MetropolisHastings.rejected q a x B
  let r := 1 - MetropolisHastings.acceptanceMass q a x
  have hq : q x B = A + M := by
    exact proposal_apply_eq_accepted_add_rejectionOn q a ha ha1 x B hB
  have hP : MetropolisHastings.kernel q a x B = A + R := by
    simp [MetropolisHastings.kernel, A, R, Measure.add_apply]
  have hM : M ≤ r := by
    calc
      M ≤ proposalRejectionOn q a x Set.univ :=
        proposalRejectionOn_le_total q a x B
      _ = r := proposalRejectionOn_univ q a ha ha1 x
  have hR : R ≤ r := by
    change MetropolisHastings.rejected q a x B ≤
      1 - MetropolisHastings.acceptanceMass q a x
    rw [MetropolisHastings.rejected_apply q a ha x B hB]
    by_cases hx : x ∈ B <;> simp [Set.indicator, hx]
  have hr : r ≤ 1 := tsub_le_self
  have hAfin : A ≠ ∞ := by
    have hAq : A ≤ q x B := by rw [hq]; exact le_add_right le_rfl
    exact ne_top_of_le_ne_top (measure_ne_top (q x) B) hAq
  have hMfin : M ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (hM.trans hr)
  have hRfin : R ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (hR.trans hr)
  rw [hP, hq, ENNReal.toReal_add hAfin hRfin, ENNReal.toReal_add hAfin hMfin]
  ring_nf
  have hrfin : r ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hr
  have hM0 : 0 ≤ M.toReal := ENNReal.toReal_nonneg
  have hR0 : 0 ≤ R.toReal := ENNReal.toReal_nonneg
  have hMreal : M.toReal ≤ r.toReal := ENNReal.toReal_mono hrfin hM
  have hRreal : R.toReal ≤ r.toReal := ENNReal.toReal_mono hrfin hR
  rw [abs_le]
  constructor <;> linarith

end DiscreteTime

end

end UniformRandomMALA
