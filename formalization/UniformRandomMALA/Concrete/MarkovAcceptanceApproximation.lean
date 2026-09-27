import UniformRandomMALA.DiscreteTime.EulerRWMPairChain
import Mathlib.Probability.Kernel.Invariance
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Absolutely continuous approximations after a first acceptance

A transition consists of a target-absolutely-continuous accepted move and a
rejection atom at the current state. The part of the law that has accepted
at least once is absolutely continuous. Its complement is exactly the
initial law weighted by the probability of rejecting every step, and its
total mass tends to zero from any finite initial measure.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory Filter DiscreteTime
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- The mass that remains at its initial state after `n` consecutive rejections. -/
def rejectionRemainder (μ : Measure α) (r : α → ℝ≥0∞) (n : ℕ) : Measure α :=
  μ.withDensity (fun x => r x ^ n)

/-- The part of the transition law that has accepted at least one move. -/
def acceptedTransitionPart (K A : Kernel α α) (μ : Measure α)
    (r : α → ℝ≥0∞) : ℕ → Measure α
  | 0 => 0
  | n + 1 => K ∘ₘ acceptedTransitionPart K A μ r n + A ∘ₘ rejectionRemainder μ r n

/-- Pointwise acceptance/rejection decomposition also decomposes every pushed-forward law. -/
theorem comp_eq_accepted_add_withDensity
    (K A : Kernel α α) (r : α → ℝ≥0∞)
    (hdecomp : ∀ x, K x = A x + r x • Measure.dirac x) (μ : Measure α) :
    K ∘ₘ μ = A ∘ₘ μ + μ.withDensity r := by
  ext s hs
  rw [Measure.bind_apply hs K.aemeasurable, Measure.add_apply,
    Measure.bind_apply hs A.aemeasurable, withDensity_apply r hs]
  simp_rw [hdecomp, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [lintegral_add_left (A.measurable_coe hs)]
  congr 1
  rw [← lintegral_indicator hs]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s <;> simp [Measure.dirac_apply', hs, hx]

/-- The first-acceptance decomposition of the actual iterated transition law. -/
theorem finiteKernelIterate_eq_acceptedTransitionPart_add_rejectionRemainder
    (K A : Kernel α α) (μ : Measure α) (r : α → ℝ≥0∞) (hr : Measurable r)
    (hdecomp : ∀ x, K x = A x + r x • Measure.dirac x) (n : ℕ) :
    finiteKernelIterate K n ∘ₘ μ =
      acceptedTransitionPart K A μ r n + rejectionRemainder μ r n := by
  induction n with
  | zero => simp [finiteKernelIterate, acceptedTransitionPart, rejectionRemainder]
  | succ n ih =>
    rw [finiteKernelIterate, ← Measure.comp_assoc, ih, Measure.comp_add,
      comp_eq_accepted_add_withDensity K A r hdecomp (rejectionRemainder μ r n)]
    change K ∘ₘ acceptedTransitionPart K A μ r n +
      (A ∘ₘ rejectionRemainder μ r n + (rejectionRemainder μ r n).withDensity r) =
      (K ∘ₘ acceptedTransitionPart K A μ r n + A ∘ₘ rejectionRemainder μ r n) +
        rejectionRemainder μ r (n + 1)
    rw [add_assoc]
    congr 1
    unfold rejectionRemainder
    rw [← withDensity_mul μ (hr.pow_const n) hr]
    congr 1
    apply withDensity_congr_ae
    exact ae_of_all _ fun x => (pow_succ (r x) n).symm

/-- A kernel whose every output is target-absolutely-continuous has the same property
after integration against an arbitrary initial measure. -/
theorem comp_absolutelyContinuous_of_forall
    (A : Kernel α α) (μ π : Measure α) (hA : ∀ x, A x ≪ π) :
    A ∘ₘ μ ≪ π := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hnull
  rw [Measure.bind_apply hs A.aemeasurable]
  simp only [show (fun x => A x s) = fun _ => 0 from
    funext fun x => hA x hnull, lintegral_zero]

/-- Once an acceptance has occurred, invariance keeps its entire later law
absolutely continuous with respect to the target. -/
theorem acceptedTransitionPart_absolutelyContinuous
    (K A : Kernel α α) (μ π : Measure α) (r : α → ℝ≥0∞)
    (hπ : Kernel.Invariant K π) (hA : ∀ x, A x ≪ π) (n : ℕ) :
    acceptedTransitionPart K A μ r n ≪ π := by
  induction n with
  | zero => simp [acceptedTransitionPart]
  | succ n ih =>
    apply Measure.AbsolutelyContinuous.add_left
    · have h := ih.comp_right K
      change K ∘ₘ π = π at hπ
      simpa only [hπ] using h
    · exact comp_absolutelyContinuous_of_forall A _ π hA

/-- The accepted part is a submeasure of the actual transition law. -/
theorem acceptedTransitionPart_le
    (K A : Kernel α α) (μ : Measure α) (r : α → ℝ≥0∞) (hr : Measurable r)
    (hdecomp : ∀ x, K x = A x + r x • Measure.dirac x) (n : ℕ) :
    acceptedTransitionPart K A μ r n ≤ finiteKernelIterate K n ∘ₘ μ := by
  rw [finiteKernelIterate_eq_acceptedTransitionPart_add_rejectionRemainder
    K A μ r hr hdecomp]
  intro s
  simp only [Measure.add_apply]
  exact le_add_right le_rfl

/-- From a probability start, the accepted part is a subprobability measure. -/
theorem acceptedTransitionPart_mass_le_one
    (K A : Kernel α α) [IsMarkovKernel K] (μ : Measure α) [IsProbabilityMeasure μ]
    (r : α → ℝ≥0∞) (hr : Measurable r)
    (hdecomp : ∀ x, K x = A x + r x • Measure.dirac x) (n : ℕ) :
    acceptedTransitionPart K A μ r n Set.univ ≤ 1 := by
  simpa using acceptedTransitionPart_le K A μ r hr hdecomp n Set.univ

/-- The probability of rejecting forever vanishes, without a uniform lower
bound on the acceptance probability and without any initial moment hypothesis. -/
theorem rejectionRemainder_mass_tendsto_zero
    (μ : Measure α) [IsFiniteMeasure μ] (r : α → ℝ≥0∞)
    (hr : Measurable r) (hr1 : ∀ x, r x < 1) :
    Tendsto (fun n => rejectionRemainder μ r n Set.univ) atTop (𝓝 0) := by
  have h := tendsto_lintegral_of_dominated_convergence (μ := μ)
    (F := fun n x => r x ^ n) (f := fun _ => 0) (fun _ => 1)
    (fun n => hr.pow_const n)
    (fun n => ae_of_all _ fun x => pow_le_one₀ bot_le (hr1 x).le)
    (by simp)
    (ae_of_all _ fun x => ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (hr1 x))
  simpa only [rejectionRemainder, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, lintegral_zero] using h

/-- The accepted mass is exactly one minus the all-rejection mass. -/
theorem acceptedTransitionPart_mass_eq
    (K A : Kernel α α) [IsMarkovKernel K] (μ : Measure α) [IsProbabilityMeasure μ]
    (r : α → ℝ≥0∞) (hr : Measurable r)
    (hdecomp : ∀ x, K x = A x + r x • Measure.dirac x) (n : ℕ) :
    acceptedTransitionPart K A μ r n Set.univ = 1 - rejectionRemainder μ r n Set.univ := by
  apply ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top
  have h := congrArg (fun ν : Measure α => ν Set.univ)
    (finiteKernelIterate_eq_acceptedTransitionPart_add_rejectionRemainder
      K A μ r hr hdecomp n)
  simpa only [measure_univ, Measure.add_apply] using h.symm

/-- The absolutely continuous accepted mass tends to one. -/
theorem acceptedTransitionPart_mass_tendsto_one
    (K A : Kernel α α) [IsMarkovKernel K] (μ : Measure α) [IsProbabilityMeasure μ]
    (r : α → ℝ≥0∞) (hr : Measurable r) (hr1 : ∀ x, r x < 1)
    (hdecomp : ∀ x, K x = A x + r x • Measure.dirac x) :
    Tendsto (fun n => acceptedTransitionPart K A μ r n Set.univ) atTop (𝓝 1) := by
  simp_rw [acceptedTransitionPart_mass_eq K A μ r hr hdecomp]
  simpa only [tsub_zero] using
    ENNReal.Tendsto.sub tendsto_const_nhds (rejectionRemainder_mass_tendsto_zero μ r hr hr1)
      (Or.inl ENNReal.one_ne_top)

/-- Normalization of the part of the law that has accepted. -/
def normalizedAcceptedTransitionLaw (K A : Kernel α α) (μ : Measure α)
    (r : α → ℝ≥0∞) (n : ℕ) : Measure α :=
  (acceptedTransitionPart K A μ r n Set.univ)⁻¹ • acceptedTransitionPart K A μ r n

theorem normalizedAcceptedTransitionLaw_isProbabilityMeasure
    (K A : Kernel α α) [IsMarkovKernel K] (μ : Measure α) [IsProbabilityMeasure μ]
    (r : α → ℝ≥0∞) (hr : Measurable r)
    (hdecomp : ∀ x, K x = A x + r x • Measure.dirac x) (n : ℕ)
    (hpos : 0 < acceptedTransitionPart K A μ r n Set.univ) :
    IsProbabilityMeasure (normalizedAcceptedTransitionLaw K A μ r n) := by
  apply isProbabilityMeasure_iff.mpr
  simp only [normalizedAcceptedTransitionLaw, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hpos.ne'
    (ne_top_of_le_ne_top ENNReal.one_ne_top
      (acceptedTransitionPart_mass_le_one K A μ r hr hdecomp n))

theorem normalizedAcceptedTransitionLaw_absolutelyContinuous
    (K A : Kernel α α) (μ π : Measure α) (r : α → ℝ≥0∞)
    (hπ : Kernel.Invariant K π) (hA : ∀ x, A x ≪ π) (n : ℕ) :
    normalizedAcceptedTransitionLaw K A μ r n ≪ π :=
  (acceptedTransitionPart_absolutelyContinuous K A μ π r hπ hA n).smul_left _

/-- An arbitrarily accurate finite-time decomposition uses a genuine
absolutely continuous probability law and a remainder of arbitrarily small mass. -/
theorem exists_normalized_accepted_transition_approximation
    (K A : Kernel α α) [IsMarkovKernel K]
    (μ π : Measure α) [IsProbabilityMeasure μ]
    (r : α → ℝ≥0∞) (hr : Measurable r) (hr1 : ∀ x, r x < 1)
    (hπ : Kernel.Invariant K π) (hA : ∀ x, A x ≪ π)
    (hdecomp : ∀ x, K x = A x + r x • Measure.dirac x)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (n : ℕ) (ν : Measure α) (a : ℝ≥0∞),
      IsProbabilityMeasure ν ∧ ν ≪ π ∧ 0 < a ∧ a ≤ 1 ∧
      finiteKernelIterate K n ∘ₘ μ = a • ν + rejectionRemainder μ r n ∧
      rejectionRemainder μ r n Set.univ < ε := by
  have hpos : ∀ᶠ n in atTop, 0 < acceptedTransitionPart K A μ r n Set.univ :=
    (acceptedTransitionPart_mass_tendsto_one K A μ r hr hr1 hdecomp).eventually
      (eventually_gt_nhds zero_lt_one)
  have hsmall : ∀ᶠ n in atTop, rejectionRemainder μ r n Set.univ < ε :=
    (rejectionRemainder_mass_tendsto_zero μ r hr hr1).eventually (eventually_lt_nhds hε)
  obtain ⟨n, hnpos, hnsmall⟩ := (hpos.and hsmall).exists
  let a := acceptedTransitionPart K A μ r n Set.univ
  have ha1 : a ≤ 1 := acceptedTransitionPart_mass_le_one K A μ r hr hdecomp n
  have hatop : a ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top ha1
  refine ⟨n, normalizedAcceptedTransitionLaw K A μ r n, a,
    normalizedAcceptedTransitionLaw_isProbabilityMeasure K A μ r hr hdecomp n hnpos,
    normalizedAcceptedTransitionLaw_absolutelyContinuous K A μ π r hπ hA n,
    hnpos, ha1, ?_, hnsmall⟩
  rw [normalizedAcceptedTransitionLaw, smul_smul]
  change finiteKernelIterate K n ∘ₘ μ = (a * a⁻¹) •
    acceptedTransitionPart K A μ r n + rejectionRemainder μ r n
  rw [ENNReal.mul_inv_cancel hnpos.ne' hatop, one_smul]
  exact finiteKernelIterate_eq_acceptedTransitionPart_add_rejectionRemainder K A μ r hr hdecomp n

/-- Every initial probability law admits absolutely continuous
subprobability approximations after finitely many transitions, with an
explicit vanishing remainder. -/
theorem exists_absolutelyContinuous_transition_approximations
    (K A : Kernel α α) [IsMarkovKernel K]
    (μ π : Measure α) [IsProbabilityMeasure μ]
    (r : α → ℝ≥0∞) (hr : Measurable r) (hr1 : ∀ x, r x < 1)
    (hπ : Kernel.Invariant K π) (hA : ∀ x, A x ≪ π)
    (hdecomp : ∀ x, K x = A x + r x • Measure.dirac x) :
    ∃ ν : ℕ → Measure α,
      (∀ n, ν n ≪ π) ∧ (∀ n, ν n Set.univ ≤ 1) ∧
      (∀ n, finiteKernelIterate K n ∘ₘ μ = ν n + rejectionRemainder μ r n) ∧
      Tendsto (fun n => rejectionRemainder μ r n Set.univ) atTop (𝓝 0) := by
  refine ⟨acceptedTransitionPart K A μ r,
    acceptedTransitionPart_absolutelyContinuous K A μ π r hπ hA,
    acceptedTransitionPart_mass_le_one K A μ r hr hdecomp,
    finiteKernelIterate_eq_acceptedTransitionPart_add_rejectionRemainder K A μ r hr hdecomp,
    rejectionRemainder_mass_tendsto_zero μ r hr hr1⟩

end
end UniformRandomMALA.Concrete
