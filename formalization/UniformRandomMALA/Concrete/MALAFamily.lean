import UniformRandomMALA.Concrete.MALA
import Mathlib.Probability.ConditionalProbability

/-!
# A jointly measurable family of MALA kernels

The paper averages `P_h` over Lebesgue measure in `h`.  A fixed-step theorem
is not enough for that integral: the family must be a single kernel on the
product of the step and state spaces.  This file builds that object.

At nonpositive parameters we use step `1`.  This totalization has no effect
on a mixture supported on `(0,H)` and lets the family be a Markov kernel on
all of `ℝ × State d`.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace Concrete

namespace FirstOrderPotential

variable {d : ℕ} (V : FirstOrderPotential d)

/-- A measurable positive totalization of a real step parameter. -/
def effectiveStep (h : ℝ) : ℝ := if 0 < h then h else 1

lemma effectiveStep_pos (h : ℝ) : 0 < effectiveStep h := by
  by_cases hh : 0 < h <;> simp [effectiveStep, hh, zero_lt_one]

lemma effectiveStep_of_pos {h : ℝ} (hh : 0 < h) : effectiveStep h = h := by
  simp [effectiveStep, hh]

lemma measurable_effectiveStep : Measurable effectiveStep := by
  exact Measurable.ite measurableSet_Ioi measurable_id measurable_const

/-- The proposal density, jointly measurable in the totalized step, current
state, and proposed state. -/
def proposalFamilyDensity (p : ℝ × State d) (y : State d) : ℝ≥0∞ :=
  V.proposalDensity (effectiveStep p.1) p.2 y

lemma measurable_uncurry_proposalFamilyDensity :
    Measurable (Function.uncurry V.proposalFamilyDensity) := by
  apply ENNReal.measurable_ofReal.comp
  unfold proposalDensityReal proposalBase proposalNormalizer
  have heff : Measurable (fun z : (ℝ × State d) × State d => effectiveStep z.1.1) :=
    measurable_effectiveStep.comp (measurable_fst.comp measurable_fst)
  have hmean : Measurable
      (fun z : (ℝ × State d) × State d =>
        V.proposalMean (effectiveStep z.1.1) z.1.2) :=
    V.continuous_proposalMean.measurable.comp
      (heff.prodMk (measurable_snd.comp measurable_fst))
  have hdiff : Measurable
      (fun z : (ℝ × State d) × State d =>
        z.2 - V.proposalMean (effectiveStep z.1.1) z.1.2) :=
    measurable_snd.sub hmean
  fun_prop

/-- Joint Gaussian proposal kernel for all real parameters. -/
def gaussianProposalKernelFamily : Kernel (ℝ × State d) (State d) :=
  Kernel.withDensity
    (Kernel.const (ℝ × State d) (volume : Measure (State d)))
    V.proposalFamilyDensity

instance gaussianProposalKernelFamily_isMarkovKernel :
    IsMarkovKernel V.gaussianProposalKernelFamily := by
  refine ⟨fun p => ⟨?_⟩⟩
  rw [gaussianProposalKernelFamily, Kernel.withDensity_apply'
    (Kernel.const (ℝ × State d) (volume : Measure (State d)))
    V.measurable_uncurry_proposalFamilyDensity p Set.univ]
  simp only [Kernel.const_apply, Measure.restrict_univ]
  exact V.proposalDensity_lintegral (effectiveStep_pos p.1) p.2

lemma gaussianProposalKernelFamily_apply (p : ℝ × State d) (s : Set (State d)) :
    V.gaussianProposalKernelFamily p s =
      ∫⁻ y in s, V.proposalDensity (effectiveStep p.1) p.2 y ∂volume := by
  rw [gaussianProposalKernelFamily, Kernel.withDensity_apply'
    (Kernel.const (ℝ × State d) (volume : Measure (State d)))
    V.measurable_uncurry_proposalFamilyDensity p s]
  rfl

/-! ## Joint accept--reject family -/

/-- Joint Metropolis acceptance probability. -/
def malaFamilyAcceptance (p : ℝ × State d) (y : State d) : ℝ≥0∞ :=
  MetropolisHastings.acceptance V.targetDensity
    (V.proposalDensity (effectiveStep p.1)) p.2 y

lemma measurable_uncurry_malaFamilyAcceptance :
    Measurable (Function.uncurry V.malaFamilyAcceptance) := by
  have hq := V.measurable_uncurry_proposalFamilyDensity
  have hcurrent : Measurable
      (fun z : (ℝ × State d) × State d =>
        V.targetDensity z.1.2 * V.proposalFamilyDensity z.1 z.2) :=
    (V.measurable_targetDensity.comp (measurable_snd.comp measurable_fst)).mul hq
  have hswap : Measurable
      (fun z : (ℝ × State d) × State d => ((z.1.1, z.2), z.1.2)) :=
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
      (measurable_snd.comp measurable_fst)
  have hreverse : Measurable
      (fun z : (ℝ × State d) × State d =>
        V.targetDensity z.2 *
          V.proposalDensity (effectiveStep z.1.1) z.2 z.1.2) :=
    (V.measurable_targetDensity.comp measurable_snd).mul (hq.comp hswap)
  exact hreverse.div hcurrent |>.inf measurable_const

lemma malaFamilyAcceptance_le_one (p : ℝ × State d) (y : State d) :
    V.malaFamilyAcceptance p y ≤ 1 :=
  MetropolisHastings.acceptance_le_one _ _ _ _

/-- Total accepted mass of the joint proposal family. -/
def malaFamilyAcceptanceMass (p : ℝ × State d) : ℝ≥0∞ :=
  ∫⁻ y, V.malaFamilyAcceptance p y ∂V.gaussianProposalKernelFamily p

lemma measurable_malaFamilyAcceptanceMass :
    Measurable V.malaFamilyAcceptanceMass := by
  exact V.measurable_uncurry_malaFamilyAcceptance.lintegral_kernel_prod_right'

lemma malaFamilyAcceptanceMass_le_one (p : ℝ × State d) :
    V.malaFamilyAcceptanceMass p ≤ 1 := by
  calc
    V.malaFamilyAcceptanceMass p ≤
        ∫⁻ _y, (1 : ℝ≥0∞) ∂V.gaussianProposalKernelFamily p := by
      exact lintegral_mono fun y => V.malaFamilyAcceptance_le_one p y
    _ = 1 := by simp

/-- Accepted part of the jointly measurable MALA family. -/
def malaAcceptedKernelFamily : Kernel (ℝ × State d) (State d) :=
  Kernel.withDensity V.gaussianProposalKernelFamily V.malaFamilyAcceptance

/-- The deterministic stay-put kernel `(h,x) ↦ δ_x`. -/
def malaStayKernelFamily : Kernel (ℝ × State d) (State d) :=
  Kernel.deterministic Prod.snd measurable_snd

instance malaStayKernelFamily_isMarkovKernel :
    IsMarkovKernel (malaStayKernelFamily (d := d)) := by
  unfold malaStayKernelFamily
  infer_instance

/-- Diagonal rejection part of the jointly measurable MALA family. -/
def malaRejectedKernelFamily : Kernel (ℝ × State d) (State d) :=
  Kernel.withDensity (malaStayKernelFamily (d := d))
    (fun p _y => 1 - V.malaFamilyAcceptanceMass p)

/-- A single Markov kernel representing the measurable family `h ↦ P_h`. -/
def malaKernelFamily : Kernel (ℝ × State d) (State d) :=
  V.malaAcceptedKernelFamily + V.malaRejectedKernelFamily

lemma malaAcceptedKernelFamily_apply_univ (p : ℝ × State d) :
    V.malaAcceptedKernelFamily p Set.univ = V.malaFamilyAcceptanceMass p := by
  rw [malaAcceptedKernelFamily, Kernel.withDensity_apply'
    V.gaussianProposalKernelFamily V.measurable_uncurry_malaFamilyAcceptance p Set.univ]
  simp [malaFamilyAcceptanceMass]

lemma measurable_uncurry_malaRejectionDensity :
    Measurable (Function.uncurry
      (fun p : ℝ × State d => fun (_y : State d) =>
        1 - V.malaFamilyAcceptanceMass p)) := by
  change Measurable (fun z : (ℝ × State d) × State d =>
    1 - V.malaFamilyAcceptanceMass z.1)
  exact measurable_const.sub
    (V.measurable_malaFamilyAcceptanceMass.comp measurable_fst)

lemma malaRejectedKernelFamily_apply_univ (p : ℝ × State d) :
    V.malaRejectedKernelFamily p Set.univ = 1 - V.malaFamilyAcceptanceMass p := by
  rw [malaRejectedKernelFamily, Kernel.withDensity_apply'
    (malaStayKernelFamily (d := d)) V.measurable_uncurry_malaRejectionDensity p Set.univ]
  rw [malaStayKernelFamily, Kernel.deterministic_apply]
  simp

instance malaKernelFamily_isMarkovKernel : IsMarkovKernel V.malaKernelFamily := by
  refine ⟨fun p => ⟨?_⟩⟩
  rw [malaKernelFamily, add_apply, Measure.add_apply,
    V.malaAcceptedKernelFamily_apply_univ,
    V.malaRejectedKernelFamily_apply_univ]
  exact add_tsub_cancel_of_le (V.malaFamilyAcceptanceMass_le_one p)

lemma sectR_gaussianProposalKernelFamily (h : ℝ) :
    Kernel.sectR V.gaussianProposalKernelFamily h =
      V.gaussianDensityProposal (effectiveStep h) := by
  ext x s hs
  rw [Kernel.sectR_apply, V.gaussianProposalKernelFamily_apply,
    V.gaussianDensityProposal_apply]

lemma sectR_malaAcceptedKernelFamily (h : ℝ) :
    Kernel.sectR V.malaAcceptedKernelFamily h =
      MetropolisHastings.accepted
        (V.gaussianDensityProposal (effectiveStep h))
        (V.malaAcceptance (effectiveStep h)) := by
  ext x s hs
  rw [Kernel.sectR_apply, malaAcceptedKernelFamily,
    Kernel.withDensity_apply' V.gaussianProposalKernelFamily
      V.measurable_uncurry_malaFamilyAcceptance (h, x) s]
  rw [MetropolisHastings.accepted,
    Kernel.withDensity_apply' (V.gaussianDensityProposal (effectiveStep h))
      (V.measurable_uncurry_malaAcceptance (effectiveStep h)) x s]
  have hproposal : V.gaussianProposalKernelFamily (h, x) =
      V.gaussianDensityProposal (effectiveStep h) x := by
    exact congrArg (fun K : Kernel (State d) (State d) => K x)
      (V.sectR_gaussianProposalKernelFamily h)
  rw [hproposal]
  rfl

lemma malaFamilyAcceptanceMass_pair (h : ℝ) (x : State d) :
    V.malaFamilyAcceptanceMass (h, x) =
      MetropolisHastings.acceptanceMass
        (V.gaussianDensityProposal (effectiveStep h))
        (V.malaAcceptance (effectiveStep h)) x := by
  unfold malaFamilyAcceptanceMass MetropolisHastings.acceptanceMass
  have hproposal : V.gaussianProposalKernelFamily (h, x) =
      V.gaussianDensityProposal (effectiveStep h) x := by
    exact congrArg (fun K : Kernel (State d) (State d) => K x)
      (V.sectR_gaussianProposalKernelFamily h)
  rw [hproposal]
  rfl

lemma sectR_malaRejectedKernelFamily (h : ℝ) :
    Kernel.sectR V.malaRejectedKernelFamily h =
      MetropolisHastings.rejected
        (V.gaussianDensityProposal (effectiveStep h))
        (V.malaAcceptance (effectiveStep h)) := by
  ext x : 1
  simp only [Kernel.sectR_apply]
  rw [malaRejectedKernelFamily,
    Kernel.withDensity_apply _ V.measurable_uncurry_malaRejectionDensity]
  rw [MetropolisHastings.rejected,
    Kernel.withDensity_apply _
      (MetropolisHastings.measurable_rejectionDensity
        (V.gaussianDensityProposal (effectiveStep h))
        (V.malaAcceptance (effectiveStep h))
        (V.measurable_uncurry_malaAcceptance (effectiveStep h)))]
  rw [malaStayKernelFamily, Kernel.deterministic_apply, Kernel.id_apply,
    V.malaFamilyAcceptanceMass_pair]

lemma sectR_malaKernelFamily (h : ℝ) :
    Kernel.sectR V.malaKernelFamily h =
      V.malaKernel (effectiveStep h) (effectiveStep_pos h) := by
  ext x : 1
  simp only [Kernel.sectR_apply]
  unfold malaKernelFamily malaKernel MetropolisHastings.kernel
  rw [add_apply, add_apply]
  have ha := congrArg (fun K : Kernel (State d) (State d) => K x)
    (V.sectR_malaAcceptedKernelFamily h)
  have hr := congrArg (fun K : Kernel (State d) (State d) => K x)
    (V.sectR_malaRejectedKernelFamily h)
  exact congrArg₂ (· + ·) ha hr

lemma sectR_malaKernelFamily_isReversible (h : ℝ) :
    Kernel.IsReversible (Kernel.sectR V.malaKernelFamily h)
      (V.target : Measure (State d)) := by
  rw [V.sectR_malaKernelFamily h]
  exact V.malaKernel_isReversible (effectiveStep h) (effectiveStep_pos h)

/-! ## Uniform mixtures on `(0,H]` -/

/-- Lebesgue measure conditioned on `(0,H]`.  The right endpoint convention
is immaterial because singleton sets are Lebesgue-null. -/
def uniformStepMeasure (H : ℝ) : Measure ℝ :=
  ProbabilityTheory.cond (volume : Measure ℝ) (Set.Ioc 0 H)

theorem uniformStepMeasure_isProbabilityMeasure (H : ℝ) (hH : 0 < H) :
    IsProbabilityMeasure (uniformStepMeasure H) := by
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · rw [Real.volume_Ioc]
    simpa using (ENNReal.ofReal_pos.mpr hH).ne'
  · rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top

/-- The paper's kernel `\overline P_H = H⁻¹ ∫₀ᴴ P_h dh`. -/
def uniformMALA (H : ℝ) (_hH : 0 < H) : Kernel (State d) (State d) :=
  Kernel.parameterMixture (uniformStepMeasure H) V.malaKernelFamily

theorem uniformMALA_isMarkovKernel (H : ℝ) (hH : 0 < H) :
    IsMarkovKernel (V.uniformMALA H hH) := by
  letI : IsProbabilityMeasure (uniformStepMeasure H) :=
    uniformStepMeasure_isProbabilityMeasure H hH
  unfold uniformMALA
  infer_instance

theorem uniformMALA_isReversible (H : ℝ) (hH : 0 < H) :
    Kernel.IsReversible (V.uniformMALA H hH) (V.target : Measure (State d)) := by
  letI : IsProbabilityMeasure (uniformStepMeasure H) :=
    uniformStepMeasure_isProbabilityMeasure H hH
  unfold uniformMALA
  exact Kernel.isReversible_parameterMixture
    (V.target : Measure (State d)) (uniformStepMeasure H) V.malaKernelFamily
    V.sectR_malaKernelFamily_isReversible

theorem uniformMALA_invariant (H : ℝ) (hH : 0 < H) :
    Kernel.Invariant (V.uniformMALA H hH) (V.target : Measure (State d)) := by
  letI : IsMarkovKernel (V.uniformMALA H hH) := V.uniformMALA_isMarkovKernel H hH
  exact (V.uniformMALA_isReversible H hH).invariant

/-- Exact Tonelli identity for the concrete uniform-random MALA kernel. -/
theorem energy_uniformMALA (H : ℝ) (hH : 0 < H)
    (f : State d → ℝ) (hf : Measurable f) :
    Dirichlet.energy (V.target : Measure (State d)) (V.uniformMALA H hH) f =
      ∫⁻ h, Dirichlet.energy (V.target : Measure (State d))
        (V.malaKernel (effectiveStep h) (effectiveStep_pos h)) f
        ∂uniformStepMeasure H := by
  letI : IsProbabilityMeasure (uniformStepMeasure H) :=
    uniformStepMeasure_isProbabilityMeasure H hH
  rw [uniformMALA, Dirichlet.energy_parameterMixture
    (V.target : Measure (State d)) (uniformStepMeasure H)
    V.malaKernelFamily f hf]
  apply lintegral_congr
  intro h
  rw [V.sectR_malaKernelFamily h]

/-- The conditioning measure has the explicit density `H⁻¹` on `(0,H]`. -/
theorem uniformStepMeasure_lintegral (H : ℝ) (g : ℝ → ℝ≥0∞) :
    ∫⁻ h, g h ∂uniformStepMeasure H =
      ((volume : Measure ℝ) (Set.Ioc 0 H))⁻¹ * ∫⁻ h in Set.Ioc 0 H, g h ∂volume := by
  rw [uniformStepMeasure, ProbabilityTheory.cond, lintegral_smul_measure]
  rfl

theorem uniformStepMeasure_lintegral_of_pos (H : ℝ) (_hH : 0 < H)
    (g : ℝ → ℝ≥0∞) :
    ∫⁻ h, g h ∂uniformStepMeasure H =
      (ENNReal.ofReal H)⁻¹ * ∫⁻ h in Set.Ioc 0 H, g h ∂volume := by
  rw [uniformStepMeasure_lintegral, Real.volume_Ioc]
  simp

/-- Lebesgue measure conditioned on a nondegenerate interval `(a,b]`. -/
def intervalStepMeasure (a b : ℝ) : Measure ℝ :=
  ProbabilityTheory.cond (volume : Measure ℝ) (Set.Ioc a b)

theorem intervalStepMeasure_isProbabilityMeasure {a b : ℝ} (hab : a < b) :
    IsProbabilityMeasure (intervalStepMeasure a b) := by
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · rw [Real.volume_Ioc]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
  · rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top

/-- The upper dyadic-half step distribution used by the paper's component
kernel `K_t`. -/
def dyadicStepMeasure (t : ℝ) : Measure ℝ :=
  intervalStepMeasure (t / 2) t

theorem dyadicStepMeasure_isProbabilityMeasure {t : ℝ} (ht : 0 < t) :
    IsProbabilityMeasure (dyadicStepMeasure t) := by
  exact intervalStepMeasure_isProbabilityMeasure (by linarith)

/-- The component `K_t = (2/t) ∫_(t/2)^t P_h dh`. -/
def dyadicMALA (t : ℝ) (_ht : 0 < t) : Kernel (State d) (State d) :=
  Kernel.parameterMixture (dyadicStepMeasure t) V.malaKernelFamily

theorem dyadicMALA_isMarkovKernel (t : ℝ) (ht : 0 < t) :
    IsMarkovKernel (V.dyadicMALA t ht) := by
  letI : IsProbabilityMeasure (dyadicStepMeasure t) :=
    dyadicStepMeasure_isProbabilityMeasure ht
  unfold dyadicMALA
  infer_instance

theorem dyadicMALA_isReversible (t : ℝ) (ht : 0 < t) :
    Kernel.IsReversible (V.dyadicMALA t ht) (V.target : Measure (State d)) := by
  letI : IsProbabilityMeasure (dyadicStepMeasure t) :=
    dyadicStepMeasure_isProbabilityMeasure ht
  unfold dyadicMALA
  exact Kernel.isReversible_parameterMixture
    (V.target : Measure (State d)) (dyadicStepMeasure t) V.malaKernelFamily
    V.sectR_malaKernelFamily_isReversible

theorem energy_dyadicMALA (t : ℝ) (ht : 0 < t)
    (f : State d → ℝ) (hf : Measurable f) :
    Dirichlet.energy (V.target : Measure (State d)) (V.dyadicMALA t ht) f =
      ∫⁻ h, Dirichlet.energy (V.target : Measure (State d))
        (V.malaKernel (effectiveStep h) (effectiveStep_pos h)) f
        ∂dyadicStepMeasure t := by
  letI : IsProbabilityMeasure (dyadicStepMeasure t) :=
    dyadicStepMeasure_isProbabilityMeasure ht
  rw [dyadicMALA, Dirichlet.energy_parameterMixture
    (V.target : Measure (State d)) (dyadicStepMeasure t)
    V.malaKernelFamily f hf]
  apply lintegral_congr
  intro h
  rw [V.sectR_malaKernelFamily h]

/-- The unnormalized contribution of a dyadic interval is dominated by the
full uniform-mixture energy.  Normalizing the restricted measure yields the
paper's `t/(2H)` component weight. -/
theorem energy_uniformMALA_restrict_dyadic_le
    (H t : ℝ) (hH : 0 < H) (f : State d → ℝ) (hf : Measurable f) :
    Dirichlet.energy (V.target : Measure (State d))
        (Kernel.parameterMixture
          ((uniformStepMeasure H).restrict (Set.Ioc (t / 2) t))
          V.malaKernelFamily) f ≤
      Dirichlet.energy (V.target : Measure (State d)) (V.uniformMALA H hH) f := by
  letI : IsProbabilityMeasure (uniformStepMeasure H) :=
    uniformStepMeasure_isProbabilityMeasure H hH
  unfold uniformMALA
  exact Dirichlet.energy_parameterMixture_restrict_le
    (V.target : Measure (State d)) (uniformStepMeasure H)
    (Set.Ioc (t / 2) t) V.malaKernelFamily f hf

/-- Exact probability with which the full `(0,H]` mixture selects the upper
dyadic half `(t/2,t]`. -/
theorem uniformStepMeasure_dyadicInterval
    (H t : ℝ) (_hH : 0 < H) (ht : 0 < t) (htH : t ≤ H) :
    uniformStepMeasure H (Set.Ioc (t / 2) t) =
      (ENNReal.ofReal H)⁻¹ * ENNReal.ofReal (t / 2) := by
  have hsub : Set.Ioc (t / 2) t ⊆ Set.Ioc 0 H := by
    intro x hx
    constructor
    · linarith [hx.1]
    · exact hx.2.trans htH
  rw [uniformStepMeasure, ProbabilityTheory.cond_apply measurableSet_Ioc,
    Set.inter_eq_right.mpr hsub, Real.volume_Ioc, Real.volume_Ioc]
  simp only [sub_zero]
  congr 2
  ring

end FirstOrderPotential

end Concrete

end

end UniformRandomMALA
