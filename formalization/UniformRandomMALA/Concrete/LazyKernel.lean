import UniformRandomMALA.Concrete.HessianMainTheorem
import Mathlib.Probability.Distributions.Uniform

/-!
# Fair lazification of a Markov kernel

This file constructs the concrete half-lazy kernel `(I + K) / 2` as a
parameter mixture: a fair Boolean coin selects either the identity kernel or
`K`.  The construction is available for an arbitrary measurable state space.

The main results prove preservation of the Markov and reversible properties,
exact scaling of Dirichlet energy by `1/2`, and exact scaling of the paper's
`L²` Rayleigh spectral gap by `1/2`.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- The fair probability measure on a Boolean choice. -/
def fairCoinMeasure : Measure Bool :=
  (PMF.uniformOfFintype Bool).toMeasure

instance fairCoinMeasure_isProbabilityMeasure :
    IsProbabilityMeasure fairCoinMeasure := by
  unfold fairCoinMeasure
  infer_instance

/-- A jointly measurable kernel family selected by a Boolean parameter:
`true` selects `K`, while `false` selects the identity kernel. -/
def halfLazyFamily (K : Kernel α α) : Kernel (Bool × α) α :=
  by
    classical
    exact Kernel.piecewise
      (s := Prod.fst ⁻¹' ({true} : Set Bool))
      ((MeasurableSet.singleton true).preimage measurable_fst)
      (Kernel.prodMkLeft Bool K)
      (Kernel.prodMkLeft Bool Kernel.id)

/-- The concrete half-lazification `(I + K) / 2`, implemented as a fair
parameter mixture. -/
def halfLazyKernel (K : Kernel α α) : Kernel α α :=
  Kernel.parameterMixture fairCoinMeasure (halfLazyFamily K)

@[simp] theorem sectR_halfLazyFamily_true (K : Kernel α α) :
    Kernel.sectR (halfLazyFamily K) true = K := by
  classical
  ext x A
  rw [Kernel.sectR_apply, halfLazyFamily, Kernel.piecewise_apply']
  simp

@[simp] theorem sectR_halfLazyFamily_false (K : Kernel α α) :
    Kernel.sectR (halfLazyFamily K) false = Kernel.id := by
  classical
  ext x A
  rw [Kernel.sectR_apply, halfLazyFamily, Kernel.piecewise_apply']
  simp

instance halfLazyFamily_isMarkovKernel (K : Kernel α α) [IsMarkovKernel K] :
    IsMarkovKernel (halfLazyFamily K) := by
  classical
  refine ⟨fun z => ?_⟩
  rw [halfLazyFamily, Kernel.piecewise_apply]
  split_ifs <;> infer_instance

/-- The identity kernel is reversible with respect to every measure. -/
theorem kernelId_isReversible (π : Measure α) :
    Kernel.IsReversible (Kernel.id : Kernel α α) π := by
  intro A B hA hB
  simp [Kernel.id_apply, Measure.dirac_apply' _ hA,
    Measure.dirac_apply' _ hB, hA, hB, Set.inter_comm]

/-- Fair lazification preserves the Markov property. -/
instance halfLazyKernel_isMarkovKernel (K : Kernel α α) [IsMarkovKernel K] :
    IsMarkovKernel (halfLazyKernel K) := by
  unfold halfLazyKernel
  infer_instance

/-- Setwise formula identifying the parameter-mixture construction with the
usual arithmetic notation `(I + K) / 2`. -/
theorem halfLazyKernel_apply
    (K : Kernel α α) [IsMarkovKernel K]
    (x : α) (A : Set α) (hA : MeasurableSet A) :
    halfLazyKernel K x A =
      (2 : ℝ≥0∞)⁻¹ * ((Kernel.id : Kernel α α) x A + K x A) := by
  rw [halfLazyKernel,
    Kernel.parameterMixture_apply fairCoinMeasure (halfLazyFamily K) x A hA]
  rw [MeasureTheory.lintegral_fintype]
  simp [fairCoinMeasure, halfLazyFamily, Kernel.piecewise_apply',
    mul_add, mul_comm, add_comm]

/-- Fair lazification preserves reversibility with respect to the same
measure. -/
theorem halfLazyKernel_isReversible
    (π : Measure α) [SFinite π]
    (K : Kernel α α) [IsMarkovKernel K]
    (hrev : Kernel.IsReversible K π) :
    Kernel.IsReversible (halfLazyKernel K) π := by
  apply Kernel.isReversible_parameterMixture
  intro b
  cases b
  · simpa using kernelId_isReversible π
  · simpa using hrev

/-- The identity kernel has zero Dirichlet energy. -/
@[simp] theorem Dirichlet.energy_id
    (π : Measure α) (f : α → ℝ) (hf : Measurable f) :
    Dirichlet.energy π (Kernel.id : Kernel α α) f = 0 := by
  unfold Dirichlet.energy
  have hinner (x : α) :
      ∫⁻ y, ENNReal.ofReal ((f x - f y) ^ 2) ∂(Kernel.id : Kernel α α) x = 0 := by
    rw [Kernel.lintegral_id']
    · simp
    · exact ENNReal.measurable_ofReal.comp
        ((measurable_const.sub hf).pow_const 2)
  simp_rw [hinner]
  simp

/-- Exact Dirichlet-energy scaling under fair lazification. -/
theorem Dirichlet.energy_halfLazyKernel
    (π : Measure α) [SFinite π]
    (K : Kernel α α) [IsMarkovKernel K]
    (f : α → ℝ) (hf : Measurable f) :
    Dirichlet.energy π (halfLazyKernel K) f =
      (2 : ℝ≥0∞)⁻¹ * Dirichlet.energy π K f := by
  rw [halfLazyKernel, Dirichlet.energy_parameterMixture
    π fairCoinMeasure (halfLazyFamily K) f hf]
  rw [MeasureTheory.lintegral_fintype]
  simp [fairCoinMeasure, Dirichlet.energy_id π f hf, mul_comm]

/-- Every Rayleigh quotient is scaled exactly by `1/2` under fair
lazification. -/
theorem rayleighQuotient_halfLazyKernel
    (π : Measure α) [SFinite π]
    (K : Kernel α α) [IsMarkovKernel K]
    (f : L2RayleighTest π) :
    rayleighQuotient π (halfLazyKernel K) f =
      (2 : ℝ≥0∞)⁻¹ * rayleighQuotient π K f := by
  rw [rayleighQuotient, rayleighQuotient,
    Dirichlet.energy_halfLazyKernel π K f f.measurable_toFun]
  rw [mul_div_assoc]

/-- The paper's `L²` Rayleigh spectral gap is scaled exactly by `1/2`
under fair lazification, including empty-test and infinite-gap cases. -/
theorem rayleighSpectralGap_halfLazyKernel
    (π : Measure α) [SFinite π]
    (K : Kernel α α) [IsMarkovKernel K] :
    rayleighSpectralGap π (halfLazyKernel K) =
      (2 : ℝ≥0∞)⁻¹ * rayleighSpectralGap π K := by
  rw [rayleighSpectralGap, rayleighSpectralGap,
    ENNReal.mul_iInf_of_ne (by norm_num) (by norm_num)]
  apply iInf_congr
  intro f
  exact rayleighQuotient_halfLazyKernel π K f

namespace FirstOrderPotential

variable {d : ℕ}

/-- The concrete fair half-lazy uniformly randomized MALA kernel. -/
def lazyUniformMALA (V : FirstOrderPotential d) (H : ℝ) (hH : 0 < H) :
    Kernel (State d) (State d) :=
  halfLazyKernel (V.uniformMALA H hH)

/-- The lazy uniformly randomized MALA kernel is Markov. -/
theorem lazyUniformMALA_isMarkovKernel
    (V : FirstOrderPotential d) (H : ℝ) (hH : 0 < H) :
    IsMarkovKernel (V.lazyUniformMALA H hH) := by
  letI : IsMarkovKernel (V.uniformMALA H hH) :=
    V.uniformMALA_isMarkovKernel H hH
  unfold lazyUniformMALA
  infer_instance

/-- The lazy uniformly randomized MALA kernel is reversible with respect to
the same concrete target. -/
theorem lazyUniformMALA_isReversible
    (V : FirstOrderPotential d) (H : ℝ) (hH : 0 < H) :
    Kernel.IsReversible (V.lazyUniformMALA H hH)
      (V.target : Measure (State d)) := by
  letI : IsMarkovKernel (V.uniformMALA H hH) :=
    V.uniformMALA_isMarkovKernel H hH
  exact halfLazyKernel_isReversible (V.target : Measure (State d))
    (V.uniformMALA H hH) (V.uniformMALA_isReversible H hH)

/-- Exact Dirichlet-energy scaling for the concrete lazy uniformly
randomized MALA kernel. -/
theorem energy_lazyUniformMALA
    (V : FirstOrderPotential d) (H : ℝ) (hH : 0 < H)
    (f : State d → ℝ) (hf : Measurable f) :
    Dirichlet.energy (V.target : Measure (State d))
        (V.lazyUniformMALA H hH) f =
      (2 : ℝ≥0∞)⁻¹ *
        Dirichlet.energy (V.target : Measure (State d))
          (V.uniformMALA H hH) f := by
  letI : IsMarkovKernel (V.uniformMALA H hH) :=
    V.uniformMALA_isMarkovKernel H hH
  exact Dirichlet.energy_halfLazyKernel
    (V.target : Measure (State d)) (V.uniformMALA H hH) f hf

/-- Exact paper-style spectral-gap scaling for the concrete lazy uniformly
randomized MALA kernel. -/
theorem rayleighSpectralGap_lazyUniformMALA
    (V : FirstOrderPotential d) (H : ℝ) (hH : 0 < H) :
    rayleighSpectralGap (V.target : Measure (State d))
        (V.lazyUniformMALA H hH) =
      (2 : ℝ≥0∞)⁻¹ *
        rayleighSpectralGap (V.target : Measure (State d))
          (V.uniformMALA H hH) := by
  letI : IsMarkovKernel (V.uniformMALA H hH) :=
    V.uniformMALA_isMarkovKernel H hH
  exact rayleighSpectralGap_halfLazyKernel
    (V.target : Measure (State d)) (V.uniformMALA H hH)

end FirstOrderPotential

namespace HessianBoundedPotential

variable {d : ℕ}

/-- The lazy clause of Theorem 2.1 under the manuscript's `C²` Hessian
assumptions: the non-lazy master right-hand side is divided exactly by two. -/
theorem universal_half_masterRHS_lazy_rayleighSpectralGap_lower
    (V : HessianBoundedPotential d) (H : ℝ) (hH : 0 < H) :
    let W := V.toFirstOrderPotential
    let p := W.universalParameters H hH
    (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal p.masterRHS ≤
      rayleighSpectralGap (W.target : Measure (State d))
        (W.lazyUniformMALA p.H p.hH) := by
  simp only
  let W := V.toFirstOrderPotential
  let p := W.universalParameters H hH
  letI : IsMarkovKernel (W.uniformMALA p.H p.hH) :=
    W.uniformMALA_isMarkovKernel p.H p.hH
  rw [W.rayleighSpectralGap_lazyUniformMALA p.H p.hH]
  exact mul_le_mul_of_nonneg_left
    (V.universal_masterRHS_rayleighSpectralGap_lower H hH) bot_le

end HessianBoundedPotential

/-- The lazy clause of Theorem 2.1 in the same displayed
existential-constant form as `exists_universal_nonlazy_paperMasterRHS_lower`.
The constants are chosen before the dimension and potential. -/
theorem exists_universal_lazy_paperMasterRHS_lower :
    ∃ A₀ b₀ c₀ : ℝ,
      2 ≤ A₀ ∧ 0 < b₀ ∧ b₀ ≤ 1 / 2 ∧ 0 < c₀ ∧
      ∀ {d : ℕ} (V : HessianBoundedPotential d) (H : ℝ) (hH : 0 < H),
        (2 : ℝ≥0∞)⁻¹ *
            ENNReal.ofReal (paperMasterRHS V A₀ b₀ c₀ H) ≤
          rayleighSpectralGap
            (V.toFirstOrderPotential.target : Measure (State d))
            (V.toFirstOrderPotential.lazyUniformMALA H hH) := by
  refine ⟨FirstOrderPotential.concreteA0,
    FirstOrderPotential.concreteB0, concreteGapConstant,
    FirstOrderPotential.concreteA0_ge_two,
    FirstOrderPotential.concreteB0_pos,
    FirstOrderPotential.concreteB0_le_half,
    concreteGapConstant_pos, ?_⟩
  intro d V H hH
  have hmain := V.universal_half_masterRHS_lazy_rayleighSpectralGap_lower H hH
  simpa [paperMasterRHS, paperMomentThreshold,
    HessianBoundedPotential.toFirstOrderPotential,
    FirstOrderPotential.universalParameters,
    FirstOrderPotential.toParameters,
    Parameters.masterRHS, Parameters.certifiedScale,
    Parameters.baseFactor, Parameters.certifiedShape,
    Parameters.rejectionShape, Parameters.safeShape] using hmain

end

end UniformRandomMALA.Concrete
