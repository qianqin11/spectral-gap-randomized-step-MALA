import UniformRandomMALA.Concrete.MALA

/-!
# Gaussian random-walk Metropolis

The elementary proof of the stationary rejection estimate couples the Euler
chain to a stationary Gaussian random-walk Metropolis (RWM) chain.  This file
constructs that RWM kernel from an explicit Lebesgue density and proves its
detailed balance with the normalized Boltzmann target.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace Concrete

namespace FirstOrderPotential

variable {d : ℕ} (V : FirstOrderPotential d)

/-- Unnormalized density of the centered Gaussian random-walk proposal with
covariance `2 δ I`. -/
def randomWalkBase (_V : FirstOrderPotential d) (δ : ℝ)
    (x y : State d) : ℝ :=
  Real.exp (-(1 / (4 * δ)) * ‖y - x‖ ^ 2)

/-- The RWM proposal uses the same finite-dimensional Gaussian normalizer as
the MALA proposal. -/
def randomWalkNormalizer (_V : FirstOrderPotential d) (δ : ℝ) : ℝ :=
  proposalNormalizer (d := d) δ

lemma randomWalkBase_integral {δ : ℝ} (hδ : 0 < δ) (x : State d) :
    ∫ y, V.randomWalkBase δ x y = V.randomWalkNormalizer δ := by
  have hb : 0 < 1 / (4 * δ) :=
    one_div_pos.mpr (mul_pos (by norm_num) hδ)
  have hgauss := GaussianFourier.integral_rexp_neg_mul_sq_norm
    (V := State d) hb
  have hshift := integral_sub_right_eq_self (μ := volume)
    (fun y : State d => Real.exp (-(1 / (4 * δ)) * ‖y‖ ^ 2)) x
  change (∫ y : State d,
    Real.exp (-(1 / (4 * δ)) * ‖y - x‖ ^ 2)) =
      V.randomWalkNormalizer δ
  rw [hshift]
  simpa [randomWalkNormalizer, proposalNormalizer] using hgauss

lemma randomWalkNormalizer_pos {δ : ℝ} (hδ : 0 < δ) :
    0 < V.randomWalkNormalizer δ := by
  exact proposalNormalizer_pos (d := d) hδ

lemma randomWalkBase_integrable {δ : ℝ} (hδ : 0 < δ) (x : State d) :
    Integrable (V.randomWalkBase δ x) := by
  have hb : 0 < 1 / (4 * δ) :=
    one_div_pos.mpr (mul_pos (by norm_num) hδ)
  have hc := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := State d) (b := ((1 / (4 * δ) : ℝ) : ℂ)) (c := 0) (w := 0)
    (by exact_mod_cast hb)
  have hg : Integrable
      (fun y : State d => Real.exp (-(1 / (4 * δ)) * ‖y‖ ^ 2)) := by
    refine hc.norm.congr ?_
    filter_upwards with y
    rw [show (↑‖y‖ : ℂ) ^ 2 = ↑(‖y‖ ^ 2) by norm_cast]
    simp [Complex.norm_exp]
    left
    simp [pow_two, Complex.mul_re]
  change Integrable
    (fun y : State d => Real.exp (-(1 / (4 * δ)) * ‖y - x‖ ^ 2))
  exact hg.comp_sub_right x

/-- Real-valued RWM proposal density. -/
def randomWalkDensityReal (V : FirstOrderPotential d) (δ : ℝ)
    (x y : State d) : ℝ :=
  V.randomWalkBase δ x y / V.randomWalkNormalizer δ

lemma randomWalkDensityReal_integral {δ : ℝ} (hδ : 0 < δ)
    (x : State d) :
    ∫ y, V.randomWalkDensityReal δ x y = 1 := by
  change (∫ y, V.randomWalkBase δ x y /
    V.randomWalkNormalizer δ) = 1
  rw [integral_div, V.randomWalkBase_integral hδ x]
  exact div_self (V.randomWalkNormalizer_pos hδ).ne'

lemma randomWalkDensityReal_integrable {δ : ℝ} (hδ : 0 < δ)
    (x : State d) :
    Integrable (V.randomWalkDensityReal δ x) :=
  (V.randomWalkBase_integrable hδ x).div_const _

lemma randomWalkDensityReal_nonneg {δ : ℝ} (hδ : 0 < δ)
    (x y : State d) :
    0 ≤ V.randomWalkDensityReal δ x y :=
  div_nonneg (Real.exp_pos _).le
    (V.randomWalkNormalizer_pos hδ).le

lemma randomWalkDensityReal_pos {δ : ℝ} (hδ : 0 < δ)
    (x y : State d) :
    0 < V.randomWalkDensityReal δ x y :=
  div_pos (Real.exp_pos _) (V.randomWalkNormalizer_pos hδ)

lemma randomWalkDensityReal_swap (δ : ℝ) (x y : State d) :
    V.randomWalkDensityReal δ x y = V.randomWalkDensityReal δ y x := by
  unfold randomWalkDensityReal randomWalkBase
  rw [norm_sub_rev]

/-- Extended-valued RWM proposal density. -/
def randomWalkDensity (V : FirstOrderPotential d) (δ : ℝ)
    (x y : State d) : ℝ≥0∞ :=
  ENNReal.ofReal (V.randomWalkDensityReal δ x y)

lemma randomWalkDensity_swap (δ : ℝ) (x y : State d) :
    V.randomWalkDensity δ x y = V.randomWalkDensity δ y x := by
  simp [randomWalkDensity, V.randomWalkDensityReal_swap δ x y]

lemma randomWalkDensity_pos {δ : ℝ} (hδ : 0 < δ) (x y : State d) :
    0 < V.randomWalkDensity δ x y :=
  ENNReal.ofReal_pos.mpr (V.randomWalkDensityReal_pos hδ x y)

lemma randomWalkDensity_ne_top (δ : ℝ) (x y : State d) :
    V.randomWalkDensity δ x y ≠ ∞ := by
  simp [randomWalkDensity]

lemma randomWalkDensity_lintegral {δ : ℝ} (hδ : 0 < δ)
    (x : State d) :
    ∫⁻ y, V.randomWalkDensity δ x y = 1 := by
  change (∫⁻ y, ENNReal.ofReal (V.randomWalkDensityReal δ x y)) = 1
  rw [← ofReal_integral_eq_lintegral_ofReal
    (V.randomWalkDensityReal_integrable hδ x)
    (ae_of_all _ (V.randomWalkDensityReal_nonneg hδ x))]
  simp [V.randomWalkDensityReal_integral hδ x]

lemma measurable_uncurry_randomWalkDensity (δ : ℝ) :
    Measurable (Function.uncurry (V.randomWalkDensity δ)) := by
  apply ENNReal.measurable_ofReal.comp
  unfold randomWalkDensityReal randomWalkBase randomWalkNormalizer
    proposalNormalizer
  have hdiff : Continuous
      (fun z : State d × State d => z.2 - z.1) :=
    continuous_snd.sub continuous_fst
  exact ((Real.continuous_exp.comp
    (continuous_const.mul ((continuous_norm.comp hdiff).pow 2))).div_const _).measurable

/-- Gaussian random-walk proposal kernel. -/
def randomWalkProposal (V : FirstOrderPotential d) (δ : ℝ) :
    Kernel (State d) (State d) :=
  Kernel.withDensity (Kernel.const (State d) (volume : Measure (State d)))
    (V.randomWalkDensity δ)

instance randomWalkProposal_isSFiniteKernel (δ : ℝ) :
    IsSFiniteKernel (V.randomWalkProposal δ) := by
  unfold randomWalkProposal
  exact Kernel.IsSFiniteKernel.withDensity _ (V.randomWalkDensity_ne_top δ)

instance randomWalkProposal_isMarkovKernel (δ : ℝ) [hδ : Fact (0 < δ)] :
    IsMarkovKernel (V.randomWalkProposal δ) := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [randomWalkProposal, Kernel.withDensity_apply'
    (Kernel.const (State d) (volume : Measure (State d)))
    (V.measurable_uncurry_randomWalkDensity δ) x Set.univ]
  simp only [Kernel.const_apply, Measure.restrict_univ]
  exact V.randomWalkDensity_lintegral hδ.out x

/-- Metropolis acceptance probability for the Gaussian random walk. -/
def rwmAcceptance (δ : ℝ) (x y : State d) : ℝ≥0∞ :=
  MetropolisHastings.acceptance V.targetDensity
    (V.randomWalkDensity δ) x y

lemma measurable_uncurry_rwmAcceptance (δ : ℝ) :
    Measurable (Function.uncurry (V.rwmAcceptance δ)) := by
  exact MetropolisHastings.measurable_uncurry_acceptance
    V.targetDensity (V.randomWalkDensity δ)
    V.measurable_targetDensity (V.measurable_uncurry_randomWalkDensity δ)

lemma rwmAcceptance_le_one (δ : ℝ) (x y : State d) :
    V.rwmAcceptance δ x y ≤ 1 :=
  MetropolisHastings.acceptance_le_one _ _ x y

/-- Symmetry of the Gaussian proposal cancels it from the RWM Metropolis
ratio.  This is the kernel-level counterpart of
`min 1 (exp (U x - U y))` used in the finite coupling. -/
lemma rwmAcceptance_eq_targetRatio {δ : ℝ} (hδ : 0 < δ)
    (x y : State d) :
    V.rwmAcceptance δ x y =
      (V.targetDensity y / V.targetDensity x) ⊓ 1 := by
  unfold rwmAcceptance MetropolisHastings.acceptance
    MetropolisHastings.edgeDensity
  rw [V.randomWalkDensity_swap δ y x]
  rw [ENNReal.mul_div_mul_right]
  · exact (V.randomWalkDensity_pos hδ x y).ne'
  · exact V.randomWalkDensity_ne_top δ x y

/-- The normalized target ratio is the usual Boltzmann energy increment;
the unknown partition function cancels exactly. -/
lemma targetDensity_ratio (x y : State d) :
    V.targetDensity y / V.targetDensity x =
      ENNReal.ofReal (Real.exp (V.U x - V.U y)) := by
  have hmass : V.boltzmannFiniteMeasure.mass ≠ 0 :=
    V.boltzmannFiniteMeasure.mass_nonzero_iff.mpr
      V.boltzmannFiniteMeasure_ne_zero
  unfold targetDensity boltzmannDensity boltzmannWeight
  rw [ENNReal.mul_div_mul_left]
  · rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos (-V.U x))]
    congr 1
    rw [← Real.exp_sub]
    congr 1
    ring
  · exact ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top
  · exact ENNReal.inv_ne_top.mpr (ENNReal.coe_ne_zero.mpr hmass)

/-- Concrete form of the RWM acceptance probability used by the elementary
coupling construction. -/
lemma rwmAcceptance_eq_boltzmann {δ : ℝ} (hδ : 0 < δ)
    (x y : State d) :
    V.rwmAcceptance δ x y =
      ENNReal.ofReal (Real.exp (V.U x - V.U y)) ⊓ 1 := by
  rw [V.rwmAcceptance_eq_targetRatio hδ x y, V.targetDensity_ratio x y]

/-- The concrete Gaussian random-walk Metropolis kernel. -/
def rwmKernel (δ : ℝ) (_hδ : 0 < δ) : Kernel (State d) (State d) := by
  exact MetropolisHastings.kernel
    (V.randomWalkProposal δ) (V.rwmAcceptance δ)

theorem rwmKernel_isMarkovKernel (δ : ℝ) (hδ : 0 < δ) :
    IsMarkovKernel (V.rwmKernel δ hδ) := by
  letI : Fact (0 < δ) := ⟨hδ⟩
  letI : Fact (Measurable (Function.uncurry (V.rwmAcceptance δ))) :=
    ⟨V.measurable_uncurry_rwmAcceptance δ⟩
  letI : Fact (∀ x y, V.rwmAcceptance δ x y ≤ 1) :=
    ⟨V.rwmAcceptance_le_one δ⟩
  unfold rwmKernel
  infer_instance

lemma rwmEdgeDensity_ne_zero {δ : ℝ} (hδ : 0 < δ)
    (x y : State d) :
    MetropolisHastings.edgeDensity V.targetDensity
      (V.randomWalkDensity δ) x y ≠ 0 := by
  exact (ENNReal.mul_pos (V.targetDensity_pos x).ne'
    (V.randomWalkDensity_pos hδ x y).ne').ne'

lemma rwmEdgeDensity_ne_top (δ : ℝ) (x y : State d) :
    MetropolisHastings.edgeDensity V.targetDensity
      (V.randomWalkDensity δ) x y ≠ ∞ := by
  exact ENNReal.mul_ne_top (V.targetDensity_ne_top x)
    (V.randomWalkDensity_ne_top δ x y)

/-- Detailed balance of the Gaussian RWM kernel with the target. -/
theorem rwmKernel_isReversible (δ : ℝ) (hδ : 0 < δ) :
    Kernel.IsReversible (V.rwmKernel δ hδ)
      (V.target : Measure (State d)) := by
  letI : Fact (0 < δ) := ⟨hδ⟩
  letI : IsSFiniteKernel
      (MetropolisHastings.densityKernel (volume : Measure (State d))
        (V.randomWalkDensity δ)) := by
    unfold MetropolisHastings.densityKernel
    exact Kernel.IsSFiniteKernel.withDensity _
      (V.randomWalkDensity_ne_top δ)
  have hacceptedDensity :=
    @MetropolisHastings.accepted_densityKernel_isReversible
      (State d) (WithLp.measurableSpace 2 (Fin d → ℝ))
      (volume : Measure (State d)) (by infer_instance)
      V.targetDensity (V.randomWalkDensity δ) (by infer_instance)
      V.measurable_targetDensity (V.measurable_uncurry_randomWalkDensity δ)
      (V.rwmEdgeDensity_ne_zero hδ) (V.rwmEdgeDensity_ne_top δ)
  have haccepted : Kernel.IsReversible
      (MetropolisHastings.accepted (V.randomWalkProposal δ)
        (V.rwmAcceptance δ))
      (V.target : Measure (State d)) := by
    change Kernel.IsReversible
      (MetropolisHastings.accepted (V.randomWalkProposal δ)
        (MetropolisHastings.acceptance V.targetDensity
          (V.randomWalkDensity δ)))
      (V.target : Measure (State d))
    rw [V.target_toMeasure_eq_withDensity]
    simpa [randomWalkProposal, MetropolisHastings.densityKernel,
      rwmAcceptance] using hacceptedDensity
  unfold rwmKernel
  exact MetropolisHastings.kernel_isReversible
    (V.target : Measure (State d)) (V.randomWalkProposal δ)
    (V.rwmAcceptance δ) (V.measurable_uncurry_rwmAcceptance δ) haccepted

theorem rwmKernel_invariant (δ : ℝ) (hδ : 0 < δ) :
    Kernel.Invariant (V.rwmKernel δ hδ)
      (V.target : Measure (State d)) := by
  letI : IsMarkovKernel (V.rwmKernel δ hδ) :=
    V.rwmKernel_isMarkovKernel δ hδ
  exact (V.rwmKernel_isReversible δ hδ).invariant

end FirstOrderPotential

end Concrete

end

end UniformRandomMALA
