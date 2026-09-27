import UniformRandomMALA.Concrete.NonconvexPotential
import UniformRandomMALA.Concrete.MALA

/-!
# Fixed-step MALA for nonconvex Boltzmann targets

These constructions use the same Gaussian drift proposal, Metropolis ratio,
and rejection atom as the standing strongly convex algorithm. Their Markov
and reversibility proofs reuse the general Metropolis--Hastings theorems;
convexity plays no role. The final equalities identify them with the existing
algorithm on the strongly convex subclass.

This supplies the algorithm definitions for the nonconvex rejection theorem
in Proposition B.1 (`prop:stationary-rejection`). The rejection bound itself
is a separate proof obligation.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

namespace Concrete

namespace NonconvexPotential

variable {d : ℕ} (V : NonconvexPotential d)

/-- The deterministic mean of the Euler proposal. -/
def proposalMean (h : ℝ) (x : State d) : State d :=
  x - h • V.gradU x

lemma continuous_proposalMean :
    Continuous (fun p : ℝ × State d => V.proposalMean p.1 p.2) := by
  unfold proposalMean
  exact continuous_snd.sub
    (continuous_fst.smul (V.continuous_gradU.comp continuous_snd))

/-- Map an input `(h,x)` and a standard Gaussian innovation to the MALA
proposal point. -/
def proposalMap (p : (ℝ × State d) × State d) : State d :=
  V.proposalMean p.1.1 p.1.2 + Real.sqrt (2 * p.1.1) • p.2

lemma continuous_proposalMap : Continuous V.proposalMap := by
  unfold proposalMap
  apply Continuous.add
  · exact V.continuous_proposalMean.comp continuous_fst
  · fun_prop

lemma measurable_proposalMap : Measurable V.proposalMap :=
  V.continuous_proposalMap.measurable

/-- The jointly measurable family `(h,x) ↦ Q_h(x,·)`. -/
def gaussianProposalFamily : Kernel (ℝ × State d) (State d) :=
  Kernel.map
    (Kernel.id ×ₖ
      Kernel.const (ℝ × State d) (stdGaussian (State d)))
    V.proposalMap

instance gaussianProposalFamily_isMarkovKernel :
    IsMarkovKernel V.gaussianProposalFamily := by
  unfold gaussianProposalFamily
  exact Kernel.IsMarkovKernel.map _ V.measurable_proposalMap

/-- The proposal at one fixed step size. -/
def gaussianProposal (h : ℝ) : Kernel (State d) (State d) :=
  Kernel.sectR V.gaussianProposalFamily h

instance gaussianProposal_isMarkovKernel (h : ℝ) :
    IsMarkovKernel (V.gaussianProposal h) := by
  unfold gaussianProposal
  infer_instance

theorem lintegral_gaussianProposalFamily
    (h : ℝ) (x : State d) {g : State d → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ y, g y ∂V.gaussianProposalFamily (h, x) =
      ∫⁻ z, g (V.proposalMean h x + Real.sqrt (2 * h) • z)
        ∂stdGaussian (State d) := by
  rw [gaussianProposalFamily,
    Kernel.lintegral_map _ V.measurable_proposalMap (h, x) hg]
  rw [Kernel.lintegral_id_prod
    (f := fun p => g (V.proposalMap p))
    (hg.comp V.measurable_proposalMap)
    (Kernel.const (ℝ × State d) (stdGaussian (State d))) (h, x)]
  rfl

theorem lintegral_gaussianProposal
    (h : ℝ) (x : State d) {g : State d → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ y, g y ∂V.gaussianProposal h x =
      ∫⁻ z, g (V.proposalMean h x + Real.sqrt (2 * h) • z)
        ∂stdGaussian (State d) := by
  exact V.lintegral_gaussianProposalFamily h x hg

/-! ## A Lebesgue-density presentation

The pushforward construction above is convenient for coupling arguments.  The
Metropolis ratio is more naturally expressed using the equivalent Gaussian
density.  We therefore construct that density directly and prove its total
mass is one.  Equality of the two presentations is isolated as a later bridge;
neither construction is an abstract kernel interface.
-/

/-- The unnormalized translated Gaussian factor in the proposal density. -/
def proposalBase (h : ℝ) (x y : State d) : ℝ :=
  Real.exp (-(1 / (4 * h)) * ‖y - V.proposalMean h x‖ ^ 2)

/-- The exact finite-dimensional Gaussian normalizer. -/
def proposalNormalizer (h : ℝ) : ℝ :=
  (Real.pi / (1 / (4 * h))) ^ ((d : ℝ) / 2)

lemma proposalBase_integral {h : ℝ} (hh : 0 < h) (x : State d) :
    ∫ y, V.proposalBase h x y = proposalNormalizer (d := d) h := by
  have hb : 0 < 1 / (4 * h) := one_div_pos.mpr (mul_pos (by norm_num) hh)
  have hgauss := GaussianFourier.integral_rexp_neg_mul_sq_norm
    (V := State d) hb
  have hshift := integral_sub_right_eq_self (μ := volume)
    (fun y : State d => Real.exp (-(1 / (4 * h)) * ‖y‖ ^ 2))
    (V.proposalMean h x)
  change (∫ y : State d, Real.exp
    (-(1 / (4 * h)) * ‖y - V.proposalMean h x‖ ^ 2)) = proposalNormalizer h
  rw [hshift]
  simpa [proposalNormalizer] using hgauss

lemma proposalNormalizer_pos {h : ℝ} (hh : 0 < h) :
    0 < proposalNormalizer (d := d) h := by
  apply Real.rpow_pos_of_pos
  exact div_pos Real.pi_pos (one_div_pos.mpr (mul_pos (by norm_num) hh))

lemma proposalBase_integrable {h : ℝ} (hh : 0 < h) (x : State d) :
    Integrable (V.proposalBase h x) := by
  have hb : 0 < 1 / (4 * h) := one_div_pos.mpr (mul_pos (by norm_num) hh)
  have hc := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := State d) (b := ((1 / (4 * h) : ℝ) : ℂ)) (c := 0) (w := 0)
    (by exact_mod_cast hb)
  have hg : Integrable
      (fun y : State d => Real.exp (-(1 / (4 * h)) * ‖y‖ ^ 2)) := by
    refine hc.norm.congr ?_
    filter_upwards with y
    rw [show (↑‖y‖ : ℂ) ^ 2 = ↑(‖y‖ ^ 2) by norm_cast]
    simp [Complex.norm_exp]
    left
    simp [pow_two, Complex.mul_re]
  change Integrable (fun y : State d =>
    Real.exp (-(1 / (4 * h)) * ‖y - V.proposalMean h x‖ ^ 2))
  exact hg.comp_sub_right (V.proposalMean h x)

/-- Real-valued Gaussian proposal density with covariance `2h I`. -/
def proposalDensityReal (h : ℝ) (x y : State d) : ℝ :=
  V.proposalBase h x y / proposalNormalizer (d := d) h

lemma proposalDensityReal_integral {h : ℝ} (hh : 0 < h) (x : State d) :
    ∫ y, V.proposalDensityReal h x y = 1 := by
  change (∫ y, V.proposalBase h x y / proposalNormalizer (d := d) h) = 1
  rw [integral_div, V.proposalBase_integral hh x]
  exact div_self (proposalNormalizer_pos (d := d) hh).ne'

lemma proposalDensityReal_integrable {h : ℝ} (hh : 0 < h) (x : State d) :
    Integrable (V.proposalDensityReal h x) :=
  (V.proposalBase_integrable hh x).div_const _

lemma proposalDensityReal_nonneg {h : ℝ} (hh : 0 < h) (x y : State d) :
    0 ≤ V.proposalDensityReal h x y :=
  div_nonneg (Real.exp_pos _).le (proposalNormalizer_pos (d := d) hh).le

lemma proposalDensityReal_pos {h : ℝ} (hh : 0 < h) (x y : State d) :
    0 < V.proposalDensityReal h x y :=
  div_pos (Real.exp_pos _) (proposalNormalizer_pos (d := d) hh)

/-- Extended-valued form of the Gaussian proposal density. -/
def proposalDensity (h : ℝ) (x y : State d) : ℝ≥0∞ :=
  ENNReal.ofReal (V.proposalDensityReal h x y)

lemma proposalDensity_pos {h : ℝ} (hh : 0 < h) (x y : State d) :
    0 < V.proposalDensity h x y :=
  ENNReal.ofReal_pos.mpr (V.proposalDensityReal_pos hh x y)

lemma proposalDensity_ne_top (h : ℝ) (x y : State d) :
    V.proposalDensity h x y ≠ ∞ := by
  simp [proposalDensity]

lemma proposalDensity_lintegral {h : ℝ} (hh : 0 < h) (x : State d) :
    ∫⁻ y, V.proposalDensity h x y = 1 := by
  change (∫⁻ y, ENNReal.ofReal (V.proposalDensityReal h x y)) = 1
  rw [← ofReal_integral_eq_lintegral_ofReal
    (V.proposalDensityReal_integrable hh x)
    (ae_of_all _ (V.proposalDensityReal_nonneg hh x))]
  simp [V.proposalDensityReal_integral hh x]

lemma measurable_uncurry_proposalDensity (h : ℝ) :
    Measurable (Function.uncurry (V.proposalDensity h)) := by
  apply ENNReal.measurable_ofReal.comp
  unfold proposalDensityReal proposalBase proposalNormalizer
  have hmean : Continuous (fun x : State d => V.proposalMean h x) :=
    V.continuous_proposalMean.comp (continuous_const.prodMk continuous_id)
  have hdiff : Continuous
      (fun z : State d × State d => z.2 - V.proposalMean h z.1) :=
    continuous_snd.sub (hmean.comp continuous_fst)
  exact ((Real.continuous_exp.comp
    (continuous_const.mul ((continuous_norm.comp hdiff).pow 2))).div_const _).measurable

/-- The proposal kernel presented directly by its Lebesgue density. -/
def gaussianDensityProposal (h : ℝ) : Kernel (State d) (State d) :=
  Kernel.withDensity (Kernel.const (State d) (volume : Measure (State d)))
    (V.proposalDensity h)

instance gaussianDensityProposal_isSFiniteKernel (h : ℝ) :
    IsSFiniteKernel (V.gaussianDensityProposal h) := by
  unfold gaussianDensityProposal
  exact Kernel.IsSFiniteKernel.withDensity _ (V.proposalDensity_ne_top h)

instance gaussianDensityProposal_isMarkovKernel (h : ℝ) [hh : Fact (0 < h)] :
    IsMarkovKernel (V.gaussianDensityProposal h) := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [gaussianDensityProposal, Kernel.withDensity_apply'
    (Kernel.const (State d) (volume : Measure (State d)))
    (V.measurable_uncurry_proposalDensity h) x Set.univ]
  simp only [Kernel.const_apply, Measure.restrict_univ]
  exact V.proposalDensity_lintegral hh.out x

lemma gaussianDensityProposal_apply {h : ℝ} (x : State d)
    (s : Set (State d)) :
    V.gaussianDensityProposal h x s =
      ∫⁻ y in s, V.proposalDensity h x y ∂volume := by
  rw [gaussianDensityProposal, Kernel.withDensity_apply'
    (Kernel.const (State d) (volume : Measure (State d)))
    (V.measurable_uncurry_proposalDensity h) x s]
  rfl

end NonconvexPotential

end Concrete

end

end UniformRandomMALA

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace Concrete

namespace NonconvexPotential

variable {d : ℕ} (V : NonconvexPotential d)

/-- The Metropolis acceptance probability for the MALA proposal. -/
def malaAcceptance (h : ℝ) (x y : State d) : ℝ≥0∞ :=
  MetropolisHastings.acceptance V.targetDensity (V.proposalDensity h) x y

lemma measurable_uncurry_malaAcceptance (h : ℝ) :
    Measurable (Function.uncurry (V.malaAcceptance h)) := by
  exact MetropolisHastings.measurable_uncurry_acceptance
    V.targetDensity (V.proposalDensity h)
    V.measurable_targetDensity (V.measurable_uncurry_proposalDensity h)

lemma malaAcceptance_le_one (h : ℝ) (x y : State d) :
    V.malaAcceptance h x y ≤ 1 :=
  MetropolisHastings.acceptance_le_one _ _ x y

/-- A fixed-step MALA transition.  The positivity proof is included because
the Gaussian density is a probability density exactly when `h > 0`. -/
def malaKernel (h : ℝ) (_hh : 0 < h) : Kernel (State d) (State d) := by
  exact MetropolisHastings.kernel
    (V.gaussianDensityProposal h) (V.malaAcceptance h)

theorem malaKernel_isMarkovKernel (h : ℝ) (hh : 0 < h) :
    IsMarkovKernel (V.malaKernel h hh) := by
  letI : Fact (0 < h) := ⟨hh⟩
  letI : Fact (Measurable (Function.uncurry (V.malaAcceptance h))) :=
    ⟨V.measurable_uncurry_malaAcceptance h⟩
  letI : Fact (∀ x y, V.malaAcceptance h x y ≤ 1) :=
    ⟨V.malaAcceptance_le_one h⟩
  unfold malaKernel
  infer_instance

lemma malaEdgeDensity_ne_zero {h : ℝ} (hh : 0 < h) (x y : State d) :
    MetropolisHastings.edgeDensity V.targetDensity (V.proposalDensity h) x y ≠ 0 := by
  exact (ENNReal.mul_pos (V.targetDensity_pos x).ne'
    (V.proposalDensity_pos hh x y).ne').ne'

lemma malaEdgeDensity_ne_top (h : ℝ) (x y : State d) :
    MetropolisHastings.edgeDensity V.targetDensity (V.proposalDensity h) x y ≠ ∞ := by
  exact ENNReal.mul_ne_top (V.targetDensity_ne_top x)
    (V.proposalDensity_ne_top h x y)

/-- Every positive-step MALA kernel satisfies detailed balance with the
normalized target. -/
theorem malaKernel_isReversible (h : ℝ) (hh : 0 < h) :
    Kernel.IsReversible (V.malaKernel h hh) (V.target : Measure (State d)) := by
  letI : Fact (0 < h) := ⟨hh⟩
  letI : IsSFiniteKernel
      (MetropolisHastings.densityKernel (volume : Measure (State d))
        (V.proposalDensity h)) := by
    unfold MetropolisHastings.densityKernel
    exact Kernel.IsSFiniteKernel.withDensity _ (V.proposalDensity_ne_top h)
  have hacceptedDensity := @MetropolisHastings.accepted_densityKernel_isReversible
    (State d) (WithLp.measurableSpace 2 (Fin d → ℝ))
    (volume : Measure (State d)) (by infer_instance)
    V.targetDensity (V.proposalDensity h) (by infer_instance)
    V.measurable_targetDensity (V.measurable_uncurry_proposalDensity h)
    (V.malaEdgeDensity_ne_zero hh) (V.malaEdgeDensity_ne_top h)
  have haccepted : Kernel.IsReversible
      (MetropolisHastings.accepted (V.gaussianDensityProposal h)
        (V.malaAcceptance h))
      (V.target : Measure (State d)) := by
    change Kernel.IsReversible
      (MetropolisHastings.accepted (V.gaussianDensityProposal h)
        (MetropolisHastings.acceptance V.targetDensity (V.proposalDensity h)))
      (V.target : Measure (State d))
    rw [V.target_toMeasure_eq_withDensity]
    simpa [gaussianDensityProposal, MetropolisHastings.densityKernel,
      malaAcceptance] using hacceptedDensity
  unfold malaKernel
  exact MetropolisHastings.kernel_isReversible
    (V.target : Measure (State d)) (V.gaussianDensityProposal h)
    (V.malaAcceptance h) (V.measurable_uncurry_malaAcceptance h) haccepted

theorem malaKernel_invariant (h : ℝ) (hh : 0 < h) :
    Kernel.Invariant (V.malaKernel h hh) (V.target : Measure (State d)) := by
  letI : IsMarkovKernel (V.malaKernel h hh) := V.malaKernel_isMarkovKernel h hh
  exact (V.malaKernel_isReversible h hh).invariant

end NonconvexPotential

end Concrete

end

end UniformRandomMALA

namespace UniformRandomMALA.Concrete.C1Potential

open MeasureTheory ProbabilityTheory

noncomputable section
variable {d : ℕ} (V : C1Potential d)

@[simp] theorem nonconvex_gaussianDensityProposal_eq (h : ℝ) :
    V.toNonconvexPotential.gaussianDensityProposal h =
      V.toFirstOrderPotential.gaussianDensityProposal h := rfl

@[simp] theorem nonconvex_malaKernel_eq (h : ℝ) (hh : 0 < h) :
    V.toNonconvexPotential.malaKernel h hh = V.toFirstOrderPotential.malaKernel h hh := rfl

end
end UniformRandomMALA.Concrete.C1Potential
