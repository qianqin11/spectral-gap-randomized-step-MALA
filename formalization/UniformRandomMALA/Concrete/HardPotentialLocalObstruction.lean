import UniformRandomMALA.Concrete.FixedStepHardPotential
import UniformRandomMALA.Concrete.SpectralGapUpperBounds
import UniformRandomMALA.DiscreteTime.GaussianLawBridge
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The local fixed-step obstruction for the smooth hard potential

This module isolates the first-coordinate test-function argument in the
fixed-step upper bound.  The zeroth coordinate of the explicit hard
potential is exactly quadratic.  Consequently its target marginal is the
one-dimensional Gaussian with variance `m⁻¹`, while a Gaussian MALA proposal
has mean increment `-h m x₀` and noise variance `2h`.  Metropolis rejection
can only decrease the squared coordinate increment.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory Gradient RealInnerProductSpace

noncomputable section

/-- Split the zeroth coordinate from a Euclidean state.  The tail is kept as
an ordinary finite function because this is the form in which the product
Lebesgue measure API is most convenient. -/
private def splitFirst (n : ℕ) :
    State (n + 1) ≃ᵐ ℝ × (Fin n → ℝ) :=
  (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0)

private lemma splitFirst_measurePreserving (n : ℕ) :
    MeasurePreserving (splitFirst n) := by
  exact (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp
    (Fin (n + 1))).trans
      (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0)

@[simp] private lemma splitFirst_fst (n : ℕ) (x : State (n + 1)) :
    (splitFirst n x).1 = x 0 := by
  rfl

/-- The part of the hard potential contributed by all coordinates except
the zeroth one, expressed in the product coordinates of `splitFirst`. -/
private def hardTailPotential (n : ℕ) (m L h : ℝ) (z : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, hardOscillatoryCoordinate m L h (z i)

private lemma fixedStepHardPotential_splitFirst_symm
    (n : ℕ) (m L h : ℝ) (u : ℝ) (z : Fin n → ℝ) :
    fixedStepHardPotential (n + 1) m L h ((splitFirst n).symm (u, z)) =
      hardGaussianCoordinate m u + hardTailPotential n m L h z := by
  rw [fixedStepHardPotential, Fin.sum_univ_succ]
  simp [splitFirst, hardCoordinate, hardTailPotential]

/-- The positive Gaussian normalization is absorbed into the tail density,
so that the first factor below is already a probability measure. -/
private def gaussianNormalization (m : ℝ) : ℝ :=
  Real.sqrt (2 * Real.pi * m⁻¹)

private def hardTailDensity (n : ℕ) (m L h : ℝ) (z : Fin n → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (gaussianNormalization m * Real.exp (-hardTailPotential n m L h z))

private lemma measurable_hardTailDensity (n : ℕ) (m L h : ℝ) :
    Measurable (hardTailDensity n m L h) := by
  unfold hardTailDensity gaussianNormalization hardTailPotential
  apply ENNReal.measurable_ofReal.comp
  apply measurable_const.mul
  apply Real.measurable_exp.comp
  apply Measurable.neg
  exact Finset.measurable_sum _ fun i _ =>
    (contDiff_hardOscillatoryCoordinate m L h).continuous.measurable.comp
      (measurable_pi_apply i)

private lemma hardTailDensity_pos
    {m : ℝ} (hm : 0 < m) (n : ℕ) (L h : ℝ) (z : Fin n → ℝ) :
    0 < hardTailDensity n m L h z := by
  apply ENNReal.ofReal_pos.mpr
  exact mul_pos (Real.sqrt_pos.2 (by positivity)) (Real.exp_pos _)

private lemma boltzmannDensity_splitFirst_symm
    (n : ℕ) (hn : 1 ≤ n) {m L h : ℝ} (hm : 0 < m) (hmL : m < L) (hh : 0 < h)
    (u : ℝ) (z : Fin n → ℝ) :
    (fixedStepHardFirstOrderPotential (d := n + 1) (by omega) hm hmL hh).boltzmannDensity
        ((splitFirst n).symm (u, z)) =
      gaussianPDF 0 ⟨m⁻¹, inv_nonneg.mpr hm.le⟩ u * hardTailDensity n m L h z := by
  let v : NNReal := ⟨m⁻¹, inv_nonneg.mpr hm.le⟩
  have hv : (v : ℝ) = m⁻¹ := rfl
  have hnorm : gaussianNormalization m ≠ 0 :=
    (Real.sqrt_pos.2 (by positivity)).ne'
  have hpdf :
      gaussianPDFReal 0 v u * gaussianNormalization m =
        Real.exp (-hardGaussianCoordinate m u) := by
    rw [gaussianPDFReal_def]
    change (Real.sqrt (2 * Real.pi * m⁻¹))⁻¹ *
        Real.exp (-(u - 0) ^ 2 / (2 * m⁻¹)) *
          Real.sqrt (2 * Real.pi * m⁻¹) =
        Real.exp (-(m / 2 * u ^ 2))
    have hexp : -(u - 0) ^ 2 / (2 * m⁻¹) = -(m / 2 * u ^ 2) := by
      field_simp [hm.ne']
      ring
    rw [hexp]
    field_simp [hnorm]
  unfold FirstOrderPotential.boltzmannDensity FirstOrderPotential.boltzmannWeight
  change ENNReal.ofReal
      (Real.exp (-fixedStepHardPotential (n + 1) m L h
        ((splitFirst n).symm (u, z)))) = _
  rw [fixedStepHardPotential_splitFirst_symm]
  rw [show -(hardGaussianCoordinate m u + hardTailPotential n m L h z) =
      -hardGaussianCoordinate m u + -hardTailPotential n m L h z by ring,
    Real.exp_add]
  change _ = ENNReal.ofReal (gaussianPDFReal 0 v u) *
    ENNReal.ofReal
      (gaussianNormalization m * Real.exp (-hardTailPotential n m L h z))
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 v u)]
  congr 1
  rw [← hpdf]
  exact mul_assoc _ _ _

private lemma map_boltzmannMeasure_splitFirst
    (n : ℕ) (hn : 1 ≤ n) {m L h : ℝ}
    (hm : 0 < m) (hmL : m < L) (hh : 0 < h) :
    Measure.map (splitFirst n)
        (fixedStepHardFirstOrderPotential (d := n + 1) (by omega)
          hm hmL hh).boltzmannMeasure =
      (gaussianReal 0 ⟨m⁻¹, inv_nonneg.mpr hm.le⟩).prod
        ((volume : Measure (Fin n → ℝ)).withDensity
          (hardTailDensity n m L h)) := by
  let V := fixedStepHardFirstOrderPotential (d := n + 1) (by omega) hm hmL hh
  let v : NNReal := ⟨m⁻¹, inv_nonneg.mpr hm.le⟩
  have hv : v ≠ 0 := by
    intro hv0
    have hcoe := congrArg (fun r : NNReal => (r : ℝ)) hv0
    change m⁻¹ = 0 at hcoe
    exact (inv_ne_zero hm.ne') hcoe
  rw [gaussianReal_of_var_ne_zero 0 hv]
  rw [prod_withDensity (measurable_gaussianPDF 0 v)
    (measurable_hardTailDensity n m L h)]
  ext s hs
  rw [Measure.map_apply_of_aemeasurable (splitFirst n).measurable.aemeasurable hs]
  rw [FirstOrderPotential.boltzmannMeasure,
    withDensity_apply _ ((splitFirst n).measurable hs)]
  rw [withDensity_apply _ hs]
  let q : ℝ × (Fin n → ℝ) → ℝ≥0∞ := fun p =>
    gaussianPDF 0 v p.1 * hardTailDensity n m L h p.2
  have hpoint (x : State (n + 1)) : V.boltzmannDensity x = q (splitFirst n x) := by
    have h := boltzmannDensity_splitFirst_symm n hn hm hmL hh
      (splitFirst n x).1 (splitFirst n x).2
    rw [(splitFirst n).symm_apply_apply] at h
    exact h
  calc
    (∫⁻ x in splitFirst n ⁻¹' s, V.boltzmannDensity x ∂volume) =
        ∫⁻ x in splitFirst n ⁻¹' s, q (splitFirst n x) ∂volume := by
      apply lintegral_congr
      exact fun x => hpoint x
    _ = ∫⁻ p in s, q p ∂volume :=
      (splitFirst_measurePreserving n).setLIntegral_comp_preimage_emb
        (splitFirst n).measurableEmbedding q s
    _ = ∫⁻ p in s,
        gaussianPDF 0 v p.1 * hardTailDensity n m L h p.2 ∂volume := rfl

/-- The normalized hard target has the exact Gaussian zeroth marginal. -/
theorem fixedStepHardTarget_map_firstCoordinate
    (n : ℕ) (hn : 1 ≤ n) {m L h : ℝ}
    (hm : 0 < m) (hmL : m < L) (hh : 0 < h) :
    Measure.map (fun x : State (n + 1) => x 0)
        ((fixedStepHardFirstOrderPotential (d := n + 1) (by omega)
          hm hmL hh).target : Measure (State (n + 1))) =
      gaussianReal 0 ⟨m⁻¹, inv_nonneg.mpr hm.le⟩ := by
  let V := fixedStepHardFirstOrderPotential (d := n + 1) (by omega) hm hmL hh
  let v : NNReal := ⟨m⁻¹, inv_nonneg.mpr hm.le⟩
  change Measure.map (fun x : State (n + 1) => x 0) V.target =
    gaussianReal 0 v
  let ν : Measure (Fin n → ℝ) :=
    (volume : Measure (Fin n → ℝ)).withDensity (hardTailDensity n m L h)
  have hν0 : ν Set.univ ≠ 0 := by
    simp only [ν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    apply ne_of_gt
    rw [lintegral_pos_iff_support (measurable_hardTailDensity n m L h)]
    have hsupp : Function.support (hardTailDensity n m L h) = Set.univ := by
      ext z
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact (hardTailDensity_pos hm n L h z).ne'
    rw [hsupp]
    exact (Measure.measure_univ_pos
      (μ := (volume : Measure (Fin n → ℝ)))).mpr
        ((Measure.measure_univ_pos
          (μ := (volume : Measure (Fin n → ℝ)))).mp
            (isOpen_univ.measure_pos volume Set.univ_nonempty))
  have hmap := map_boltzmannMeasure_splitFirst n hn hm hmL hh
  change Measure.map (splitFirst n) V.boltzmannMeasure =
    (gaussianReal 0 v).prod ν at hmap
  have hprodUniv : ((gaussianReal 0 v).prod ν) Set.univ = ν Set.univ := by
    rw [← Set.univ_prod_univ, Measure.prod_prod]
    simp
  have hνTop : ν Set.univ ≠ ∞ := by
    have hu := congrArg (fun μ : Measure (ℝ × (Fin n → ℝ)) => μ Set.univ) hmap
    rw [Measure.map_apply_of_aemeasurable
      (splitFirst n).measurable.aemeasurable MeasurableSet.univ] at hu
    rw [hprodUniv] at hu
    have hu' : V.boltzmannMeasure Set.univ = ν Set.univ := hu
    rw [← hu']
    exact (V.isFiniteMeasure_boltzmannMeasure.measure_univ_lt_top).ne
  have hcoordBoltzmann :
      Measure.map (fun x : State (n + 1) => x 0) V.boltzmannMeasure =
        (ν Set.univ) • gaussianReal 0 v := by
    have hcomp : (fun x : State (n + 1) => x 0) =
        Prod.fst ∘ splitFirst n := by
      funext x
      rfl
    rw [hcomp, ← Measure.map_map measurable_fst (splitFirst n).measurable]
    rw [hmap]
    rw [Measure.map_fst_prod]
  have hmass :
      (V.boltzmannFiniteMeasure.mass : ℝ≥0∞) = ν Set.univ := by
    rw [FiniteMeasure.ennreal_mass]
    change V.boltzmannMeasure Set.univ = ν Set.univ
    have hu := congrArg (fun μ : Measure (ℝ × (Fin n → ℝ)) => μ Set.univ) hmap
    rw [Measure.map_apply_of_aemeasurable
      (splitFirst n).measurable.aemeasurable MeasurableSet.univ] at hu
    rw [hprodUniv] at hu
    exact hu
  rw [show (V.target : Measure (State (n + 1))) =
      (V.boltzmannFiniteMeasure.mass⁻¹ : NNReal) • V.boltzmannMeasure by
    exact V.boltzmannFiniteMeasure.toMeasure_normalize_eq_of_nonzero
      V.boltzmannFiniteMeasure_ne_zero]
  rw [Measure.map_smul, hcoordBoltzmann]
  change (V.boltzmannFiniteMeasure.mass⁻¹ : NNReal) •
      ((ν Set.univ) • gaussianReal 0 v) = gaussianReal 0 v
  have hmass0 : V.boltzmannFiniteMeasure.mass ≠ 0 :=
    V.boltzmannFiniteMeasure.mass_nonzero_iff.mpr
      V.boltzmannFiniteMeasure_ne_zero
  ext s hs
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def]
  rw [ENNReal.coe_inv hmass0, hmass, ← mul_assoc,
    ENNReal.inv_mul_cancel hν0 hνTop, one_mul]

/-- Metropolis acceptance can only decrease the Dirichlet energy of the
underlying proposal.  This statement is useful independently of the hard
potential and deliberately allows infinite energies. -/
theorem FirstOrderPotential.energy_malaKernel_le_gaussianDensityProposal
    {d : ℕ} (V : FirstOrderPotential d) (h : ℝ) (hh : 0 < h)
    (f : State d → ℝ) (hf : Measurable f) :
    Dirichlet.energy (V.target : Measure (State d)) (V.malaKernel h hh) f ≤
      Dirichlet.energy (V.target : Measure (State d))
        (V.gaussianDensityProposal h) f := by
  unfold Dirichlet.energy
  refine mul_le_mul le_rfl ?_ (by positivity) (by positivity)
  apply lintegral_mono
  intro x
  let g : State d → ℝ≥0∞ := fun y => ENNReal.ofReal ((f x - f y) ^ 2)
  have hg : Measurable g := by
    exact ENNReal.measurable_ofReal.comp
      ((measurable_const.sub hf).pow_const 2)
  let q := V.gaussianDensityProposal h
  let a := V.malaAcceptance h
  have ha : Measurable (Function.uncurry a) :=
    V.measurable_uncurry_malaAcceptance h
  have hrej : Measurable (Function.uncurry
      (fun x (_y : State d) => 1 - MetropolisHastings.acceptanceMass q a x)) :=
    MetropolisHastings.measurable_rejectionDensity q a ha
  change ∫⁻ y, g y ∂MetropolisHastings.kernel q a x ≤ ∫⁻ y, g y ∂q x
  rw [MetropolisHastings.kernel]
  change ∫⁻ y, g y ∂(MetropolisHastings.accepted q a x +
      MetropolisHastings.rejected q a x) ≤ _
  rw [lintegral_add_measure]
  rw [MetropolisHastings.accepted,
    Kernel.lintegral_withDensity q ha x hg]
  rw [MetropolisHastings.rejected,
    Kernel.lintegral_withDensity
      (Kernel.id : Kernel (State d) (State d)) hrej x hg]
  have hid : (∫⁻ y, (1 - MetropolisHastings.acceptanceMass q a x) * g y
      ∂(Kernel.id : Kernel (State d) (State d)) x) = 0 := by
    rw [Kernel.id_apply]
    simp [g]
  rw [hid, add_zero]
  apply lintegral_mono
  intro y
  calc
    a x y * g y ≤ 1 * g y :=
      mul_le_mul (V.malaAcceptance_le_one h x y) le_rfl (by positivity) (by positivity)
    _ = g y := one_mul _

/-- Exact second moment of an affine function of a centered real Gaussian. -/
theorem integral_sq_affine_gaussianReal_zero
    (v : NNReal) (a b : ℝ) :
    (∫ u, (a + b * u) ^ 2 ∂gaussianReal 0 v) = a ^ 2 + b ^ 2 * (v : ℝ) := by
  have hid2 : Integrable (fun u : ℝ => u ^ 2) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq
  have hid : Integrable (fun u : ℝ => u) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal (μ := 0) (v := v) 1).integrable
      (by norm_num)
  have hsq : (∫ u : ℝ, u ^ 2 ∂gaussianReal 0 v) = (v : ℝ) := by
    have hv := variance_fun_id_gaussianReal (μ := 0) (v := v)
    rw [variance_eq_integral measurable_id'.aemeasurable,
      integral_id_gaussianReal] at hv
    simpa using hv
  have hconst : Integrable (fun _u : ℝ => a ^ 2) (gaussianReal 0 v) :=
    integrable_const _
  have hlin : Integrable (fun u : ℝ => (2 * a * b) * u)
      (gaussianReal 0 v) := hid.const_mul _
  have hquad : Integrable (fun u : ℝ => b ^ 2 * u ^ 2)
      (gaussianReal 0 v) := hid2.const_mul _
  simp_rw [show ∀ u : ℝ,
      (a + b * u) ^ 2 = a ^ 2 + (2 * a * b) * u + b ^ 2 * u ^ 2 by
        intro u; ring]
  change (∫ u, ((fun _u : ℝ => a ^ 2) +
      (fun u : ℝ => (2 * a * b) * u) +
      (fun u : ℝ => b ^ 2 * u ^ 2)) u ∂gaussianReal 0 v) = _
  rw [integral_add' (hconst.add hlin) hquad,
    integral_add' hconst hlin, integral_const, integral_const_mul,
    integral_const_mul, integral_id_gaussianReal, hsq]
  simp only [probReal_univ]
  ring

/-- Extended-nonnegative form of `integral_sq_affine_gaussianReal_zero`. -/
theorem lintegral_ofReal_sq_affine_gaussianReal_zero
    (v : NNReal) (a b : ℝ) :
    (∫⁻ u, ENNReal.ofReal ((a + b * u) ^ 2) ∂gaussianReal 0 v) =
      ENNReal.ofReal (a ^ 2 + b ^ 2 * (v : ℝ)) := by
  have hint : Integrable (fun u : ℝ => (a + b * u) ^ 2)
      (gaussianReal 0 v) := by
    have hL2 : MemLp (fun u : ℝ => a + b * u) 2 (gaussianReal 0 v) :=
      (memLp_const a).add
        ((memLp_id_gaussianReal (μ := 0) (v := v) 2).const_mul b)
    exact hL2.integrable_sq
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun u => sq_nonneg (a + b * u)),
    integral_sq_affine_gaussianReal_zero]

/-- Extended second moment of an affine centered Gaussian, with an added
nonnegative constant. -/
theorem lintegral_ofReal_sq_affine_add_gaussianReal_zero
    (v : NNReal) (a b c : ℝ) (hc : 0 ≤ c) :
    (∫⁻ u, ENNReal.ofReal ((a + b * u) ^ 2 + c) ∂gaussianReal 0 v) =
      ENNReal.ofReal (a ^ 2 + b ^ 2 * (v : ℝ) + c) := by
  simp_rw [ENNReal.ofReal_add (sq_nonneg (a + b * _)) hc]
  rw [lintegral_add_left (by fun_prop),
    lintegral_ofReal_sq_affine_gaussianReal_zero, lintegral_const]
  rw [measure_univ, mul_one,
    ← ENNReal.ofReal_add (by positivity) hc]

/-- The zeroth coordinate of a standard Euclidean Gaussian is standard
one-dimensional Gaussian. -/
theorem stdGaussian_map_firstCoordinate (n : ℕ) :
    Measure.map (fun z : State (n + 1) => z 0) (stdGaussian (State (n + 1))) =
      gaussianReal 0 1 := by
  let p : StrongDual ℝ (State (n + 1)) := EuclideanSpace.proj 0
  have hvar : Var[p; stdGaussian (State (n + 1))] = 1 := by
    have hraw := variance_eval_multivariateGaussian
      (μ := (0 : State (n + 1))) (S := (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))
      Matrix.PosSemidef.one (0 : Fin (n + 1))
    rw [multivariateGaussian_zero_one] at hraw
    exact hraw
  have h := IsGaussian.map_eq_gaussianReal
    (μ := stdGaussian (State (n + 1))) p
  rw [integral_strongDual_stdGaussian, hvar] at h
  simpa [p] using h

/-- Distributional form of the exact first-marginal calculation. -/
theorem fixedStepHardFirstCoordinate_identDistrib
    (n : ℕ) (hn : 1 ≤ n) {m L h : ℝ}
    (hm : 0 < m) (hmL : m < L) (hh : 0 < h) :
    IdentDistrib (fun x : State (n + 1) => x 0) id
      ((fixedStepHardFirstOrderPotential (d := n + 1) (by omega)
        hm hmL hh).target : Measure (State (n + 1)))
      (gaussianReal 0 ⟨m⁻¹, inv_nonneg.mpr hm.le⟩) := by
  refine ⟨(by fun_prop), measurable_id'.aemeasurable, ?_⟩
  rw [fixedStepHardTarget_map_firstCoordinate n hn hm hmL hh]
  simp

/-- The zeroth-coordinate test belongs to the manuscript's `L²` class. -/
theorem fixedStepHardFirstCoordinate_memLp_two
    (n : ℕ) (hn : 1 ≤ n) {m L h : ℝ}
    (hm : 0 < m) (hmL : m < L) (hh : 0 < h) :
    MemLp (fun x : State (n + 1) => x 0) 2
      ((fixedStepHardFirstOrderPotential (d := n + 1) (by omega)
        hm hmL hh).target : Measure (State (n + 1))) := by
  apply (fixedStepHardFirstCoordinate_identDistrib n hn hm hmL hh).memLp_iff.mpr
  simpa only [id_eq] using
    (memLp_id_gaussianReal' (μ := 0)
      (v := ⟨m⁻¹, inv_nonneg.mpr hm.le⟩) (2 : ℝ≥0∞) (by norm_num))

/-- Exact extended variance of the zeroth-coordinate test. -/
theorem fixedStepHardFirstCoordinate_evariance
    (n : ℕ) (hn : 1 ≤ n) {m L h : ℝ}
    (hm : 0 < m) (hmL : m < L) (hh : 0 < h) :
    evariance (fun x : State (n + 1) => x 0)
        ((fixedStepHardFirstOrderPotential (d := n + 1) (by omega)
          hm hmL hh).target : Measure (State (n + 1))) =
      ENNReal.ofReal m⁻¹ := by
  let v : NNReal := ⟨m⁻¹, inv_nonneg.mpr hm.le⟩
  have hid := fixedStepHardFirstCoordinate_identDistrib n hn hm hmL hh
  rw [hid.evariance_eq]
  have hL2 := memLp_id_gaussianReal (μ := 0) (v := v) 2
  rw [← hL2.ofReal_variance_eq, variance_id_gaussianReal]
  rfl

@[simp] theorem fixedStepHardProposalMean_firstCoordinate
    (n : ℕ) (hn : 1 ≤ n) {m L h : ℝ}
    (hm : 0 < m) (hmL : m < L) (hh : 0 < h) (x : State (n + 1)) :
    (fixedStepHardFirstOrderPotential (d := n + 1) (by omega)
      hm hmL hh).proposalMean h x 0 = (1 - h * m) * x 0 := by
  rw [FirstOrderPotential.proposalMean,
    fixedStepHardFirstOrderPotential_gradU (by omega) hm hmL hh]
  simp [hardCoordinateGradient]
  ring

/-- Exact proposal squared increment in the Gaussian coordinate. -/
theorem fixedStepHardProposal_firstCoordinate_sqDiff_lintegral
    (n : ℕ) (hn : 1 ≤ n) {m L h : ℝ}
    (hm : 0 < m) (hmL : m < L) (hh : 0 < h) (x : State (n + 1)) :
    (∫⁻ y, ENNReal.ofReal ((x 0 - y 0) ^ 2)
        ∂(fixedStepHardFirstOrderPotential (d := n + 1) (by omega)
          hm hmL hh).gaussianDensityProposal h x) =
      ENNReal.ofReal ((h * m * x 0) ^ 2 + 2 * h) := by
  let V := fixedStepHardFirstOrderPotential (d := n + 1) (by omega) hm hmL hh
  let F : State (n + 1) → ℝ≥0∞ := fun y =>
    ENNReal.ofReal ((x 0 - y 0) ^ 2)
  have hF : Measurable F := by
    fun_prop
  rw [UniformRandomMALA.DiscreteTime.gaussianDensityProposal_eq_map_stdGaussian
    V hh x]
  rw [lintegral_map hF (by fun_prop)]
  have hmean := fixedStepHardProposalMean_firstCoordinate n hn hm hmL hh x
  change (∫⁻ z : State (n + 1), ENNReal.ofReal
      ((x 0 - ((V.proposalMean h x + Real.sqrt (2 * h) • z) 0)) ^ 2)
      ∂stdGaussian (State (n + 1))) = _
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [hmean]
  have halg (z : State (n + 1)) :
      x 0 - ((1 - h * m) * x 0 + Real.sqrt (2 * h) * z 0) =
        h * m * x 0 + (-Real.sqrt (2 * h)) * z 0 := by ring
  simp_rw [halg]
  calc
    (∫⁻ z : State (n + 1), ENNReal.ofReal
        ((h * m * x 0 + -Real.sqrt (2 * h) * z 0) ^ 2)
        ∂stdGaussian (State (n + 1))) =
        ∫⁻ u : ℝ, ENNReal.ofReal
          ((h * m * x 0 + -Real.sqrt (2 * h) * u) ^ 2)
          ∂Measure.map (fun z : State (n + 1) => z 0)
            (stdGaussian (State (n + 1))) := by
      symm
      rw [lintegral_map (by fun_prop) (by fun_prop)]
    _ = ∫⁻ u : ℝ, ENNReal.ofReal
          ((h * m * x 0 + -Real.sqrt (2 * h) * u) ^ 2)
          ∂gaussianReal 0 1 := by
      rw [stdGaussian_map_firstCoordinate]
    _ = ENNReal.ofReal
          ((h * m * x 0) ^ 2 + (-Real.sqrt (2 * h)) ^ 2 * (1 : ℝ)) := by
      exact lintegral_ofReal_sq_affine_gaussianReal_zero
        1 (h * m * x 0) (-Real.sqrt (2 * h))
    _ = ENNReal.ofReal ((h * m * x 0) ^ 2 + 2 * h) := by
      congr 1
      rw [neg_sq, Real.sq_sqrt (by positivity)]
      ring

/-- Exact proposal contribution to the Dirichlet energy of the first
coordinate, before the conventional factor `1/2`. -/
theorem fixedStepHardProposal_firstCoordinate_doubleEnergy
    (n : ℕ) (hn : 1 ≤ n) {m L h : ℝ}
    (hm : 0 < m) (hmL : m < L) (hh : 0 < h) :
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal ((x 0 - y 0) ^ 2)
        ∂(fixedStepHardFirstOrderPotential (d := n + 1) (by omega)
          hm hmL hh).gaussianDensityProposal h x
        ∂(fixedStepHardFirstOrderPotential (d := n + 1) (by omega)
          hm hmL hh).target) =
      ENNReal.ofReal (m * h ^ 2 + 2 * h) := by
  let V := fixedStepHardFirstOrderPotential (d := n + 1) (by omega) hm hmL hh
  simp_rw [fixedStepHardProposal_firstCoordinate_sqDiff_lintegral
    n hn hm hmL hh]
  let G : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal ((h * m * u) ^ 2 + 2 * h)
  calc
    (∫⁻ x : State (n + 1), ENNReal.ofReal ((h * m * x 0) ^ 2 + 2 * h)
        ∂V.target) =
        ∫⁻ u : ℝ, G u ∂Measure.map (fun x : State (n + 1) => x 0) V.target := by
      symm
      rw [lintegral_map (by fun_prop) (by fun_prop)]
    _ = ∫⁻ u : ℝ, G u ∂gaussianReal 0
          (NNReal.mk m⁻¹ (inv_nonneg.mpr hm.le)) := by
      rw [fixedStepHardTarget_map_firstCoordinate n hn hm hmL hh]
      congr 2
    _ = ENNReal.ofReal
          (0 ^ 2 + (h * m) ^ 2 *
            ((NNReal.mk m⁻¹ (inv_nonneg.mpr hm.le) : NNReal) : ℝ) + 2 * h) := by
      dsimp [G]
      convert lintegral_ofReal_sq_affine_add_gaussianReal_zero
        (NNReal.mk m⁻¹ (inv_nonneg.mpr hm.le)) 0 (h * m) (2 * h) (by positivity) using 1 <;>
        simp
    _ = ENNReal.ofReal (m * h ^ 2 + 2 * h) := by
      congr 1
      rw [NNReal.coe_mk]
      field_simp [hm.ne']
      ring

/-- Exact Gaussian-proposal energy of the first-coordinate test. -/
theorem fixedStepHardFirstCoordinate_gaussianProposal_energy
    (n : ℕ) (hn : 1 ≤ n) {m L h : ℝ}
    (hm : 0 < m) (hmL : m < L) (hh : 0 < h) :
    Dirichlet.energy
        ((fixedStepHardFirstOrderPotential (d := n + 1) (by omega)
          hm hmL hh).target : Measure (State (n + 1)))
        ((fixedStepHardFirstOrderPotential (d := n + 1) (by omega)
          hm hmL hh).gaussianDensityProposal h)
        (fun x : State (n + 1) => x 0) =
      ENNReal.ofReal (h + m * h ^ 2 / 2) := by
  rw [Dirichlet.energy,
    fixedStepHardProposal_firstCoordinate_doubleEnergy n hn hm hmL hh]
  have htwo : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
  rw [htwo]
  rw [← ENNReal.ofReal_inv_of_pos (show (0 : ℝ) < 2 by norm_num),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- Metropolis correction cannot increase the exact first-coordinate
proposal energy. -/
theorem fixedStepHardFirstCoordinate_mala_energy_le
    (n : ℕ) (hn : 1 ≤ n) {m L h : ℝ}
    (hm : 0 < m) (hmL : m < L) (hh : 0 < h) :
    Dirichlet.energy
        ((fixedStepHardFirstOrderPotential (d := n + 1) (by omega)
          hm hmL hh).target : Measure (State (n + 1)))
        ((fixedStepHardFirstOrderPotential (d := n + 1) (by omega)
          hm hmL hh).malaKernel h hh)
        (fun x : State (n + 1) => x 0) ≤
      ENNReal.ofReal (h + m * h ^ 2 / 2) := by
  let V := fixedStepHardFirstOrderPotential (d := n + 1) (by omega) hm hmL hh
  calc
    Dirichlet.energy (V.target : Measure (State (n + 1)))
        (V.malaKernel h hh) (fun x : State (n + 1) => x 0) ≤
        Dirichlet.energy (V.target : Measure (State (n + 1)))
          (V.gaussianDensityProposal h) (fun x : State (n + 1) => x 0) :=
      V.energy_malaKernel_le_gaussianDensityProposal h hh _ (by fun_prop)
    _ = ENNReal.ofReal (h + m * h ^ 2 / 2) :=
      fixedStepHardFirstCoordinate_gaussianProposal_energy n hn hm hmL hh

/-- Local test-function branch of the fixed-step obstruction.  The first
coordinate is exactly `N(0,m⁻¹)`, while Metropolis acceptance can only
decrease its proposal energy. -/
theorem fixedStepHardMALA_rayleighSpectralGap_le_local_succ
    (n : ℕ) (hn : 1 ≤ n) {m L h : ℝ}
    (hm : 0 < m) (hmL : m < L) (hh : 0 < h) :
    rayleighSpectralGap
        ((fixedStepHardFirstOrderPotential (d := n + 1) (by omega)
          hm hmL hh).target : Measure (State (n + 1)))
        ((fixedStepHardFirstOrderPotential (d := n + 1) (by omega)
          hm hmL hh).malaKernel h hh) ≤
      ENNReal.ofReal (m * h + (m * h) ^ 2 / 2) := by
  let V := fixedStepHardFirstOrderPotential (d := n + 1) (by omega) hm hmL hh
  let f : State (n + 1) → ℝ := fun x => x 0
  have hf : Measurable f := by fun_prop
  have hL2 : MemLp f 2 (V.target : Measure (State (n + 1))) :=
    fixedStepHardFirstCoordinate_memLp_two n hn hm hmL hh
  have hvar : evariance f (V.target : Measure (State (n + 1))) ≠ 0 := by
    rw [fixedStepHardFirstCoordinate_evariance n hn hm hmL hh]
    exact ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr hm)
  have htest := rayleighSpectralGap_le_energy_div_evariance
    (π := (V.target : Measure (State (n + 1)))) (V.malaKernel h hh)
    f hf hL2 hvar
  rw [fixedStepHardFirstCoordinate_evariance n hn hm hmL hh] at htest
  calc
    rayleighSpectralGap (V.target : Measure (State (n + 1)))
        (V.malaKernel h hh) ≤
        Dirichlet.energy (V.target : Measure (State (n + 1)))
          (V.malaKernel h hh) f / ENNReal.ofReal m⁻¹ := htest
    _ ≤ ENNReal.ofReal (h + m * h ^ 2 / 2) / ENNReal.ofReal m⁻¹ :=
      ENNReal.div_le_div_right
        (fixedStepHardFirstCoordinate_mala_energy_le n hn hm hmL hh)
        (ENNReal.ofReal m⁻¹)
    _ = ENNReal.ofReal ((h + m * h ^ 2 / 2) / m⁻¹) := by
      rw [ENNReal.ofReal_div_of_pos (inv_pos.mpr hm)]
    _ = ENNReal.ofReal (m * h + (m * h) ^ 2 / 2) := by
      congr 1
      field_simp [hm.ne']

/-- Dimension-indexed form of the local fixed-step obstruction, matching
the hard witness's natural hypothesis `2 ≤ d`. -/
theorem fixedStepHardMALA_rayleighSpectralGap_le_local
    {d : ℕ} (hd : 2 ≤ d) {m L h : ℝ}
    (hm : 0 < m) (hmL : m < L) (hh : 0 < h) :
    rayleighSpectralGap
        ((fixedStepHardFirstOrderPotential (d := d) hd hm hmL hh).target :
          Measure (State d))
        ((fixedStepHardFirstOrderPotential (d := d) hd hm hmL hh).malaKernel h hh) ≤
      ENNReal.ofReal (m * h + (m * h) ^ 2 / 2) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  exact fixedStepHardMALA_rayleighSpectralGap_le_local_succ
    n (by omega) hm hmL hh

end

end UniformRandomMALA.Concrete
