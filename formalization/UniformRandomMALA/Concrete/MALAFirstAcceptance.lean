import UniformRandomMALA.Concrete.MALAFamily
import UniformRandomMALA.Concrete.LazyKernel

/-!
# Acceptance and absolute continuity from every starting state

A MALA acceptance has positive probability from every state, and its
destination law is absolutely continuous with respect to the target.
These facts are ingredients of the arbitrary-start CLT transfer. They
do not by themselves assert Gaussian convergence.
-/

namespace UniformRandomMALA.Concrete.FirstOrderPotential

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
noncomputable section
variable {d : ℕ} (V : FirstOrderPotential d)

theorem volume_absolutelyContinuous_target :
    (volume : Measure (State d)) ≪ (V.target : Measure (State d)) := by
  rw [V.target_toMeasure_eq_withDensity]
  exact withDensity_absolutelyContinuous' V.measurable_targetDensity.aemeasurable
    (ae_of_all _ fun x => (V.targetDensity_pos x).ne')

theorem malaAcceptance_pos {h : ℝ} (hh : 0 < h) (x y : State d) :
    0 < V.malaAcceptance h x y := by
  unfold malaAcceptance MetropolisHastings.acceptance
  exact lt_min (ENNReal.div_pos (V.malaEdgeDensity_ne_zero hh y x)
    (V.malaEdgeDensity_ne_top h x y)) zero_lt_one

theorem malaFamilyAcceptance_pos (p : ℝ × State d) (y : State d) :
    0 < V.malaFamilyAcceptance p y :=
  V.malaAcceptance_pos (effectiveStep_pos p.1) p.2 y

theorem malaFamilyAcceptanceMass_pos (p : ℝ × State d) :
    0 < V.malaFamilyAcceptanceMass p := by
  apply bot_lt_iff_ne_bot.mpr
  intro hzero
  have heq := (lintegral_eq_zero_iff
    (V.measurable_uncurry_malaFamilyAcceptance.comp
      (measurable_const.prodMk measurable_id))).mp hzero
  obtain ⟨y, hy⟩ := heq.exists
  exact (V.malaFamilyAcceptance_pos p y).ne' hy

instance malaAcceptedKernelFamily_isSFiniteKernel : IsSFiniteKernel V.malaAcceptedKernelFamily := by
  unfold malaAcceptedKernelFamily
  exact Kernel.IsSFiniteKernel.withDensity _ (fun p y =>
    (lt_of_le_of_lt (V.malaFamilyAcceptance_le_one p y) (by simp : (1 : ℝ≥0∞) < ∞)).ne)

theorem malaAcceptedKernelFamily_absolutelyContinuous_target (p : ℝ × State d) :
    V.malaAcceptedKernelFamily p ≪ (V.target : Measure (State d)) := by
  rw [malaAcceptedKernelFamily, Kernel.withDensity_apply _
    V.measurable_uncurry_malaFamilyAcceptance p]
  apply (withDensity_absolutelyContinuous _ _).trans
  rw [gaussianProposalKernelFamily, Kernel.withDensity_apply _
    V.measurable_uncurry_proposalFamilyDensity p]
  exact (withDensity_absolutelyContinuous _ _).trans V.volume_absolutelyContinuous_target

/-- Accepted part of the actual uniformly randomized MALA transition. -/
def uniformMALAAccepted (H : ℝ) : Kernel (State d) (State d) :=
  UniformRandomMALA.Kernel.parameterMixture (uniformStepMeasure H) V.malaAcceptedKernelFamily

theorem uniformMALAAccepted_absolutelyContinuous_target (H : ℝ) (hH : 0 < H)
    (x : State d) : V.uniformMALAAccepted H x ≪ (V.target : Measure (State d)) := by
  let : IsProbabilityMeasure (uniformStepMeasure H) := uniformStepMeasure_isProbabilityMeasure H hH
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hnull
  rw [uniformMALAAccepted, UniformRandomMALA.Kernel.parameterMixture_apply _ _ _ _ hs]
  simp only [show (fun h : ℝ => V.malaAcceptedKernelFamily (h, x) s) = fun _ => 0 from
    funext fun h => V.malaAcceptedKernelFamily_absolutelyContinuous_target (h, x) hnull,
    lintegral_zero]

theorem uniformMALAAccepted_mass_pos (H : ℝ) (hH : 0 < H) (x : State d) :
    0 < V.uniformMALAAccepted H x Set.univ := by
  let : IsProbabilityMeasure (uniformStepMeasure H) := uniformStepMeasure_isProbabilityMeasure H hH
  rw [uniformMALAAccepted, UniformRandomMALA.Kernel.parameterMixture_apply _ _ _ _ MeasurableSet.univ]
  simp_rw [V.malaAcceptedKernelFamily_apply_univ]
  apply bot_lt_iff_ne_bot.mpr
  intro hzero
  have heq := (lintegral_eq_zero_iff
    (V.measurable_malaFamilyAcceptanceMass.comp (measurable_id.prodMk measurable_const))).mp hzero
  obtain ⟨h, hh⟩ := heq.exists
  exact (V.malaFamilyAcceptanceMass_pos (h, x)).ne' hh

instance malaRejectedKernelFamily_isSFiniteKernel : IsSFiniteKernel V.malaRejectedKernelFamily := by
  unfold malaRejectedKernelFamily
  apply Kernel.IsSFiniteKernel.withDensity
  intro p y
  exact (lt_of_le_of_lt tsub_le_self (by simp : (1 : ℝ≥0∞) < ∞)).ne

theorem malaRejectedKernelFamily_eq_smul_dirac (p : ℝ × State d) :
    V.malaRejectedKernelFamily p = (1 - V.malaFamilyAcceptanceMass p) • Measure.dirac p.2 := by
  rw [malaRejectedKernelFamily, Kernel.withDensity_apply _
    V.measurable_uncurry_malaRejectionDensity p,
    malaStayKernelFamily, Kernel.deterministic_apply, withDensity_const]

/-- The actual probability of staying put by rejection, averaged over the
uniform step. The Gaussian accepted part has no atoms. -/
def uniformMALARejectionWeight (H : ℝ) (x : State d) : ℝ≥0∞ :=
  ∫⁻ h, 1 - V.malaFamilyAcceptanceMass (h, x) ∂uniformStepMeasure H

theorem measurable_uniformMALARejectionWeight (H : ℝ) (hH : 0 < H) :
    Measurable (V.uniformMALARejectionWeight H) := by
  let : IsProbabilityMeasure (uniformStepMeasure H) := uniformStepMeasure_isProbabilityMeasure H hH
  have hm : Measurable (fun p : State d × ℝ => 1 - V.malaFamilyAcceptanceMass (p.2, p.1)) :=
    measurable_const.sub (V.measurable_malaFamilyAcceptanceMass.comp measurable_swap)
  exact hm.lintegral_prod_right

theorem uniformMALARejectionWeight_le_one (H : ℝ) (hH : 0 < H) (x : State d) :
    V.uniformMALARejectionWeight H x ≤ 1 := by
  let : IsProbabilityMeasure (uniformStepMeasure H) := uniformStepMeasure_isProbabilityMeasure H hH
  calc
    _ ≤ ∫⁻ _h, (1 : ℝ≥0∞) ∂uniformStepMeasure H := lintegral_mono fun _ => tsub_le_self
    _ = 1 := by simp

/-- Exact accepted-plus-rejection decomposition of the concrete uniform
MALA transition from every starting point. -/
theorem uniformMALA_eq_accepted_add_rejection (H : ℝ) (hH : 0 < H) (x : State d) :
    V.uniformMALA H hH x = V.uniformMALAAccepted H x +
      V.uniformMALARejectionWeight H x • Measure.dirac x := by
  let : IsProbabilityMeasure (uniformStepMeasure H) := uniformStepMeasure_isProbabilityMeasure H hH
  ext s hs
  rw [uniformMALA, UniformRandomMALA.Kernel.parameterMixture_apply _ _ _ _ hs,
    Measure.add_apply, uniformMALAAccepted,
    UniformRandomMALA.Kernel.parameterMixture_apply _ _ _ _ hs]
  simp_rw [malaKernelFamily, add_apply, Measure.add_apply]
  have hm : Measurable (fun h : ℝ => V.malaAcceptedKernelFamily (h, x) s) :=
    (V.malaAcceptedKernelFamily.measurable_coe hs).comp
      (measurable_id.prodMk measurable_const)
  rw [lintegral_add_left hm]
  congr 1
  simp_rw [V.malaRejectedKernelFamily_eq_smul_dirac, Measure.smul_apply,
    smul_eq_mul, Measure.dirac_apply' _ hs]
  by_cases hx : x ∈ s <;> simp [hx, uniformMALARejectionWeight]

theorem uniformMALARejectionWeight_lt_one (H : ℝ) (hH : 0 < H) (x : State d) :
    V.uniformMALARejectionWeight H x < 1 := by
  let : IsMarkovKernel (V.uniformMALA H hH) := V.uniformMALA_isMarkovKernel H hH
  have hmass := congrArg (fun μ : Measure (State d) => μ Set.univ)
    (V.uniformMALA_eq_accepted_add_rejection H hH x)
  simp only [measure_univ, Measure.add_apply, Measure.smul_apply,
    smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_univ x), mul_one] at hmass
  have hfinite := (lt_of_le_of_lt (V.uniformMALARejectionWeight_le_one H hH x)
    (by simp : (1 : ℝ≥0∞) < ∞)).ne
  have h := ENNReal.lt_add_right hfinite (V.uniformMALAAccepted_mass_pos H hH x).ne'
  have hmass' : V.uniformMALAAccepted H x Set.univ + V.uniformMALARejectionWeight H x = 1 := by
    simpa using hmass.symm
  exact h.trans_eq (by rw [add_comm]; exact hmass')

/-- Accepted part of the half-lazy transition. -/
def lazyUniformMALAAccepted (H : ℝ) : Kernel (State d) (State d) where
  toFun x := (2 : ℝ≥0∞)⁻¹ • V.uniformMALAAccepted H x
  measurable' := Measure.measurable_of_measurable_coe _ fun _s hs =>
    measurable_const.mul ((V.uniformMALAAccepted H).measurable_coe hs)

def lazyUniformMALARejectionWeight (H : ℝ) (x : State d) : ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ * (1 + V.uniformMALARejectionWeight H x)

theorem measurable_lazyUniformMALARejectionWeight (H : ℝ) (hH : 0 < H) :
    Measurable (V.lazyUniformMALARejectionWeight H) :=
  measurable_const.mul (measurable_const.add (V.measurable_uniformMALARejectionWeight H hH))

theorem lazyUniformMALAAccepted_absolutelyContinuous_target (H : ℝ) (hH : 0 < H)
    (x : State d) : V.lazyUniformMALAAccepted H x ≪ (V.target : Measure (State d)) :=
  (V.uniformMALAAccepted_absolutelyContinuous_target H hH x).smul_left _

theorem lazyUniformMALA_eq_accepted_add_rejection (H : ℝ) (hH : 0 < H) (x : State d) :
    V.lazyUniformMALA H hH x = V.lazyUniformMALAAccepted H x +
      V.lazyUniformMALARejectionWeight H x • Measure.dirac x := by
  let : IsMarkovKernel (V.uniformMALA H hH) := V.uniformMALA_isMarkovKernel H hH
  ext s hs
  rw [lazyUniformMALA, halfLazyKernel_apply _ _ _ hs,
    V.uniformMALA_eq_accepted_add_rejection H hH x]
  change (2 : ℝ≥0∞)⁻¹ * (Measure.dirac x s +
    (V.uniformMALAAccepted H x + V.uniformMALARejectionWeight H x • Measure.dirac x) s) =
    ((2 : ℝ≥0∞)⁻¹ • V.uniformMALAAccepted H x +
      V.lazyUniformMALARejectionWeight H x • Measure.dirac x) s
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    lazyUniformMALARejectionWeight]
  ring

theorem lazyUniformMALARejectionWeight_lt_one (H : ℝ) (hH : 0 < H) (x : State d) :
    V.lazyUniformMALARejectionWeight H x < 1 := by
  have h := ENNReal.mul_lt_mul_right (a := (2 : ℝ≥0∞)⁻¹) (by norm_num) (by norm_num)
    (ENNReal.add_lt_add_left ENNReal.one_ne_top (V.uniformMALARejectionWeight_lt_one H hH x))
  simpa only [lazyUniformMALARejectionWeight, show (1 + 1 : ℝ≥0∞) = 2 from by norm_num,
    ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)] using h

end
end UniformRandomMALA.Concrete.FirstOrderPotential
