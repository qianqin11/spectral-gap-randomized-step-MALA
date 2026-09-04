import UniformRandomMALA.Concrete.MALARejectionGoodSet
import UniformRandomMALA.Concrete.MALASetwiseTV

/-!
# Conditional local overlap for dyadically randomized MALA

This file contains the elementary assembly step in the local part of
Proposition 3.2.  The only analytic input is a uniform fixed-step moment
bound for the rejection probability.  Jensen--Markov supplies a good set on
which the *averaged* rejection is at most `1/3`; the remaining argument is the
accept/reject triangle inequality and the `1/32` Gaussian proposal bound.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace Concrete
namespace FirstOrderPotential

variable {d : ℕ} (V : FirstOrderPotential d)

/-- If the dyadically averaged rejection probabilities at two points are at
most `1/3`, then their randomized MALA kernels differ by at most `67/96` on
every measurable set. -/
theorem abs_dyadicMALA_apply_toReal_sub_le_sixty_seven_div_ninety_six
    {t : ℝ} (ht : 0 < t) (htL : t ≤ 2 / V.L)
    (x y : State d) (hxy : ‖x - y‖ ≤ Real.sqrt t / 16)
    (hxrej : (∫ h, V.malaRejectionMassReal h x ∂dyadicStepMeasure t) ≤ 1 / 3)
    (hyrej : (∫ h, V.malaRejectionMassReal h y ∂dyadicStepMeasure t) ≤ 1 / 3)
    {B : Set (State d)} (hB : MeasurableSet B) :
    |(V.dyadicMALA t ht x B).toReal - (V.dyadicMALA t ht y B).toReal| ≤
      67 / 96 := by
  let ν : Measure ℝ := dyadicStepMeasure t
  let K := V.malaKernelFamily
  let fx : ℝ → ℝ := fun h => (K (h, x) B).toReal
  let fy : ℝ → ℝ := fun h => (K (h, y) B).toReal
  let rx : ℝ → ℝ := fun h => V.malaRejectionMassReal h x
  let ry : ℝ → ℝ := fun h => V.malaRejectionMassReal h y
  letI : IsProbabilityMeasure ν := dyadicStepMeasure_isProbabilityMeasure ht
  letI : IsMarkovKernel (V.dyadicMALA t ht) :=
    V.dyadicMALA_isMarkovKernel t ht
  have hmem : ∀ᵐ h ∂ν, h ∈ Set.Ioc (t / 2) t := by
    change ∀ᵐ h ∂(volume : Measure ℝ)[|Set.Ioc (t / 2) t],
      h ∈ Set.Ioc (t / 2) t
    exact ProbabilityTheory.ae_cond_mem measurableSet_Ioc
  have hfxMeas : Measurable fx := by
    exact ENNReal.measurable_toReal.comp ((K.measurable_coe hB).comp
      (measurable_id.prodMk measurable_const))
  have hfyMeas : Measurable fy := by
    exact ENNReal.measurable_toReal.comp ((K.measurable_coe hB).comp
      (measurable_id.prodMk measurable_const))
  have hfxBound : ∀ h, ‖fx h‖ ≤ 1 := by
    intro h
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    have hle : K (h, x) B ≤ 1 := by
      calc
        K (h, x) B ≤ K (h, x) Set.univ := measure_mono (Set.subset_univ B)
        _ = 1 := by simp
    exact ENNReal.toReal_mono ENNReal.one_ne_top hle
  have hfyBound : ∀ h, ‖fy h‖ ≤ 1 := by
    intro h
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    have hle : K (h, y) B ≤ 1 := by
      calc
        K (h, y) B ≤ K (h, y) Set.univ := measure_mono (Set.subset_univ B)
        _ = 1 := by simp
    exact ENNReal.toReal_mono ENNReal.one_ne_top hle
  have hfxInt : Integrable fx ν :=
    Integrable.of_bound hfxMeas.aestronglyMeasurable 1 (ae_of_all _ hfxBound)
  have hfyInt : Integrable fy ν :=
    Integrable.of_bound hfyMeas.aestronglyMeasurable 1 (ae_of_all _ hfyBound)
  have hrxMeas : Measurable rx := by
    exact V.measurable_uncurry_malaRejectionMassReal.comp
      (measurable_id.prodMk measurable_const)
  have hryMeas : Measurable ry := by
    exact V.measurable_uncurry_malaRejectionMassReal.comp
      (measurable_id.prodMk measurable_const)
  have hrxInt : Integrable rx ν := by
    apply Integrable.of_bound hrxMeas.aestronglyMeasurable 1
    exact ae_of_all _ fun h => by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (V.malaRejectionMassReal_nonneg h x)]
      exact V.malaRejectionMassReal_le_one h x
  have hryInt : Integrable ry ν := by
    apply Integrable.of_bound hryMeas.aestronglyMeasurable 1
    exact ae_of_all _ fun h => by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (V.malaRejectionMassReal_nonneg h y)]
      exact V.malaRejectionMassReal_le_one h y
  have hpoint : ∀ᵐ h ∂ν,
      |fx h - fy h| ≤ rx h + 1 / 32 + ry h := by
    filter_upwards [hmem] with h hhmem
    have hh : 0 < h := lt_of_lt_of_le (by linarith [ht]) hhmem.1.le
    have hh2L : h ≤ 2 / V.L := hhmem.2.trans htL
    have hxsect := congrArg (fun κ : Kernel (State d) (State d) => κ x B)
      (V.sectR_malaKernelFamily h)
    have hysect := congrArg (fun κ : Kernel (State d) (State d) => κ y B)
      (V.sectR_malaKernelFamily h)
    simp only [Kernel.sectR_apply, effectiveStep_of_pos hh] at hxsect hysect
    have hxacc : |fx h - (V.gaussianDensityProposal h x B).toReal| ≤ rx h := by
      rw [show fx h = (V.malaKernel h hh x B).toReal by
        exact congrArg ENNReal.toReal hxsect]
      rw [show rx h = (1 - MetropolisHastings.acceptanceMass
          (V.gaussianDensityProposal h) (V.malaAcceptance h) x).toReal by
        exact V.malaRejectionMassReal_eq_fixed hh x]
      exact V.abs_malaKernel_apply_toReal_sub_gaussianProposal_le_rejection
        hh x hB
    have hyacc : |(V.gaussianDensityProposal h y B).toReal - fy h| ≤ ry h := by
      rw [abs_sub_comm]
      rw [show fy h = (V.malaKernel h hh y B).toReal by
        exact congrArg ENNReal.toReal hysect]
      rw [show ry h = (1 - MetropolisHastings.acceptanceMass
          (V.gaussianDensityProposal h) (V.malaAcceptance h) y).toReal by
        exact V.malaRejectionMassReal_eq_fixed hh y]
      exact V.abs_malaKernel_apply_toReal_sub_gaussianProposal_le_rejection
        hh y hB
    have hproposal :
        |(V.gaussianDensityProposal h x B).toReal -
          (V.gaussianDensityProposal h y B).toReal| ≤ 1 / 32 :=
      V.abs_gaussianDensityProposal_apply_toReal_sub_le_one_div_32
        ht hh hhmem.1.le hh2L x y hxy hB
    calc
      |fx h - fy h| ≤
          |fx h - (V.gaussianDensityProposal h x B).toReal| +
            |(V.gaussianDensityProposal h x B).toReal - fy h| :=
        abs_sub_le _ _ _
      _ ≤ |fx h - (V.gaussianDensityProposal h x B).toReal| +
          (|(V.gaussianDensityProposal h x B).toReal -
              (V.gaussianDensityProposal h y B).toReal| +
            |(V.gaussianDensityProposal h y B).toReal - fy h|) := by
        gcongr
        exact abs_sub_le _ _ _
      _ ≤ rx h + (1 / 32 + ry h) := by gcongr
      _ = rx h + 1 / 32 + ry h := by ring
  have hKx : V.dyadicMALA t ht x B = ∫⁻ h, K (h, x) B ∂ν := by
    rw [dyadicMALA, Kernel.parameterMixture_apply _ _ _ _ hB]
  have hKy : V.dyadicMALA t ht y B = ∫⁻ h, K (h, y) B ∂ν := by
    rw [dyadicMALA, Kernel.parameterMixture_apply _ _ _ _ hB]
  have hKxReal : (V.dyadicMALA t ht x B).toReal = ∫ h, fx h ∂ν := by
    rw [hKx]
    exact (integral_toReal
      (((K.measurable_coe hB).comp
        (measurable_id.prodMk measurable_const)).aemeasurable)
      (ae_of_all _ fun h => (measure_lt_top (K (h, x)) B))).symm
  have hKyReal : (V.dyadicMALA t ht y B).toReal = ∫ h, fy h ∂ν := by
    rw [hKy]
    exact (integral_toReal
      (((K.measurable_coe hB).comp
        (measurable_id.prodMk measurable_const)).aemeasurable)
      (ae_of_all _ fun h => (measure_lt_top (K (h, y)) B))).symm
  have hdomInt : Integrable (fun h => rx h + 1 / 32 + ry h) ν := by
    fun_prop
  calc
    |(V.dyadicMALA t ht x B).toReal - (V.dyadicMALA t ht y B).toReal| =
        |(∫ h, fx h ∂ν) - ∫ h, fy h ∂ν| := by rw [hKxReal, hKyReal]
    _ = |∫ h, fx h - fy h ∂ν| := by rw [integral_sub hfxInt hfyInt]
    _ ≤ ∫ h, |fx h - fy h| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ h, (rx h + 1 / 32 + ry h) ∂ν := by
      exact integral_mono_ae (hfxInt.sub hfyInt).abs hdomInt hpoint
    _ = (∫ h, (rx h + 1 / 32) ∂ν) + ∫ h, ry h ∂ν :=
      integral_add (hrxInt.add (integrable_const _)) hryInt
    _ = ((∫ h, rx h ∂ν) + ∫ _h, (1 / 32 : ℝ) ∂ν) +
          ∫ h, ry h ∂ν := by
      rw [integral_add hrxInt (integrable_const _)]
    _ = (∫ h, rx h ∂ν) + 1 / 32 + ∫ h, ry h ∂ν := by simp
    _ ≤ 1 / 3 + 1 / 32 + 1 / 3 := by
      dsimp [ν, rx, ry] at hxrej hyrej ⊢
      gcongr
    _ = 67 / 96 := by norm_num

/-- Conditional local clause of Proposition 3.2.  The good set is produced
from a uniform fixed-step rejection `p`-moment bound. -/
theorem exists_dyadicMALALocalOverlap_goodSet
    {t p C : ℝ} (ht : 0 < t) (htL : t ≤ 2 / V.L)
    (hp : 1 ≤ p) (hC : 0 ≤ C)
    (hmoment : ∀ h ∈ Set.Ioc (t / 2) t,
      (∫ x : State d,
        ((1 - MetropolisHastings.acceptanceMass
          (V.gaussianDensityProposal h) (V.malaAcceptance h) x).toReal) ^ p
          ∂(V.target : Measure (State d))) ≤ C ^ p) :
    ∃ G : Set (State d),
      MeasurableSet G ∧
      (V.target : Measure (State d)) Gᶜ ≤
        ENNReal.ofReal ((3 * C) ^ p) ∧
      ∀ x ∈ G, ∀ y ∈ G, ‖x - y‖ ≤ Real.sqrt t / 16 →
        setwiseTV (V.dyadicMALA t ht x) (V.dyadicMALA t ht y) ≤ 3 / 4 := by
  obtain ⟨G, hG, hGmass, hgood⟩ :=
    V.exists_dyadicMALARejection_goodSet_one_third ht hp hC hmoment
  refine ⟨G, hG, hGmass, ?_⟩
  intro x hx y hy hxy
  apply setwiseTV_le_of_forall
  intro B hB
  have hstrong :=
    V.abs_dyadicMALA_apply_toReal_sub_le_sixty_seven_div_ninety_six
      ht htL x y hxy (hgood x hx) (hgood y hy) hB
  have hconst : (67 : ℝ) / 96 ≤ 3 / 4 := by norm_num
  simpa [Measure.real_def] using hstrong.trans hconst

end FirstOrderPotential
end Concrete

end
end UniformRandomMALA
