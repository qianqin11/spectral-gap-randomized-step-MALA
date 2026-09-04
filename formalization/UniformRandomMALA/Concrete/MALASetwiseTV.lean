import UniformRandomMALA.DiscreteTime.SetwiseAcceptReject
import UniformRandomMALA.Concrete.GaussianProposalTV
import UniformRandomMALA.Concrete.SafeAcceptance
import UniformRandomMALA.Concrete.MALAFamily

/-!
# Setwise MALA comparison without signed measures

The fixed-step overlap argument is assembled from three elementary setwise
terms: rejection at the first point, equal-covariance Gaussian proposal
discrepancy, and rejection at the second point.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace Concrete
namespace FirstOrderPotential

variable {d : ℕ} (V : FirstOrderPotential d)

/-- A MALA transition differs from its Gaussian proposal on every measurable
set by at most its one-step rejection probability. -/
theorem abs_malaKernel_apply_toReal_sub_gaussianProposal_le_rejection
    {h : ℝ} (hh : 0 < h) (x : State d)
    {B : Set (State d)} (hB : MeasurableSet B) :
    |(V.malaKernel h hh x B).toReal -
        (V.gaussianDensityProposal h x B).toReal| ≤
      (1 - MetropolisHastings.acceptanceMass
        (V.gaussianDensityProposal h) (V.malaAcceptance h) x).toReal := by
  letI : Fact (0 < h) := ⟨hh⟩
  change |(MetropolisHastings.kernel
      (V.gaussianDensityProposal h) (V.malaAcceptance h) x B).toReal -
        (V.gaussianDensityProposal h x B).toReal| ≤ _
  exact DiscreteTime.abs_metropolisKernel_apply_toReal_sub_proposal_le_rejection
    (V.gaussianDensityProposal h) (V.malaAcceptance h)
    (V.measurable_uncurry_malaAcceptance h)
    (V.malaAcceptance_le_one h) x B hB

/-- The safe-acceptance estimate implies a linear rejection bound. -/
theorem malaRejectionMass_toReal_le
    {h : ℝ} (hh : 0 < h) (hhL : h ≤ 1 / V.L) (x : State d) :
    (1 - MetropolisHastings.acceptanceMass
      (V.gaussianDensityProposal h) (V.malaAcceptance h) x).toReal ≤
        V.L * h * (d : ℝ) / 2 := by
  letI : Fact (0 < h) := ⟨hh⟩
  let A := MetropolisHastings.acceptanceMass
    (V.gaussianDensityProposal h) (V.malaAcceptance h) x
  let u := V.L * h * (d : ℝ) / 2
  have hA1 : A ≤ 1 :=
    MetropolisHastings.acceptanceMass_le_one
      (V.gaussianDensityProposal h) (V.malaAcceptance h)
      (V.malaAcceptance_le_one h) x
  have hAfin : A ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hA1
  have hlow : ENNReal.ofReal (Real.exp (-u)) ≤ A := by
    simpa [A, u] using V.malaAcceptanceMass_ge_exp hh hhL x
  have hlowReal : Real.exp (-u) ≤ A.toReal := by
    have := ENNReal.toReal_mono hAfin hlow
    simpa [Real.exp_nonneg] using this
  have hexp : -u + 1 ≤ Real.exp (-u) := Real.add_one_le_exp (-u)
  rw [ENNReal.toReal_sub_of_le hA1 ENNReal.one_ne_top]
  change 1 - A.toReal ≤ u
  linarith

/-- Fixed-step, paper-ready global overlap estimate.  This is the elementary
core of the global clause of Proposition 3.2; averaging over an interval of
steps is a subsequent scalar integration step. -/
theorem abs_malaKernel_apply_toReal_sub_le_seventeen_div_32
    {t h : ℝ} (ht : 0 < t) (hh : 0 < h) (hhalf : t / 2 ≤ h)
    (hsmall : h ≤ 1 / (2 * V.L * (d : ℝ)))
    (x y : State d) (hxy : ‖x - y‖ ≤ Real.sqrt t / 16)
    {B : Set (State d)} (hB : MeasurableSet B) :
    |(V.malaKernel h hh x B).toReal - (V.malaKernel h hh y B).toReal| ≤
      17 / 32 := by
  have hd1 : 1 ≤ (d : ℝ) := V.dimension_real_one
  have hden : 0 < 2 * V.L * (d : ℝ) :=
    mul_pos (mul_pos (by norm_num) V.hL) V.dimension_real_pos
  have hhL : h ≤ 1 / V.L := by
    exact hsmall.trans (one_div_le_one_div_of_le V.hL (by
      nlinarith [V.hL]))
  have hh2L : h ≤ 2 / V.L := hhL.trans (by
    exact div_le_div_of_nonneg_right (by norm_num) V.hL.le)
  have hrej : V.L * h * (d : ℝ) / 2 ≤ 1 / 4 := by
    have hmul : h * (2 * V.L * (d : ℝ)) ≤ 1 :=
      (le_div_iff₀ hden).mp hsmall
    calc
      V.L * h * (d : ℝ) / 2 = (h * (2 * V.L * (d : ℝ))) / 4 := by ring
      _ ≤ 1 / 4 := div_le_div_of_nonneg_right hmul (by norm_num)
  let Px := (V.malaKernel h hh x B).toReal
  let Py := (V.malaKernel h hh y B).toReal
  let Qx := (V.gaussianDensityProposal h x B).toReal
  let Qy := (V.gaussianDensityProposal h y B).toReal
  have hxrej : |Px - Qx| ≤ 1 / 4 := by
    exact (V.abs_malaKernel_apply_toReal_sub_gaussianProposal_le_rejection
      hh x hB).trans ((V.malaRejectionMass_toReal_le hh hhL x).trans hrej)
  have hyrej : |Qy - Py| ≤ 1 / 4 := by
    rw [abs_sub_comm]
    exact (V.abs_malaKernel_apply_toReal_sub_gaussianProposal_le_rejection
      hh y hB).trans ((V.malaRejectionMass_toReal_le hh hhL y).trans hrej)
  have hproposal : |Qx - Qy| ≤ 1 / 32 :=
    V.abs_gaussianDensityProposal_apply_toReal_sub_le_one_div_32
      ht hh hhalf hh2L x y hxy hB
  calc
    |Px - Py| ≤ |Px - Qx| + |Qx - Py| := abs_sub_le Px Qx Py
    _ ≤ |Px - Qx| + (|Qx - Qy| + |Qy - Py|) := by
      gcongr
      exact abs_sub_le Qx Qy Py
    _ ≤ 1 / 4 + (1 / 32 + 1 / 4) := by gcongr
    _ = 17 / 32 := by norm_num

set_option maxHeartbeats 800000 in
/-- The global fixed-step estimate is preserved by the paper's upper-half
step-size mixture.  This proves the setwise form of the global clause of
Proposition 3.2 with the stronger constant `17/32 < 3/4`. -/
theorem abs_dyadicMALA_apply_toReal_sub_le_seventeen_div_32
    {t : ℝ} (ht : 0 < t)
    (hsmall : t ≤ 1 / (2 * V.L * (d : ℝ)))
    (x y : State d) (hxy : ‖x - y‖ ≤ Real.sqrt t / 16)
    {B : Set (State d)} (hB : MeasurableSet B) :
    |(V.dyadicMALA t ht x B).toReal - (V.dyadicMALA t ht y B).toReal| ≤
      17 / 32 := by
  let ν := dyadicStepMeasure t
  let K := V.malaKernelFamily
  let c : ℝ := 17 / 32
  let cE : ℝ≥0∞ := ENNReal.ofReal c
  letI : IsProbabilityMeasure ν := dyadicStepMeasure_isProbabilityMeasure ht
  letI : IsMarkovKernel (V.dyadicMALA t ht) :=
    V.dyadicMALA_isMarkovKernel t ht
  have hmem : ∀ᵐ h ∂ν, h ∈ Set.Ioc (t / 2) t := by
    change ∀ᵐ h ∂(volume : Measure ℝ)[|Set.Ioc (t / 2) t],
      h ∈ Set.Ioc (t / 2) t
    exact ProbabilityTheory.ae_cond_mem measurableSet_Ioc
  have hpoint : ∀ᵐ h ∂ν,
      |(K (h, x) B).toReal - (K (h, y) B).toReal| ≤ c := by
    filter_upwards [hmem] with h hhmem
    have hh : 0 < h := lt_of_lt_of_le (by linarith [ht]) hhmem.1.le
    have hhsmall : h ≤ 1 / (2 * V.L * (d : ℝ)) := hhmem.2.trans hsmall
    have hxsect := congrArg (fun κ : Kernel (State d) (State d) => κ x B)
      (V.sectR_malaKernelFamily h)
    have hysect := congrArg (fun κ : Kernel (State d) (State d) => κ y B)
      (V.sectR_malaKernelFamily h)
    simp only [Kernel.sectR_apply, effectiveStep_of_pos hh] at hxsect hysect
    rw [hxsect, hysect]
    exact V.abs_malaKernel_apply_toReal_sub_le_seventeen_div_32
      ht hh hhmem.1.le hhsmall x y hxy hB
  have hxyE : ∀ᵐ h ∂ν, K (h, x) B ≤ K (h, y) B + cE := by
    filter_upwards [hpoint] with h hbound
    have hxfin : K (h, x) B ≠ ∞ := measure_ne_top (K (h, x)) B
    have hyfin : K (h, y) B ≠ ∞ := measure_ne_top (K (h, y)) B
    have hcfin : cE ≠ ∞ := ENNReal.ofReal_ne_top
    apply (ENNReal.toReal_le_toReal hxfin (ENNReal.add_ne_top.mpr ⟨hyfin, hcfin⟩)).mp
    rw [ENNReal.toReal_add hyfin hcfin]
    have hc0 : 0 ≤ c := by norm_num [c]
    rw [ENNReal.toReal_ofReal hc0]
    have hsub := (abs_le.mp hbound).2
    linarith
  have hyxE : ∀ᵐ h ∂ν, K (h, y) B ≤ K (h, x) B + cE := by
    filter_upwards [hpoint] with h hbound
    have hxfin : K (h, x) B ≠ ∞ := measure_ne_top (K (h, x)) B
    have hyfin : K (h, y) B ≠ ∞ := measure_ne_top (K (h, y)) B
    have hcfin : cE ≠ ∞ := ENNReal.ofReal_ne_top
    apply (ENNReal.toReal_le_toReal hyfin (ENNReal.add_ne_top.mpr ⟨hxfin, hcfin⟩)).mp
    rw [ENNReal.toReal_add hxfin hcfin]
    have hc0 : 0 ≤ c := by norm_num [c]
    rw [ENNReal.toReal_ofReal hc0]
    have hneg : -c ≤ (K (h, x) B).toReal - (K (h, y) B).toReal :=
      (abs_le.mp hbound).1
    linarith
  have hKx : V.dyadicMALA t ht x B = ∫⁻ h, K (h, x) B ∂ν := by
    rw [dyadicMALA, Kernel.parameterMixture_apply _ _ _ _ hB]
  have hKy : V.dyadicMALA t ht y B = ∫⁻ h, K (h, y) B ∂ν := by
    rw [dyadicMALA, Kernel.parameterMixture_apply _ _ _ _ hB]
  have hmixXY : V.dyadicMALA t ht x B ≤ V.dyadicMALA t ht y B + cE := by
    rw [hKx, hKy]
    calc
      (∫⁻ h, K (h, x) B ∂ν) ≤ ∫⁻ h, K (h, y) B + cE ∂ν :=
        lintegral_mono_ae hxyE
      _ = (∫⁻ h, K (h, y) B ∂ν) + ∫⁻ _h, cE ∂ν :=
        lintegral_add_left ((K.measurable_coe hB).comp
          (measurable_id.prodMk measurable_const)) _
      _ = (∫⁻ h, K (h, y) B ∂ν) + cE := by simp
  have hmixYX : V.dyadicMALA t ht y B ≤ V.dyadicMALA t ht x B + cE := by
    rw [hKx, hKy]
    calc
      (∫⁻ h, K (h, y) B ∂ν) ≤ ∫⁻ h, K (h, x) B + cE ∂ν :=
        lintegral_mono_ae hyxE
      _ = (∫⁻ h, K (h, x) B ∂ν) + ∫⁻ _h, cE ∂ν :=
        lintegral_add_left ((K.measurable_coe hB).comp
          (measurable_id.prodMk measurable_const)) _
      _ = (∫⁻ h, K (h, x) B ∂ν) + cE := by simp
  have hxfin : V.dyadicMALA t ht x B ≠ ∞ :=
    measure_ne_top (V.dyadicMALA t ht x) B
  have hyfin : V.dyadicMALA t ht y B ≠ ∞ :=
    measure_ne_top (V.dyadicMALA t ht y) B
  have hcfin : cE ≠ ∞ := ENNReal.ofReal_ne_top
  have hrealXY : (V.dyadicMALA t ht x B).toReal ≤
      (V.dyadicMALA t ht y B).toReal + c := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hyfin, hcfin⟩) hmixXY
    rw [ENNReal.toReal_add hyfin hcfin,
      ENNReal.toReal_ofReal (by norm_num [c] : 0 ≤ c)] at this
    exact this
  have hrealYX : (V.dyadicMALA t ht y B).toReal ≤
      (V.dyadicMALA t ht x B).toReal + c := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hxfin, hcfin⟩) hmixYX
    rw [ENNReal.toReal_add hxfin hcfin,
      ENNReal.toReal_ofReal (by norm_num [c] : 0 ≤ c)] at this
    exact this
  rw [abs_le]
  constructor <;> dsimp [c] at * <;> linarith

theorem abs_dyadicMALA_apply_toReal_sub_le_three_quarters
    {t : ℝ} (ht : 0 < t)
    (hsmall : t ≤ 1 / (2 * V.L * (d : ℝ)))
    (x y : State d) (hxy : ‖x - y‖ ≤ Real.sqrt t / 16)
    {B : Set (State d)} (hB : MeasurableSet B) :
    |(V.dyadicMALA t ht x B).toReal - (V.dyadicMALA t ht y B).toReal| ≤
      3 / 4 := by
  exact (V.abs_dyadicMALA_apply_toReal_sub_le_seventeen_div_32
    ht hsmall x y hxy hB).trans (by norm_num)

/-- Supremum-over-measurable-sets packaging of the stronger dyadic MALA
comparison. -/
theorem setwiseTV_dyadicMALA_le_seventeen_div_32
    {t : ℝ} (ht : 0 < t)
    (hsmall : t ≤ 1 / (2 * V.L * (d : ℝ)))
    (x y : State d) (hxy : ‖x - y‖ ≤ Real.sqrt t / 16) :
    setwiseTV (V.dyadicMALA t ht x) (V.dyadicMALA t ht y) ≤ 17 / 32 := by
  apply setwiseTV_le_of_forall
  intro B hB
  simpa [Measure.real_def] using
    V.abs_dyadicMALA_apply_toReal_sub_le_seventeen_div_32
      ht hsmall x y hxy hB

/-- The global clause of Proposition 3.2 in the project's concrete
total-variation convention. -/
theorem setwiseTV_dyadicMALA_le_three_quarters
    {t : ℝ} (ht : 0 < t)
    (hsmall : t ≤ 1 / (2 * V.L * (d : ℝ)))
    (x y : State d) (hxy : ‖x - y‖ ≤ Real.sqrt t / 16) :
    setwiseTV (V.dyadicMALA t ht x) (V.dyadicMALA t ht y) ≤ 3 / 4 := by
  exact (V.setwiseTV_dyadicMALA_le_seventeen_div_32
    ht hsmall x y hxy).trans (by norm_num)

end FirstOrderPotential
end Concrete

end
end UniformRandomMALA
