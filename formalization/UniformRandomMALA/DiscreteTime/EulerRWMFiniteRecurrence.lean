import UniformRandomMALA.DiscreteTime.EulerRWMRecurrence
import UniformRandomMALA.DiscreteTime.Recursion
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Finite stationary Euler--RWM coupling recurrence

This file lifts the unequal-start one-step estimate to measures and then to
the finite coupled chain started from the diagonal target law.  The explicit
RWM second marginal remains stationary at every step.  All expectations are
ordinary Bochner integrals against finite-dimensional measures.
-/

namespace UniformRandomMALA
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory unitInterval RealInnerProductSpace
noncomputable section
namespace DiscreteTime
open Concrete
variable {d : ℕ}

lemma integrable_unit_pair_difference_sq
    (V : FirstOrderPotential d) (δ : ℝ) (x y z : State d) :
    Integrable (fun u : Set.Icc (0 : ℝ) 1 =>
      ‖explicitEulerUpdate V δ x z -
        explicitRWMRejectionUniformUpdate V δ y (z, u)‖ ^ 2) := by
  let A := eulerMeanDifference V δ x y
  let B : Set.Icc (0 : ℝ) 1 → State d := fun u =>
    explicitEulerUpdate V δ y z -
      explicitRWMRejectionUniformUpdate V δ y (z, u)
  have hB := integrable_unit_sameStartDifference V δ y z
  have hBsq := integrable_unit_sameStartDifference_sq V δ y z
  have hrhs : Integrable (fun u =>
      (‖A‖ ^ 2 + 2 * @inner ℝ (State d) _ A (B u)) + ‖B u‖ ^ 2) :=
    ((integrable_const _).add ((hB.const_inner A).const_mul 2)).add hBsq
  exact hrhs.congr (ae_of_all _ fun u => by
    change (‖A‖ ^ 2 + 2 * @inner ℝ (State d) _ A (B u)) + ‖B u‖ ^ 2 =
      ‖explicitEulerUpdate V δ x z -
        explicitRWMRejectionUniformUpdate V δ y (z, u)‖ ^ 2
    rw [pair_difference_decomposition]
    exact (norm_add_sq_real _ _).symm)

lemma integrable_gaussian_pairOneStepSquaredDistance
    (V : FirstOrderPotential d) (δ : ℝ)
    (x y : State d) :
    Integrable (fun z : State d =>
      ∫ u : Set.Icc (0 : ℝ) 1,
        ‖explicitEulerUpdate V δ x z -
          explicitRWMRejectionUniformUpdate V δ y (z, u)‖ ^ 2 ∂volume)
      (stdGaussian (State d)) := by
  let A := eulerMeanDifference V δ x y
  let D : State d → State d := fun z =>
    ∫ u : Set.Icc (0 : ℝ) 1,
      explicitEulerUpdate V δ y z -
        explicitRWMRejectionUniformUpdate V δ y (z, u) ∂volume
  let S : State d → ℝ := fun z =>
    ∫ u : Set.Icc (0 : ℝ) 1,
      ‖explicitEulerUpdate V δ y z -
        explicitRWMRejectionUniformUpdate V δ y (z, u)‖ ^ 2 ∂volume
  have hD : Integrable D (stdGaussian (State d)) :=
    integrable_gaussian_integral_unit_sameStartDifference V δ y
  have hS : Integrable S (stdGaussian (State d)) :=
    integrable_gaussian_sameStart_sq V δ y
  have hrhs : Integrable (fun z =>
      (‖A‖ ^ 2 + 2 * @inner ℝ (State d) _ A (D z)) + S z)
      (stdGaussian (State d)) :=
    ((integrable_const _).add ((hD.const_inner A).const_mul 2)).add hS
  exact hrhs.congr (ae_of_all _ fun z =>
    (integral_unit_pair_difference_sq_eq V δ x y z).symm)

lemma integrable_pairUpdateSquaredDistance_noise
    (V : FirstOrderPotential d) (δ : ℝ)
    (xy : State d × State d) :
    Integrable (fun zu : State d × Set.Icc (0 : ℝ) 1 =>
      pairSquaredDistance (eulerRWMPairUpdate V δ xy zu))
      (gaussianUniformNoise d) := by
  rw [gaussianUniformNoise]
  let F : State d × Set.Icc (0 : ℝ) 1 → ℝ := fun zu =>
    pairSquaredDistance (eulerRWMPairUpdate V δ xy zu)
  have hFmeas : Measurable F :=
    measurable_pairSquaredDistance.comp (measurable_eulerRWMPairUpdate V δ xy)
  apply (integrable_prod_iff hFmeas.aestronglyMeasurable).2
  constructor
  · exact ae_of_all _ fun z => integrable_unit_pair_difference_sq
      V δ xy.1 xy.2 z
  · have houter := integrable_gaussian_pairOneStepSquaredDistance
      V δ xy.1 xy.2
    apply houter.congr
    exact ae_of_all _ fun z => by
      apply integral_congr_ae
      exact ae_of_all _ fun u => by
        change ‖explicitEulerUpdate V δ xy.1 z -
            explicitRWMRejectionUniformUpdate V δ xy.2 (z, u)‖ ^ 2 =
          |‖explicitEulerUpdate V δ xy.1 z -
            explicitRWMRejectionUniformUpdate V δ xy.2 (z, u)‖ ^ 2|
        rw [abs_of_nonneg (sq_nonneg _)]

lemma integrable_pairSquaredDistance_pairKernel
    (V : FirstOrderPotential d) (δ : ℝ)
    (xy : State d × State d) :
    Integrable pairSquaredDistance (eulerRWMPairKernel V δ xy) := by
  rw [eulerRWMPairKernel_apply_eq_pairLaw, eulerRWMPairLaw]
  exact (integrable_map_measure measurable_pairSquaredDistance.aestronglyMeasurable
    (measurable_eulerRWMPairUpdate V δ xy).aemeasurable).2
      (integrable_pairUpdateSquaredDistance_noise V δ xy)

lemma integral_pairSquaredDistance_pairKernel
    (V : FirstOrderPotential d) (δ : ℝ)
    (xy : State d × State d) :
    (∫ xy', pairSquaredDistance xy' ∂eulerRWMPairKernel V δ xy) =
      pairOneStepSquaredDistance V δ xy := by
  rw [eulerRWMPairKernel_apply_eq_pairLaw, eulerRWMPairLaw,
    integral_map (measurable_eulerRWMPairUpdate V δ xy).aemeasurable
      measurable_pairSquaredDistance.aestronglyMeasurable,
    gaussianUniformNoise]
  rw [integral_prod _ (integrable_pairUpdateSquaredDistance_noise V δ xy)]
  rfl

lemma integrable_pairOneStepSquaredDistance_of_stationary_snd
    (V : FirstOrderPotential d) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδL : δ ≤ 2 / V.L)
    (μ : Measure (State d × State d)) [IsProbabilityMeasure μ]
    (henergy : Integrable pairSquaredDistance μ)
    (hsnd : Measure.map Prod.snd μ = (V.target : Measure (State d))) :
    Integrable (pairOneStepSquaredDistance V δ) μ := by
  let g : State d × State d → ℝ := fun xy =>
    (1 + δ) * pairSquaredDistance xy +
      pointwiseEulerRWMRecurrenceError V δ xy.2
  have hlocalTarget := integrable_pointwiseEulerRWMRecurrenceError V δ
  have hlocalMap : Integrable (pointwiseEulerRWMRecurrenceError V δ)
      (Measure.map Prod.snd μ) := by simpa only [hsnd] using hlocalTarget
  have hlocalμ : Integrable
      (fun xy : State d × State d =>
        pointwiseEulerRWMRecurrenceError V δ xy.2) μ := by
    simpa only [Function.comp_def] using hlocalMap.comp_measurable measurable_snd
  have hgint : Integrable g μ :=
    (henergy.const_mul (1 + δ)).add hlocalμ
  apply hgint.mono
    (measurable_pairOneStepSquaredDistance V δ).aestronglyMeasurable
  exact ae_of_all _ fun xy => by
    have hle := iteratedIntegral_pair_difference_sq_delta_le
      V δ hδ hδ1 hδL xy.1 xy.2
    change pairOneStepSquaredDistance V δ xy ≤
      (1 + δ) * ‖xy.1 - xy.2‖ ^ 2 +
        (Real.sqrt (2 * δ)) ^ 3 * pointwiseEulerRWMCouplingConstant V xy.2 +
        δ ^ 2 * (2 * ‖V.gradU xy.2‖ ^ 2 +
          8 * (pointwiseRWMRejectionBiasConstant V xy.2) ^ 2) at hle
    have hf0 : 0 ≤ pairOneStepSquaredDistance V δ xy := by
      unfold pairOneStepSquaredDistance
      exact integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
    have hg0 : 0 ≤ g xy := by
      apply hf0.trans
      dsimp [g, pairSquaredDistance, pointwiseEulerRWMRecurrenceError]
      nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg hf0,
      Real.norm_eq_abs, abs_of_nonneg hg0]
    dsimp [g, pairSquaredDistance,
      pointwiseEulerRWMRecurrenceError]
    nlinarith

lemma integrable_pairSquaredDistance_pairKernel_comp
    (V : FirstOrderPotential d) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδL : δ ≤ 2 / V.L)
    (μ : Measure (State d × State d)) [IsProbabilityMeasure μ]
    (henergy : Integrable pairSquaredDistance μ)
    (hsnd : Measure.map Prod.snd μ = (V.target : Measure (State d))) :
    Integrable pairSquaredDistance (eulerRWMPairKernel V δ ∘ₘ μ) := by
  apply (Measure.integrable_comp_iff
    measurable_pairSquaredDistance.aestronglyMeasurable).2
  constructor
  · exact ae_of_all _ fun xy =>
      integrable_pairSquaredDistance_pairKernel V δ xy
  · have hnext := integrable_pairOneStepSquaredDistance_of_stationary_snd
      V δ hδ hδ1 hδL μ henergy hsnd
    apply hnext.congr
    exact ae_of_all _ fun xy => by
      calc
        pairOneStepSquaredDistance V δ xy =
            ∫ xy', pairSquaredDistance xy'
              ∂eulerRWMPairKernel V δ xy :=
          (integral_pairSquaredDistance_pairKernel V δ xy).symm
        _ = (∫ xy', ‖pairSquaredDistance xy'‖
          ∂eulerRWMPairKernel V δ xy) := by
          apply integral_congr_ae
          exact ae_of_all _ fun xy' => by
            change pairSquaredDistance xy' = |pairSquaredDistance xy'|
            rw [abs_of_nonneg]
            unfold pairSquaredDistance
            exact sq_nonneg _

lemma integral_pairSquaredDistance_pairKernel_comp
    (V : FirstOrderPotential d) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδL : δ ≤ 2 / V.L)
    (μ : Measure (State d × State d)) [IsProbabilityMeasure μ]
    (henergy : Integrable pairSquaredDistance μ)
    (hsnd : Measure.map Prod.snd μ = (V.target : Measure (State d))) :
    (∫ xy, pairSquaredDistance xy ∂(eulerRWMPairKernel V δ ∘ₘ μ)) =
      ∫ xy, pairOneStepSquaredDistance V δ xy ∂μ := by
  have hcomp := integrable_pairSquaredDistance_pairKernel_comp
    V δ hδ hδ1 hδL μ henergy hsnd
  let κ0 : Kernel Unit (State d × State d) := Kernel.const Unit μ
  have hcomp' : Integrable pairSquaredDistance
      ((eulerRWMPairKernel V δ ∘ₖ κ0) ()) := by
    change Integrable pairSquaredDistance (eulerRWMPairKernel V δ ∘ₘ μ)
    exact hcomp
  calc
    (∫ xy, pairSquaredDistance xy ∂(eulerRWMPairKernel V δ ∘ₘ μ)) =
        ∫ xy, pairSquaredDistance xy
          ∂(eulerRWMPairKernel V δ ∘ₖ κ0) () := by
      rw [Measure.comp_eq_comp_const_apply]
    _ = ∫ xy, (∫ xy', pairSquaredDistance xy'
          ∂eulerRWMPairKernel V δ xy) ∂μ := by
      rw [Kernel.integral_comp hcomp']
      rfl
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun xy =>
        integral_pairSquaredDistance_pairKernel V δ xy

def diagonalTargetPairLaw (V : FirstOrderPotential d) :
    Measure (State d × State d) :=
  Measure.map (fun x : State d => (x, x))
    (V.target : Measure (State d))

instance diagonalTargetPairLaw_isProbabilityMeasure
    (V : FirstOrderPotential d) :
    IsProbabilityMeasure (diagonalTargetPairLaw V) := by
  constructor
  have hdiag : Measurable (fun x : State d => (x, x)) :=
    measurable_id.prodMk measurable_id
  rw [diagonalTargetPairLaw,
    Measure.map_apply hdiag MeasurableSet.univ]
  simp

lemma map_snd_diagonalTargetPairLaw (V : FirstOrderPotential d) :
    Measure.map Prod.snd (diagonalTargetPairLaw V) =
      (V.target : Measure (State d)) := by
  have hdiag : Measurable (fun x : State d => (x, x)) :=
    measurable_id.prodMk measurable_id
  rw [diagonalTargetPairLaw,
    Measure.map_map measurable_snd hdiag]
  change Measure.map id (V.target : Measure (State d)) = V.target
  exact Measure.map_id

lemma map_snd_pairKernel_comp
    (V : FirstOrderPotential d) (δ : ℝ)
    (μ : Measure (State d × State d)) [SFinite μ] :
    Measure.map Prod.snd (eulerRWMPairKernel V δ ∘ₘ μ) =
      explicitRWMKernel V δ ∘ₘ Measure.map Prod.snd μ := by
  rw [Measure.map_comp μ (eulerRWMPairKernel V δ) measurable_snd,
    ← Kernel.snd_eq,
    snd_eulerRWMPairKernel, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map]

def stationaryEulerRWMPairChainLaw
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ) :
    Measure (State d × State d) :=
  eulerRWMPairChainKernel V δ n ∘ₘ diagonalTargetPairLaw V

instance stationaryEulerRWMPairChainLaw_isProbabilityMeasure
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ) :
    IsProbabilityMeasure (stationaryEulerRWMPairChainLaw V δ n) := by
  unfold stationaryEulerRWMPairChainLaw
  infer_instance

lemma stationaryEulerRWMPairChainLaw_succ
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ) :
    stationaryEulerRWMPairChainLaw V δ (n + 1) =
      eulerRWMPairKernel V δ ∘ₘ
        stationaryEulerRWMPairChainLaw V δ n := by
  change finiteKernelIterate (eulerRWMPairKernel V δ) (n + 1) ∘ₘ
      diagonalTargetPairLaw V =
    eulerRWMPairKernel V δ ∘ₘ
      (finiteKernelIterate (eulerRWMPairKernel V δ) n ∘ₘ
        diagonalTargetPairLaw V)
  rw [finiteKernelIterate]
  exact Measure.comp_assoc.symm

lemma map_snd_stationaryEulerRWMPairChainLaw
    (V : FirstOrderPotential d) (δ : ℝ) : ∀ n : ℕ,
    Measure.map Prod.snd (stationaryEulerRWMPairChainLaw V δ n) =
      (V.target : Measure (State d)) := by
  intro n
  induction n with
  | zero =>
      rw [stationaryEulerRWMPairChainLaw,
        eulerRWMPairChainKernel, finiteKernelIterate, Measure.id_comp]
      exact map_snd_diagonalTargetPairLaw V
  | succ n ih =>
      rw [stationaryEulerRWMPairChainLaw_succ,
        map_snd_pairKernel_comp, ih]
      exact (explicitRWMKernel_invariant V δ).def

lemma integrable_pairSquaredDistance_diagonalTargetPairLaw
    (V : FirstOrderPotential d) :
    Integrable pairSquaredDistance (diagonalTargetPairLaw V) := by
  unfold diagonalTargetPairLaw
  apply (integrable_map_measure measurable_pairSquaredDistance.aestronglyMeasurable
    (measurable_id.prodMk measurable_id).aemeasurable).2
  have hz : Integrable (fun _x : State d => (0 : ℝ))
      (V.target : Measure (State d)) := integrable_const _
  exact hz.congr (ae_of_all _ fun x => by
    simp [pairSquaredDistance])

lemma integrable_pairSquaredDistance_stationaryEulerRWMPairChainLaw
    (V : FirstOrderPotential d) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδL : δ ≤ 2 / V.L) :
    ∀ n : ℕ, Integrable pairSquaredDistance
      (stationaryEulerRWMPairChainLaw V δ n) := by
  intro n
  induction n with
  | zero =>
      rw [stationaryEulerRWMPairChainLaw,
        eulerRWMPairChainKernel, finiteKernelIterate, Measure.id_comp]
      exact integrable_pairSquaredDistance_diagonalTargetPairLaw V
  | succ n ih =>
      rw [stationaryEulerRWMPairChainLaw_succ]
      exact integrable_pairSquaredDistance_pairKernel_comp
        V δ hδ hδ1 hδL _ ih
          (map_snd_stationaryEulerRWMPairChainLaw V δ n)

theorem stationaryEulerRWMPairChain_energy_step
    (V : FirstOrderPotential d) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδL : δ ≤ 2 / V.L)
    (n : ℕ) :
    (∫ xy, pairSquaredDistance xy
      ∂stationaryEulerRWMPairChainLaw V δ (n + 1)) ≤
      (1 + δ) * (∫ xy, pairSquaredDistance xy
        ∂stationaryEulerRWMPairChainLaw V δ n) +
        stationaryEulerRWMRecurrenceError V δ := by
  rw [stationaryEulerRWMPairChainLaw_succ]
  calc
    (∫ xy, pairSquaredDistance xy
      ∂(eulerRWMPairKernel V δ ∘ₘ
        stationaryEulerRWMPairChainLaw V δ n)) =
      ∫ xy, pairOneStepSquaredDistance V δ xy
        ∂stationaryEulerRWMPairChainLaw V δ n :=
      integral_pairSquaredDistance_pairKernel_comp V δ hδ hδ1 hδL _
        (integrable_pairSquaredDistance_stationaryEulerRWMPairChainLaw
          V δ hδ hδ1 hδL n)
        (map_snd_stationaryEulerRWMPairChainLaw V δ n)
    _ ≤ _ := integral_pairOneStepSquaredDistance_le V δ hδ hδ1 hδL _
      (integrable_pairSquaredDistance_stationaryEulerRWMPairChainLaw
        V δ hδ hδ1 hδL n)
      (map_snd_stationaryEulerRWMPairChainLaw V δ n)

lemma stationaryEulerRWMRecurrenceError_nonneg
    (V : FirstOrderPotential d) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδL : δ ≤ 2 / V.L) :
    0 ≤ stationaryEulerRWMRecurrenceError V δ := by
  rw [← integral_pointwiseEulerRWMRecurrenceError V δ]
  apply integral_nonneg
  intro y
  have hle := iteratedIntegral_pair_difference_sq_delta_le
    V δ hδ hδ1 hδL y y
  have hleft : 0 ≤
      (∫ z : State d,
        (∫ u : Set.Icc (0 : ℝ) 1,
          ‖explicitEulerUpdate V δ y z -
            explicitRWMRejectionUniformUpdate V δ y (z, u)‖ ^ 2 ∂volume)
        ∂stdGaussian (State d)) :=
    integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
  have hlocal := hleft.trans hle
  simpa [pointwiseEulerRWMRecurrenceError] using hlocal

lemma integral_pairSquaredDistance_stationaryEulerRWMPairChainLaw_zero
    (V : FirstOrderPotential d) (δ : ℝ) :
    (∫ xy, pairSquaredDistance xy
      ∂stationaryEulerRWMPairChainLaw V δ 0) = 0 := by
  rw [stationaryEulerRWMPairChainLaw,
    eulerRWMPairChainKernel, finiteKernelIterate, Measure.id_comp,
    diagonalTargetPairLaw]
  have hdiag : Measurable (fun x : State d => (x, x)) :=
    measurable_id.prodMk measurable_id
  rw [integral_map hdiag.aemeasurable
    measurable_pairSquaredDistance.aestronglyMeasurable]
  simp [pairSquaredDistance]

theorem stationaryEulerRWMPairChain_energy_le
    (V : FirstOrderPotential d) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδL : δ ≤ 2 / V.L)
    (n : ℕ) :
    (∫ xy, pairSquaredDistance xy
      ∂stationaryEulerRWMPairChainLaw V δ n) ≤
      (n : ℝ) * stationaryEulerRWMRecurrenceError V δ *
        (1 + δ) ^ n := by
  let a : ℕ → ℝ := fun k =>
    ∫ xy, pairSquaredDistance xy
      ∂stationaryEulerRWMPairChainLaw V δ k
  apply affine_recursion_bound a (1 + δ)
  · linarith
  · exact stationaryEulerRWMRecurrenceError_nonneg
      V δ hδ hδ1 hδL
  · dsimp [a]
    rw [integral_pairSquaredDistance_stationaryEulerRWMPairChainLaw_zero]
  · intro k
    exact stationaryEulerRWMPairChain_energy_step
      V δ hδ hδ1 hδL k

end DiscreteTime
end
end UniformRandomMALA
