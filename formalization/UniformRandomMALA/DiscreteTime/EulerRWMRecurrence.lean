import UniformRandomMALA.DiscreteTime.EulerRWMPairChain
import UniformRandomMALA.Concrete.Cocoercivity

/-!
# Unequal-start Euler--RWM one-step recurrence

This file inserts a same-start Euler update between an Euler state and an
explicit RWM state.  Exact integration of the cross term uses the elementary
rejection-bias expansion, while cocoercivity controls the deterministic
Euler mean difference.  The resulting recurrence has coefficient `1 + δ`,
not the factor `2` produced by a direct squared triangle inequality.
-/

namespace UniformRandomMALA
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory unitInterval RealInnerProductSpace
noncomputable section
namespace DiscreteTime
open Concrete
variable {d : ℕ}

def eulerMeanDifference (V : FirstOrderPotential d) (δ : ℝ)
    (x y : State d) : State d :=
  (x - δ • V.gradU x) - (y - δ • V.gradU y)

lemma explicitEulerUpdate_sub_explicitEulerUpdate
    (V : FirstOrderPotential d) (δ : ℝ) (x y z : State d) :
    explicitEulerUpdate V δ x z - explicitEulerUpdate V δ y z =
      eulerMeanDifference V δ x y := by
  unfold explicitEulerUpdate eulerMeanDifference
  module

lemma pair_difference_decomposition
    (V : FirstOrderPotential d) (δ : ℝ) (x y z : State d)
    (u : Set.Icc (0 : ℝ) 1) :
    explicitEulerUpdate V δ x z -
        explicitRWMRejectionUniformUpdate V δ y (z, u) =
      eulerMeanDifference V δ x y +
        (explicitEulerUpdate V δ y z -
          explicitRWMRejectionUniformUpdate V δ y (z, u)) := by
  rw [← explicitEulerUpdate_sub_explicitEulerUpdate V δ x y z]
  abel

lemma norm_eulerMeanDifference_le
    (V : FirstOrderPotential d) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδL : δ ≤ 2 / V.L) (x y : State d) :
    ‖eulerMeanDifference V δ x y‖ ≤ ‖x - y‖ := by
  exact V.norm_proposalMean_sub_le δ hδ hδL x y

lemma integrable_gaussian_sameStart_sq
    (V : FirstOrderPotential d) (δ : ℝ) (y : State d) :
    Integrable (fun z : State d =>
      ∫ u : Set.Icc (0 : ℝ) 1,
        ‖explicitEulerUpdate V δ y z -
          explicitRWMRejectionUniformUpdate V δ y (z, u)‖ ^ 2 ∂volume)
      (stdGaussian (State d)) := by
  let F : State d × Set.Icc (0 : ℝ) 1 → ℝ := fun zu =>
    ‖explicitEulerUpdate V δ y zu.1 -
      explicitRWMRejectionUniformUpdate V δ y zu‖ ^ 2
  let f : State d → ℝ := fun z => ∫ u, F (z, u) ∂volume
  let g : State d → ℝ := fun z =>
    2 * V.scaledRWMRejectionSecondMomentIntegrand δ y z +
      2 * δ ^ 2 * ‖V.gradU y‖ ^ 2
  have hFmeas : Measurable F := by
    have he : Measurable (fun zu : State d × Set.Icc (0 : ℝ) 1 =>
        explicitEulerUpdate V δ y zu.1) :=
      (Measurable.of_uncurry_left
        (measurable_uncurry_explicitEulerUpdate V δ)).comp measurable_fst
    exact (he.sub (measurable_explicitRWMRejectionUniformUpdate V δ y)).norm.pow_const 2
  have hfmeas : Measurable f :=
    hFmeas.stronglyMeasurable.integral_prod_right'.measurable
  have hsecond := integrable_scaledRWMRejectionSecondMomentIntegrand V δ y
  have hgint : Integrable g (stdGaussian (State d)) := by
    exact (hsecond.const_mul 2).add (integrable_const _)
  have hfint : Integrable f (stdGaussian (State d)) := by
    apply hgint.mono hfmeas.aestronglyMeasurable
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg, Real.norm_eq_abs, abs_of_nonneg]
      · exact integral_unitInterval_norm_explicitEuler_sub_rwm_sq_le V δ y z
      · dsimp [g]
        exact add_nonneg
          (mul_nonneg (by norm_num) (by
            unfold Concrete.FirstOrderPotential.scaledRWMRejectionSecondMomentIntegrand
            exact mul_nonneg (rejectionProfile_nonneg _) (sq_nonneg _)))
          (by positivity)
      · dsimp [f]
        exact integral_nonneg fun _ => sq_nonneg _
  exact hfint

lemma integrable_unit_sameStartDifference
    (V : FirstOrderPotential d) (δ : ℝ) (y z : State d) :
    Integrable (fun u : Set.Icc (0 : ℝ) 1 =>
      explicitEulerUpdate V δ y z -
        explicitRWMRejectionUniformUpdate V δ y (z, u)) := by
  rw [show (fun u : Set.Icc (0 : ℝ) 1 =>
      explicitEulerUpdate V δ y z -
        explicitRWMRejectionUniformUpdate V δ y (z, u)) =
      fun u => V.bernoulliRWMRejectedIncrement δ y z u - δ • V.gradU y by
    funext u
    exact explicitEulerUpdate_sub_explicitRWMRejectionUniformUpdate V δ y z u]
  exact (integrable_thresholdConst _ _).sub (integrable_const _)

lemma integral_unit_sameStartDifference
    (V : FirstOrderPotential d) (δ : ℝ) (y z : State d) :
    (∫ u : Set.Icc (0 : ℝ) 1,
      explicitEulerUpdate V δ y z -
        explicitRWMRejectionUniformUpdate V δ y (z, u) ∂volume) =
      V.scaledRWMRejectionDisplacement δ y z - δ • V.gradU y := by
  rw [show (fun u : Set.Icc (0 : ℝ) 1 =>
      explicitEulerUpdate V δ y z -
        explicitRWMRejectionUniformUpdate V δ y (z, u)) =
      fun u => V.bernoulliRWMRejectedIncrement δ y z u - δ • V.gradU y by
    funext u
    exact explicitEulerUpdate_sub_explicitRWMRejectionUniformUpdate V δ y z u]
  unfold Concrete.FirstOrderPotential.bernoulliRWMRejectedIncrement
  rw [integral_sub (integrable_thresholdConst _ _) (integrable_const _),
    integral_thresholdConst _ (rejectionProfile_nonneg _)
      (rejectionProfile_le_one _) _, integral_const]
  have hvol : (volume : Measure (Set.Icc (0 : ℝ) 1)).real Set.univ = 1 := by
    rw [MeasureTheory.measureReal_def]
    simp
  rw [hvol, one_smul]
  rfl

lemma integrable_gaussian_integral_unit_sameStartDifference
    (V : FirstOrderPotential d) (δ : ℝ) (y : State d) :
    Integrable (fun z : State d =>
      ∫ u : Set.Icc (0 : ℝ) 1,
        explicitEulerUpdate V δ y z -
          explicitRWMRejectionUniformUpdate V δ y (z, u) ∂volume)
      (stdGaussian (State d)) := by
  apply (V.integrable_scaledRWMRejectionDisplacement δ y).sub (integrable_const _)
    |>.congr
  exact ae_of_all _ fun z => (integral_unit_sameStartDifference V δ y z).symm

lemma iteratedIntegral_sameStartDifference_eq_bias
    (V : FirstOrderPotential d) (δ : ℝ) (hδ : 0 ≤ δ) (y : State d) :
    (∫ z : State d,
      (∫ u : Set.Icc (0 : ℝ) 1,
        explicitEulerUpdate V δ y z -
          explicitRWMRejectionUniformUpdate V δ y (z, u) ∂volume)
      ∂stdGaussian (State d)) =
      ∫ z : State d, V.scaledRWMRejectionExpansionError δ y z
        ∂stdGaussian (State d) := by
  rw [integral_congr_ae (ae_of_all _ fun z =>
      integral_unit_sameStartDifference V δ y z),
    integral_sub (V.integrable_scaledRWMRejectionDisplacement δ y)
      (integrable_const _), integral_const,
    V.integral_scaledRWMRejectionDisplacement_eq δ hδ y]
  simp

lemma integrable_unit_sameStartDifference_sq
    (V : FirstOrderPotential d) (δ : ℝ) (y z : State d) :
    Integrable (fun u : Set.Icc (0 : ℝ) 1 =>
      ‖explicitEulerUpdate V δ y z -
        explicitRWMRejectionUniformUpdate V δ y (z, u)‖ ^ 2) := by
  let B : Set.Icc (0 : ℝ) 1 → State d := fun u =>
    explicitEulerUpdate V δ y z -
      explicitRWMRejectionUniformUpdate V δ y (z, u)
  have hBmeas : Measurable B := by
    exact measurable_const.sub
      ((measurable_explicitRWMRejectionUniformUpdate V δ y).comp
        (measurable_const.prodMk measurable_id))
  let C : ℝ :=
    (‖Real.sqrt (2 * δ) • z‖ + ‖δ • V.gradU y‖) ^ 2
  apply Integrable.of_bound (hBmeas.norm.pow_const 2).aestronglyMeasurable C
  exact ae_of_all _ fun u => by
    have hnorm : ‖B u‖ ≤
        ‖V.bernoulliRWMRejectedIncrement δ y z u‖ +
          ‖δ • V.gradU y‖ := by
      dsimp [B]
      rw [explicitEulerUpdate_sub_explicitRWMRejectionUniformUpdate]
      exact norm_sub_le _ _
    have hR : ‖V.bernoulliRWMRejectedIncrement δ y z u‖ ≤
        ‖Real.sqrt (2 * δ) • z‖ := by
      change ‖thresholdConst
          (rejectionProfile
            (V.rwmEnergyIncrement y (Real.sqrt (2 * δ) • z)))
          (Real.sqrt (2 * δ) • z) u‖ ≤ ‖Real.sqrt (2 * δ) • z‖
      unfold thresholdConst
      split <;> simp
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 (hnorm.trans
        (add_le_add hR le_rfl))

lemma integral_unit_pair_difference_sq_eq
    (V : FirstOrderPotential d) (δ : ℝ) (x y z : State d) :
    (∫ u : Set.Icc (0 : ℝ) 1,
      ‖explicitEulerUpdate V δ x z -
        explicitRWMRejectionUniformUpdate V δ y (z, u)‖ ^ 2 ∂volume) =
      ‖eulerMeanDifference V δ x y‖ ^ 2 +
        2 * @inner ℝ (State d) _ (eulerMeanDifference V δ x y)
          (∫ u : Set.Icc (0 : ℝ) 1,
            explicitEulerUpdate V δ y z -
              explicitRWMRejectionUniformUpdate V δ y (z, u) ∂volume) +
        (∫ u : Set.Icc (0 : ℝ) 1,
          ‖explicitEulerUpdate V δ y z -
            explicitRWMRejectionUniformUpdate V δ y (z, u)‖ ^ 2 ∂volume) := by
  let A := eulerMeanDifference V δ x y
  let B : Set.Icc (0 : ℝ) 1 → State d := fun u =>
    explicitEulerUpdate V δ y z -
      explicitRWMRejectionUniformUpdate V δ y (z, u)
  have hB := integrable_unit_sameStartDifference V δ y z
  have hBsq := integrable_unit_sameStartDifference_sq V δ y z
  have hcross : Integrable (fun u => 2 * @inner ℝ (State d) _ A (B u)) :=
    (hB.const_inner A).const_mul 2
  calc
    (∫ u : Set.Icc (0 : ℝ) 1,
      ‖explicitEulerUpdate V δ x z -
        explicitRWMRejectionUniformUpdate V δ y (z, u)‖ ^ 2 ∂volume) =
      ∫ u : Set.Icc (0 : ℝ) 1,
        (‖A‖ ^ 2 + 2 * @inner ℝ (State d) _ A (B u)) + ‖B u‖ ^ 2
        ∂volume := by
      apply integral_congr_ae
      exact ae_of_all _ fun u => by
        change ‖explicitEulerUpdate V δ x z -
            explicitRWMRejectionUniformUpdate V δ y (z, u)‖ ^ 2 =
          ‖A‖ ^ 2 + 2 * @inner ℝ (State d) _ A (B u) + ‖B u‖ ^ 2
        rw [pair_difference_decomposition]
        exact norm_add_sq_real _ _
    _ = (∫ _u : Set.Icc (0 : ℝ) 1,
          ‖A‖ ^ 2 + 2 * @inner ℝ (State d) _ A (B _u) ∂volume) +
        ∫ u : Set.Icc (0 : ℝ) 1, ‖B u‖ ^ 2 ∂volume :=
      integral_add ((integrable_const _).add hcross) hBsq
    _ = ((∫ _u : Set.Icc (0 : ℝ) 1, ‖A‖ ^ 2 ∂volume) +
          ∫ u : Set.Icc (0 : ℝ) 1,
            2 * @inner ℝ (State d) _ A (B u) ∂volume) +
        ∫ u : Set.Icc (0 : ℝ) 1, ‖B u‖ ^ 2 ∂volume := by
      rw [integral_add (integrable_const _) hcross]
    _ = _ := by
      rw [integral_const, integral_const_mul, integral_inner hB]
      have hvol : (volume : Measure (Set.Icc (0 : ℝ) 1)).real Set.univ = 1 := by
        rw [MeasureTheory.measureReal_def]
        simp
      rw [hvol, one_smul]

theorem iteratedIntegral_pair_difference_sq_eq
    (V : FirstOrderPotential d) (δ : ℝ) (hδ : 0 ≤ δ)
    (x y : State d) :
    (∫ z : State d,
      (∫ u : Set.Icc (0 : ℝ) 1,
        ‖explicitEulerUpdate V δ x z -
          explicitRWMRejectionUniformUpdate V δ y (z, u)‖ ^ 2 ∂volume)
      ∂stdGaussian (State d)) =
      ‖eulerMeanDifference V δ x y‖ ^ 2 +
        2 * @inner ℝ (State d) _ (eulerMeanDifference V δ x y)
          (∫ z : State d, V.scaledRWMRejectionExpansionError δ y z
            ∂stdGaussian (State d)) +
        (∫ z : State d,
          (∫ u : Set.Icc (0 : ℝ) 1,
            ‖explicitEulerUpdate V δ y z -
              explicitRWMRejectionUniformUpdate V δ y (z, u)‖ ^ 2 ∂volume)
          ∂stdGaussian (State d)) := by
  let A := eulerMeanDifference V δ x y
  let D : State d → State d := fun z =>
    ∫ u : Set.Icc (0 : ℝ) 1,
      explicitEulerUpdate V δ y z -
        explicitRWMRejectionUniformUpdate V δ y (z, u) ∂volume
  let S : State d → ℝ := fun z =>
    ∫ u : Set.Icc (0 : ℝ) 1,
      ‖explicitEulerUpdate V δ y z -
        explicitRWMRejectionUniformUpdate V δ y (z, u)‖ ^ 2 ∂volume
  let T : State d → ℝ := fun z =>
    ∫ u : Set.Icc (0 : ℝ) 1,
      ‖explicitEulerUpdate V δ x z -
        explicitRWMRejectionUniformUpdate V δ y (z, u)‖ ^ 2 ∂volume
  have hDint : Integrable D (stdGaussian (State d)) :=
    integrable_gaussian_integral_unit_sameStartDifference V δ y
  have hSint : Integrable S (stdGaussian (State d)) :=
    integrable_gaussian_sameStart_sq V δ y
  have hcross : Integrable
      (fun z => 2 * @inner ℝ (State d) _ A (D z))
      (stdGaussian (State d)) := (hDint.const_inner A).const_mul 2
  have hcond : ∀ z, T z =
      (‖A‖ ^ 2 + 2 * @inner ℝ (State d) _ A (D z)) + S z := by
    intro z
    exact integral_unit_pair_difference_sq_eq V δ x y z
  have hT : Integrable T (stdGaussian (State d)) := by
    exact (((integrable_const _).add hcross).add hSint).congr
      (ae_of_all _ fun z => (hcond z).symm)
  have hDmean :
      (∫ z : State d, D z ∂stdGaussian (State d)) =
        ∫ z : State d, V.scaledRWMRejectionExpansionError δ y z
          ∂stdGaussian (State d) :=
    iteratedIntegral_sameStartDifference_eq_bias V δ hδ y
  calc
    (∫ z : State d,
      (∫ u : Set.Icc (0 : ℝ) 1,
        ‖explicitEulerUpdate V δ x z -
          explicitRWMRejectionUniformUpdate V δ y (z, u)‖ ^ 2 ∂volume)
      ∂stdGaussian (State d)) = ∫ z, T z ∂stdGaussian (State d) := rfl
    _ = ∫ z : State d,
        ((‖A‖ ^ 2 + 2 * @inner ℝ (State d) _ A (D z)) + S z)
        ∂stdGaussian (State d) := by
      exact integral_congr_ae (ae_of_all _ hcond)
    _ = (∫ z : State d,
          ‖A‖ ^ 2 + 2 * @inner ℝ (State d) _ A (D z)
          ∂stdGaussian (State d)) +
        ∫ z : State d, S z ∂stdGaussian (State d) :=
      integral_add ((integrable_const _).add hcross) hSint
    _ = ((∫ _z : State d, ‖A‖ ^ 2 ∂stdGaussian (State d)) +
          ∫ z : State d, 2 * @inner ℝ (State d) _ A (D z)
            ∂stdGaussian (State d)) +
        ∫ z : State d, S z ∂stdGaussian (State d) := by
      rw [integral_add (integrable_const _) hcross]
    _ = _ := by
      rw [integral_const, integral_const_mul, integral_inner hDint,
        hDmean]
      have hgauss : (stdGaussian (State d)).real Set.univ = 1 := by
        rw [MeasureTheory.measureReal_def]
        simp
      rw [hgauss, one_smul]

def pointwiseRWMRejectionBiasConstant
    (V : FirstOrderPotential d) (y : State d) : ℝ :=
  ((V.L / 2) + 2 * ‖V.gradU y‖ ^ 2) * gaussianNormMoment d 3 +
    4 * (V.L / 2) ^ 2 * gaussianNormMoment d 5

lemma two_mul_le_epsilon_sq_add_sq_div
    (a b ε : ℝ) (hε : 0 < ε) :
    2 * a * b ≤ ε * a ^ 2 + b ^ 2 / ε := by
  rw [show ε * a ^ 2 + b ^ 2 / ε =
      (ε ^ 2 * a ^ 2 + b ^ 2) / ε by field_simp]
  rw [le_div_iff₀ hε]
  nlinarith [sq_nonneg (ε * a - b)]

theorem iteratedIntegral_pair_difference_sq_epsilon_le
    (V : FirstOrderPotential d) (δ ε : ℝ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hδL : δ ≤ 2 / V.L)
    (hε : 0 < ε) (x y : State d) :
    (∫ z : State d,
      (∫ u : Set.Icc (0 : ℝ) 1,
        ‖explicitEulerUpdate V δ x z -
          explicitRWMRejectionUniformUpdate V δ y (z, u)‖ ^ 2 ∂volume)
      ∂stdGaussian (State d)) ≤
      (1 + ε) * ‖x - y‖ ^ 2 +
        (Real.sqrt (2 * δ)) ^ 3 * pointwiseEulerRWMCouplingConstant V y +
        2 * δ ^ 2 * ‖V.gradU y‖ ^ 2 +
        ((Real.sqrt (2 * δ)) ^ 3 *
          pointwiseRWMRejectionBiasConstant V y) ^ 2 / ε := by
  let A := eulerMeanDifference V δ x y
  let E : State d :=
    ∫ z : State d, V.scaledRWMRejectionExpansionError δ y z
      ∂stdGaussian (State d)
  let S : ℝ :=
    ∫ z : State d,
      (∫ u : Set.Icc (0 : ℝ) 1,
        ‖explicitEulerUpdate V δ y z -
          explicitRWMRejectionUniformUpdate V δ y (z, u)‖ ^ 2 ∂volume)
      ∂stdGaussian (State d)
  let B : ℝ := (Real.sqrt (2 * δ)) ^ 3 *
    pointwiseRWMRejectionBiasConstant V y
  have hexact := iteratedIntegral_pair_difference_sq_eq V δ hδ x y
  have hA : ‖A‖ ≤ ‖x - y‖ := norm_eulerMeanDifference_le V δ hδ hδL x y
  have hE : ‖E‖ ≤ B := by
    have h := V.norm_integral_scaledRWMRejectionExpansionError_le δ hδ hδ1 y
    simpa only [E, B, pointwiseRWMRejectionBiasConstant,
      gaussianNormMoment] using h
  have hB0 : 0 ≤ B := (norm_nonneg E).trans hE
  have hcross :
      @inner ℝ (State d) _ A E ≤ ‖x - y‖ * B := by
    calc
      @inner ℝ (State d) _ A E ≤ ‖A‖ * ‖E‖ := real_inner_le_norm A E
      _ ≤ ‖x - y‖ * B := mul_le_mul hA hE (norm_nonneg E) (norm_nonneg _)
  have hS := iteratedIntegral_norm_explicitEuler_sub_rwm_sq_pointwise_le
    V δ hδ hδ1 y
  have hyoung := two_mul_le_epsilon_sq_add_sq_div ‖x - y‖ B ε hε
  calc
    (∫ z : State d,
      (∫ u : Set.Icc (0 : ℝ) 1,
        ‖explicitEulerUpdate V δ x z -
          explicitRWMRejectionUniformUpdate V δ y (z, u)‖ ^ 2 ∂volume)
      ∂stdGaussian (State d)) =
        ‖A‖ ^ 2 + 2 * @inner ℝ (State d) _ A E + S := hexact
    _ ≤ ‖x - y‖ ^ 2 + 2 * (‖x - y‖ * B) + S := by
      have hAsq := (sq_le_sq₀ (norm_nonneg A) (norm_nonneg _)).2 hA
      nlinarith
    _ ≤ ‖x - y‖ ^ 2 + 2 * (‖x - y‖ * B) +
        ((Real.sqrt (2 * δ)) ^ 3 * pointwiseEulerRWMCouplingConstant V y +
          2 * δ ^ 2 * ‖V.gradU y‖ ^ 2) := by
      nlinarith
    _ ≤ (1 + ε) * ‖x - y‖ ^ 2 +
        (Real.sqrt (2 * δ)) ^ 3 * pointwiseEulerRWMCouplingConstant V y +
        2 * δ ^ 2 * ‖V.gradU y‖ ^ 2 + B ^ 2 / ε := by
      nlinarith
    _ = _ := rfl

theorem iteratedIntegral_pair_difference_sq_delta_le
    (V : FirstOrderPotential d) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδL : δ ≤ 2 / V.L)
    (x y : State d) :
    (∫ z : State d,
      (∫ u : Set.Icc (0 : ℝ) 1,
        ‖explicitEulerUpdate V δ x z -
          explicitRWMRejectionUniformUpdate V δ y (z, u)‖ ^ 2 ∂volume)
      ∂stdGaussian (State d)) ≤
      (1 + δ) * ‖x - y‖ ^ 2 +
        (Real.sqrt (2 * δ)) ^ 3 * pointwiseEulerRWMCouplingConstant V y +
        δ ^ 2 * (2 * ‖V.gradU y‖ ^ 2 +
          8 * (pointwiseRWMRejectionBiasConstant V y) ^ 2) := by
  have h := iteratedIntegral_pair_difference_sq_epsilon_le
    V δ δ hδ.le hδ1 hδL hδ x y
  calc
    _ ≤ (1 + δ) * ‖x - y‖ ^ 2 +
        (Real.sqrt (2 * δ)) ^ 3 * pointwiseEulerRWMCouplingConstant V y +
        2 * δ ^ 2 * ‖V.gradU y‖ ^ 2 +
        ((Real.sqrt (2 * δ)) ^ 3 *
          pointwiseRWMRejectionBiasConstant V y) ^ 2 / δ := h
    _ = _ := by
      have hsqrt : (Real.sqrt (2 * δ)) ^ 2 = 2 * δ := by
        rw [Real.sq_sqrt]
        positivity
      have hsqrt6 : (Real.sqrt (2 * δ)) ^ 6 = 8 * δ ^ 3 := by
        calc
          (Real.sqrt (2 * δ)) ^ 6 =
              ((Real.sqrt (2 * δ)) ^ 2) ^ 3 := by ring
          _ = (2 * δ) ^ 3 := by rw [hsqrt]
          _ = 8 * δ ^ 3 := by ring
      field_simp [ne_of_gt hδ]
      rw [show (Real.sqrt (δ * 2)) ^ 6 = 8 * δ ^ 3 by
        simpa [mul_comm] using hsqrt6]
      ring

lemma integrable_pointwiseRWMRejectionBiasConstant_sq
    (V : FirstOrderPotential d) :
    Integrable (fun y : State d =>
      (pointwiseRWMRejectionBiasConstant V y) ^ 2)
      (V.target : Measure (State d)) := by
  let M3 := gaussianNormMoment d 3
  let M5 := gaussianNormMoment d 5
  let c0 : ℝ := (V.L / 2) * M3 + 4 * (V.L / 2) ^ 2 * M5
  let c2 : ℝ := 2 * M3
  have h2 := integrable_target_gradU_norm_sq V
  have h4 := V.integrable_gradU_norm_fourth
  have hpoly : Integrable (fun y : State d =>
      c0 ^ 2 + (2 * c0 * c2) * ‖V.gradU y‖ ^ 2 +
        c2 ^ 2 * ‖V.gradU y‖ ^ 4)
      (V.target : Measure (State d)) :=
    ((integrable_const _).add (h2.const_mul (2 * c0 * c2))).add
      (h4.const_mul (c2 ^ 2))
  apply hpoly.congr
  exact ae_of_all _ fun y => by
    dsimp [pointwiseRWMRejectionBiasConstant,
      gaussianNormMoment, M3, M5, c0, c2]
    ring

def stationaryRWMRejectionBiasSqConstant
    (V : FirstOrderPotential d) : ℝ :=
  ∫ y : State d, (pointwiseRWMRejectionBiasConstant V y) ^ 2
    ∂(V.target : Measure (State d))

def pointwiseEulerRWMRecurrenceError
    (V : FirstOrderPotential d) (δ : ℝ) (y : State d) : ℝ :=
  (Real.sqrt (2 * δ)) ^ 3 * pointwiseEulerRWMCouplingConstant V y +
    δ ^ 2 * (2 * ‖V.gradU y‖ ^ 2 +
      8 * (pointwiseRWMRejectionBiasConstant V y) ^ 2)

def stationaryEulerRWMRecurrenceError
    (V : FirstOrderPotential d) (δ : ℝ) : ℝ :=
  (Real.sqrt (2 * δ)) ^ 3 * stationaryEulerRWMCouplingConstant V +
    δ ^ 2 * (2 * targetGradNormMoment V 2 +
      8 * stationaryRWMRejectionBiasSqConstant V)

lemma integrable_pointwiseEulerRWMRecurrenceError
    (V : FirstOrderPotential d) (δ : ℝ) :
    Integrable (pointwiseEulerRWMRecurrenceError V δ)
      (V.target : Measure (State d)) := by
  exact (integrable_pointwiseEulerRWMCouplingConstant V |>.const_mul
      ((Real.sqrt (2 * δ)) ^ 3)).add
    (((integrable_target_gradU_norm_sq V |>.const_mul 2).add
      (integrable_pointwiseRWMRejectionBiasConstant_sq V |>.const_mul 8)).const_mul
        (δ ^ 2))

lemma integral_pointwiseEulerRWMRecurrenceError
    (V : FirstOrderPotential d) (δ : ℝ) :
    (∫ y : State d, pointwiseEulerRWMRecurrenceError V δ y
      ∂(V.target : Measure (State d))) =
      stationaryEulerRWMRecurrenceError V δ := by
  have hC := integrable_pointwiseEulerRWMCouplingConstant V
  have h2 := integrable_target_gradU_norm_sq V
  have hB := integrable_pointwiseRWMRejectionBiasConstant_sq V
  unfold pointwiseEulerRWMRecurrenceError
    stationaryEulerRWMRecurrenceError
    stationaryRWMRejectionBiasSqConstant targetGradNormMoment
  calc
    _ = (∫ y : State d,
          (Real.sqrt (2 * δ)) ^ 3 * pointwiseEulerRWMCouplingConstant V y
          ∂(V.target : Measure (State d))) +
        ∫ y : State d, δ ^ 2 *
          (2 * ‖V.gradU y‖ ^ 2 +
            8 * pointwiseRWMRejectionBiasConstant V y ^ 2)
          ∂(V.target : Measure (State d)) :=
      integral_add (hC.const_mul _) (((h2.const_mul 2).add
        (hB.const_mul 8)).const_mul (δ ^ 2))
    _ = (Real.sqrt (2 * δ)) ^ 3 *
          (∫ y : State d, pointwiseEulerRWMCouplingConstant V y
            ∂(V.target : Measure (State d))) +
        δ ^ 2 * (∫ y : State d,
          (2 * ‖V.gradU y‖ ^ 2 +
            8 * pointwiseRWMRejectionBiasConstant V y ^ 2)
          ∂(V.target : Measure (State d))) := by
      rw [integral_const_mul, integral_const_mul]
    _ = (Real.sqrt (2 * δ)) ^ 3 *
          (∫ y : State d, pointwiseEulerRWMCouplingConstant V y
            ∂(V.target : Measure (State d))) +
        δ ^ 2 * ((∫ y : State d, 2 * ‖V.gradU y‖ ^ 2
            ∂(V.target : Measure (State d))) +
          ∫ y : State d, 8 * pointwiseRWMRejectionBiasConstant V y ^ 2
            ∂(V.target : Measure (State d))) := by
      rw [integral_add (h2.const_mul 2) (hB.const_mul 8)]
    _ = _ := by
      rw [integral_pointwiseEulerRWMCouplingConstant,
        integral_const_mul, integral_const_mul]

def pairSquaredDistance (xy : State d × State d) : ℝ :=
  ‖xy.1 - xy.2‖ ^ 2

def pairOneStepSquaredDistance
    (V : FirstOrderPotential d) (δ : ℝ) (xy : State d × State d) : ℝ :=
  ∫ z : State d,
    (∫ u : Set.Icc (0 : ℝ) 1,
      ‖explicitEulerUpdate V δ xy.1 z -
        explicitRWMRejectionUniformUpdate V δ xy.2 (z, u)‖ ^ 2 ∂volume)
    ∂stdGaussian (State d)

lemma measurable_pairSquaredDistance :
    Measurable (pairSquaredDistance : State d × State d → ℝ) := by
  exact (measurable_fst.sub measurable_snd).norm.pow_const 2

lemma measurable_pairOneStepSquaredDistance
    (V : FirstOrderPotential d) (δ : ℝ) :
    Measurable (pairOneStepSquaredDistance V δ) := by
  let H : ((State d × State d) × State d) × Set.Icc (0 : ℝ) 1 → ℝ := fun p =>
    ‖explicitEulerUpdate V δ p.1.1.1 p.1.2 -
      explicitRWMRejectionUniformUpdate V δ p.1.1.2 (p.1.2, p.2)‖ ^ 2
  let xyzu : ((State d × State d) × State d) × Set.Icc (0 : ℝ) 1 →
      (State d × State d) × (State d × Set.Icc (0 : ℝ) 1) :=
    fun p => (p.1.1, (p.1.2, p.2))
  have hxyzu : Measurable xyzu :=
    (measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hupdate : Measurable (fun p => eulerRWMPairUpdate V δ p.1.1
      (p.1.2, p.2) : ((State d × State d) × State d) ×
        Set.Icc (0 : ℝ) 1 → State d × State d) :=
    (measurable_uncurry_eulerRWMPairUpdate V δ).comp hxyzu
  have hH : Measurable H :=
    ((measurable_fst.comp hupdate).sub
      (measurable_snd.comp hupdate)).norm.pow_const 2
  have hinner : Measurable (fun p : (State d × State d) × State d =>
      ∫ u : Set.Icc (0 : ℝ) 1, H (p, u) ∂volume) :=
    hH.stronglyMeasurable.integral_prod_right'.measurable
  exact hinner.stronglyMeasurable.integral_prod_right'.measurable

theorem integral_pairOneStepSquaredDistance_le
    (V : FirstOrderPotential d) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδL : δ ≤ 2 / V.L)
    (μ : Measure (State d × State d)) [IsProbabilityMeasure μ]
    (henergy : Integrable pairSquaredDistance μ)
    (hsnd : Measure.map Prod.snd μ = (V.target : Measure (State d))) :
    (∫ xy : State d × State d,
      pairOneStepSquaredDistance V δ xy ∂μ) ≤
      (1 + δ) * (∫ xy : State d × State d,
        pairSquaredDistance xy ∂μ) +
        stationaryEulerRWMRecurrenceError V δ := by
  let f := pairOneStepSquaredDistance V δ
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
  have hfmeas : Measurable f :=
    measurable_pairOneStepSquaredDistance V δ
  have hfint : Integrable f μ := by
    apply hgint.mono hfmeas.aestronglyMeasurable
    exact ae_of_all _ fun xy => by
      have hle := iteratedIntegral_pair_difference_sq_delta_le
        V δ hδ hδ1 hδL xy.1 xy.2
      have hf0 : 0 ≤ f xy := by
        dsimp [f, pairOneStepSquaredDistance]
        exact integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
      have hg0 : 0 ≤ g xy := by
        apply hf0.trans
        dsimp [f, g, pairSquaredDistance,
          pairOneStepSquaredDistance,
          pointwiseEulerRWMRecurrenceError]
        nlinarith
      rw [Real.norm_eq_abs, abs_of_nonneg hf0,
        Real.norm_eq_abs, abs_of_nonneg hg0]
      dsimp [f, g, pairSquaredDistance,
        pairOneStepSquaredDistance,
        pointwiseEulerRWMRecurrenceError]
      nlinarith
  have hlocalIntegral :
      (∫ xy : State d × State d,
        pointwiseEulerRWMRecurrenceError V δ xy.2 ∂μ) =
        stationaryEulerRWMRecurrenceError V δ := by
    have hmap := integral_map measurable_snd.aemeasurable
      hlocalMap.aestronglyMeasurable
    rw [hsnd, integral_pointwiseEulerRWMRecurrenceError] at hmap
    exact hmap.symm
  calc
    (∫ xy : State d × State d,
      pairOneStepSquaredDistance V δ xy ∂μ) = ∫ xy, f xy ∂μ := rfl
    _ ≤ ∫ xy, g xy ∂μ := by
      apply integral_mono hfint hgint
      intro xy
      have hle := iteratedIntegral_pair_difference_sq_delta_le
        V δ hδ hδ1 hδL xy.1 xy.2
      dsimp [f, g, pairSquaredDistance,
        pairOneStepSquaredDistance,
        pointwiseEulerRWMRecurrenceError]
      nlinarith
    _ = (1 + δ) * (∫ xy : State d × State d,
        pairSquaredDistance xy ∂μ) +
        stationaryEulerRWMRecurrenceError V δ := by
      dsimp [g]
      rw [integral_add (henergy.const_mul (1 + δ)) hlocalμ,
        integral_const_mul, hlocalIntegral]

end DiscreteTime
end
end UniformRandomMALA
