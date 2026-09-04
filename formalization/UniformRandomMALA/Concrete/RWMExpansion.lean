import UniformRandomMALA.Concrete.EuclideanTarget
import UniformRandomMALA.DiscreteTime.Acceptance
import UniformRandomMALA.DiscreteTime.AcceptanceExpansion
import UniformRandomMALA.DiscreteTime.BernoulliUniform
import UniformRandomMALA.DiscreteTime.GaussianPositivePart

/-!
# One elementary RWM rejection displacement

This file connects the scalar Metropolis expansion and the exact Gaussian
positive-part identity to the concrete strongly convex potential.  It is the
one-step analytic core of the fully discrete Euler/RWM endpoint coupling.

For `s = sqrt (2 δ) Z`, the rejected RWM displacement is decomposed as

`E[rejection(U(x+s)-U(x)) s] = δ ∇U(x) + E[error]`.

The error is an explicit finite-dimensional Gaussian integral and has a
pointwise polynomial bound.  No filtration, SDE, or diffusion approximation
is involved.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace

noncomputable section

namespace Concrete

namespace FirstOrderPotential

variable {d : ℕ} (V : FirstOrderPotential d)

/-- Exact energy increment for a displacement `s`. -/
def rwmEnergyIncrement (x s : State d) : ℝ :=
  V.U (x + s) - V.U x

/-- First-order energy increment at `x`. -/
def rwmLinearIncrement (x s : State d) : ℝ :=
  ⟪V.gradU x, s⟫

/-- Rejected part of an RWM proposal displacement. -/
def rwmRejectionDisplacement (x s : State d) : State d :=
  DiscreteTime.rejectionProfile (V.rwmEnergyIncrement x s) • s

/-- Positive-part first-order approximation to the rejected displacement. -/
def rwmLinearRejectionDisplacement (x s : State d) : State d :=
  max (V.rwmLinearIncrement x s) 0 • s

/-- Error after subtracting the first-order rejected displacement. -/
def rwmRejectionExpansionError (x s : State d) : State d :=
  V.rwmRejectionDisplacement x s - V.rwmLinearRejectionDisplacement x s

/-- Convexity and `L`-smoothness sandwich the energy remainder. -/
theorem rwmEnergyRemainder_bounds (x s : State d) :
    0 ≤ V.rwmEnergyIncrement x s - V.rwmLinearIncrement x s ∧
      V.rwmEnergyIncrement x s - V.rwmLinearIncrement x s ≤
        (V.L / 2) * ‖s‖ ^ 2 := by
  have hlo := V.lowerTaylor x (x + s)
  have hup := V.upperTaylor x (x + s)
  simp only [add_sub_cancel_left] at hlo hup
  constructor
  · have hmterm : 0 ≤ (V.m / 2) * ‖s‖ ^ 2 :=
      mul_nonneg (div_nonneg V.hm.le (by norm_num)) (sq_nonneg _)
    unfold rwmEnergyIncrement rwmLinearIncrement
    linarith
  · unfold rwmEnergyIncrement rwmLinearIncrement
    linarith

/-- Absolute form of the smooth energy remainder. -/
theorem abs_rwmEnergyRemainder_le (x s : State d) :
    |V.rwmEnergyIncrement x s - V.rwmLinearIncrement x s| ≤
      (V.L / 2) * ‖s‖ ^ 2 := by
  rw [abs_of_nonneg (V.rwmEnergyRemainder_bounds x s).1]
  exact (V.rwmEnergyRemainder_bounds x s).2

/-- Concrete pointwise Metropolis expansion. -/
theorem abs_rwmRejectionWeight_sub_linear_le (x s : State d) :
    |DiscreteTime.rejectionProfile (V.rwmEnergyIncrement x s) -
        max (V.rwmLinearIncrement x s) 0| ≤
      (V.L / 2) * ‖s‖ ^ 2 +
        (|V.rwmLinearIncrement x s| + (V.L / 2) * ‖s‖ ^ 2) ^ 2 := by
  exact DiscreteTime.abs_rejectionProfile_sub_posPart_le_of_abs_sub_le
    (V.rwmEnergyIncrement x s) (V.rwmLinearIncrement x s)
    ((V.L / 2) * ‖s‖ ^ 2)
    (mul_nonneg (div_nonneg V.hL.le (by norm_num)) (sq_nonneg _))
    (V.abs_rwmEnergyRemainder_le x s)

/-- Vector form of the one-step error bound. -/
theorem norm_rwmRejectionExpansionError_le (x s : State d) :
    ‖V.rwmRejectionExpansionError x s‖ ≤
      ((V.L / 2) * ‖s‖ ^ 2 +
        (|V.rwmLinearIncrement x s| + (V.L / 2) * ‖s‖ ^ 2) ^ 2) * ‖s‖ := by
  rw [rwmRejectionExpansionError, rwmRejectionDisplacement,
    rwmLinearRejectionDisplacement, ← sub_smul, norm_smul,
    Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right
    (V.abs_rwmRejectionWeight_sub_linear_le x s) (norm_nonneg _)

/-- RWM rejected displacement as a function of one standard Gaussian
innovation. -/
def scaledRWMRejectionDisplacement
    (δ : ℝ) (x : State d) (z : State d) : State d :=
  V.rwmRejectionDisplacement x (Real.sqrt (2 * δ) • z)

/-- Linearized rejected displacement as a function of the same innovation. -/
def scaledRWMLinearRejectionDisplacement
    (δ : ℝ) (x : State d) (z : State d) : State d :=
  V.rwmLinearRejectionDisplacement x (Real.sqrt (2 * δ) • z)

/-- Expansion error driven by the same innovation. -/
def scaledRWMRejectionExpansionError
    (δ : ℝ) (x : State d) (z : State d) : State d :=
  V.rwmRejectionExpansionError x (Real.sqrt (2 * δ) • z)

theorem integrable_scaledRWMRejectionDisplacement
    (δ : ℝ) (x : State d) :
    Integrable (V.scaledRWMRejectionDisplacement δ x)
      (stdGaussian (State d)) := by
  let a : ℝ := Real.sqrt (2 * δ)
  have hinc : Integrable (fun z : State d => a • z)
      (stdGaussian (State d)) := IsGaussian.integrable_id.smul a
  have hcont : Continuous (V.scaledRWMRejectionDisplacement δ x) := by
    change Continuous (fun z : State d =>
      DiscreteTime.rejectionProfile (V.U (x + a • z) - V.U x) • (a • z))
    have hs : Continuous (fun z : State d => a • z) :=
      continuous_id.const_smul a
    have hu : Continuous (fun z : State d => V.U (x + a • z) - V.U x) :=
      (V.continuous_U.comp (continuous_const.add hs)).sub continuous_const
    exact (DiscreteTime.continuous_rejectionProfile.comp hu).smul hs
  apply hinc.mono hcont.aestronglyMeasurable
  exact ae_of_all _ fun z => by
    change ‖DiscreteTime.rejectionProfile
      (V.rwmEnergyIncrement x (a • z)) • (a • z)‖ ≤ ‖a • z‖
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (DiscreteTime.rejectionProfile_nonneg _)]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (DiscreteTime.rejectionProfile_le_one _)

theorem integrable_scaledRWMLinearRejectionDisplacement
    (δ : ℝ) (x : State d) :
    Integrable (V.scaledRWMLinearRejectionDisplacement δ x)
      (stdGaussian (State d)) := by
  let a : ℝ := Real.sqrt (2 * δ)
  let L : StrongDual ℝ (State d) := a • (toDualMap ℝ (State d) (V.gradU x))
  have hbase := DiscreteTime.integrable_gaussianPositivePart_smul L
  have hscaled : Integrable (fun z : State d => a • (max (L z) 0 • z))
      (stdGaussian (State d)) := hbase.smul a
  apply hscaled.congr
  exact ae_of_all _ fun z => by
    have hLz : L z = a * ⟪V.gradU x, z⟫ := by
      change (a • (toDualMap ℝ (State d) (V.gradU x)) :
        StrongDual ℝ (State d)) z = _
      rfl
    change a • (max (L z) 0 • z) =
      V.rwmLinearRejectionDisplacement x (a • z)
    rw [rwmLinearRejectionDisplacement, rwmLinearIncrement, hLz]
    simp only [inner_smul_right, smul_smul]
    congr 1
    ring

theorem integrable_scaledRWMRejectionExpansionError
    (δ : ℝ) (x : State d) :
    Integrable (V.scaledRWMRejectionExpansionError δ x)
      (stdGaussian (State d)) := by
  change Integrable (fun z =>
    V.scaledRWMRejectionDisplacement δ x z -
      V.scaledRWMLinearRejectionDisplacement δ x z)
    (stdGaussian (State d))
  exact (V.integrable_scaledRWMRejectionDisplacement δ x).sub
    (V.integrable_scaledRWMLinearRejectionDisplacement δ x)

/-- After scaling `s = sqrt (2 δ) z`, the expansion error is bounded by
`(sqrt (2 δ))³` times an integrable polynomial in `‖z‖`.  This is the
elementary `δ^(3/2)` estimate used in the coupling recursion. -/
theorem norm_scaledRWMRejectionExpansionError_le
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (x z : State d) :
    ‖V.scaledRWMRejectionExpansionError δ x z‖ ≤
      (Real.sqrt (2 * δ)) ^ 3 *
        (((V.L / 2) + 2 * ‖V.gradU x‖ ^ 2) * ‖z‖ ^ 3 +
          4 * (V.L / 2) ^ 2 * ‖z‖ ^ 5) := by
  let a : ℝ := Real.sqrt (2 * δ)
  let A : ℝ := V.L / 2
  let b : ℝ := ‖V.gradU x‖
  let r : ℝ := ‖z‖
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hA : 0 ≤ A := div_nonneg V.hL.le (by norm_num)
  have hb : 0 ≤ b := norm_nonneg _
  have hr : 0 ≤ r := norm_nonneg _
  have ha_sq : a ^ 2 = 2 * δ := by
    dsimp [a]
    rw [Real.sq_sqrt]
    positivity
  have ha2 : a ^ 2 ≤ 2 := by nlinarith
  have hnorm : ‖a • z‖ = a * r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
  have hq : |V.rwmLinearIncrement x (a • z)| ≤ b * (a * r) := by
    unfold rwmLinearIncrement
    calc
      |⟪V.gradU x, a • z⟫| ≤ ‖V.gradU x‖ * ‖a • z‖ :=
        abs_real_inner_le_norm _ _
      _ = b * (a * r) := by rw [hnorm]
  have hsum :
      |V.rwmLinearIncrement x (a • z)| + A * (a * r) ^ 2 ≤
        b * (a * r) + A * (a * r) ^ 2 := add_le_add hq le_rfl
  have hsq :
      (|V.rwmLinearIncrement x (a • z)| + A * (a * r) ^ 2) ^ 2 ≤
        (b * (a * r) + A * (a * r) ^ 2) ^ 2 := by
    exact (sq_le_sq₀ (by positivity) (by positivity)).2 hsum
  calc
    ‖V.scaledRWMRejectionExpansionError δ x z‖ =
        ‖V.rwmRejectionExpansionError x (a • z)‖ := rfl
    _ ≤ (A * ‖a • z‖ ^ 2 +
        (|V.rwmLinearIncrement x (a • z)| + A * ‖a • z‖ ^ 2) ^ 2) *
          ‖a • z‖ := V.norm_rwmRejectionExpansionError_le x (a • z)
    _ = (A * (a * r) ^ 2 +
        (|V.rwmLinearIncrement x (a • z)| + A * (a * r) ^ 2) ^ 2) *
          (a * r) := by rw [hnorm]
    _ ≤ (A * (a * r) ^ 2 +
        (b * (a * r) + A * (a * r) ^ 2) ^ 2) * (a * r) :=
      mul_le_mul_of_nonneg_right (add_le_add le_rfl hsq)
        (mul_nonneg ha hr)
    _ ≤ a ^ 3 *
        ((A + 2 * b ^ 2) * r ^ 3 + 4 * A ^ 2 * r ^ 5) :=
      DiscreteTime.scaled_rejection_polynomial_bound
        a A b r ha hA hb hr ha2

/-- Integrated one-step bias bound.  The two Gaussian norm moments are
finite constants depending only on the dimension. -/
theorem norm_integral_scaledRWMRejectionExpansionError_le
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (x : State d) :
    ‖∫ z, V.scaledRWMRejectionExpansionError δ x z
        ∂stdGaussian (State d)‖ ≤
      (Real.sqrt (2 * δ)) ^ 3 *
        (((V.L / 2) + 2 * ‖V.gradU x‖ ^ 2) *
            (∫ z : State d, ‖z‖ ^ 3 ∂stdGaussian (State d)) +
          4 * (V.L / 2) ^ 2 *
            (∫ z : State d, ‖z‖ ^ 5 ∂stdGaussian (State d))) := by
  let a : ℝ := Real.sqrt (2 * δ)
  let C3 : ℝ := (V.L / 2) + 2 * ‖V.gradU x‖ ^ 2
  let C5 : ℝ := 4 * (V.L / 2) ^ 2
  have h3 : Integrable (fun z : State d => ‖z‖ ^ 3)
      (stdGaussian (State d)) :=
    (IsGaussian.memLp_id (stdGaussian (State d)) 3 (by norm_num)).integrable_norm_pow
      (by norm_num)
  have h5 : Integrable (fun z : State d => ‖z‖ ^ 5)
      (stdGaussian (State d)) :=
    (IsGaussian.memLp_id (stdGaussian (State d)) 5 (by norm_num)).integrable_norm_pow
      (by norm_num)
  have hC3 : 0 ≤ C3 := by
    dsimp [C3]
    exact add_nonneg (div_nonneg V.hL.le (by norm_num)) (by positivity)
  have hC5 : 0 ≤ C5 := by dsimp [C5]; positivity
  have ha3 : 0 ≤ a ^ 3 := by dsimp [a]; positivity
  have hmajor : Integrable
      (fun z : State d => a ^ 3 * (C3 * ‖z‖ ^ 3 + C5 * ‖z‖ ^ 5))
      (stdGaussian (State d)) :=
    ((h3.const_mul C3).add (h5.const_mul C5)).const_mul (a ^ 3)
  have herr := V.integrable_scaledRWMRejectionExpansionError δ x
  calc
    ‖∫ z, V.scaledRWMRejectionExpansionError δ x z
        ∂stdGaussian (State d)‖ ≤
        ∫ z, ‖V.scaledRWMRejectionExpansionError δ x z‖
          ∂stdGaussian (State d) := norm_integral_le_integral_norm _
    _ ≤ ∫ z, a ^ 3 * (C3 * ‖z‖ ^ 3 + C5 * ‖z‖ ^ 5)
          ∂stdGaussian (State d) := by
      apply integral_mono_ae herr.norm hmajor
      exact ae_of_all _ fun z => by
        simpa only [a, C3, C5] using
          V.norm_scaledRWMRejectionExpansionError_le δ hδ hδ1 x z
    _ = a ^ 3 *
        (C3 * (∫ z : State d, ‖z‖ ^ 3 ∂stdGaussian (State d)) +
          C5 * (∫ z : State d, ‖z‖ ^ 5 ∂stdGaussian (State d))) := by
      rw [integral_const_mul, integral_add (h3.const_mul C3) (h5.const_mul C5),
        integral_const_mul, integral_const_mul]
    _ = (Real.sqrt (2 * δ)) ^ 3 *
        (((V.L / 2) + 2 * ‖V.gradU x‖ ^ 2) *
            (∫ z : State d, ‖z‖ ^ 3 ∂stdGaussian (State d)) +
          4 * (V.L / 2) ^ 2 *
            (∫ z : State d, ‖z‖ ^ 5 ∂stdGaussian (State d))) := rfl

/-- Conditional second-moment integrand of the Bernoulli rejected
displacement, after integrating out the acceptance uniform. -/
def scaledRWMRejectionSecondMomentIntegrand
    (δ : ℝ) (x : State d) (z : State d) : ℝ :=
  DiscreteTime.rejectionProfile
      (V.rwmEnergyIncrement x (Real.sqrt (2 * δ) • z)) *
    ‖Real.sqrt (2 * δ) • z‖ ^ 2

/-- Pointwise `δ^(3/2)` bound for the conditional second moment. -/
theorem scaledRWMRejectionSecondMomentIntegrand_le
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (x z : State d) :
    V.scaledRWMRejectionSecondMomentIntegrand δ x z ≤
      (Real.sqrt (2 * δ)) ^ 3 *
        (‖V.gradU x‖ * ‖z‖ ^ 3 +
          (2 * (V.L / 2) + 4 * ‖V.gradU x‖ ^ 2) * ‖z‖ ^ 4 +
          16 * (V.L / 2) ^ 2 * ‖z‖ ^ 6) := by
  let a : ℝ := Real.sqrt (2 * δ)
  let A : ℝ := V.L / 2
  let b : ℝ := ‖V.gradU x‖
  let r : ℝ := ‖z‖
  let q : ℝ := V.rwmLinearIncrement x (a • z)
  let u : ℝ := V.rwmEnergyIncrement x (a • z)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hA : 0 ≤ A := div_nonneg V.hL.le (by norm_num)
  have hb : 0 ≤ b := norm_nonneg _
  have hr : 0 ≤ r := norm_nonneg _
  have ha_sq : a ^ 2 = 2 * δ := by
    dsimp [a]
    rw [Real.sq_sqrt]
    positivity
  have ha_sq_le : a ^ 2 ≤ 2 := by nlinarith
  have ha2 : a ≤ 2 := by nlinarith [sq_nonneg (a - 2)]
  have hnorm : ‖a • z‖ = a * r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
  have hq : |q| ≤ b * (a * r) := by
    unfold q rwmLinearIncrement
    calc
      |⟪V.gradU x, a • z⟫| ≤ ‖V.gradU x‖ * ‖a • z‖ :=
        abs_real_inner_le_norm _ _
      _ = b * (a * r) := by rw [hnorm]
  have hqpos : max q 0 ≤ b * (a * r) := by
    calc
      max q 0 ≤ |q| := by
        by_cases hq0 : 0 ≤ q
        · simp [max_eq_left hq0, abs_of_nonneg hq0]
        · have hq0' : q ≤ 0 := le_of_not_ge hq0
          simp [max_eq_right hq0', abs_nonneg]
      _ ≤ b * (a * r) := hq
  have hsum : |q| + A * (a * r) ^ 2 ≤
      b * (a * r) + A * (a * r) ^ 2 := add_le_add hq le_rfl
  have hsq : (|q| + A * (a * r) ^ 2) ^ 2 ≤
      (b * (a * r) + A * (a * r) ^ 2) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hsum
  have herr : |DiscreteTime.rejectionProfile u - max q 0| ≤
      A * (a * r) ^ 2 + (|q| + A * (a * r) ^ 2) ^ 2 := by
    simpa only [u, q, A, hnorm] using
      V.abs_rwmRejectionWeight_sub_linear_le x (a • z)
  have hprof : DiscreteTime.rejectionProfile u ≤
      b * (a * r) + A * (a * r) ^ 2 +
        (b * (a * r) + A * (a * r) ^ 2) ^ 2 := by
    calc
      DiscreteTime.rejectionProfile u ≤
          max q 0 + |DiscreteTime.rejectionProfile u - max q 0| := by
        linarith [le_abs_self (DiscreteTime.rejectionProfile u - max q 0)]
      _ ≤ b * (a * r) +
          (A * (a * r) ^ 2 + (|q| + A * (a * r) ^ 2) ^ 2) :=
        add_le_add hqpos herr
      _ ≤ b * (a * r) + A * (a * r) ^ 2 +
          (b * (a * r) + A * (a * r) ^ 2) ^ 2 := by
        linarith
  calc
    V.scaledRWMRejectionSecondMomentIntegrand δ x z =
        DiscreteTime.rejectionProfile u * (a * r) ^ 2 := by
      rw [scaledRWMRejectionSecondMomentIntegrand, hnorm]
    _ ≤ (b * (a * r) + A * (a * r) ^ 2 +
        (b * (a * r) + A * (a * r) ^ 2) ^ 2) * (a * r) ^ 2 :=
      mul_le_mul_of_nonneg_right hprof (sq_nonneg _)
    _ ≤ a ^ 3 *
        (b * r ^ 3 + (2 * A + 4 * b ^ 2) * r ^ 4 +
          16 * A ^ 2 * r ^ 6) :=
      DiscreteTime.scaled_rejection_secondMoment_polynomial_bound
        a A b r ha ha2 hA hb hr

/-- Integrated conditional second-moment bound. -/
theorem integral_scaledRWMRejectionSecondMomentIntegrand_le
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (x : State d) :
    (∫ z, V.scaledRWMRejectionSecondMomentIntegrand δ x z
        ∂stdGaussian (State d)) ≤
      (Real.sqrt (2 * δ)) ^ 3 *
        (‖V.gradU x‖ *
            (∫ z : State d, ‖z‖ ^ 3 ∂stdGaussian (State d)) +
          (2 * (V.L / 2) + 4 * ‖V.gradU x‖ ^ 2) *
            (∫ z : State d, ‖z‖ ^ 4 ∂stdGaussian (State d)) +
          16 * (V.L / 2) ^ 2 *
            (∫ z : State d, ‖z‖ ^ 6 ∂stdGaussian (State d))) := by
  let a : ℝ := Real.sqrt (2 * δ)
  let C3 : ℝ := ‖V.gradU x‖
  let C4 : ℝ := 2 * (V.L / 2) + 4 * ‖V.gradU x‖ ^ 2
  let C6 : ℝ := 16 * (V.L / 2) ^ 2
  have h3 : Integrable (fun z : State d => ‖z‖ ^ 3)
      (stdGaussian (State d)) :=
    (IsGaussian.memLp_id (stdGaussian (State d)) 3 (by norm_num)).integrable_norm_pow
      (by norm_num)
  have h4 : Integrable (fun z : State d => ‖z‖ ^ 4)
      (stdGaussian (State d)) :=
    (IsGaussian.memLp_id (stdGaussian (State d)) 4 (by norm_num)).integrable_norm_pow
      (by norm_num)
  have h6 : Integrable (fun z : State d => ‖z‖ ^ 6)
      (stdGaussian (State d)) :=
    (IsGaussian.memLp_id (stdGaussian (State d)) 6 (by norm_num)).integrable_norm_pow
      (by norm_num)
  have hC3 : 0 ≤ C3 := by dsimp [C3]; positivity
  have hC4 : 0 ≤ C4 := by
    dsimp [C4]
    exact add_nonneg (mul_nonneg (by norm_num)
      (div_nonneg V.hL.le (by norm_num))) (by positivity)
  have hC6 : 0 ≤ C6 := by dsimp [C6]; positivity
  have ha3 : 0 ≤ a ^ 3 := by dsimp [a]; positivity
  have hmajor : Integrable (fun z : State d =>
      a ^ 3 * (C3 * ‖z‖ ^ 3 + C4 * ‖z‖ ^ 4 + C6 * ‖z‖ ^ 6))
      (stdGaussian (State d)) :=
    (((h3.const_mul C3).add (h4.const_mul C4)).add
      (h6.const_mul C6)).const_mul (a ^ 3)
  have hcont : Continuous
      (V.scaledRWMRejectionSecondMomentIntegrand δ x) := by
    change Continuous (fun z : State d =>
      DiscreteTime.rejectionProfile
          (V.U (x + a • z) - V.U x) * ‖a • z‖ ^ 2)
    have hs : Continuous (fun z : State d => a • z) :=
      continuous_id.const_smul a
    have hu : Continuous (fun z : State d => V.U (x + a • z) - V.U x) :=
      (V.continuous_U.comp (continuous_const.add hs)).sub continuous_const
    exact (DiscreteTime.continuous_rejectionProfile.comp hu).mul
      ((continuous_norm.comp hs).pow 2)
  have hint : Integrable (V.scaledRWMRejectionSecondMomentIntegrand δ x)
      (stdGaussian (State d)) := by
    apply hmajor.mono' hcont.aestronglyMeasurable
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · simpa only [a, C3, C4, C6] using
          V.scaledRWMRejectionSecondMomentIntegrand_le δ hδ hδ1 x z
      · unfold scaledRWMRejectionSecondMomentIntegrand
        exact mul_nonneg (DiscreteTime.rejectionProfile_nonneg _) (sq_nonneg _)
  have h34 :
      (∫ z : State d, C3 * ‖z‖ ^ 3 + C4 * ‖z‖ ^ 4
        ∂stdGaussian (State d)) =
        (∫ z : State d, C3 * ‖z‖ ^ 3 ∂stdGaussian (State d)) +
          ∫ z : State d, C4 * ‖z‖ ^ 4 ∂stdGaussian (State d) := by
    simpa only [Pi.add_apply] using
      integral_add (h3.const_mul C3) (h4.const_mul C4)
  have h346 :
      (∫ z : State d, C3 * ‖z‖ ^ 3 + C4 * ‖z‖ ^ 4 + C6 * ‖z‖ ^ 6
        ∂stdGaussian (State d)) =
        (∫ z : State d, C3 * ‖z‖ ^ 3 + C4 * ‖z‖ ^ 4
          ∂stdGaussian (State d)) +
          ∫ z : State d, C6 * ‖z‖ ^ 6 ∂stdGaussian (State d) := by
    simpa only [Pi.add_apply] using
      integral_add ((h3.const_mul C3).add (h4.const_mul C4))
        (h6.const_mul C6)
  calc
    (∫ z, V.scaledRWMRejectionSecondMomentIntegrand δ x z
        ∂stdGaussian (State d)) ≤
        ∫ z, a ^ 3 *
          (C3 * ‖z‖ ^ 3 + C4 * ‖z‖ ^ 4 + C6 * ‖z‖ ^ 6)
          ∂stdGaussian (State d) := by
      apply integral_mono_ae hint hmajor
      exact ae_of_all _ fun z => by
        simpa only [a, C3, C4, C6] using
          V.scaledRWMRejectionSecondMomentIntegrand_le δ hδ hδ1 x z
    _ = a ^ 3 *
        (C3 * (∫ z : State d, ‖z‖ ^ 3 ∂stdGaussian (State d)) +
          C4 * (∫ z : State d, ‖z‖ ^ 4 ∂stdGaussian (State d)) +
          C6 * (∫ z : State d, ‖z‖ ^ 6 ∂stdGaussian (State d))) := by
      rw [integral_const_mul, h346, h34,
        integral_const_mul, integral_const_mul, integral_const_mul]
    _ = (Real.sqrt (2 * δ)) ^ 3 *
        (‖V.gradU x‖ *
            (∫ z : State d, ‖z‖ ^ 3 ∂stdGaussian (State d)) +
          (2 * (V.L / 2) + 4 * ‖V.gradU x‖ ^ 2) *
            (∫ z : State d, ‖z‖ ^ 4 ∂stdGaussian (State d)) +
          16 * (V.L / 2) ^ 2 *
            (∫ z : State d, ‖z‖ ^ 6 ∂stdGaussian (State d))) := rfl

/-- Exact finite-dimensional one-step bias decomposition.  The leading
term is the Euler drift, and everything else is the explicit expansion
error. -/
theorem integral_scaledRWMRejectionDisplacement_eq
    (δ : ℝ) (hδ : 0 ≤ δ) (x : State d) :
    (∫ z, V.scaledRWMRejectionDisplacement δ x z
      ∂stdGaussian (State d)) =
      δ • V.gradU x +
        ∫ z, V.scaledRWMRejectionExpansionError δ x z
          ∂stdGaussian (State d) := by
  have hlin := V.integrable_scaledRWMLinearRejectionDisplacement δ x
  have herr := V.integrable_scaledRWMRejectionExpansionError δ x
  calc
    (∫ z, V.scaledRWMRejectionDisplacement δ x z
        ∂stdGaussian (State d)) =
        ∫ z, V.scaledRWMLinearRejectionDisplacement δ x z +
          V.scaledRWMRejectionExpansionError δ x z
          ∂stdGaussian (State d) := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        unfold scaledRWMRejectionDisplacement
          scaledRWMLinearRejectionDisplacement
          scaledRWMRejectionExpansionError rwmRejectionExpansionError
        abel
    _ = (∫ z, V.scaledRWMLinearRejectionDisplacement δ x z
          ∂stdGaussian (State d)) +
        ∫ z, V.scaledRWMRejectionExpansionError δ x z
          ∂stdGaussian (State d) := integral_add hlin herr
    _ = δ • V.gradU x +
        ∫ z, V.scaledRWMRejectionExpansionError δ x z
          ∂stdGaussian (State d) := by
      rw [show (∫ z, V.scaledRWMLinearRejectionDisplacement δ x z
          ∂stdGaussian (State d)) = δ • V.gradU x by
        exact DiscreteTime.integral_scaledGaussian_positivePart_smul
          δ hδ (V.gradU x)]

/-- The actual rejected increment obtained from one Gaussian innovation and
one unit uniform. -/
def bernoulliRWMRejectedIncrement
    (δ : ℝ) (x : State d)
    (z : State d) (u : Set.Icc (0 : ℝ) 1) : State d :=
  DiscreteTime.thresholdConst
    (DiscreteTime.rejectionProfile
      (V.rwmEnergyIncrement x (Real.sqrt (2 * δ) • z)))
    (Real.sqrt (2 * δ) • z) u

/-- Integrating out the unit uniform and then the Gaussian gives exactly
the bias decomposition proved above. -/
theorem iteratedIntegral_bernoulliRWMRejectedIncrement_eq
    (δ : ℝ) (hδ : 0 ≤ δ) (x : State d) :
    (∫ z : State d,
        (∫ u : Set.Icc (0 : ℝ) 1,
          V.bernoulliRWMRejectedIncrement δ x z u ∂volume)
      ∂stdGaussian (State d)) =
      δ • V.gradU x +
        ∫ z, V.scaledRWMRejectionExpansionError δ x z
          ∂stdGaussian (State d) := by
  calc
    (∫ z : State d,
        (∫ u : Set.Icc (0 : ℝ) 1,
          V.bernoulliRWMRejectedIncrement δ x z u ∂volume)
      ∂stdGaussian (State d)) =
        ∫ z : State d,
          V.scaledRWMRejectionDisplacement δ x z
          ∂stdGaussian (State d) := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        unfold bernoulliRWMRejectedIncrement
          scaledRWMRejectionDisplacement rwmRejectionDisplacement
        exact DiscreteTime.integral_thresholdConst _
          (DiscreteTime.rejectionProfile_nonneg _)
          (DiscreteTime.rejectionProfile_le_one _) _
    _ = δ • V.gradU x +
        ∫ z, V.scaledRWMRejectionExpansionError δ x z
          ∂stdGaussian (State d) :=
      V.integral_scaledRWMRejectionDisplacement_eq δ hδ x

/-- After the uniform coordinate is integrated out, the second moment of
the actual Bernoulli rejected increment is exactly the scalar conditional
second-moment integrand. -/
theorem iteratedIntegral_norm_bernoulliRWMRejectedIncrement_sq_eq
    (δ : ℝ) (x : State d) :
    (∫ z : State d,
        (∫ u : Set.Icc (0 : ℝ) 1,
          ‖V.bernoulliRWMRejectedIncrement δ x z u‖ ^ 2 ∂volume)
      ∂stdGaussian (State d)) =
      ∫ z : State d, V.scaledRWMRejectionSecondMomentIntegrand δ x z
        ∂stdGaussian (State d) := by
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    unfold bernoulliRWMRejectedIncrement
      scaledRWMRejectionSecondMomentIntegrand
    exact DiscreteTime.integral_norm_thresholdConst_sq _
      (DiscreteTime.rejectionProfile_nonneg _)
      (DiscreteTime.rejectionProfile_le_one _) _

end FirstOrderPotential

end Concrete

end

end UniformRandomMALA
