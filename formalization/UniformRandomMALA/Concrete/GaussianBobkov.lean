import UniformRandomMALA.Concrete.GaussianOU
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Local algebra for the Gaussian Bobkov interpolation

This file begins the pointwise part of the Gaussian Bobkov argument.  It
records the interpolation coefficient `c(s) = 1 - exp(-2s)`, its derivative,
the radicand endpoint, the exact cancellation using `I I'' = -1`, the scalar
two-block Cauchy--Schwarz atom, and the final square-root sign calculation.

`GaussianOUGenerator` combines these algebraic lemmas with Gaussian
integration by parts, the OU generator, and time differentiation of
`P_s Q_s` to obtain the local interpolation inequality.
-/

namespace UniformRandomMALA

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace Concrete

/-- The time-dependent coefficient in the local Gaussian Bobkov interpolation. -/
def bobkovVarianceCoeff (s : ℝ) : ℝ := 1 - Real.exp (-2 * s)

@[simp] lemma bobkovVarianceCoeff_zero : bobkovVarianceCoeff 0 = 0 := by
  simp [bobkovVarianceCoeff]

lemma bobkovVarianceCoeff_nonneg {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ bobkovVarianceCoeff s := by
  exact one_sub_exp_neg_two_mul_nonneg hs

lemma bobkovVarianceCoeff_lt_one (s : ℝ) : bobkovVarianceCoeff s < 1 := by
  unfold bobkovVarianceCoeff
  linarith [Real.exp_pos (-2 * s)]

/-- The interpolation coefficient satisfies `c' = 2(1-c)`. -/
theorem hasDerivAt_bobkovVarianceCoeff (s : ℝ) :
    HasDerivAt bobkovVarianceCoeff (2 * (1 - bobkovVarianceCoeff s)) s := by
  have hneg : HasDerivAt (fun x : ℝ => -2 * x) (-2) s := by
    simpa using (hasDerivAt_id s).const_mul (-2)
  have hraw : HasDerivAt (fun x : ℝ => 1 - Real.exp (-2 * x))
      (2 * Real.exp (-2 * s)) s := by
    have htmp := (hasDerivAt_const s 1).sub
      ((Real.hasDerivAt_exp (-2 * s)).comp s hneg)
    have htmp' : HasDerivAt ((fun _ : ℝ => (1 : ℝ)) -
        Real.exp ∘ fun x : ℝ => -2 * x) (2 * Real.exp (-2 * s)) s :=
      htmp.congr_deriv (by ring)
    apply htmp'.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun _ => rfl
  have hcoeff : 2 * Real.exp (-2 * s) =
      2 * (1 - bobkovVarianceCoeff s) := by
    simp [bobkovVarianceCoeff]
  apply (hraw.congr_deriv hcoeff).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun _ => rfl

theorem deriv_bobkovVarianceCoeff (s : ℝ) :
    deriv bobkovVarianceCoeff s = 2 * (1 - bobkovVarianceCoeff s) :=
  (hasDerivAt_bobkovVarianceCoeff s).deriv

/-- The Bobkov coefficient is the squared noise coefficient in Mehler's
formula. -/
theorem bobkovVarianceCoeff_eq_ouNoiseCoeff_sq {s : ℝ} (hs : 0 ≤ s) :
    bobkovVarianceCoeff s = ouNoiseCoeff s ^ 2 := by
  rw [ouNoiseCoeff, Real.sq_sqrt (one_sub_exp_neg_two_mul_nonneg hs)]
  rfl

/-- The scalar radicand in the local Bobkov interpolation. -/
def bobkovRadicand (s u gradSq : ℝ) : ℝ :=
  normalProfile u ^ 2 + bobkovVarianceCoeff s * gradSq

lemma bobkovRadicand_nonneg {s u gradSq : ℝ}
    (hs : 0 ≤ s) (hgrad : 0 ≤ gradSq) :
    0 ≤ bobkovRadicand s u gradSq := by
  exact add_nonneg (sq_nonneg _) (mul_nonneg (bobkovVarianceCoeff_nonneg hs) hgrad)

@[simp] theorem bobkovRadicand_zero (u gradSq : ℝ) :
    bobkovRadicand 0 u gradSq = normalProfile u ^ 2 := by
  simp [bobkovRadicand]

/-- At the initial interpolation time the square-root integrand reduces to
the normal profile. -/
theorem sqrt_bobkovRadicand_zero {u gradSq : ℝ}
    (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    Real.sqrt (bobkovRadicand 0 u gradSq) = normalProfile u := by
  rw [bobkovRadicand_zero, Real.sqrt_sq_eq_abs,
    abs_of_pos (normalProfile_pos hu)]

/-- The exact scalar cancellation in the `(partial_s + L) A` computation.
The profile term supplies `I I'' = -1`, while the time coefficient supplies
`c' = 2(1-c)`. -/
theorem bobkov_g2_scalar_cancellation
    {s u gradSq hessSq : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    2 * ((deriv normalProfile u) ^ 2 +
          normalProfile u * deriv (deriv normalProfile) u) * gradSq +
        deriv bobkovVarianceCoeff s * gradSq +
        2 * bobkovVarianceCoeff s * (gradSq + hessSq) =
      2 * (deriv normalProfile u) ^ 2 * gradSq +
        2 * bobkovVarianceCoeff s * hessSq := by
  rw [normalProfile_mul_secondDeriv hu, deriv_bobkovVarianceCoeff]
  ring

/-- Cauchy--Schwarz for a scalar block paired with a Hilbert-space block. -/
theorem bobkov_block_cauchy_schwarz
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a b : ℝ) (v w : H) :
    (a * b + inner ℝ v w) ^ 2 ≤
      (a ^ 2 + ‖v‖ ^ 2) * (b ^ 2 + ‖w‖ ^ 2) := by
  let x : WithLp 2 (ℝ × H) := WithLp.toLp 2 (a, v)
  let y : WithLp 2 (ℝ × H) := WithLp.toLp 2 (b, w)
  calc
    (a * b + inner ℝ v w) ^ 2 =
        inner ℝ x y * inner ℝ x y := by
      simp [x, y, pow_two, mul_comm]
    _ ≤ inner ℝ x x * inner ℝ y y :=
      real_inner_mul_inner_self_le x y
    _ = (a ^ 2 + ‖v‖ ^ 2) * (b ^ 2 + ‖w‖ ^ 2) := by
      simp only [x, y, WithLp.prod_inner_apply]
      simp [pow_two]

/-- Weighted Hilbert-block Cauchy--Schwarz.  Taking `c` to be the Bobkov
variance coefficient gives the pointwise block estimate used for the gradient
of the radicand. -/
theorem bobkov_weighted_block_cauchy_schwarz
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {c : ℝ} (hc : 0 ≤ c) (a b : ℝ) (v w : H) :
    (a * b + c * inner ℝ v w) ^ 2 ≤
      (a ^ 2 + c * ‖v‖ ^ 2) * (b ^ 2 + c * ‖w‖ ^ 2) := by
  have h := bobkov_block_cauchy_schwarz a b
    (Real.sqrt c • v) (Real.sqrt c • w)
  have hinner : inner ℝ (Real.sqrt c • v) (Real.sqrt c • w) =
      c * inner ℝ v w := by
    simp only [inner_smul_left, inner_smul_right, RCLike.conj_to_real]
    rw [← mul_assoc, Real.mul_self_sqrt hc]
  have hnormv : ‖Real.sqrt c • v‖ ^ 2 = c * ‖v‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg c),
      mul_pow, Real.sq_sqrt hc]
  have hnormw : ‖Real.sqrt c • w‖ ^ 2 = c * ‖w‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg c),
      mul_pow, Real.sq_sqrt hc]
  rwa [hinner, hnormv, hnormw] at h

/-- Scalar two-block Cauchy--Schwarz, the algebraic atom in the pointwise
gradient estimate for the Bobkov radicand. -/
theorem bobkov_two_block_cauchy_schwarz (a b c d : ℝ) :
    (a * b + c * d) ^ 2 ≤
      (a ^ 2 + c ^ 2) * (b ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a * d - b * c)]

/-- The summed finite-dimensional form of the weighted block estimate.  This
is the coordinate inequality behind the bound for `|∇A|²`. -/
theorem bobkov_g3_sum
    {n : Type*} [Fintype n]
    {c : ℝ} (hc : 0 ≤ c) (I Ip : ℝ)
    (v : EuclideanSpace ℝ n) (H : n → EuclideanSpace ℝ n) :
    ∑ j, (I * Ip * v j + c * inner ℝ v (H j)) ^ 2 ≤
      (I ^ 2 + c * ‖v‖ ^ 2) *
        (Ip ^ 2 * ‖v‖ ^ 2 + c * ∑ j, ‖H j‖ ^ 2) := by
  have hj : ∀ j : n,
      (I * Ip * v j + c * inner ℝ v (H j)) ^ 2 ≤
        (I ^ 2 + c * ‖v‖ ^ 2) *
          (Ip ^ 2 * (v j) ^ 2 + c * ‖H j‖ ^ 2) := by
    intro j
    simpa [mul_assoc, mul_pow] using
      (bobkov_weighted_block_cauchy_schwarz hc I (Ip * v j) v (H j))
  calc
    ∑ j, (I * Ip * v j + c * inner ℝ v (H j)) ^ 2 ≤
        ∑ j, (I ^ 2 + c * ‖v‖ ^ 2) *
          (Ip ^ 2 * (v j) ^ 2 + c * ‖H j‖ ^ 2) :=
      Finset.sum_le_sum fun j _ => hj j
    _ = (I ^ 2 + c * ‖v‖ ^ 2) *
        (Ip ^ 2 * ‖v‖ ^ 2 + c * ∑ j, ‖H j‖ ^ 2) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← EuclideanSpace.real_norm_sq_eq v]

/-- The factor-four form of `bobkov_g3_sum`, matching the coordinate formula
for the gradient of the Bobkov radicand. -/
theorem bobkov_g3_gradient
    {n : Type*} [Fintype n]
    {c : ℝ} (hc : 0 ≤ c) (I Ip : ℝ)
    (v : EuclideanSpace ℝ n) (H : n → EuclideanSpace ℝ n) :
    ∑ j, (2 * (I * Ip * v j + c * inner ℝ v (H j))) ^ 2 ≤
      4 * (I ^ 2 + c * ‖v‖ ^ 2) *
        (Ip ^ 2 * ‖v‖ ^ 2 + c * ∑ j, ‖H j‖ ^ 2) := by
  have h := bobkov_g3_sum hc I Ip v H
  calc
    ∑ j, (2 * (I * Ip * v j + c * inner ℝ v (H j))) ^ 2 =
        4 * ∑ j, (I * Ip * v j + c * inner ℝ v (H j)) ^ 2 := by
      simp_rw [mul_pow]
      norm_num
      rw [Finset.mul_sum]
    _ ≤ 4 * ((I ^ 2 + c * ‖v‖ ^ 2) *
        (Ip ^ 2 * ‖v‖ ^ 2 + c * ∑ j, ‖H j‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 4 * (I ^ 2 + c * ‖v‖ ^ 2) *
        (Ip ^ 2 * ‖v‖ ^ 2 + c * ∑ j, ‖H j‖ ^ 2) := by ring

/-- The exact `|grad A|² ≤ 2 A (∂ₛ+L)A` form of G3 after the
scalar cancellation has identified `(∂ₛ+L)A` with twice the second
factor. -/
theorem bobkov_g3_full
    {n : Type*} [Fintype n]
    {c : ℝ} (hc : 0 ≤ c) (I Ip : ℝ)
    (v : EuclideanSpace ℝ n) (H : n → EuclideanSpace ℝ n) :
    ∑ j, (2 * (I * Ip * v j + c * inner ℝ v (H j))) ^ 2 ≤
      2 * (I ^ 2 + c * ‖v‖ ^ 2) *
        (2 * (Ip ^ 2 * ‖v‖ ^ 2 + c * ∑ j, ‖H j‖ ^ 2)) := by
  have h := bobkov_g3_gradient hc I Ip v H
  convert h using 1 <;> ring

/-- Reindexing the mixed Hessian term.  This is the finite-coordinate
identity that cancels the drift contribution in the Gaussian OU Bochner
calculation. -/
theorem bobkov_cross_sum_comm
    {n : Type*} [Fintype n]
    (x v : n → ℝ) (H : n → n → ℝ) :
    ∑ j, v j * (∑ i, x i * H i j) =
      ∑ i, x i * (∑ j, v j * H i j) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Coordinate algebra underlying the Gaussian OU Bochner identity
`(∂ₛ+L)|∇u|² = 2(|∇u|²+‖Hess u‖²)`.  The inputs name the
gradient, the gradient of the Laplacian, and the Hessian entries; analytic
chain rules identifying those inputs are deliberately kept separate. -/
theorem gaussianOU_bochner_coordinate_identity
    {n : Type*} [Fintype n]
    (x v lapGrad : n → ℝ) (H : n → n → ℝ) :
    2 * ∑ j, v j * (-lapGrad j + v j + ∑ i, x i * H i j) +
        (2 * ∑ j, v j * lapGrad j +
          2 * ∑ i, ∑ j, (H i j) ^ 2) -
        2 * ∑ i, x i * (∑ j, v j * H i j) =
      2 * ((∑ j, (v j) ^ 2) + ∑ i, ∑ j, (H i j) ^ 2) := by
  have htime :
      (∑ j, v j * (-lapGrad j + v j + ∑ i, x i * H i j)) =
        -(∑ j, v j * lapGrad j) + ∑ j, (v j) ^ 2 +
          ∑ j, v j * (∑ i, x i * H i j) := by
    simp_rw [mul_add, mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    ring
  rw [htime, bobkov_cross_sum_comm x v H]
  ring

/-- The complete cancellation for the radicand of the canonical Bobkov
square root, stated solely in finite coordinates.  The two long parenthesized
expressions are respectively the time derivative and OU generator of

`I(u)^2 + c * |grad u|^2`

when `u` solves the backward OU equation.  Keeping this lemma algebraic means
that the analytic layer only has to identify the named derivatives; none of
the cancellation has to be repeated under integrals. -/
theorem bobkov_canonical_radicand_residual_identity
    {n : Type*} [Fintype n]
    (x v lapGrad : EuclideanSpace ℝ n)
    (H : n → EuclideanSpace ℝ n)
    (I Ip Ipp c cp : ℝ)
    (hprofile : I * Ipp = -1)
    (hcoeff : cp = 2 * (1 - c)) :
    let Lu : ℝ := ∑ i, (H i i - x i * v i)
    let us : ℝ := -Lu
    let vs : EuclideanSpace ℝ n := WithLp.toLp 2 (fun j =>
      -lapGrad j + v j + ∑ i, x i * H i j)
    let At : ℝ :=
      2 * I * Ip * us + cp * ‖v‖ ^ 2 +
        2 * c * ∑ j, v j * vs j
    let LA : ℝ :=
      2 * (Ip ^ 2 + I * Ipp) * ‖v‖ ^ 2 + 2 * I * Ip * Lu +
        c * (2 * ∑ j, v j * lapGrad j +
          2 * ∑ i, ‖H i‖ ^ 2 -
          2 * ∑ i, x i * (∑ j, v j * H i j))
    At + LA =
      2 * (Ip ^ 2 * ‖v‖ ^ 2 + c * ∑ i, ‖H i‖ ^ 2) := by
  dsimp only
  have hbochner := gaussianOU_bochner_coordinate_identity
    (fun i => x i) (fun i => v i) (fun i => lapGrad i)
      (fun i j => H i j)
  have hbochner' :
      2 * ∑ j, v j * (-lapGrad j + v j + ∑ i, x i * H i j) +
          (2 * ∑ j, v j * lapGrad j +
            2 * ∑ i, ‖H i‖ ^ 2) -
          2 * ∑ i, x i * (∑ j, v j * H i j) =
        2 * (‖v‖ ^ 2 + ∑ i, ‖H i‖ ^ 2) := by
    simpa only [← EuclideanSpace.real_norm_sq_eq] using hbochner
  rw [hcoeff, hprofile]
  linear_combination c * hbochner'

/-- The square-root chain-rule expression is nonnegative once the pointwise
estimate `gradSq ≤ 2 A B` is known. -/
theorem bobkov_sqrt_chain_nonneg {A B gradSq : ℝ}
    (hA : 0 < A) (hG3 : gradSq ≤ 2 * A * B) :
    0 ≤ B / (2 * Real.sqrt A) -
      gradSq / (4 * (Real.sqrt A) ^ 3) := by
  have hsqrt : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  have hdenom1 : 0 < 4 * (Real.sqrt A) ^ 3 := by positivity
  have hdenom2 : 0 < 2 * Real.sqrt A := by positivity
  rw [sub_nonneg, div_le_div_iff₀ hdenom1 hdenom2]
  calc
    gradSq * (2 * Real.sqrt A) ≤
        (2 * A * B) * (2 * Real.sqrt A) :=
      mul_le_mul_of_nonneg_right hG3 hdenom2.le
    _ = B * (4 * (Real.sqrt A) ^ 3) := by
      let r := Real.sqrt A
      have hr2 : r ^ 2 = A := Real.sq_sqrt hA.le
      change (2 * A * B) * (2 * r) = B * (4 * r ^ 3)
      rw [← hr2]
      ring

/-- Pointwise nonnegativity of the square-root diffusion-chain expression,
with the full G3 coordinate estimate discharged internally. -/
theorem bobkov_g3_sqrt_supersolution
    {n : Type*} [Fintype n]
    {c : ℝ} (hc : 0 ≤ c) {I : ℝ} (hI : 0 < I) (Ip : ℝ)
    (v : EuclideanSpace ℝ n) (H : n → EuclideanSpace ℝ n) :
    0 ≤
      (2 * (Ip ^ 2 * ‖v‖ ^ 2 + c * ∑ j, ‖H j‖ ^ 2)) /
          (2 * Real.sqrt (I ^ 2 + c * ‖v‖ ^ 2)) -
        (∑ j, (2 * (I * Ip * v j + c * inner ℝ v (H j))) ^ 2) /
          (4 * (Real.sqrt (I ^ 2 + c * ‖v‖ ^ 2)) ^ 3) := by
  have hA : 0 < I ^ 2 + c * ‖v‖ ^ 2 := by
    have hIsq : 0 < I ^ 2 := sq_pos_of_pos hI
    nlinarith [mul_nonneg hc (sq_nonneg ‖v‖)]
  apply bobkov_sqrt_chain_nonneg hA
  exact bobkov_g3_full hc I Ip v H

/-- The explicit square-root residual appearing in the local Bobkov flow. -/
def bobkovSqrtResidual
    {n : Type*} [Fintype n]
    (c I Ip : ℝ) (v : EuclideanSpace ℝ n)
    (H : n → EuclideanSpace ℝ n) : ℝ :=
  (2 * (Ip ^ 2 * ‖v‖ ^ 2 + c * ∑ j, ‖H j‖ ^ 2)) /
      (2 * Real.sqrt (I ^ 2 + c * ‖v‖ ^ 2)) -
    (∑ j, (2 * (I * Ip * v j + c * inner ℝ v (H j))) ^ 2) /
    (4 * (Real.sqrt (I ^ 2 + c * ‖v‖ ^ 2)) ^ 3)

/-- After the radicand cancellation, the ordinary square-root chain rule is
definitionally the explicit nonnegative Bobkov residual.  This is the exact
identity needed when the canonical time and spatial derivative fields have
been constructed. -/
theorem bobkov_canonical_sqrt_residual_identity
    {n : Type*} [Fintype n]
    (c I Ip : ℝ) (v : EuclideanSpace ℝ n)
    (H : n → EuclideanSpace ℝ n) :
    let A : ℝ := I ^ 2 + c * ‖v‖ ^ 2
    let B : ℝ := 2 * (Ip ^ 2 * ‖v‖ ^ 2 + c * ∑ j, ‖H j‖ ^ 2)
    let gradSq : ℝ :=
      ∑ j, (2 * (I * Ip * v j + c * inner ℝ v (H j))) ^ 2
    B / (2 * Real.sqrt A) - gradSq / (4 * (Real.sqrt A) ^ 3) =
      bobkovSqrtResidual c I Ip v H := by
  rfl

/-- G3 says that the explicit Bobkov square-root residual is nonnegative. -/
theorem bobkovSqrtResidual_nonneg
    {n : Type*} [Fintype n]
    {c : ℝ} (hc : 0 ≤ c) {I : ℝ} (hI : 0 < I) (Ip : ℝ)
    (v : EuclideanSpace ℝ n) (H : n → EuclideanSpace ℝ n) :
    0 ≤ bobkovSqrtResidual c I Ip v H := by
  exact bobkov_g3_sqrt_supersolution hc hI Ip v H

/-- The one-variable monotonicity closure used at the end of G3.  Endpoint
continuity is kept explicit because the square-root flow is differentiated
only in the open time interval. -/
theorem bobkov_interpolation_endpoint_le
    {t : ℝ} (ht : 0 ≤ t) {F F' : ℝ → ℝ}
    (hcont : ContinuousOn F (Set.Icc 0 t))
    (hderiv : ∀ s ∈ Set.Ioo 0 t, HasDerivAt F (F' s) s)
    (hnonneg : ∀ s ∈ Set.Ioo 0 t, 0 ≤ F' s) :
    F 0 ≤ F t := by
  have hinterior : interior (Set.Icc (0 : ℝ) t) ⊆ Set.Ioo 0 t := by
    rw [interior_Icc]
  have hmono : MonotoneOn F (Set.Icc 0 t) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 t) hcont
      (fun s hs => (hderiv s (hinterior hs)).differentiableAt.differentiableWithinAt)
      (fun s hs => by
        rw [(hderiv s (hinterior hs)).deriv]
        exact hnonneg s (hinterior hs))
  exact hmono (Set.left_mem_Icc.mpr ht) (Set.right_mem_Icc.mpr ht)
    ht

end Concrete

end

end UniformRandomMALA
