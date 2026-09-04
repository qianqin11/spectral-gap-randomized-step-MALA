import UniformRandomMALA.Concrete.HessianToFirstOrder
import UniformRandomMALA.Concrete.MALA
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
# The smooth perturbed-Gaussian fixed-step obstruction

This module defines the explicit separable potential used in the appendix's
fixed-step obstruction.  Its definitions use the paper's formula literally:
the zeroth coordinate is Gaussian with curvature `m`, while every remaining
coordinate is a quadratic potential plus a cosine perturbation at wavelength
`sqrt h`.

The potential is proved `C^∞`.  The second Fréchet derivative is computed as
a diagonal quadratic form and is bounded between `m` and `L`; consequently
the general Hessian-to-first-order bridge constructs the concrete target and
MALA kernel without recording an unrelated gradient field.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory Gradient

noncomputable section

/-- The scalar potential in the first, purely Gaussian coordinate. -/
def hardGaussianCoordinate (m : ℝ) (u : ℝ) : ℝ :=
  (m / 2) * u ^ 2

/-- The scalar cosine-perturbed quadratic used in coordinates `i ≥ 2` in
the manuscript (indices are zero-based in Lean). -/
def hardOscillatoryCoordinate (m L h : ℝ) (u : ℝ) : ℝ :=
  ((L + m) / 4) * u ^ 2 -
    ((L - m) * h / 2) * Real.cos (u / Real.sqrt h)

/-- Coordinate-wise form of the hard potential. -/
def hardCoordinate (m L h : ℝ) (i : Fin d) (u : ℝ) : ℝ :=
  if (i : ℕ) = 0 then hardGaussianCoordinate m u
  else hardOscillatoryCoordinate m L h u

/-- The explicit potential `U_{d,h}` from the fixed-step obstruction. -/
def fixedStepHardPotential (d : ℕ) (m L h : ℝ) (x : State d) : ℝ :=
  ∑ i : Fin d, hardCoordinate m L h i (x i)

@[fun_prop] lemma contDiff_hardGaussianCoordinate (m : ℝ) :
    ContDiff ℝ ⊤ (hardGaussianCoordinate m) := by
  unfold hardGaussianCoordinate
  fun_prop

@[fun_prop] lemma contDiff_hardOscillatoryCoordinate (m L h : ℝ) :
    ContDiff ℝ ⊤ (hardOscillatoryCoordinate m L h) := by
  unfold hardOscillatoryCoordinate
  fun_prop

@[fun_prop] lemma contDiff_hardCoordinate (m L h : ℝ) (i : Fin d) :
    ContDiff ℝ ⊤ (hardCoordinate m L h i) := by
  unfold hardCoordinate
  split_ifs
  · exact contDiff_hardGaussianCoordinate m
  · exact contDiff_hardOscillatoryCoordinate m L h

/-- The hard potential is infinitely Fréchet differentiable. -/
theorem contDiff_infty_fixedStepHardPotential (d : ℕ) (m L h : ℝ) :
    ContDiff ℝ ⊤ (fixedStepHardPotential d m L h) := by
  unfold fixedStepHardPotential
  fun_prop

lemma iteratedDeriv_two_hardGaussianCoordinate (m u : ℝ) :
    iteratedDeriv 2 (hardGaussianCoordinate m) u = m := by
  have hfirst : deriv (hardGaussianCoordinate m) = fun x => m * x := by
    funext x
    change deriv (fun y : ℝ => (m / 2) * y ^ 2) x = m * x
    have hd := (hasDerivAt_pow 2 x).const_mul (m / 2)
    apply HasDerivAt.deriv
    simpa only [Function.id_def] using hd.congr_deriv (by simp; ring)
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_one, hfirst]
  simpa only [Function.id_def, mul_one] using
    ((hasDerivAt_id u).const_mul m).deriv

lemma iteratedDeriv_two_hardOscillatoryCoordinate
    {h : ℝ} (hh : 0 < h) (m L u : ℝ) :
    iteratedDeriv 2 (hardOscillatoryCoordinate m L h) u =
      (L + m) / 2 + (L - m) / 2 * Real.cos (u / Real.sqrt h) := by
  have hs : Real.sqrt h ≠ 0 := (Real.sqrt_pos.2 hh).ne'
  have hfirst : deriv (hardOscillatoryCoordinate m L h) =
      fun x => ((L + m) / 2) * x +
        (((L - m) * h / 2) / Real.sqrt h) *
          Real.sin (x / Real.sqrt h) := by
    funext x
    change deriv (fun y : ℝ => ((L + m) / 4) * y ^ 2 -
      ((L - m) * h / 2) * Real.cos (y / Real.sqrt h)) x = _
    have hsq := (hasDerivAt_pow 2 x).const_mul ((L + m) / 4)
    have harg := (hasDerivAt_id x).div_const (Real.sqrt h)
    have hcos := harg.cos.const_mul ((L - m) * h / 2)
    apply HasDerivAt.deriv
    change HasDerivAt
      ((fun y : ℝ => ((L + m) / 4) * y ^ 2) -
        fun y : ℝ => ((L - m) * h / 2) * Real.cos (y / Real.sqrt h)) _ x
    exact (hsq.sub hcos).congr_deriv (by
      simp [div_eq_mul_inv]
      field_simp [hs]
      ring)
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_one, hfirst]
  have harg := (hasDerivAt_id u).div_const (Real.sqrt h)
  have hsin := harg.sin.const_mul (((L - m) * h / 2) / Real.sqrt h)
  have hlin := (hasDerivAt_id u).const_mul ((L + m) / 2)
  apply HasDerivAt.deriv
  change HasDerivAt
    ((fun x : ℝ => ((L + m) / 2) * x) +
      fun x : ℝ => (((L - m) * h / 2) / Real.sqrt h) *
        Real.sin (x / Real.sqrt h)) _ u
  exact (hlin.add hsin).congr_deriv (by
    simp [div_eq_mul_inv]
    field_simp [hs]
    rw [Real.sq_sqrt hh.le])

lemma iteratedDeriv_two_hardCoordinate
    {h : ℝ} (hh : 0 < h) (m L : ℝ) (i : Fin d) (u : ℝ) :
    iteratedDeriv 2 (hardCoordinate m L h i) u =
      if (i : ℕ) = 0 then m
      else (L + m) / 2 + (L - m) / 2 * Real.cos (u / Real.sqrt h) := by
  unfold hardCoordinate
  split_ifs
  · exact iteratedDeriv_two_hardGaussianCoordinate m u
  · exact iteratedDeriv_two_hardOscillatoryCoordinate hh m L u

/-- The explicit first derivative of a scalar hard coordinate. -/
def hardCoordinateGradient (m L h : ℝ) (i : Fin d) (u : ℝ) : ℝ :=
  if (i : ℕ) = 0 then m * u
  else (L + m) / 2 * u +
    ((L - m) * h / 2 / Real.sqrt h) * Real.sin (u / Real.sqrt h)

lemma hasDerivAt_hardGaussianCoordinate (m u : ℝ) :
    HasDerivAt (hardGaussianCoordinate m) (m * u) u := by
  change HasDerivAt (fun y : ℝ => (m / 2) * y ^ 2) (m * u) u
  have hd := (hasDerivAt_pow 2 u).const_mul (m / 2)
  simpa only [Function.id_def] using hd.congr_deriv (by simp; ring)

lemma hasDerivAt_hardOscillatoryCoordinate
    {h : ℝ} (hh : 0 < h) (m L u : ℝ) :
    HasDerivAt (hardOscillatoryCoordinate m L h)
      ((L + m) / 2 * u +
        ((L - m) * h / 2 / Real.sqrt h) *
          Real.sin (u / Real.sqrt h)) u := by
  have hs : Real.sqrt h ≠ 0 := (Real.sqrt_pos.2 hh).ne'
  change HasDerivAt (fun y : ℝ => ((L + m) / 4) * y ^ 2 -
    ((L - m) * h / 2) * Real.cos (y / Real.sqrt h)) _ u
  have hsq := (hasDerivAt_pow 2 u).const_mul ((L + m) / 4)
  have harg := (hasDerivAt_id u).div_const (Real.sqrt h)
  have hcos := harg.cos.const_mul ((L - m) * h / 2)
  change HasDerivAt
    ((fun y : ℝ => ((L + m) / 4) * y ^ 2) -
      fun y : ℝ => ((L - m) * h / 2) * Real.cos (y / Real.sqrt h)) _ u
  exact (hsq.sub hcos).congr_deriv (by
    simp [div_eq_mul_inv]
    field_simp [hs]
    ring)

lemma hasDerivAt_hardCoordinate
    {h : ℝ} (hh : 0 < h) (m L : ℝ) (i : Fin d) (u : ℝ) :
    HasDerivAt (hardCoordinate m L h i)
      (hardCoordinateGradient m L h i u) u := by
  unfold hardCoordinate hardCoordinateGradient
  split_ifs
  · exact hasDerivAt_hardGaussianCoordinate m u
  · exact hasDerivAt_hardOscillatoryCoordinate hh m L u

/-- The explicit Euclidean gradient of the separable hard potential. -/
def fixedStepHardGradient (d : ℕ) (m L h : ℝ) (x : State d) : State d :=
  ∑ i : Fin d,
    hardCoordinateGradient m L h i (x i) • EuclideanSpace.single i 1

lemma hasGradientAt_hardCoordinate_comp
    {h : ℝ} (hh : 0 < h) (m L : ℝ) (i : Fin d) (x : State d) :
    HasGradientAt (fun z : State d => hardCoordinate m L h i (z i))
      (hardCoordinateGradient m L h i (x i) • EuclideanSpace.single i 1) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hscalar := (hasDerivAt_hardCoordinate hh m L i (x i)).hasFDerivAt
  have hproj := PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := (2 : ℝ≥0∞)) x i
  have hcomp := hscalar.comp x hproj
  apply hcomp.congr_fderiv
  ext v
  simp [InnerProductSpace.toDual_apply_apply,
    EuclideanSpace.inner_single_left, mul_comm]

/-- The displayed coordinate formula is the genuine Riesz gradient of the
displayed hard potential. -/
theorem hasGradientAt_fixedStepHardPotential
    {h : ℝ} (hh : 0 < h) (d : ℕ) (m L : ℝ) (x : State d) :
    HasGradientAt (fixedStepHardPotential d m L h)
      (fixedStepHardGradient d m L h x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  unfold fixedStepHardPotential fixedStepHardGradient
  rw [map_sum]
  apply HasFDerivAt.fun_sum
  intro i hi
  exact (hasGradientAt_hardCoordinate_comp hh m L i x).hasFDerivAt

/-- Pointwise equality between mathlib's Riesz gradient and the explicit
coordinate formula. -/
theorem gradient_fixedStepHardPotential
    {h : ℝ} (hh : 0 < h) (d : ℕ) (m L : ℝ) (x : State d) :
    ∇ (fixedStepHardPotential d m L h) x =
      fixedStepHardGradient d m L h x :=
  (hasGradientAt_fixedStepHardPotential hh d m L x).gradient

@[simp] theorem fixedStepHardGradient_apply
    (d : ℕ) (m L h : ℝ) (x : State d) (j : Fin d) :
    fixedStepHardGradient d m L h x j =
      hardCoordinateGradient m L h j (x j) := by
  classical
  unfold fixedStepHardGradient
  simp [Pi.single_apply]

@[simp] theorem fixedStepHardGradient_zero
    (d : ℕ) (m L h : ℝ) :
    fixedStepHardGradient d m L h 0 = 0 := by
  ext i
  simp [hardCoordinateGradient]

/-- The diagonal curvature coefficient of the hard potential. -/
def hardCoordinateCurvature (m L h : ℝ) (i : Fin d) (u : ℝ) : ℝ :=
  if (i : ℕ) = 0 then m
  else (L + m) / 2 + (L - m) / 2 * Real.cos (u / Real.sqrt h)

lemma iteratedFDeriv_two_hardCoordinate_comp_proj
    {h : ℝ} (hh : 0 < h) (m L : ℝ) (i : Fin d)
    (x v w : State d) :
    iteratedFDeriv ℝ 2
        (fun z : State d => hardCoordinate m L h i (z i)) x ![v, w] =
      hardCoordinateCurvature m L h i (x i) * v i * w i := by
  let p : State d →L[ℝ] ℝ := EuclideanSpace.proj i
  have hfun : (fun z : State d => hardCoordinate m L h i (z i)) =
      hardCoordinate m L h i ∘ p := by
    rfl
  rw [hfun, p.iteratedFDeriv_comp_right
    (contDiff_hardCoordinate m L h i) x (by simp : 2 ≤ (⊤ : WithTop ℕ∞))]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
  rw [iteratedDeriv_two_hardCoordinate hh]
  simp [p, hardCoordinateCurvature]
  ring_nf

/-- Exact diagonal formula for the Hessian quadratic form. -/
theorem iteratedFDeriv_two_fixedStepHardPotential
    {h : ℝ} (hh : 0 < h) (d : ℕ) (m L : ℝ)
    (x v w : State d) :
    iteratedFDeriv ℝ 2 (fixedStepHardPotential d m L h) x ![v, w] =
      ∑ i : Fin d, hardCoordinateCurvature m L h i (x i) * v i * w i := by
  unfold fixedStepHardPotential
  rw [iteratedFDeriv_fun_sum_apply]
  · change ContinuousMultilinearMap.applyAddHom ![v, w]
        (∑ j, iteratedFDeriv ℝ 2
          (fun x : State d => hardCoordinate m L h j (x j)) x) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact iteratedFDeriv_two_hardCoordinate_comp_proj hh m L i x v w
  · intro i hi
    have houter : ContDiff ℝ 2 (hardCoordinate m L h i) :=
      (contDiff_hardCoordinate m L h i).of_le (by simp)
    have hproj : ContDiff ℝ 2 (fun z : State d => z i) :=
      (EuclideanSpace.proj i : State d →L[ℝ] ℝ).contDiff
    exact houter.contDiffAt.comp x hproj.contDiffAt

lemma hardCoordinateCurvature_lower
    (hmL : m ≤ L) (h : ℝ) (i : Fin d) (u : ℝ) :
    m ≤ hardCoordinateCurvature m L h i u := by
  unfold hardCoordinateCurvature
  split_ifs
  · exact le_rfl
  · have hc := Real.neg_one_le_cos (u / Real.sqrt h)
    nlinarith

lemma hardCoordinateCurvature_upper
    (hmL : m ≤ L) (h : ℝ) (i : Fin d) (u : ℝ) :
    hardCoordinateCurvature m L h i u ≤ L := by
  unfold hardCoordinateCurvature
  split_ifs
  · exact hmL
  · have hc := Real.cos_le_one (u / Real.sqrt h)
    nlinarith

/-- The actual second Fréchet derivative of the hard potential has curvature
at least `m` in every direction. -/
theorem fixedStepHardPotential_hessian_lower
    {h : ℝ} (hh : 0 < h) (d : ℕ) {m L : ℝ} (hmL : m ≤ L)
    (x v : State d) :
    m * ‖v‖ ^ 2 ≤
      iteratedFDeriv ℝ 2 (fixedStepHardPotential d m L h) x ![v, v] := by
  rw [iteratedFDeriv_two_fixedStepHardPotential hh]
  rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hc := hardCoordinateCurvature_lower hmL h i (x i)
  have hv : 0 ≤ (v i) ^ 2 := sq_nonneg _
  calc
    m * (v i) ^ 2 ≤
        hardCoordinateCurvature m L h i (x i) * (v i) ^ 2 :=
      mul_le_mul_of_nonneg_right hc hv
    _ = hardCoordinateCurvature m L h i (x i) * v i * v i := by ring

/-- The actual second Fréchet derivative of the hard potential has curvature
at most `L` in every direction. -/
theorem fixedStepHardPotential_hessian_upper
    {h : ℝ} (hh : 0 < h) (d : ℕ) {m L : ℝ} (hmL : m ≤ L)
    (x v : State d) :
    iteratedFDeriv ℝ 2 (fixedStepHardPotential d m L h) x ![v, v] ≤
      L * ‖v‖ ^ 2 := by
  rw [iteratedFDeriv_two_fixedStepHardPotential hh]
  rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hc := hardCoordinateCurvature_upper hmL h i (x i)
  have hv : 0 ≤ (v i) ^ 2 := sq_nonneg _
  calc
    hardCoordinateCurvature m L h i (x i) * v i * v i =
        hardCoordinateCurvature m L h i (x i) * (v i) ^ 2 := by ring
    _ ≤ L * (v i) ^ 2 := mul_le_mul_of_nonneg_right hc hv

/-- The explicit hard potential packaged through the coordinate-free
Hessian interface.  Its `U` field is exactly the displayed formula, and the
gradient used by the resulting MALA kernel is the Riesz gradient of this
same function. -/
def fixedStepHardHessianPotential
    {d : ℕ} (hd : 2 ≤ d) {m L h : ℝ}
    (hm : 0 < m) (hmL : m < L) (hh : 0 < h) :
    HessianBoundedPotential d where
  U := fixedStepHardPotential d m L h
  m := m
  L := L
  hd := lt_of_lt_of_le (by norm_num) hd
  hm := hm
  hmL := hmL.le
  contDiff_U := (contDiff_infty_fixedStepHardPotential d m L h).of_le (by simp)
  hessian_lower := fixedStepHardPotential_hessian_lower hh d hmL.le
  hessian_upper := fixedStepHardPotential_hessian_upper hh d hmL.le

/-- The concrete first-order potential, target, proposal, and MALA kernel
associated with the smooth hard witness. -/
def fixedStepHardFirstOrderPotential
    {d : ℕ} (hd : 2 ≤ d) {m L h : ℝ}
    (hm : 0 < m) (hmL : m < L) (hh : 0 < h) : FirstOrderPotential d :=
  (fixedStepHardHessianPotential hd hm hmL hh).toFirstOrderPotential

@[simp] theorem fixedStepHardFirstOrderPotential_U
    {d : ℕ} (hd : 2 ≤ d) {m L h : ℝ}
    (hm : 0 < m) (hmL : m < L) (hh : 0 < h) :
    (fixedStepHardFirstOrderPotential hd hm hmL hh).U =
      fixedStepHardPotential d m L h := rfl

theorem fixedStepHardFirstOrderPotential_gradU
    {d : ℕ} (hd : 2 ≤ d) {m L h : ℝ}
    (hm : 0 < m) (hmL : m < L) (hh : 0 < h) :
    (fixedStepHardFirstOrderPotential hd hm hmL hh).gradU =
      fixedStepHardGradient d m L h := by
  funext x
  exact gradient_fixedStepHardPotential hh d m L x

end

end UniformRandomMALA.Concrete
