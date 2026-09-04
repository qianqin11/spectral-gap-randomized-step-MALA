import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Finite likelihood products as a kernel recursion

Rather than constructing a trajectory random variable first, we define the
moment of a finite likelihood product by backward recursion.  If `ell x y`
is a one-step likelihood and `kappa x` is the reference transition, then

`T_p g(x) = integral ell(x,y)^p g(y) d kappa(x)(y)`.

The `n`-step product moment with terminal weight `W` is `T_p^n W`.
This representation is exactly what repeated finite integration gives, but
it avoids filtration, martingale, and path-space infrastructure.

The main theorem below says that a one-step Lyapunov estimate

`T_p W <= B W`

propagates to `T_p^n W <= B^n W`.  The proof also establishes all
measurability and integrability facts required at each induction step.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory

noncomputable section

namespace DiscreteTime

section Recursion

variable {X : Type*} [MeasurableSpace X]

/-- Backward recursion for a finite product of one-step likelihood powers. -/
def finiteKernelProductMoment
    (kappa : Kernel X X) (ell : X × X → ℝ) (p : ℝ)
    (terminal : X → ℝ) : ℕ → X → ℝ
  | 0 => terminal
  | n + 1 => fun x =>
      ∫ y, (ell (x, y)) ^ p *
        finiteKernelProductMoment kappa ell p terminal n y ∂kappa x

/-- Joint measurability of the one-step likelihood propagates through every
finite backward recursion. -/
theorem measurable_finiteKernelProductMoment
    {kappa : Kernel X X} [IsSFiniteKernel kappa]
    {ell : X × X → ℝ} {p : ℝ} {terminal : X → ℝ}
    (hp : 0 ≤ p) (hell : Measurable ell)
    (hterminal : Measurable terminal) :
    ∀ n, Measurable (finiteKernelProductMoment kappa ell p terminal n) := by
  intro n
  induction n with
  | zero => simpa [finiteKernelProductMoment] using hterminal
  | succ n ih =>
      unfold finiteKernelProductMoment
      have hpow : Measurable (fun z : X × X => (ell z) ^ p) :=
        (Real.continuous_rpow_const hp).measurable.comp hell
      have hintegrand : Measurable (fun z : X × X =>
          (ell z) ^ p * finiteKernelProductMoment kappa ell p terminal n z.2) :=
        hpow.mul (ih.comp measurable_snd)
      simpa only using
        (MeasureTheory.StronglyMeasurable.integral_kernel_prod_right'
          (κ := kappa) hintegrand.stronglyMeasurable).measurable

/-- If a one-step likelihood integrates to one, every finite product has
mean one.  This is iterated integration written as induction, not as a
martingale theorem. -/
theorem finiteKernelProductMoment_one_eq_one
    {kappa : Kernel X X} {ell : X × X → ℝ}
    (hellMean : ∀ x, ∫ y, ell (x, y) ∂kappa x = 1) :
    ∀ n x, finiteKernelProductMoment kappa ell 1 (fun _ => 1) n x = 1 := by
  intro n
  induction n with
  | zero => simp [finiteKernelProductMoment]
  | succ n ih =>
      intro x
      simp only [finiteKernelProductMoment, ih, Real.rpow_one, mul_one]
      exact hellMean x

/-- A one-step Lyapunov inequality for the powered likelihood propagates
through an arbitrary finite number of steps.

The conclusion contains measurability, nonnegativity, and the quantitative
bound together.  Keeping them in one induction ensures that every integral
used in the next step is justified by the previous step's domination. -/
theorem finiteKernelProductMoment_nonneg_le
    {kappa : Kernel X X} [IsSFiniteKernel kappa]
    {ell : X × X → ℝ} {p B : ℝ} {W : X → ℝ}
    (hp : 0 ≤ p) (hB : 0 ≤ B)
    (hell : Measurable ell) (hell0 : ∀ z, 0 ≤ ell z)
    (hW : Measurable W) (hW0 : ∀ x, 0 ≤ W x)
    (hStepInt : ∀ x, Integrable
      (fun y => (ell (x, y)) ^ p * W y) (kappa x))
    (hStep : ∀ x,
      (∫ y, (ell (x, y)) ^ p * W y ∂kappa x) ≤ B * W x) :
    ∀ n,
      Measurable (finiteKernelProductMoment kappa ell p W n) ∧
      (∀ x, 0 ≤ finiteKernelProductMoment kappa ell p W n x) ∧
      ∀ x, finiteKernelProductMoment kappa ell p W n x ≤ B ^ n * W x := by
  intro n
  induction n with
  | zero =>
      refine ⟨by simpa [finiteKernelProductMoment] using hW,
        by simpa [finiteKernelProductMoment] using hW0, ?_⟩
      intro x
      simp [finiteKernelProductMoment]
  | succ n ih =>
      have hMeas : Measurable
          (finiteKernelProductMoment kappa ell p W (n + 1)) :=
        measurable_finiteKernelProductMoment hp hell hW (n + 1)
      have hNonneg : ∀ x,
          0 ≤ finiteKernelProductMoment kappa ell p W (n + 1) x := by
        intro x
        rw [finiteKernelProductMoment]
        exact integral_nonneg_of_ae (ae_of_all _ fun y =>
          mul_nonneg (Real.rpow_nonneg (hell0 (x, y)) p) (ih.2.1 y))
      refine ⟨hMeas, hNonneg, ?_⟩
      intro x
      have hIntegrandMeas : Measurable (fun y =>
          (ell (x, y)) ^ p *
            finiteKernelProductMoment kappa ell p W n y) := by
        exact ((Real.continuous_rpow_const hp).measurable.comp
          (hell.comp measurable_prodMk_left)).mul ih.1
      have hDom : ∀ y,
          (ell (x, y)) ^ p *
              finiteKernelProductMoment kappa ell p W n y ≤
            B ^ n * ((ell (x, y)) ^ p * W y) := by
        intro y
        calc
          (ell (x, y)) ^ p *
                finiteKernelProductMoment kappa ell p W n y ≤
              (ell (x, y)) ^ p * (B ^ n * W y) :=
            mul_le_mul_of_nonneg_left (ih.2.2 y)
              (Real.rpow_nonneg (hell0 (x, y)) p)
          _ = B ^ n * ((ell (x, y)) ^ p * W y) := by ring
      have hDomInt : Integrable
          (fun y => B ^ n * ((ell (x, y)) ^ p * W y)) (kappa x) :=
        (hStepInt x).const_mul _
      have hCurrentInt : Integrable (fun y =>
          (ell (x, y)) ^ p *
            finiteKernelProductMoment kappa ell p W n y) (kappa x) := by
        apply integrable_of_le_of_le hIntegrandMeas.aestronglyMeasurable
          (ae_of_all _ fun y => mul_nonneg
            (Real.rpow_nonneg (hell0 (x, y)) p) (ih.2.1 y))
          (ae_of_all _ hDom)
          (integrable_zero X ℝ (kappa x)) hDomInt
      calc
        finiteKernelProductMoment kappa ell p W (n + 1) x =
            ∫ y, (ell (x, y)) ^ p *
              finiteKernelProductMoment kappa ell p W n y ∂kappa x := rfl
        _ ≤ ∫ y, B ^ n * ((ell (x, y)) ^ p * W y) ∂kappa x :=
          integral_mono_ae hCurrentInt hDomInt (ae_of_all _ hDom)
        _ = B ^ n * (∫ y, (ell (x, y)) ^ p * W y ∂kappa x) := by
          rw [integral_const_mul]
        _ ≤ B ^ n * (B * W x) :=
          mul_le_mul_of_nonneg_left (hStep x) (pow_nonneg hB n)
        _ = B ^ (n + 1) * W x := by
          rw [pow_succ]
          ring

end Recursion

end DiscreteTime

end

end UniformRandomMALA
