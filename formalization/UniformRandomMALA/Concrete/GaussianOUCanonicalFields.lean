import UniformRandomMALA.Concrete.GaussianOUGenerator

/-!
# Canonical bounded Mehler fields for the Bobkov interpolation

This module packages Gaussian Mehler averages as bounded continuous
functions.  It then constructs the backward value and gradient fields used
by the canonical G3 interpolation.  These elementary fields isolate the
remaining higher-spatial-derivative calculation from continuity,
boundedness, range preservation, and endpoint bookkeeping.
-/

namespace UniformRandomMALA

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace Concrete

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [SecondCountableTopology E]

section Average

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F]

/-- A Mehler average with a general Banach-valued bounded continuous
integrand. -/
def gaussianOUAverage (t : ℝ) (f : BoundedContinuousFunction E F) (x : E) : F :=
  ∫ z, f (gaussianOUTransition t x z) ∂stdGaussian E

/-- A Mehler average for a raw Banach-valued function.  The accompanying
lemmas take continuity and a uniform norm bound explicitly; this avoids
reducible-instance diamonds for functions valued in iterated operator
spaces. -/
def gaussianOUAverageRaw (t : ℝ) (f : E → F) (x : E) : F :=
  ∫ z, f (gaussianOUTransition t x z) ∂stdGaussian E

theorem continuous_gaussianOUAverageRaw_of_bound
    (t : ℝ) (f : E → F) (hf : Continuous f) (C : ℝ)
    (hC : ∀ y, ‖f y‖ ≤ C) :
    Continuous (gaussianOUAverageRaw t f) := by
  rw [continuous_iff_continuousAt]
  intro x
  apply tendsto_integral_filter_of_norm_le_const
  · exact Filter.Eventually.of_forall fun y =>
      (hf.comp (by
        unfold gaussianOUTransition
        fun_prop)).aestronglyMeasurable
  · exact ⟨C, Filter.Eventually.of_forall fun _ =>
      Filter.Eventually.of_forall fun z => hC _⟩
  · exact Filter.Eventually.of_forall fun z => by
      have htransition : Continuous
          (fun y : E => gaussianOUTransition t y z) := by
        unfold gaussianOUTransition
        fun_prop
      exact hf.continuousAt.tendsto.comp htransition.continuousAt

theorem norm_gaussianOUAverageRaw_le
    (t : ℝ) (f : E → F) (C : ℝ) (hC : ∀ y, ‖f y‖ ≤ C) (x : E) :
    ‖gaussianOUAverageRaw t f x‖ ≤ C := by
  have h := norm_integral_le_of_norm_le_const
    (μ := stdGaussian E)
    (f := fun z => f (gaussianOUTransition t x z))
    (Filter.Eventually.of_forall fun z => hC _)
  simpa [gaussianOUAverageRaw] using h

/-- A concrete pointwise-norm bound extracted from the metric boundedness
stored in a bounded continuous function.  Unlike the supremum norm, this
definition remains usable for iterated continuous-linear-map codomains where
Lean's reducible metric instances can otherwise obscure the normed-space
instance. -/
def boundedContinuousFunctionAnchoredBound
    (f : BoundedContinuousFunction E F) : ℝ :=
  Classical.choose f.map_bounded' + ‖f 0‖

theorem norm_coe_le_anchoredBound
    (f : BoundedContinuousFunction E F) (x : E) :
    ‖f x‖ ≤ boundedContinuousFunctionAnchoredBound f := by
  let C := Classical.choose f.map_bounded'
  have hC := Classical.choose_spec f.map_bounded'
  calc
    ‖f x‖ ≤ ‖f x - f 0‖ + ‖f 0‖ := by
      simpa using norm_add_le (f x - f 0) (f 0)
    _ = dist (f x) (f 0) + ‖f 0‖ := by rw [dist_eq_norm]
    _ ≤ C + ‖f 0‖ := by
      dsimp only [C]
      simpa [add_comm] using add_le_add_right (hC x 0) ‖f 0‖
    _ = boundedContinuousFunctionAnchoredBound f := rfl

/-- Continuity of a Mehler average proved from the metric bound stored in
`f`, without invoking the supremum-norm instance on the function space. -/
theorem continuous_gaussianOUAverage_anchored
    (t : ℝ) (f : BoundedContinuousFunction E F) :
    Continuous (gaussianOUAverage t f) := by
  rw [continuous_iff_continuousAt]
  intro x
  apply tendsto_integral_filter_of_norm_le_const
  · exact Filter.Eventually.of_forall fun y =>
      (f.continuous.comp (by
        unfold gaussianOUTransition
        fun_prop)).aestronglyMeasurable
  · refine ⟨boundedContinuousFunctionAnchoredBound f,
      Filter.Eventually.of_forall fun _ =>
        Filter.Eventually.of_forall fun z => ?_⟩
    exact norm_coe_le_anchoredBound f _
  · exact Filter.Eventually.of_forall fun z => by
      have htransition : Continuous
          (fun y : E => gaussianOUTransition t y z) := by
        unfold gaussianOUTransition
        fun_prop
      exact f.continuous.continuousAt.tendsto.comp htransition.continuousAt

theorem norm_gaussianOUAverage_le_anchored
    (t : ℝ) (f : BoundedContinuousFunction E F) (x : E) :
    ‖gaussianOUAverage t f x‖ ≤ boundedContinuousFunctionAnchoredBound f := by
  have h := norm_integral_le_of_norm_le_const
    (μ := stdGaussian E)
    (f := fun z => f (gaussianOUTransition t x z))
    (Filter.Eventually.of_forall fun z =>
      norm_coe_le_anchoredBound f (gaussianOUTransition t x z))
  simpa [gaussianOUAverage] using h

theorem continuous_gaussianOUAverage
    (t : ℝ) (f : BoundedContinuousFunction E F) :
    Continuous (gaussianOUAverage t f) := by
  rw [continuous_iff_continuousAt]
  intro x
  apply tendsto_integral_filter_of_norm_le_const
  · exact Filter.Eventually.of_forall fun y =>
      (f.continuous.comp (by
        unfold gaussianOUTransition
        fun_prop)).aestronglyMeasurable
  · refine ⟨‖f‖, Filter.Eventually.of_forall fun _ =>
      Filter.Eventually.of_forall fun z => ?_⟩
    exact f.norm_coe_le_norm _
  · exact Filter.Eventually.of_forall fun z => by
      have htransition : Continuous
          (fun y : E => gaussianOUTransition t y z) := by
        unfold gaussianOUTransition
        fun_prop
      exact f.continuous.continuousAt.tendsto.comp htransition.continuousAt

/-- Joint continuity of a bounded continuous Mehler average in time and
space.  This is the parameter-continuity input needed to make the canonical
Bobkov flow continuous rather than recording that fact in a certificate. -/
theorem continuous_gaussianOUAverage_joint
    (f : BoundedContinuousFunction E F) :
    Continuous (fun p : ℝ × E => gaussianOUAverage p.1 f p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  apply tendsto_integral_filter_of_norm_le_const
  · exact Filter.Eventually.of_forall fun q =>
      (f.continuous.comp (by
        unfold gaussianOUTransition
        fun_prop)).aestronglyMeasurable
  · refine ⟨‖f‖, Filter.Eventually.of_forall fun _ =>
      Filter.Eventually.of_forall fun z => ?_⟩
    exact f.norm_coe_le_norm _
  · exact Filter.Eventually.of_forall fun z => by
      have htransition : Continuous
          (fun q : ℝ × E => gaussianOUTransition q.1 q.2 z) := by
        unfold gaussianOUTransition ouDriftCoeff ouNoiseCoeff
        fun_prop
      exact f.continuous.continuousAt.tendsto.comp htransition.continuousAt

theorem norm_gaussianOUAverage_le
    (t : ℝ) (f : BoundedContinuousFunction E F) (x : E) :
    ‖gaussianOUAverage t f x‖ ≤ ‖f‖ := by
  have h := norm_integral_le_of_norm_le_const
    (μ := stdGaussian E)
    (Filter.Eventually.of_forall fun z =>
      f.norm_coe_le_norm (gaussianOUTransition t x z))
  simpa [gaussianOUAverage] using h

/-- The Banach-valued Mehler average as a bounded continuous function. -/
def gaussianOUAverageBCF (t : ℝ) (f : BoundedContinuousFunction E F) :
    BoundedContinuousFunction E F :=
  BoundedContinuousFunction.mkOfBound
    ⟨gaussianOUAverage t f, continuous_gaussianOUAverage t f⟩
    (2 * ‖f‖) (by
      intro x y
      rw [dist_eq_norm]
      calc
        ‖gaussianOUAverage t f x - gaussianOUAverage t f y‖ ≤
            ‖gaussianOUAverage t f x‖ + ‖gaussianOUAverage t f y‖ :=
          norm_sub_le _ _
        _ ≤ ‖f‖ + ‖f‖ := add_le_add
          (norm_gaussianOUAverage_le t f x)
          (norm_gaussianOUAverage_le t f y)
        _ = 2 * ‖f‖ := by ring)

@[simp] theorem gaussianOUAverageBCF_apply
    (t : ℝ) (f : BoundedContinuousFunction E F) (x : E) :
    gaussianOUAverageBCF t f x = gaussianOUAverage t f x := rfl

@[simp] theorem gaussianOUAverageBCF_zero
    (f : BoundedContinuousFunction E F) :
    gaussianOUAverageBCF 0 f = f := by
  ext x
  simp [gaussianOUAverage]

/-- Positive-time differentiation of a Banach-valued Mehler average.  This
is the vector-valued counterpart of
`hasDerivAt_gaussianOUSemigroup_time_direct` and is used for the backward
gradient field. -/
theorem hasDerivAt_gaussianOUAverage_time_direct
    {t : ℝ} (ht : 0 < t)
    (f : BoundedContinuousFunction E F)
    (Df : BoundedContinuousFunction E (E →L[ℝ] F))
    (hDf : ∀ y, HasFDerivAt f (Df y) y) (x : E) :
    HasDerivAt (fun r => gaussianOUAverage r f x)
      (∫ z, Df (gaussianOUTransition t x z)
        (gaussianOUTransitionTimeDeriv t x z) ∂stdGaussian E) t := by
  let U : Set ℝ := Metric.ball t (t / 2)
  let a0 : ℝ := ouDriftCoeff (t / 2)
  let b0 : ℝ := ouNoiseCoeff (t / 2)
  let k : ℝ := a0 ^ 2 / b0
  let bound : E → ℝ := fun z => ‖Df‖ * (a0 * ‖x‖ + k * ‖z‖)
  have ht2 : 0 < t / 2 := by linarith
  have hb0 : 0 < b0 := by
    dsimp only [b0, ouNoiseCoeff]
    exact Real.sqrt_pos.2 (by
      change 0 < bobkovVarianceCoeff (t / 2)
      exact bobkovVarianceCoeff_pos ht2)
  have ha0 : 0 < a0 := ouDriftCoeff_pos _
  have hU : U ∈ nhds t := Metric.ball_mem_nhds t ht2
  have hrpos : ∀ r ∈ U, 0 < r := by
    intro r hr
    have hdist : |r - t| < t / 2 := by
      simpa [U, Real.dist_eq] using hr
    rw [abs_lt] at hdist
    linarith
  have ha_le : ∀ r ∈ U, ouDriftCoeff r ≤ a0 := by
    intro r hr
    exact antitone_ouDriftCoeff (by
      have hdist : |r - t| < t / 2 := by
        simpa [U, Real.dist_eq] using hr
      rw [abs_lt] at hdist
      linarith)
  have hb_le : ∀ r ∈ U, b0 ≤ ouNoiseCoeff r := by
    intro r hr
    apply monotone_ouNoiseCoeff_on_nonneg ht2.le (hrpos r hr).le
    have hdist : |r - t| < t / 2 := by
      simpa [U, Real.dist_eq] using hr
    rw [abs_lt] at hdist
    linarith
  have hk_le : ∀ r ∈ U,
      ouDriftCoeff r ^ 2 / ouNoiseCoeff r ≤ k := by
    intro r hr
    have har0 : 0 ≤ ouDriftCoeff r := (ouDriftCoeff_pos r).le
    have hbr0 : 0 < ouNoiseCoeff r := by
      dsimp only [ouNoiseCoeff]
      exact Real.sqrt_pos.2 (by
        change 0 < bobkovVarianceCoeff r
        exact bobkovVarianceCoeff_pos (hrpos r hr))
    exact div_le_div₀ (sq_nonneg a0)
      ((sq_le_sq₀ har0 ha0.le).2 (ha_le r hr)) hb0 (hb_le r hr)
  have hboundInt : Integrable bound (stdGaussian E) := by
    have hnorm : Integrable (fun z : E => ‖z‖) (stdGaussian E) :=
      IsGaussian.integrable_id.norm
    exact ((integrable_const (a0 * ‖x‖)).add
      (hnorm.const_mul k)).const_mul ‖Df‖
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := stdGaussian E)
    (F := fun r z => f (gaussianOUTransition r x z))
    (F' := fun r z => Df (gaussianOUTransition r x z)
      (gaussianOUTransitionTimeDeriv r x z))
    (bound := bound) hU
  have hresult : HasDerivAt
      (fun r => ∫ z, f (gaussianOUTransition r x z) ∂stdGaussian E)
      (∫ z, Df (gaussianOUTransition t x z)
        (gaussianOUTransitionTimeDeriv t x z) ∂stdGaussian E) t := by
    apply (hmain ?_ ?_ ?_ ?_ hboundInt ?_).2
    · exact Filter.Eventually.of_forall fun r =>
        (f.continuous.comp (by
          unfold gaussianOUTransition
          fun_prop)).aestronglyMeasurable
    · refine Integrable.of_bound
        (f.continuous.comp (by
          unfold gaussianOUTransition
          fun_prop)).aestronglyMeasurable ‖f‖ ?_
      exact Filter.Eventually.of_forall fun z => f.norm_coe_le_norm _
    · exact (show Continuous (fun z : E =>
          Df (gaussianOUTransition t x z)
            (gaussianOUTransitionTimeDeriv t x z)) by
        unfold gaussianOUTransition gaussianOUTransitionTimeDeriv
        fun_prop).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun z r hr => by
        have haabs : |ouDriftCoeff r| ≤ a0 := by
          rw [abs_of_pos (ouDriftCoeff_pos r)]
          exact ha_le r hr
        have hkabs : |ouDriftCoeff r ^ 2 / ouNoiseCoeff r| ≤ k := by
          rw [abs_of_nonneg (div_nonneg (sq_nonneg _)
            (ouNoiseCoeff_nonneg r))]
          exact hk_le r hr
        have hvel : ‖gaussianOUTransitionTimeDeriv r x z‖ ≤
            a0 * ‖x‖ + k * ‖z‖ := by
          unfold gaussianOUTransitionTimeDeriv
          calc
            ‖(-ouDriftCoeff r) • x +
                (ouDriftCoeff r ^ 2 / ouNoiseCoeff r) • z‖ ≤
                ‖(-ouDriftCoeff r) • x‖ +
                  ‖(ouDriftCoeff r ^ 2 / ouNoiseCoeff r) • z‖ :=
              norm_add_le _ _
            _ = |ouDriftCoeff r| * ‖x‖ +
                |ouDriftCoeff r ^ 2 / ouNoiseCoeff r| * ‖z‖ := by
              simp only [norm_smul, Real.norm_eq_abs, abs_neg]
            _ ≤ a0 * ‖x‖ + k * ‖z‖ :=
              add_le_add
                (mul_le_mul_of_nonneg_right haabs (norm_nonneg _))
                (mul_le_mul_of_nonneg_right hkabs (norm_nonneg _))
        calc
          ‖Df (gaussianOUTransition r x z)
              (gaussianOUTransitionTimeDeriv r x z)‖ ≤
              ‖Df (gaussianOUTransition r x z)‖ *
                ‖gaussianOUTransitionTimeDeriv r x z‖ :=
            (Df (gaussianOUTransition r x z)).le_opNorm _
          _ ≤ ‖Df‖ * ‖gaussianOUTransitionTimeDeriv r x z‖ :=
            mul_le_mul_of_nonneg_right (Df.norm_coe_le_norm _) (norm_nonneg _)
          _ ≤ ‖Df‖ * (a0 * ‖x‖ + k * ‖z‖) :=
            mul_le_mul_of_nonneg_left hvel (norm_nonneg Df)
          _ = bound z := rfl
    · exact Filter.Eventually.of_forall fun z r hr => by
        have hcomp := (hDf (gaussianOUTransition r x z)).comp r
          (hasDerivAt_gaussianOUTransition_time (hrpos r hr) x z).hasFDerivAt
        simpa [Function.comp_def] using hcomp.hasDerivAt
  simpa [gaussianOUAverage] using hresult

/-- Fréchet-derivative commutation for a Banach-valued Mehler average.
This extends `hasFDerivAt_gaussianOUSemigroup` from scalar functions to the
covector- and Hessian-valued fields needed below. -/
theorem hasFDerivAt_gaussianOUAverage
    (t : ℝ) (f : BoundedContinuousFunction E F)
    (Df : BoundedContinuousFunction E (E →L[ℝ] F))
    (hDf : ∀ y, HasFDerivAt f (Df y) y) (x : E) :
    HasFDerivAt (gaussianOUAverage t f)
      (ouDriftCoeff t •
        ∫ z, Df (gaussianOUTransition t x z) ∂stdGaussian E) x := by
  let G : E → E → F := fun y z => f (gaussianOUTransition t y z)
  let G' : E → E → E →L[ℝ] F := fun y z =>
    ouDriftCoeff t • Df (gaussianOUTransition t y z)
  have hcore : HasFDerivAt (fun y : E => ∫ z, G y z ∂stdGaussian E)
      (∫ z, G' x z ∂stdGaussian E) x := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le
      (s := Set.univ) (bound := fun _ : E => |ouDriftCoeff t| * ‖Df‖)
    · exact Filter.univ_mem
    · exact Filter.Eventually.of_forall fun y =>
        (f.continuous.comp (by
          unfold gaussianOUTransition
          fun_prop)).aestronglyMeasurable
    · refine Integrable.of_bound
        (f.continuous.comp (by
          unfold gaussianOUTransition
          fun_prop)).aestronglyMeasurable ‖f‖ ?_
      exact Filter.Eventually.of_forall fun z => f.norm_coe_le_norm _
    · exact (Df.continuous.comp (by
          unfold gaussianOUTransition
          fun_prop)).const_smul (ouDriftCoeff t) |>.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun z y _ => by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (Df.norm_coe_le_norm _) (abs_nonneg _)
    · exact integrable_const _
    · exact Filter.Eventually.of_forall fun z y _ => by
        have haff : HasFDerivAt (fun w : E => gaussianOUTransition t w z)
            (ouDriftCoeff t • ContinuousLinearMap.id ℝ E) y := by
          simpa [gaussianOUTransition] using
            ((hasFDerivAt_id y).const_smul (ouDriftCoeff t)).add_const
              (ouNoiseCoeff t • z)
        have hcomp := (hDf (gaussianOUTransition t y z)).comp y haff
        apply hcomp.congr_fderiv
        ext v
        simp [G']
  change HasFDerivAt (fun y : E => ∫ z, G y z ∂stdGaussian E) _ x
  convert hcore using 1
  rw [integral_smul]

/-- Spatial differentiation with an explicitly bounded raw derivative
field.  This variant is tailored to iterated operator-valued derivatives. -/
theorem hasFDerivAt_gaussianOUAverage_of_rawDerivative
    (t : ℝ) (f : BoundedContinuousFunction E F)
    (Df : E → E →L[ℝ] F) (hDfContinuous : Continuous Df)
    (C : ℝ) (hC : ∀ y, ‖Df y‖ ≤ C)
    (hDf : ∀ y, HasFDerivAt f (Df y) y) (x : E) :
    HasFDerivAt (gaussianOUAverage t f)
      (ouDriftCoeff t •
        ∫ z, Df (gaussianOUTransition t x z) ∂stdGaussian E) x := by
  let G : E → E → F := fun y z => f (gaussianOUTransition t y z)
  let G' : E → E → E →L[ℝ] F := fun y z =>
    ouDriftCoeff t • Df (gaussianOUTransition t y z)
  have hcore : HasFDerivAt (fun y : E => ∫ z, G y z ∂stdGaussian E)
      (∫ z, G' x z ∂stdGaussian E) x := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le
      (s := Set.univ) (bound := fun _ : E => |ouDriftCoeff t| * C)
    · exact Filter.univ_mem
    · exact Filter.Eventually.of_forall fun y =>
        (f.continuous.comp (by
          unfold gaussianOUTransition
          fun_prop)).aestronglyMeasurable
    · refine Integrable.of_bound
        (f.continuous.comp (by
          unfold gaussianOUTransition
          fun_prop)).aestronglyMeasurable ‖f‖ ?_
      exact Filter.Eventually.of_forall fun z => f.norm_coe_le_norm _
    · exact (hDfContinuous.comp (by
          unfold gaussianOUTransition
          fun_prop)).const_smul (ouDriftCoeff t) |>.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun z y _ => by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _)
    · exact integrable_const _
    · exact Filter.Eventually.of_forall fun z y _ => by
        have haff : HasFDerivAt (fun w : E => gaussianOUTransition t w z)
            (ouDriftCoeff t • ContinuousLinearMap.id ℝ E) y := by
          simpa [gaussianOUTransition] using
            ((hasFDerivAt_id y).const_smul (ouDriftCoeff t)).add_const
              (ouNoiseCoeff t • z)
        have hcomp := (hDf (gaussianOUTransition t y z)).comp y haff
        apply hcomp.congr_fderiv
        ext v
        simp [G']
  change HasFDerivAt (fun y : E => ∫ z, G y z ∂stdGaussian E) _ x
  convert hcore using 1
  rw [integral_smul]

end Average

section RealAverage

/-- A Mehler average preserves a closed scalar range. -/
theorem gaussianOUAverage_mem_Icc
    (t : ℝ) (f : BoundedContinuousFunction E ℝ)
    {a b : ℝ} (hf : ∀ x, f x ∈ Icc a b) (x : E) :
    gaussianOUAverage t f x ∈ Icc a b := by
  have hfi : Integrable
      (fun z => f (gaussianOUTransition t x z)) (stdGaussian E) := by
    refine Integrable.of_bound
      (f.continuous.comp (by
        unfold gaussianOUTransition
        fun_prop)).aestronglyMeasurable ‖f‖ ?_
    exact Filter.Eventually.of_forall fun z => f.norm_coe_le_norm _
  constructor
  · have h := integral_mono_ae (integrable_const a) hfi
      (Filter.Eventually.of_forall fun z => (hf _).1)
    simpa [gaussianOUAverage] using h
  · have h := integral_mono_ae hfi (integrable_const b)
      (Filter.Eventually.of_forall fun z => (hf _).2)
    simpa [gaussianOUAverage] using h

end RealAverage

section BackwardFields

/-- The backward value field `u_s = P_(t-s) f`, bundled continuously and
boundedly in the spatial variable. -/
def backwardGaussianOUValueBCF (t s : ℝ)
    (f : BoundedContinuousFunction E ℝ) :
    BoundedContinuousFunction E ℝ :=
  gaussianOUAverageBCF (t - s) f

/-- The canonical backward spatial derivative
`exp(-(t-s)) P_(t-s) Df`. -/
def backwardGaussianOUDerivBCF (t s : ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ)) :
    BoundedContinuousFunction E (E →L[ℝ] ℝ) :=
  ouDriftCoeff (t - s) • gaussianOUAverageBCF (t - s) Df

theorem continuous_backwardGaussianOUValue_joint
    (t : ℝ) (f : BoundedContinuousFunction E ℝ) :
    Continuous (fun p : ℝ × E => backwardGaussianOUValueBCF t p.1 f p.2) := by
  have harg : Continuous (fun p : ℝ × E => (t - p.1, p.2)) := by
    fun_prop
  change Continuous (fun p : ℝ × E =>
    gaussianOUAverage (t - p.1) f p.2)
  convert (continuous_gaussianOUAverage_joint f).comp harg using 1
  funext p
  rfl

theorem continuous_backwardGaussianOUDeriv_joint
    (t : ℝ) (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ)) :
    Continuous (fun p : ℝ × E => backwardGaussianOUDerivBCF t p.1 Df p.2) := by
  have harg : Continuous (fun p : ℝ × E => (t - p.1, p.2)) := by
    fun_prop
  have havg : Continuous (fun p : ℝ × E =>
      gaussianOUAverage (t - p.1) Df p.2) := by
    rw [continuous_iff_continuousAt]
    intro p
    apply tendsto_integral_filter_of_norm_le_const
    · exact Filter.Eventually.of_forall fun q =>
        (Df.continuous.comp (by
          unfold gaussianOUTransition
          fun_prop)).aestronglyMeasurable
    · refine ⟨‖Df‖, Filter.Eventually.of_forall fun _ =>
        Filter.Eventually.of_forall fun z => ?_⟩
      exact Df.norm_coe_le_norm _
    · exact Filter.Eventually.of_forall fun z => by
        have htransition : Continuous
            (fun q : ℝ × E =>
              gaussianOUTransition (t - q.1) q.2 z) := by
          unfold gaussianOUTransition ouDriftCoeff ouNoiseCoeff
          fun_prop
        exact Df.continuous.continuousAt.tendsto.comp
          htransition.continuousAt
  have hcoeff : Continuous (fun p : ℝ × E => ouDriftCoeff (t - p.1)) := by
    unfold ouDriftCoeff
    fun_prop
  change Continuous (fun p : ℝ × E =>
    ouDriftCoeff (t - p.1) • gaussianOUAverage (t - p.1) Df p.2)
  convert hcoeff.smul havg using 1
  funext p
  rfl

@[simp] theorem backwardGaussianOUValueBCF_apply
    (t s : ℝ) (f : BoundedContinuousFunction E ℝ) (x : E) :
    backwardGaussianOUValueBCF t s f x =
      gaussianOUSemigroup (t - s) f x := rfl

@[simp] theorem backwardGaussianOUDerivBCF_apply
    (t s : ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ)) (x : E) :
    backwardGaussianOUDerivBCF t s Df x =
      ouDriftCoeff (t - s) •
        ∫ z, Df (gaussianOUTransition (t - s) x z) ∂stdGaussian E := rfl

theorem hasFDerivAt_backwardGaussianOUValueBCF
    (t s : ℝ) (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (hDf : ∀ y, HasFDerivAt f (Df y) y) (x : E) :
    HasFDerivAt (backwardGaussianOUValueBCF t s f)
      (backwardGaussianOUDerivBCF t s Df x) x := by
  exact hasFDerivAt_gaussianOUSemigroup (t - s) f Df hDf x

/-- The explicit backward-time derivative of the value field.  It is kept
as a raw (generally unbounded in `x`) function because the Mehler velocity
has linear growth. -/
def backwardGaussianOUValueTimeDeriv (t s : ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ)) (x : E) : ℝ :=
  -∫ z, Df (gaussianOUTransition (t - s) x z)
    (gaussianOUTransitionTimeDeriv (t - s) x z) ∂stdGaussian E

/-- Positive-lag backward-time differentiation of `P_(t-s) f`. -/
theorem hasDerivAt_backwardGaussianOUValueBCF_time
    (t s : ℝ) (hst : s < t)
    (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (hDf : ∀ y, HasFDerivAt f (Df y) y) (x : E) :
    HasDerivAt (fun r => backwardGaussianOUValueBCF t r f x)
      (backwardGaussianOUValueTimeDeriv t s Df x) s := by
  have hlag : 0 < t - s := sub_pos.2 hst
  have havg := hasDerivAt_gaussianOUAverage_time_direct
    hlag f Df hDf x
  have hinner : HasDerivAt (fun r : ℝ => t - r) (-1) s := by
    convert (hasDerivAt_const s t).sub (hasDerivAt_id s) using 1 <;>
      first | rfl | norm_num
  have hcomp := havg.scomp s hinner
  simpa [backwardGaussianOUValueBCF, backwardGaussianOUValueTimeDeriv,
    Function.comp_def, gaussianOUAverage] using hcomp

/-- The explicit backward-time derivative of the covector field
`exp(-(t-s)) P_(t-s) Df`. -/
def backwardGaussianOUDerivTimeDeriv (t s : ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (D2f : BoundedContinuousFunction E
      (E →L[ℝ] (E →L[ℝ] ℝ))) (x : E) : E →L[ℝ] ℝ :=
  ouDriftCoeff (t - s) • gaussianOUAverage (t - s) Df x -
    ouDriftCoeff (t - s) •
      (∫ z, D2f (gaussianOUTransition (t - s) x z)
        (gaussianOUTransitionTimeDeriv (t - s) x z) ∂stdGaussian E)

/-- Positive-lag backward-time differentiation of the canonical covector
field, assuming a bounded continuous Hessian field for `f`. -/
theorem hasDerivAt_backwardGaussianOUDerivBCF_time
    (t s : ℝ) (hst : s < t)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (D2f : BoundedContinuousFunction E
      (E →L[ℝ] (E →L[ℝ] ℝ)))
    (hD2f : ∀ y, HasFDerivAt Df (D2f y) y) (x : E) :
    HasDerivAt (fun r => backwardGaussianOUDerivBCF t r Df x)
      (backwardGaussianOUDerivTimeDeriv t s Df D2f x) s := by
  have hlag : 0 < t - s := sub_pos.2 hst
  have havg := hasDerivAt_gaussianOUAverage_time_direct
    hlag Df D2f hD2f x
  have hcoeff := hasDerivAt_ouDriftCoeff (t - s)
  have hproduct := hcoeff.smul havg
  have hinner : HasDerivAt (fun r : ℝ => t - r) (-1) s := by
    convert (hasDerivAt_const s t).sub (hasDerivAt_id s) using 1 <;>
      first | rfl | norm_num
  have hcomp := hproduct.scomp s hinner
  simpa [backwardGaussianOUDerivBCF, backwardGaussianOUDerivTimeDeriv,
    Function.comp_def, gaussianOUAverage, sub_eq_add_neg, add_comm,
    add_left_comm, add_assoc] using hcomp

@[simp] theorem backwardGaussianOUValueBCF_terminal
    (t : ℝ) (f : BoundedContinuousFunction E ℝ) :
    backwardGaussianOUValueBCF t t f = f := by
  simp [backwardGaussianOUValueBCF]

@[simp] theorem backwardGaussianOUDerivBCF_terminal
    (t : ℝ) (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ)) :
    backwardGaussianOUDerivBCF t t Df = Df := by
  simp [backwardGaussianOUDerivBCF]

theorem backwardGaussianOUValueBCF_mem_Icc
    (t s : ℝ) (f : BoundedContinuousFunction E ℝ)
    {a b : ℝ} (hf : ∀ x, f x ∈ Icc a b) (x : E) :
    backwardGaussianOUValueBCF t s f x ∈ Icc a b := by
  exact gaussianOUAverage_mem_Icc (t - s) f hf x

end BackwardFields

section BobkovField

/-- Turn a bounded continuous covector field into its Riesz-representative
gradient vector field.  The isometry preserves pointwise norms exactly. -/
def rieszGradientBCF
    (D : BoundedContinuousFunction E (E →L[ℝ] ℝ)) :
    BoundedContinuousFunction E E :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => (InnerProductSpace.toDual ℝ E).symm (D x),
      (InnerProductSpace.toDual ℝ E).symm.continuous.comp D.continuous⟩
    (2 * ‖D‖) (by
      intro x y
      rw [dist_eq_norm]
      change ‖(InnerProductSpace.toDual ℝ E).symm (D x) -
        (InnerProductSpace.toDual ℝ E).symm (D y)‖ ≤ 2 * ‖D‖
      rw [← map_sub, (InnerProductSpace.toDual ℝ E).symm.norm_map]
      calc
        ‖D x - D y‖ ≤ ‖D x‖ + ‖D y‖ := norm_sub_le _ _
        _ ≤ ‖D‖ + ‖D‖ :=
          add_le_add (D.norm_coe_le_norm x) (D.norm_coe_le_norm y)
        _ = 2 * ‖D‖ := by ring)

@[simp] theorem norm_rieszGradientBCF
    (D : BoundedContinuousFunction E (E →L[ℝ] ℝ)) (x : E) :
    ‖rieszGradientBCF D x‖ = ‖D x‖ := by
  exact (InnerProductSpace.toDual ℝ E).symm.norm_map (D x)

@[simp] theorem inner_rieszGradientBCF
    (D : BoundedContinuousFunction E (E →L[ℝ] ℝ)) (x h : E) :
    inner ℝ (rieszGradientBCF D x) h = D x h := by
  exact InnerProductSpace.toDual_symm_apply

/-- Apply the inverse real Riesz isometry to the output of every covector
Hessian in a bounded continuous field. -/
def rieszHessianBCF
    (D2 : BoundedContinuousFunction E
      (E →L[ℝ] (E →L[ℝ] ℝ))) :
    BoundedContinuousFunction E (E →L[ℝ] E) :=
  let L :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E) L)
    |>.compLeftContinuousBounded E D2

@[simp] theorem rieszHessianBCF_apply
    (D2 : BoundedContinuousFunction E
      (E →L[ℝ] (E →L[ℝ] ℝ))) (x : E) :
    rieszHessianBCF D2 x =
      (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (D2 x) := rfl

/-- The covector Hessian of the backward OU value field.  It is kept as a
raw field: pointwise differentiation only needs its value, while avoiding a
fragile bounded-function instance for iterated operator spaces. -/
def backwardGaussianOUCovectorHessian (t s : ℝ)
    (D2f : BoundedContinuousFunction E
      (E →L[ℝ] (E →L[ℝ] ℝ))) (x : E) :
    E →L[ℝ] (E →L[ℝ] ℝ) :=
  (ouDriftCoeff (t - s) ^ 2) •
    gaussianOUAverageRaw (t - s) (fun y => D2f y) x

/-- The Riesz-represented Hessian of the backward OU value field. -/
def backwardGaussianOUHessian (t s : ℝ)
    (D2f : BoundedContinuousFunction E
      (E →L[ℝ] (E →L[ℝ] ℝ))) (x : E) : E →L[ℝ] E :=
  (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (backwardGaussianOUCovectorHessian t s D2f x)

/-- Spatial differentiation of the backward covector field. -/
theorem hasFDerivAt_backwardGaussianOUDerivBCF
    (t s : ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (D2f : BoundedContinuousFunction E
      (E →L[ℝ] (E →L[ℝ] ℝ)))
    (M : ℝ) (hD2bound : ∀ y, ‖D2f y‖ ≤ M)
    (hD2f : ∀ y, HasFDerivAt Df (D2f y) y) (x : E) :
    HasFDerivAt (backwardGaussianOUDerivBCF t s Df)
      (backwardGaussianOUCovectorHessian t s D2f x) x := by
  have havg := hasFDerivAt_gaussianOUAverage_of_rawDerivative
    (E := E) (F := E →L[ℝ] ℝ) (t - s) Df (fun y => D2f y)
    D2f.continuous M hD2bound hD2f x
  have hscaled := havg.const_smul (ouDriftCoeff (t - s))
  convert hscaled using 1 <;>
    first
    | rfl
    | simp [backwardGaussianOUDerivBCF,
        backwardGaussianOUCovectorHessian, gaussianOUAverageBCF,
        gaussianOUAverageRaw, smul_smul, pow_two]

/-- Spatial differentiation of the Riesz gradient field. -/
theorem hasFDerivAt_rieszGradient_backwardGaussianOU
    (t s : ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (D2f : BoundedContinuousFunction E
      (E →L[ℝ] (E →L[ℝ] ℝ)))
    (M : ℝ) (hD2bound : ∀ y, ‖D2f y‖ ≤ M)
    (hD2f : ∀ y, HasFDerivAt Df (D2f y) y) (x : E) :
    HasFDerivAt
      (rieszGradientBCF (backwardGaussianOUDerivBCF t s Df))
      (backwardGaussianOUHessian t s D2f x) x := by
  let L :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hcov := hasFDerivAt_backwardGaussianOUDerivBCF
    t s Df D2f M hD2bound hD2f x
  have hcomp := L.hasFDerivAt.comp x hcov
  simpa [L, rieszGradientBCF, backwardGaussianOUHessian,
    Function.comp_def] using hcomp

/-- The Riesz-represented backward-time derivative of the gradient field. -/
def backwardGaussianOUGradientTimeDeriv (t s : ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (D2f : BoundedContinuousFunction E
      (E →L[ℝ] (E →L[ℝ] ℝ))) (x : E) : E :=
  (InnerProductSpace.toDual ℝ E).symm
    (backwardGaussianOUDerivTimeDeriv t s Df D2f x)

/-- Positive-lag backward-time differentiation of the Riesz gradient. -/
theorem hasDerivAt_rieszGradient_backwardGaussianOU_time
    (t s : ℝ) (hst : s < t)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (D2f : BoundedContinuousFunction E
      (E →L[ℝ] (E →L[ℝ] ℝ)))
    (hD2f : ∀ y, HasFDerivAt Df (D2f y) y) (x : E) :
    HasDerivAt
      (fun r => rieszGradientBCF
        (backwardGaussianOUDerivBCF t r Df) x)
      (backwardGaussianOUGradientTimeDeriv t s Df D2f x) s := by
  let L :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hcov := hasDerivAt_backwardGaussianOUDerivBCF_time
    t s hst Df D2f hD2f x
  have hcomp := L.hasFDerivAt.comp_hasDerivAt s hcov
  simpa [L, rieszGradientBCF, backwardGaussianOUGradientTimeDeriv,
    Function.comp_def] using hcomp

/-- The bounded continuous square-root field associated with a profile field
`q`, a covector field `D`, and a scalar variance coefficient `c`. -/
def bobkovSqrtBCF (c : ℝ) (q : BoundedContinuousFunction E ℝ)
    (D : BoundedContinuousFunction E (E →L[ℝ] ℝ)) :
    BoundedContinuousFunction E ℝ :=
  let M := Real.sqrt (‖q‖ ^ 2 + |c| * ‖D‖ ^ 2)
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => Real.sqrt (q x ^ 2 + c * ‖D x‖ ^ 2), by fun_prop⟩
    (2 * M) (by
      intro x y
      have hvalue (z : E) :
          ‖Real.sqrt (q z ^ 2 + c * ‖D z‖ ^ 2)‖ ≤ M := by
        have hqnorm : |q z| ≤ ‖q‖ := by
          simpa [Real.norm_eq_abs] using q.norm_coe_le_norm z
        have hDnorm : ‖D z‖ ≤ ‖D‖ := D.norm_coe_le_norm z
        have hqsq : q z ^ 2 ≤ ‖q‖ ^ 2 := by
          rw [← sq_abs]
          exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 hqnorm
        have hDsq : ‖D z‖ ^ 2 ≤ ‖D‖ ^ 2 := by
          simpa [pow_two] using
            (mul_self_le_mul_self (norm_nonneg (D z)) hDnorm)
        have hcD : c * ‖D z‖ ^ 2 ≤ |c| * ‖D‖ ^ 2 := by
          calc
            c * ‖D z‖ ^ 2 ≤ |c| * ‖D z‖ ^ 2 :=
              mul_le_mul_of_nonneg_right (le_abs_self c) (sq_nonneg _)
            _ ≤ |c| * ‖D‖ ^ 2 :=
              mul_le_mul_of_nonneg_left hDsq (abs_nonneg c)
        have hrad : q z ^ 2 + c * ‖D z‖ ^ 2 ≤
            ‖q‖ ^ 2 + |c| * ‖D‖ ^ 2 := add_le_add hqsq hcD
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact Real.sqrt_le_sqrt hrad
      rw [Real.dist_eq]
      calc
        |Real.sqrt (q x ^ 2 + c * ‖D x‖ ^ 2) -
            Real.sqrt (q y ^ 2 + c * ‖D y‖ ^ 2)| ≤
            ‖Real.sqrt (q x ^ 2 + c * ‖D x‖ ^ 2)‖ +
              ‖Real.sqrt (q y ^ 2 + c * ‖D y‖ ^ 2)‖ := by
          simpa [Real.norm_eq_abs] using norm_sub_le
            (Real.sqrt (q x ^ 2 + c * ‖D x‖ ^ 2))
            (Real.sqrt (q y ^ 2 + c * ‖D y‖ ^ 2))
        _ ≤ M + M := add_le_add (hvalue x) (hvalue y)
        _ = 2 * M := by ring)

@[simp] theorem bobkovSqrtBCF_apply
    (c : ℝ) (q : BoundedContinuousFunction E ℝ)
    (D : BoundedContinuousFunction E (E →L[ℝ] ℝ)) (x : E) :
    bobkovSqrtBCF c q D x = Real.sqrt (q x ^ 2 + c * ‖D x‖ ^ 2) := rfl

/-- Spatial Fréchet derivative of the canonical Bobkov square root, written
with a genuine gradient vector field.  This formulation avoids imposing a
Hilbert-space structure on the space of covectors.  Later the Riesz isometry
identifies the norm of this vector with the norm of the recorded derivative
used in `canonicalGaussianBobkovQ`.

The theorem only uses first derivatives of `u` and of its gradient.  The
strict interior condition makes the radicand positive, so the square-root
chain rule has no singular case. -/
theorem hasFDerivAt_bobkovSqrt_of_gradient
    {u : E → ℝ} {v : E → E}
    {Dux : E →L[ℝ] ℝ} {Hx : E →L[ℝ] E}
    {x : E} {c : ℝ}
    (hu : HasFDerivAt u Dux x)
    (hv : HasFDerivAt v Hx x)
    (hux : u x ∈ Ioo (0 : ℝ) 1) (hc : 0 ≤ c) :
    HasFDerivAt
      (fun y => Real.sqrt (normalProfile (u y) ^ 2 + c * ‖v y‖ ^ 2))
      ((1 / (2 * Real.sqrt
          (normalProfile (u x) ^ 2 + c * ‖v x‖ ^ 2))) •
        (((2 : ℕ) • normalProfile (u x) *
            (-lowerQuantile standardGaussianMeasure (u x))) • Dux +
          c • (2 • (innerSL ℝ (v x)).comp Hx))) x := by
  have hI := (hasDerivAt_normalProfile hux).comp_hasFDerivAt x hu
  have hIsq := hI.pow 2
  have hvsq := hv.norm_sq
  have hA := hIsq.add (hvsq.const_mul c)
  have hApos : 0 < normalProfile (u x) ^ 2 + c * ‖v x‖ ^ 2 := by
    have hIp : 0 < normalProfile (u x) := normalProfile_pos hux
    nlinarith [mul_nonneg hc (sq_nonneg ‖v x‖)]
  have hs := hA.sqrt hApos.ne'
  simpa only [Function.comp_apply, Pi.add_apply, Nat.reduceSub, pow_one,
    Nat.cast_ofNat, smul_smul, mul_assoc] using hs

/-- Time derivative of the same square-root field.  The formula exposes the
time derivative of the radicand verbatim.  In the canonical application
`c = bobkovVarianceCoeff`, so its derivative is subsequently replaced by
`2 * (1-c)` and combined with the backward OU/Bochner identities. -/
theorem hasDerivAt_bobkovSqrt_time
    {u : ℝ → ℝ} {v : ℝ → E} {c : ℝ → ℝ}
    {s us cp : ℝ} {vs : E}
    (hu : HasDerivAt u us s)
    (hv : HasDerivAt v vs s)
    (hcvar : HasDerivAt c cp s)
    (hus : u s ∈ Ioo (0 : ℝ) 1) (hcs : 0 ≤ c s) :
    HasDerivAt
      (fun r => Real.sqrt
        (normalProfile (u r) ^ 2 + c r * ‖v r‖ ^ 2))
      ((2 * normalProfile (u s) *
            (-lowerQuantile standardGaussianMeasure (u s)) * us +
          cp * ‖v s‖ ^ 2 + 2 * c s * inner ℝ (v s) vs) /
        (2 * Real.sqrt
          (normalProfile (u s) ^ 2 + c s * ‖v s‖ ^ 2))) s := by
  have hI := (hasDerivAt_normalProfile hus).comp s hu
  have hIsq := hI.pow 2
  have hvsq := hv.norm_sq
  have hprod := hcvar.mul hvsq
  have hA := hIsq.add hprod
  have hApos : 0 < normalProfile (u s) ^ 2 + c s * ‖v s‖ ^ 2 := by
    have hIp : 0 < normalProfile (u s) := normalProfile_pos hus
    nlinarith [mul_nonneg hcs (sq_nonneg ‖v s‖)]
  have hsqrt := hA.sqrt hApos.ne'
  have hsqrt' := hsqrt
  simp only [Function.comp_apply, Pi.pow_apply, Pi.add_apply, Pi.mul_apply,
    Nat.reduceSub, pow_one, Nat.cast_ofNat] at hsqrt'
  apply hsqrt'.congr_deriv
  ring

/-- The canonical Bobkov square-root field formed from an interior-valued
scalar field and its recorded derivative. -/
def gaussianBobkovQBCF (s : ℝ) (u : BoundedContinuousFunction E ℝ)
    (Du : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (ε : ℝ) (hε : 0 < ε) (hu : ∀ x, u x ∈ Icc ε (1 - ε)) :
    BoundedContinuousFunction E ℝ :=
  bobkovSqrtBCF (bobkovVarianceCoeff s)
    (normalProfileCompBCF u ε hε hu) Du

@[simp] theorem gaussianBobkovQBCF_apply
    (s : ℝ) (u : BoundedContinuousFunction E ℝ)
    (Du : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (ε : ℝ) (hε : 0 < ε) (hu : ∀ x, u x ∈ Icc ε (1 - ε))
    (x : E) :
    gaussianBobkovQBCF s u Du ε hε hu x =
      Real.sqrt (normalProfile (u x) ^ 2 +
        bobkovVarianceCoeff s * ‖Du x‖ ^ 2) := rfl

@[simp] theorem gaussianBobkovQBCF_zero
    (u : BoundedContinuousFunction E ℝ)
    (Du : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (ε : ℝ) (hε : 0 < ε) (hu : ∀ x, u x ∈ Icc ε (1 - ε))
    (x : E) :
    gaussianBobkovQBCF 0 u Du ε hε hu x = normalProfile (u x) := by
  rw [gaussianBobkovQBCF_apply, bobkovVarianceCoeff_zero, zero_mul,
    add_zero, Real.sqrt_sq_eq_abs]
  apply abs_of_pos
  exact normalProfile_pos
    ⟨hε.trans_le (hu x).1, (hu x).2.trans_lt (by linarith)⟩

/-- The canonical backward square-root field
`Q_s = sqrt(I(P_(t-s)f)^2 + c_s |∇P_(t-s)f|^2)`. -/
def canonicalGaussianBobkovQ
    (t : ℝ) (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (ε : ℝ) (hε : 0 < ε) (hf : ∀ x, f x ∈ Icc ε (1 - ε))
    (s : ℝ) : BoundedContinuousFunction E ℝ :=
  gaussianBobkovQBCF s
    (backwardGaussianOUValueBCF t s f)
    (backwardGaussianOUDerivBCF t s Df)
    ε hε (backwardGaussianOUValueBCF_mem_Icc t s f hf)

@[simp] theorem canonicalGaussianBobkovQ_apply
    (t : ℝ) (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (ε : ℝ) (hε : 0 < ε) (hf : ∀ x, f x ∈ Icc ε (1 - ε))
    (s : ℝ) (x : E) :
    canonicalGaussianBobkovQ t f Df ε hε hf s x =
      Real.sqrt
        (normalProfile (gaussianOUSemigroup (t - s) f x) ^ 2 +
          bobkovVarianceCoeff s *
            ‖backwardGaussianOUDerivBCF t s Df x‖ ^ 2) := rfl

/-- The spatial derivative of the canonical field, reduced to the Hessian of
the backward OU value.  Thus the remaining spatial analysis is precisely the
construction of a bounded derivative for the Riesz gradient; the nonlinear
normal-profile and square-root chain rules are discharged here. -/
theorem hasFDerivAt_canonicalGaussianBobkovQ_of_gradientDerivative
    (t : ℝ) (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (hDf : ∀ y, HasFDerivAt f (Df y) y)
    (ε : ℝ) (hε : 0 < ε) (hf : ∀ x, f x ∈ Icc ε (1 - ε))
    {s : ℝ} (hs : 0 ≤ s) {x : E} {H : E →L[ℝ] E}
    (hH : HasFDerivAt
      (rieszGradientBCF (backwardGaussianOUDerivBCF t s Df)) H x) :
    HasFDerivAt
      (canonicalGaussianBobkovQ t f Df ε hε hf s)
      ((1 / (2 * Real.sqrt
          (normalProfile (backwardGaussianOUValueBCF t s f x) ^ 2 +
            bobkovVarianceCoeff s *
              ‖backwardGaussianOUDerivBCF t s Df x‖ ^ 2))) •
        (((2 : ℕ) • normalProfile (backwardGaussianOUValueBCF t s f x) *
            (-lowerQuantile standardGaussianMeasure
              (backwardGaussianOUValueBCF t s f x))) •
              backwardGaussianOUDerivBCF t s Df x +
          bobkovVarianceCoeff s •
            (2 • (innerSL ℝ
              (rieszGradientBCF
                (backwardGaussianOUDerivBCF t s Df) x)).comp H))) x := by
  have huxClosed := backwardGaussianOUValueBCF_mem_Icc t s f hf x
  have hux : backwardGaussianOUValueBCF t s f x ∈ Ioo (0 : ℝ) 1 :=
    ⟨hε.trans_le huxClosed.1, huxClosed.2.trans_lt (by linarith)⟩
  have hu := hasFDerivAt_backwardGaussianOUValueBCF t s f Df hDf x
  have hraw := hasFDerivAt_bobkovSqrt_of_gradient hu hH hux
    (bobkovVarianceCoeff_nonneg hs)
  change HasFDerivAt
    (fun y => Real.sqrt
      (normalProfile (backwardGaussianOUValueBCF t s f y) ^ 2 +
        bobkovVarianceCoeff s *
          ‖backwardGaussianOUDerivBCF t s Df y‖ ^ 2)) _ x
  simpa only [norm_rieszGradientBCF] using hraw

/-- The time derivative of the canonical field, reduced to the backward time
derivatives of its value and Riesz-gradient fields.  The derivative of the
Bobkov variance coefficient is supplied by
`hasDerivAt_bobkovVarianceCoeff`. -/
theorem hasDerivAt_canonicalGaussianBobkovQ_of_backwardTimeDerivatives
    (t : ℝ) (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (ε : ℝ) (hε : 0 < ε) (hf : ∀ x, f x ∈ Icc ε (1 - ε))
    {s : ℝ} (hs : 0 ≤ s) (x : E) {us : ℝ} {vs : E}
    (hu : HasDerivAt
      (fun r => backwardGaussianOUValueBCF t r f x) us s)
    (hv : HasDerivAt
      (fun r => rieszGradientBCF
        (backwardGaussianOUDerivBCF t r Df) x) vs s) :
    HasDerivAt
      (fun r => canonicalGaussianBobkovQ t f Df ε hε hf r x)
      ((2 * normalProfile (backwardGaussianOUValueBCF t s f x) *
            (-lowerQuantile standardGaussianMeasure
              (backwardGaussianOUValueBCF t s f x)) * us +
          (2 * (1 - bobkovVarianceCoeff s)) *
            ‖backwardGaussianOUDerivBCF t s Df x‖ ^ 2 +
          2 * bobkovVarianceCoeff s *
            inner ℝ
              (rieszGradientBCF
                (backwardGaussianOUDerivBCF t s Df) x) vs) /
        (2 * Real.sqrt
          (normalProfile (backwardGaussianOUValueBCF t s f x) ^ 2 +
            bobkovVarianceCoeff s *
              ‖backwardGaussianOUDerivBCF t s Df x‖ ^ 2))) s := by
  have husClosed := backwardGaussianOUValueBCF_mem_Icc t s f hf x
  have hus : backwardGaussianOUValueBCF t s f x ∈ Ioo (0 : ℝ) 1 :=
    ⟨hε.trans_le husClosed.1, husClosed.2.trans_lt (by linarith)⟩
  have hraw := hasDerivAt_bobkovSqrt_time hu hv
    (hasDerivAt_bobkovVarianceCoeff s) hus
    (bobkovVarianceCoeff_nonneg hs)
  change HasDerivAt
    (fun r => Real.sqrt
      (normalProfile (backwardGaussianOUValueBCF t r f x) ^ 2 +
        bobkovVarianceCoeff r *
          ‖backwardGaussianOUDerivBCF t r Df x‖ ^ 2)) _ s
  simpa only [norm_rieszGradientBCF] using hraw

/-- The explicit spatial derivative produced by the canonical square-root
chain rule once a Riesz Hessian `H` is known. -/
def canonicalGaussianBobkovQSpatialDeriv
    (t : ℝ) (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (s : ℝ) (x : E) (H : E →L[ℝ] E) : E →L[ℝ] ℝ :=
  (1 / (2 * Real.sqrt
      (normalProfile (backwardGaussianOUValueBCF t s f x) ^ 2 +
        bobkovVarianceCoeff s *
          ‖backwardGaussianOUDerivBCF t s Df x‖ ^ 2))) •
    (((2 : ℕ) • normalProfile (backwardGaussianOUValueBCF t s f x) *
        (-lowerQuantile standardGaussianMeasure
          (backwardGaussianOUValueBCF t s f x))) •
          backwardGaussianOUDerivBCF t s Df x +
      bobkovVarianceCoeff s •
        (2 • (innerSL ℝ
          (rieszGradientBCF
            (backwardGaussianOUDerivBCF t s Df) x)).comp H))

/-- The explicit time derivative produced by the canonical square-root
chain rule from the backward value and gradient time derivatives. -/
def canonicalGaussianBobkovQTimeDeriv
    (t : ℝ) (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (s : ℝ) (x : E) (us : ℝ) (vs : E) : ℝ :=
  (2 * normalProfile (backwardGaussianOUValueBCF t s f x) *
        (-lowerQuantile standardGaussianMeasure
          (backwardGaussianOUValueBCF t s f x)) * us +
      (2 * (1 - bobkovVarianceCoeff s)) *
        ‖backwardGaussianOUDerivBCF t s Df x‖ ^ 2 +
      2 * bobkovVarianceCoeff s *
        inner ℝ
          (rieszGradientBCF
            (backwardGaussianOUDerivBCF t s Df) x) vs) /
    (2 * Real.sqrt
      (normalProfile (backwardGaussianOUValueBCF t s f x) ^ 2 +
        bobkovVarianceCoeff s *
          ‖backwardGaussianOUDerivBCF t s Df x‖ ^ 2))

/-- The canonical spatial derivative, with the Hessian premise discharged
by bounded second-derivative data for the terminal function. -/
theorem hasFDerivAt_canonicalGaussianBobkovQ_of_boundedHessian
    (t : ℝ) (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (hDf : ∀ y, HasFDerivAt f (Df y) y)
    (D2f : BoundedContinuousFunction E
      (E →L[ℝ] (E →L[ℝ] ℝ)))
    (M : ℝ) (hD2bound : ∀ y, ‖D2f y‖ ≤ M)
    (hD2f : ∀ y, HasFDerivAt Df (D2f y) y)
    (ε : ℝ) (hε : 0 < ε) (hf : ∀ x, f x ∈ Icc ε (1 - ε))
    {s : ℝ} (hs : 0 ≤ s) (x : E) :
    HasFDerivAt (canonicalGaussianBobkovQ t f Df ε hε hf s)
      (canonicalGaussianBobkovQSpatialDeriv t f Df s x
        (backwardGaussianOUHessian t s D2f x)) x := by
  have hH := hasFDerivAt_rieszGradient_backwardGaussianOU
    t s Df D2f M hD2bound hD2f x
  simpa [canonicalGaussianBobkovQSpatialDeriv] using
    hasFDerivAt_canonicalGaussianBobkovQ_of_gradientDerivative
      t f Df hDf ε hε hf hs hH

/-- The canonical time derivative, with both backward-time premises
discharged by bounded first- and second-derivative data. -/
theorem hasDerivAt_canonicalGaussianBobkovQ_of_boundedHessian
    (t : ℝ) (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (hDf : ∀ y, HasFDerivAt f (Df y) y)
    (D2f : BoundedContinuousFunction E
      (E →L[ℝ] (E →L[ℝ] ℝ)))
    (hD2f : ∀ y, HasFDerivAt Df (D2f y) y)
    (ε : ℝ) (hε : 0 < ε) (hf : ∀ x, f x ∈ Icc ε (1 - ε))
    {s : ℝ} (hs : 0 ≤ s) (hst : s < t) (x : E) :
    HasDerivAt
      (fun r => canonicalGaussianBobkovQ t f Df ε hε hf r x)
      (canonicalGaussianBobkovQTimeDeriv t f Df s x
        (backwardGaussianOUValueTimeDeriv t s Df x)
        (backwardGaussianOUGradientTimeDeriv t s Df D2f x)) s := by
  have hu := hasDerivAt_backwardGaussianOUValueBCF_time
    t s hst f Df hDf x
  have hv := hasDerivAt_rieszGradient_backwardGaussianOU_time
    t s hst Df D2f hD2f x
  simpa [canonicalGaussianBobkovQTimeDeriv] using
    hasDerivAt_canonicalGaussianBobkovQ_of_backwardTimeDerivatives
      t f Df ε hε hf hs x hu hv

/-- Joint time/space continuity of the canonical square-root field.  The
normal profile is only composed with backward values in the fixed compact
subinterval `[ε,1-ε]`, so its endpoint singularities never enter. -/
theorem continuous_canonicalGaussianBobkovQ_joint
    (t : ℝ) (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (ε : ℝ) (hε : 0 < ε) (hf : ∀ x, f x ∈ Icc ε (1 - ε)) :
    Continuous (fun p : ℝ × E =>
      canonicalGaussianBobkovQ t f Df ε hε hf p.1 p.2) := by
  have hu : Continuous (fun p : ℝ × E =>
      backwardGaussianOUValueBCF t p.1 f p.2) :=
    continuous_backwardGaussianOUValue_joint t f
  have hD : Continuous (fun p : ℝ × E =>
      backwardGaussianOUDerivBCF t p.1 Df p.2) :=
    continuous_backwardGaussianOUDeriv_joint t Df
  have hI : Continuous (fun p : ℝ × E =>
      normalProfile (backwardGaussianOUValueBCF t p.1 f p.2)) := by
    rw [continuous_iff_continuousAt]
    intro p
    have hpClosed := backwardGaussianOUValueBCF_mem_Icc
      t p.1 f hf p.2
    have hp : backwardGaussianOUValueBCF t p.1 f p.2 ∈ Ioo (0 : ℝ) 1 :=
      ⟨hε.trans_le hpClosed.1,
        hpClosed.2.trans_lt (by linarith)⟩
    exact (hasDerivAt_normalProfile hp).continuousAt.comp'
      (f := fun q : ℝ × E => backwardGaussianOUValueBCF t q.1 f q.2)
      hu.continuousAt
  have hc : Continuous (fun p : ℝ × E => bobkovVarianceCoeff p.1) := by
    unfold bobkovVarianceCoeff
    fun_prop
  change Continuous (fun p : ℝ × E => Real.sqrt
    (normalProfile (backwardGaussianOUValueBCF t p.1 f p.2) ^ 2 +
      bobkovVarianceCoeff p.1 *
        ‖backwardGaussianOUDerivBCF t p.1 Df p.2‖ ^ 2))
  exact Real.continuous_sqrt.comp
    ((hI.pow 2).add (hc.mul ((continuous_norm.comp hD).pow 2)))

theorem norm_backwardGaussianOUDerivBCF_le
    (t s : ℝ) (hst : s ≤ t)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ)) (x : E) :
    ‖backwardGaussianOUDerivBCF t s Df x‖ ≤ ‖Df‖ := by
  change ‖ouDriftCoeff (t - s) • gaussianOUAverage (t - s) Df x‖ ≤ ‖Df‖
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (ouDriftCoeff_pos (t - s))]
  have hc : ouDriftCoeff (t - s) ≤ 1 := by
    unfold ouDriftCoeff
    rw [Real.exp_le_one_iff]
    linarith
  calc
    ouDriftCoeff (t - s) * ‖gaussianOUAverage (t - s) Df x‖ ≤
        1 * ‖gaussianOUAverage (t - s) Df x‖ :=
      mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ ≤ 1 * ‖Df‖ := mul_le_mul_of_nonneg_left
      (norm_gaussianOUAverage_le (t - s) Df x) (by norm_num)
    _ = ‖Df‖ := one_mul _

/-- A uniform bound for the canonical field on its interpolation interval.
It supplies the dominator for continuity of the integrated flow. -/
theorem norm_canonicalGaussianBobkovQ_le
    (t : ℝ) (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (ε : ℝ) (hε : 0 < ε) (hf : ∀ x, f x ∈ Icc ε (1 - ε))
    {s : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (x : E) :
    ‖canonicalGaussianBobkovQ t f Df ε hε hf s x‖ ≤
      Real.sqrt
        ((Real.sqrt (2 * Real.pi))⁻¹ ^ 2 + ‖Df‖ ^ 2) := by
  let u := backwardGaussianOUValueBCF t s f x
  have huClosed := backwardGaussianOUValueBCF_mem_Icc t s f hf x
  have hu : u ∈ Ioo (0 : ℝ) 1 :=
    ⟨hε.trans_le huClosed.1, huClosed.2.trans_lt (by linarith)⟩
  have hI0 : 0 ≤ normalProfile u := (normalProfile_pos hu).le
  have hI : normalProfile u ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by
    have h := normalProfileClosed_le_inv_sqrt_two_pi u
    rwa [normalProfileClosed_eq_normalProfile hu] at h
  have hK0 : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ :=
    inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hIsq : normalProfile u ^ 2 ≤
      (Real.sqrt (2 * Real.pi))⁻¹ ^ 2 :=
    (sq_le_sq₀ hI0 hK0).2 hI
  have hD : ‖backwardGaussianOUDerivBCF t s Df x‖ ≤ ‖Df‖ :=
    norm_backwardGaussianOUDerivBCF_le t s hst Df x
  have hDsq : ‖backwardGaussianOUDerivBCF t s Df x‖ ^ 2 ≤ ‖Df‖ ^ 2 :=
    by simpa [pow_two] using
      (mul_self_le_mul_self
        (norm_nonneg (backwardGaussianOUDerivBCF t s Df x)) hD)
  have hc0 : 0 ≤ bobkovVarianceCoeff s :=
    bobkovVarianceCoeff_nonneg hs0
  have hc1 : bobkovVarianceCoeff s ≤ 1 :=
    (bobkovVarianceCoeff_lt_one s).le
  have hcD : bobkovVarianceCoeff s *
      ‖backwardGaussianOUDerivBCF t s Df x‖ ^ 2 ≤ ‖Df‖ ^ 2 := by
    calc
      bobkovVarianceCoeff s *
          ‖backwardGaussianOUDerivBCF t s Df x‖ ^ 2 ≤
          1 * ‖backwardGaussianOUDerivBCF t s Df x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hc1 (sq_nonneg _)
      _ ≤ 1 * ‖Df‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hDsq (by norm_num)
      _ = ‖Df‖ ^ 2 := one_mul _
  rw [canonicalGaussianBobkovQ_apply, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  apply Real.sqrt_le_sqrt
  exact add_le_add hIsq hcD

/-- Continuity of the canonical integrated interpolation flow on its full
closed time interval.  Joint field continuity handles the pointwise limit,
while `norm_canonicalGaussianBobkovQ_le` supplies one Gaussian-integrable
constant on `[0,t]`. -/
theorem continuousOn_canonicalGaussianBobkovFlow
    (t : ℝ)
    (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (ε : ℝ) (hε : 0 < ε) (hf : ∀ x, f x ∈ Icc ε (1 - ε))
    (x : E) :
    ContinuousOn
      (fun s => gaussianOUSemigroup s
        (canonicalGaussianBobkovQ t f Df ε hε hf s) x)
      (Icc 0 t) := by
  intro s hs
  unfold gaussianOUSemigroup
  apply tendsto_integral_filter_of_norm_le_const
  · exact Filter.Eventually.of_forall fun r =>
      ((canonicalGaussianBobkovQ t f Df ε hε hf r).continuous.comp
        (by
          unfold gaussianOUTransition ouDriftCoeff ouNoiseCoeff
          fun_prop)).aestronglyMeasurable
  · refine ⟨Real.sqrt
        ((Real.sqrt (2 * Real.pi))⁻¹ ^ 2 + ‖Df‖ ^ 2), ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact Filter.Eventually.of_forall fun z =>
      norm_canonicalGaussianBobkovQ_le t f Df ε hε hf
        hr.1 hr.2 (gaussianOUTransition r x z)
  · exact Filter.Eventually.of_forall fun z => by
      have harg : Continuous (fun r : ℝ =>
          (r, gaussianOUTransition r x z)) := by
        unfold gaussianOUTransition ouDriftCoeff ouNoiseCoeff
        fun_prop
      have hcomp :=
        (continuous_canonicalGaussianBobkovQ_joint t f Df ε hε hf).comp harg
      have hg : Continuous (fun r : ℝ =>
          canonicalGaussianBobkovQ t f Df ε hε hf r
            (gaussianOUTransition r x z)) := by
        convert hcomp using 1
        funext r
        rfl
      exact hg.continuousAt.mono_left inf_le_left

@[simp] theorem canonicalGaussianBobkovQ_initial
    (t : ℝ) (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (ε : ℝ) (hε : 0 < ε) (hf : ∀ x, f x ∈ Icc ε (1 - ε))
    (x : E) :
    canonicalGaussianBobkovQ t f Df ε hε hf 0 x =
      normalProfile (gaussianOUSemigroup t f x) := by
  unfold canonicalGaussianBobkovQ
  rw [gaussianBobkovQBCF_zero]
  simpa using backwardGaussianOUValueBCF_apply t 0 f x

@[simp] theorem canonicalGaussianBobkovQ_terminal
    (t : ℝ) (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (ε : ℝ) (hε : 0 < ε) (hf : ∀ x, f x ∈ Icc ε (1 - ε))
    (x : E) :
    canonicalGaussianBobkovQ t f Df ε hε hf t x =
      Real.sqrt (normalProfile (f x) ^ 2 +
        bobkovVarianceCoeff t * ‖Df x‖ ^ 2) := by
  rw [canonicalGaussianBobkovQ_apply]
  simp

/-- The canonical field specialized to the affine endpoint truncation used
by G4. -/
def canonicalTruncatedGaussianBobkovQ
    (e : ℝ) (he0 : 0 < e) (he1 : e < 1 / 2)
    (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (hf : ∀ x, f x ∈ Icc (0 : ℝ) 1) (t s : ℝ) :
    BoundedContinuousFunction E ℝ :=
  canonicalGaussianBobkovQ t
    (bobkovTruncationBCF e f) ((1 - 2 * e) • Df)
    e he0 (fun x => bobkovTruncationBCF_mem_Icc e f hf he1 x) s

@[simp] theorem canonicalTruncatedGaussianBobkovQ_initial
    (e : ℝ) (he0 : 0 < e) (he1 : e < 1 / 2)
    (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (hf : ∀ x, f x ∈ Icc (0 : ℝ) 1) (t : ℝ) (x : E) :
    canonicalTruncatedGaussianBobkovQ e he0 he1 f Df hf t 0 x =
      normalProfile
        (gaussianOUSemigroup t (bobkovTruncationBCF e f) x) := by
  exact canonicalGaussianBobkovQ_initial t
    (bobkovTruncationBCF e f) ((1 - 2 * e) • Df)
    e he0 (fun y => bobkovTruncationBCF_mem_Icc e f hf he1 y) x

@[simp] theorem canonicalTruncatedGaussianBobkovQ_terminal
    (e : ℝ) (he0 : 0 < e) (he1 : e < 1 / 2)
    (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (hf : ∀ x, f x ∈ Icc (0 : ℝ) 1) (t : ℝ) (x : E) :
    canonicalTruncatedGaussianBobkovQ e he0 he1 f Df hf t t x =
      Real.sqrt
        ((normalProfileCompBCF (bobkovTruncationBCF e f) e he0
            (fun y => bobkovTruncationBCF_mem_Icc e f hf he1 y) x) ^ 2 +
          bobkovVarianceCoeff t * ‖((1 - 2 * e) • Df) x‖ ^ 2) := by
  unfold canonicalTruncatedGaussianBobkovQ
  rw [canonicalGaussianBobkovQ_terminal]
  rfl

theorem continuousOn_canonicalTruncatedGaussianBobkovFlow
    (e : ℝ) (he0 : 0 < e) (he1 : e < 1 / 2)
    (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (hf : ∀ x, f x ∈ Icc (0 : ℝ) 1) (t : ℝ) (x : E) :
    ContinuousOn
      (fun s => gaussianOUSemigroup s
        (canonicalTruncatedGaussianBobkovQ e he0 he1 f Df hf t s) x)
      (Icc 0 t) := by
  simpa only [canonicalTruncatedGaussianBobkovQ] using
    continuousOn_canonicalGaussianBobkovFlow t
      (bobkovTruncationBCF e f) ((1 - 2 * e) • Df)
      e he0 (fun y => bobkovTruncationBCF_mem_Icc e f hf he1 y) x

/-- The exact remaining G3 certificate after fixing the canonical backward
Mehler square-root field.  Endpoint identities and continuity of the
integrated flow are no longer fields of this structure; they are theorems of
`canonicalTruncatedGaussianBobkovQ`. -/
structure CanonicalGaussianBobkovInterpolation
    (e : ℝ) (he0 : 0 < e) (he1 : e < 1 / 2)
    (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (hf : ∀ x, f x ∈ Icc (0 : ℝ) 1) (t : ℝ) (x : E) where
  residual : ℝ → BoundedContinuousFunction E ℝ
  hasDerivAt_flow : ∀ s ∈ Ioo 0 t,
    HasDerivAt
      (fun r => gaussianOUSemigroup r
        (canonicalTruncatedGaussianBobkovQ e he0 he1 f Df hf t r) x)
      (gaussianOUSemigroup s (residual s) x) s
  residual_nonneg : ∀ s ∈ Ioo 0 t, ∀ y, 0 ≤ residual s y

/-- A stronger, coordinate-level version of the canonical certificate.  Its
only pointwise field is the exact residual representation produced by the
radicand and square-root chain rules.  Nonnegativity is derived internally
from the checked finite-dimensional G3 inequality. -/
structure CanonicalGaussianBobkovResidualInterpolation
    {ι : Type*} [Fintype ι]
    (e : ℝ) (he0 : 0 < e) (he1 : e < 1 / 2)
    (f : BoundedContinuousFunction (EuclideanSpace ℝ ι) ℝ)
    (Df : BoundedContinuousFunction (EuclideanSpace ℝ ι)
      (EuclideanSpace ℝ ι →L[ℝ] ℝ))
    (hf : ∀ x, f x ∈ Icc (0 : ℝ) 1) (t : ℝ)
    (x : EuclideanSpace ℝ ι) where
  residual : ℝ → BoundedContinuousFunction (EuclideanSpace ℝ ι) ℝ
  hasDerivAt_flow : ∀ s ∈ Ioo 0 t,
    HasDerivAt
      (fun r => gaussianOUSemigroup r
        (canonicalTruncatedGaussianBobkovQ e he0 he1 f Df hf t r) x)
      (gaussianOUSemigroup s (residual s) x) s
  residual_representation : ∀ s ∈ Ioo 0 t, ∀ y,
    ∃ (I Ip : ℝ) (v : EuclideanSpace ℝ ι)
      (H : ι → EuclideanSpace ℝ ι),
      0 < I ∧ residual s y =
        bobkovSqrtResidual (bobkovVarianceCoeff s) I Ip v H

/-- Forget the coordinate representation.  The only discarded information is
the witness used to invoke `bobkovSqrtResidual_nonneg`. -/
def CanonicalGaussianBobkovResidualInterpolation.toCanonical
    {ι : Type*} [Fintype ι]
    {e : ℝ} {he0 : 0 < e} {he1 : e < 1 / 2}
    {f : BoundedContinuousFunction (EuclideanSpace ℝ ι) ℝ}
    {Df : BoundedContinuousFunction (EuclideanSpace ℝ ι)
      (EuclideanSpace ℝ ι →L[ℝ] ℝ)}
    {hf : ∀ x, f x ∈ Icc (0 : ℝ) 1} {t : ℝ}
    {x : EuclideanSpace ℝ ι}
    (h : CanonicalGaussianBobkovResidualInterpolation
      e he0 he1 f Df hf t x) :
    CanonicalGaussianBobkovInterpolation e he0 he1 f Df hf t x where
  residual := h.residual
  hasDerivAt_flow := h.hasDerivAt_flow
  residual_nonneg := by
    intro s hs y
    obtain ⟨I, Ip, v, H, hI, hres⟩ :=
      h.residual_representation s hs y
    rw [hres]
    exact bobkovSqrtResidual_nonneg
      (bobkovVarianceCoeff_nonneg hs.1.le) hI Ip v H

/-- Forget the canonical presentation and obtain the interpolation
certificate consumed by the existing G3-to-G4 closure. -/
def CanonicalGaussianBobkovInterpolation.toSmoothInterpolation
    {e : ℝ} {he0 : 0 < e} {he1 : e < 1 / 2}
    {f : BoundedContinuousFunction E ℝ}
    {Df : BoundedContinuousFunction E (E →L[ℝ] ℝ)}
    {hf : ∀ x, f x ∈ Icc (0 : ℝ) 1} {t : ℝ} {x : E}
    (h : CanonicalGaussianBobkovInterpolation e he0 he1 f Df hf t x) :
    GaussianBobkovSmoothInterpolation
      (bobkovTruncationBCF e f)
      (normalProfileCompBCF (bobkovTruncationBCF e f) e he0
        (fun y => bobkovTruncationBCF_mem_Icc e f hf he1 y))
      ((1 - 2 * e) • Df) t x where
  Q := canonicalTruncatedGaussianBobkovQ e he0 he1 f Df hf t
  residual := h.residual
  continuous_flow := continuousOn_canonicalTruncatedGaussianBobkovFlow
    e he0 he1 f Df hf t x
  hasDerivAt_flow := h.hasDerivAt_flow
  residual_nonneg := h.residual_nonneg
  initial := canonicalTruncatedGaussianBobkovQ_initial
    e he0 he1 f Df hf t x
  terminal := canonicalTruncatedGaussianBobkovQ_terminal
    e he0 he1 f Df hf t

/-- The remaining smooth G3 obligation with the interpolation field fixed
definitionally to the canonical backward Mehler field. -/
def CanonicalGaussianBobkovInterpolationProperty : Prop :=
  ∀ (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (hf : ∀ y, f y ∈ Icc (0 : ℝ) 1),
    ContDiff ℝ (⊤ : ℕ∞) (⇑f) →
    (∀ y, fderiv ℝ (⇑f) y = Df y) →
    ∀ (e : ℝ) (he0 : 0 < e) (he1 : e < 1 / 2)
      (t : ℝ) (ht : 0 ≤ t),
      Nonempty (CanonicalGaussianBobkovInterpolation
        e he0 he1 f Df hf t 0)

/-- A canonical-field G3 construction supplies the former unrestricted
smooth interpolation property. -/
theorem gaussianBobkovSmoothInterpolationProperty_of_canonical
    (hcanonical : CanonicalGaussianBobkovInterpolationProperty (E := E)) :
    GaussianBobkovSmoothInterpolationProperty (X := E) := by
  intro f Df hf hsmooth hDf e he0 he1 t ht
  exact ⟨(Classical.choice
    (hcanonical f Df hf hsmooth hDf e he0 he1 t ht)).toSmoothInterpolation⟩

end BobkovField

end Concrete

end

end UniformRandomMALA
