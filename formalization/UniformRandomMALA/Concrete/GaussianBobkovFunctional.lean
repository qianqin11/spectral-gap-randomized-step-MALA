import UniformRandomMALA.Concrete.GaussianBobkov

/-!
# Long-time closure of the Gaussian Bobkov interpolation

This file formalizes the `t → ∞` step from a local OU inequality to the
functional Gaussian Bobkov inequality.  The integrand is allowed to vary with
time through both the Mehler transition and `c(t) = 1-exp(-2t)`, so the main
limit is proved directly by dominated convergence.

The theorem `gaussianBobkov_functional_of_local` retains a convenient bridge
from a local inequality.  The later `GaussianOUGenerator` module constructs
that inequality from smooth OU-generator data and the checked G3 residual
sign.  The G4 long-time passage is unconditional for bounded interior `C¹`
data whose normal-profile composition is bounded continuous, and the
closed-profile/truncation theorems remove the endpoint restriction for
`[0,1]`-valued data.
-/

namespace UniformRandomMALA

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace Concrete

/-- The Bobkov variance coefficient tends to one at long times. -/
theorem tendsto_bobkovVarianceCoeff_atTop :
    Tendsto bobkovVarianceCoeff atTop (nhds 1) := by
  have hsq : Tendsto (fun t : ℝ => ouNoiseCoeff t ^ 2) atTop
      (nhds (1 ^ 2)) := tendsto_ouNoiseCoeff_atTop.pow 2
  simpa using hsq.congr' (by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (bobkovVarianceCoeff_eq_ouNoiseCoeff_sq ht).symm)

variable {X : Type*} [TopologicalSpace X]

/-- The normal profile composed with a bounded function uniformly separated
from the endpoints is itself bounded continuous. -/
def normalProfileCompBCF (f : BoundedContinuousFunction X ℝ)
    (ε : ℝ) (hε : 0 < ε)
    (hf : ∀ x, f x ∈ Set.Icc ε (1 - ε)) :
    BoundedContinuousFunction X ℝ where
  toFun := fun x => normalProfile (f x)
  continuous_toFun := continuous_iff_continuousAt.2 fun x =>
    (hasDerivAt_normalProfile ⟨hε.trans_le (hf x).1,
      (hf x).2.trans_lt (by linarith)⟩).continuousAt.comp
        f.continuous.continuousAt
  map_bounded' := by
    have hcont : ContinuousOn normalProfile (Set.Icc ε (1 - ε)) := by
      intro u hu
      exact (hasDerivAt_normalProfile
        ⟨hε.trans_le hu.1, hu.2.trans_lt (by linarith)⟩).continuousAt.continuousWithinAt
    have himage : Bornology.IsBounded
        (normalProfile '' Set.Icc ε (1 - ε)) :=
      (isCompact_Icc.image_of_continuousOn hcont).isBounded
    apply Metric.isBounded_range_iff.mp
    exact himage.subset fun y hy => by
      rcases hy with ⟨x, rfl⟩
      exact ⟨f x, hf x, rfl⟩

@[simp] theorem normalProfileCompBCF_apply
    (f : BoundedContinuousFunction X ℝ) (ε : ℝ) (hε : 0 < ε)
    (hf : ∀ x, f x ∈ Set.Icc ε (1 - ε)) (x : X) :
    normalProfileCompBCF f ε hε hf x = normalProfile (f x) := rfl

/-- The canonical closed normal profile composed with a bounded continuous
`[0,1]`-valued function. -/
def normalProfileClosedCompBCF (f : BoundedContinuousFunction X ℝ)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    BoundedContinuousFunction X ℝ where
  toFun := fun x => normalProfileClosed (f x)
  continuous_toFun := continuous_normalProfileClosed.comp f.continuous
  map_bounded' := by
    have himage : Bornology.IsBounded
        (normalProfileClosed '' Set.Icc (0 : ℝ) 1) :=
      (isCompact_Icc.image continuous_normalProfileClosed).isBounded
    apply Metric.isBounded_range_iff.mp
    exact himage.subset fun y hy => by
      rcases hy with ⟨x, rfl⟩
      exact ⟨f x, hf x, rfl⟩

@[simp] theorem normalProfileClosedCompBCF_apply
    (f : BoundedContinuousFunction X ℝ)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (x : X) :
    normalProfileClosedCompBCF f hf x = normalProfileClosed (f x) := rfl

/-- Affine truncation into the interior of the unit interval. -/
def bobkovTruncation (e u : ℝ) : ℝ := e + (1 - 2 * e) * u

theorem bobkovTruncation_mem_Icc
    {e u : ℝ} (he1 : e < 1 / 2)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    bobkovTruncation e u ∈ Set.Icc e (1 - e) := by
  have hc0 : 0 ≤ 1 - 2 * e := by linarith
  constructor
  · unfold bobkovTruncation
    nlinarith [mul_nonneg hc0 hu.1]
  · unfold bobkovTruncation
    nlinarith [mul_le_mul_of_nonneg_left hu.2 hc0]

theorem bobkovTruncation_mem_Ioo
    {e u : ℝ} (he0 : 0 < e) (he1 : e < 1 / 2)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    bobkovTruncation e u ∈ Set.Ioo (0 : ℝ) 1 := by
  have hclosed := bobkovTruncation_mem_Icc he1 hu
  constructor <;> linarith [hclosed.1, hclosed.2]

theorem tendsto_bobkovTruncation_zero (u : ℝ) :
    Tendsto (fun e : ℝ => bobkovTruncation e u) (nhds 0) (nhds u) := by
  have h : ContinuousAt (fun e : ℝ => bobkovTruncation e u) 0 := by
    unfold bobkovTruncation
    fun_prop
  change Tendsto (fun e : ℝ => bobkovTruncation e u) (nhds 0)
    (nhds (bobkovTruncation 0 u)) at h
  simpa [bobkovTruncation] using h

/-- Affine endpoint truncation as a bounded continuous function. -/
def bobkovTruncationBCF (e : ℝ) (f : BoundedContinuousFunction X ℝ) :
    BoundedContinuousFunction X ℝ :=
  BoundedContinuousFunction.const X e + (1 - 2 * e) • f

@[simp] theorem bobkovTruncationBCF_apply
    (e : ℝ) (f : BoundedContinuousFunction X ℝ) (x : X) :
    bobkovTruncationBCF e f x = bobkovTruncation e (f x) := by
  simp [bobkovTruncationBCF, bobkovTruncation]

theorem bobkovTruncationBCF_mem_Icc
    (e : ℝ) (f : BoundedContinuousFunction X ℝ)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (he1 : e < 1 / 2) (x : X) :
    bobkovTruncationBCF e f x ∈ Set.Icc e (1 - e) := by
  rw [bobkovTruncationBCF_apply]
  exact bobkovTruncation_mem_Icc he1 (hf x)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [SecondCountableTopology E]

/-- The varying Mehler integral occurring at the long-time endpoint of the
local Bobkov inequality.  The function `q` represents `I ∘ f`, and `Df`
represents the Fréchet derivative of `f`. -/
def gaussianBobkovOUIntegral (t : ℝ)
    (q : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ)) (x : E) : ℝ :=
  ∫ z, Real.sqrt
    (q (gaussianOUTransition t x z) ^ 2 +
      bobkovVarianceCoeff t * ‖Df (gaussianOUTransition t x z)‖ ^ 2)
    ∂stdGaussian E

/-- Uniform separation of the values of `f` from `0` and `1` also separates
its Gaussian mean from the endpoints. -/
theorem integral_mem_Ioo_of_uniformInterior
    (f : BoundedContinuousFunction E ℝ) (ε : ℝ) (hε : 0 < ε)
    (hf : ∀ x, f x ∈ Set.Icc ε (1 - ε)) :
    (∫ x, f x ∂stdGaussian E) ∈ Set.Ioo (0 : ℝ) 1 := by
  have hfint : Integrable f (stdGaussian E) := by
    refine Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖ ?_
    exact Filter.Eventually.of_forall fun x => f.norm_coe_le_norm x
  have hlower : ε ≤ ∫ x, f x ∂stdGaussian E := by
    have h := integral_mono_ae (integrable_const ε) hfint
      (Filter.Eventually.of_forall fun x => (hf x).1)
    simpa using h
  have hupper : (∫ x, f x ∂stdGaussian E) ≤ 1 - ε := by
    have h := integral_mono_ae hfint (integrable_const (1 - ε))
      (Filter.Eventually.of_forall fun x => (hf x).2)
    simpa using h
  constructor <;> linarith

/-- The Gaussian mean of a `[0,1]`-valued bounded continuous function still
belongs to the closed unit interval. -/
theorem integral_mem_Icc_of_mem_Icc
    (f : BoundedContinuousFunction E ℝ)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ x, f x ∂stdGaussian E) ∈ Set.Icc (0 : ℝ) 1 := by
  have hfint : Integrable f (stdGaussian E) := by
    refine Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖ ?_
    exact Filter.Eventually.of_forall fun x => f.norm_coe_le_norm x
  constructor
  · have h := integral_mono_ae (integrable_const (0 : ℝ)) hfint
      (Filter.Eventually.of_forall fun x => (hf x).1)
    simpa using h
  · have h := integral_mono_ae hfint (integrable_const (1 : ℝ))
      (Filter.Eventually.of_forall fun x => (hf x).2)
    simpa using h

/-- Direct dominated-convergence limit for the varying Bobkov--Mehler
integral. -/
theorem tendsto_gaussianBobkovOUIntegral_atTop
    (q : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ)) (x : E) :
    Tendsto (fun t : ℝ => gaussianBobkovOUIntegral t q Df x) atTop
      (nhds (∫ z, Real.sqrt (q z ^ 2 + ‖Df z‖ ^ 2) ∂stdGaussian E)) := by
  apply tendsto_integral_filter_of_norm_le_const
  · exact Filter.Eventually.of_forall fun t =>
      (show Continuous (fun z : E => Real.sqrt
        (q (gaussianOUTransition t x z) ^ 2 +
          bobkovVarianceCoeff t * ‖Df (gaussianOUTransition t x z)‖ ^ 2)) by
        unfold gaussianOUTransition
        fun_prop).aestronglyMeasurable
  · refine ⟨Real.sqrt (‖q‖ ^ 2 + ‖Df‖ ^ 2), ?_⟩
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact Filter.Eventually.of_forall fun z => by
      let y := gaussianOUTransition t x z
      have hqnorm : |q y| ≤ ‖q‖ := by
        simpa [Real.norm_eq_abs] using q.norm_coe_le_norm y
      have hDnorm : ‖Df y‖ ≤ ‖Df‖ := Df.norm_coe_le_norm y
      have hqsq : q y ^ 2 ≤ ‖q‖ ^ 2 := by
        rw [← sq_abs]
        exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 hqnorm
      have hDsq : ‖Df y‖ ^ 2 ≤ ‖Df‖ ^ 2 :=
        (sq_le_sq₀ (norm_nonneg (Df y)) (norm_nonneg Df)).2 hDnorm
      have hcD : bobkovVarianceCoeff t * ‖Df y‖ ^ 2 ≤
          1 * ‖Df‖ ^ 2 :=
        mul_le_mul (bobkovVarianceCoeff_lt_one t).le hDsq
          (sq_nonneg _) zero_le_one
      have hrad : q y ^ 2 + bobkovVarianceCoeff t * ‖Df y‖ ^ 2 ≤
          ‖q‖ ^ 2 + ‖Df‖ ^ 2 := by
        simpa using add_le_add hqsq hcD
      simpa [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using
        Real.sqrt_le_sqrt hrad
  · exact Filter.Eventually.of_forall fun z => by
      have hy := tendsto_gaussianOUTransition_atTop x z
      have hq := q.continuous.continuousAt.tendsto.comp hy
      have hD := Df.continuous.continuousAt.tendsto.comp hy
      have hrad : Tendsto (fun t : ℝ =>
          q (gaussianOUTransition t x z) ^ 2 +
            bobkovVarianceCoeff t * ‖Df (gaussianOUTransition t x z)‖ ^ 2)
          atTop (nhds (q z ^ 2 + ‖Df z‖ ^ 2)) := by
        simpa only [Function.comp_apply, one_mul] using
          (hq.pow 2).add
            (tendsto_bobkovVarianceCoeff_atTop.mul (hD.norm.pow 2))
      change Tendsto ((fun r : ℝ => Real.sqrt r) ∘ fun t : ℝ =>
        q (gaussianOUTransition t x z) ^ 2 +
          bobkovVarianceCoeff t * ‖Df (gaussianOUTransition t x z)‖ ^ 2)
        atTop (nhds (Real.sqrt (q z ^ 2 + ‖Df z‖ ^ 2)))
      exact Real.continuous_sqrt.continuousAt.tendsto.comp hrad

/-- G4 long-time closure: any local OU Bobkov inequality implies the
functional Gaussian inequality for bounded interior data. -/
theorem gaussianBobkov_functional_of_local
    (f : BoundedContinuousFunction E ℝ)
    (q : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (hq : ∀ y, q y = normalProfile (f y))
    (hmean : (∫ y, f y ∂stdGaussian E) ∈ Set.Ioo (0 : ℝ) 1)
    (x : E)
    (hlocal : ∀ t, 0 ≤ t →
      normalProfile (gaussianOUSemigroup t f x) ≤
        gaussianBobkovOUIntegral t q Df x) :
    normalProfile (∫ y, f y ∂stdGaussian E) ≤
      ∫ y, Real.sqrt (normalProfile (f y) ^ 2 + ‖Df y‖ ^ 2)
        ∂stdGaussian E := by
  have hleft : Tendsto
      (fun t : ℝ => normalProfile (gaussianOUSemigroup t f x)) atTop
      (nhds (normalProfile (∫ y, f y ∂stdGaussian E))) := by
    change Tendsto (normalProfile ∘ fun t : ℝ => gaussianOUSemigroup t f x)
      atTop (nhds (normalProfile (∫ y, f y ∂stdGaussian E)))
    exact (hasDerivAt_normalProfile hmean).continuousAt.tendsto.comp
      (tendsto_gaussianOUSemigroup_atTop f x)
  have hright := tendsto_gaussianBobkovOUIntegral_atTop q Df x
  have hle : normalProfile (∫ y, f y ∂stdGaussian E) ≤
      ∫ y, Real.sqrt (q y ^ 2 + ‖Df y‖ ^ 2) ∂stdGaussian E := by
    apply le_of_tendsto_of_tendsto hleft hright
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact hlocal t ht
  simpa only [hq] using hle

/-- G4 closure with the profile composition and interior mean hypotheses
discharged from a uniform range condition. -/
theorem gaussianBobkov_functional_of_local_uniformInterior
    (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (ε : ℝ) (hε : 0 < ε)
    (hf : ∀ y, f y ∈ Set.Icc ε (1 - ε))
    (x : E)
    (hlocal : ∀ t, 0 ≤ t →
      normalProfile (gaussianOUSemigroup t f x) ≤
        gaussianBobkovOUIntegral t (normalProfileCompBCF f ε hε hf) Df x) :
    normalProfile (∫ y, f y ∂stdGaussian E) ≤
      ∫ y, Real.sqrt (normalProfile (f y) ^ 2 + ‖Df y‖ ^ 2)
        ∂stdGaussian E := by
  exact gaussianBobkov_functional_of_local
    (E := E) (f := f) (q := normalProfileCompBCF f ε hε hf)
    (Df := Df) (fun _ => rfl)
    (integral_mem_Ioo_of_uniformInterior f ε hε hf) x hlocal

/-- Endpoint-complete G4 closure.  Once the local OU inequality is available
for the canonical closed profile, the long-time limit proves the functional
Bobkov inequality for arbitrary bounded continuous `[0,1]`-valued data; no
uniform separation from `0` and `1` is required. -/
theorem gaussianBobkov_functionalClosed_of_local
    (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (hf : ∀ y, f y ∈ Set.Icc (0 : ℝ) 1)
    (x : E)
    (hlocal : ∀ t, 0 ≤ t →
      normalProfileClosed (gaussianOUSemigroup t f x) ≤
        gaussianBobkovOUIntegral t (normalProfileClosedCompBCF f hf) Df x) :
    normalProfileClosed (∫ y, f y ∂stdGaussian E) ≤
      ∫ y, Real.sqrt (normalProfileClosed (f y) ^ 2 + ‖Df y‖ ^ 2)
        ∂stdGaussian E := by
  have hleft : Tendsto
      (fun t : ℝ => normalProfileClosed (gaussianOUSemigroup t f x)) atTop
      (nhds (normalProfileClosed (∫ y, f y ∂stdGaussian E))) := by
    change Tendsto
      (normalProfileClosed ∘ fun t : ℝ => gaussianOUSemigroup t f x)
      atTop (nhds (normalProfileClosed (∫ y, f y ∂stdGaussian E)))
    exact continuous_normalProfileClosed.continuousAt.tendsto.comp
      (tendsto_gaussianOUSemigroup_atTop f x)
  have hright := tendsto_gaussianBobkovOUIntegral_atTop
    (normalProfileClosedCompBCF f hf) Df x
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact hlocal t ht

/-- G4 endpoint truncation.  If the functional Bobkov inequality is known for
every affine interior truncation `e + (1-2e)f`, then dominated convergence
gives the canonical closed-profile inequality for the original `[0,1]`-valued
datum. -/
theorem gaussianBobkov_functionalClosed_of_truncations
    (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (hf : ∀ y, f y ∈ Set.Icc (0 : ℝ) 1)
    (htrunc : ∀ e, 0 < e → e < 1 / 2 →
      normalProfile (∫ y, bobkovTruncation e (f y) ∂stdGaussian E) ≤
        ∫ y, Real.sqrt
          (normalProfile (bobkovTruncation e (f y)) ^ 2 +
            ‖(1 - 2 * e) • Df y‖ ^ 2) ∂stdGaussian E) :
    normalProfileClosed (∫ y, f y ∂stdGaussian E) ≤
      ∫ y, Real.sqrt (normalProfileClosed (f y) ^ 2 + ‖Df y‖ ^ 2)
        ∂stdGaussian E := by
  let l : Filter ℝ := nhdsWithin 0 (Set.Ioo (0 : ℝ) (1 / 2))
  haveI : NeBot l := left_nhdsWithin_Ioo_neBot (by norm_num)
  have hl0 : Tendsto (fun e : ℝ => e) l (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have hmean : Integrable f (stdGaussian E) := by
    refine Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖ ?_
    exact Filter.Eventually.of_forall fun x => f.norm_coe_le_norm x
  have hint (e : ℝ) :
      ∫ y, bobkovTruncation e (f y) ∂stdGaussian E =
        bobkovTruncation e (∫ y, f y ∂stdGaussian E) := by
    unfold bobkovTruncation
    rw [integral_add (integrable_const e) (hmean.const_mul (1 - 2 * e)),
      integral_const, integral_const_mul]
    simp
  have hleft : Tendsto (fun e : ℝ => normalProfileClosed
      (∫ y, bobkovTruncation e (f y) ∂stdGaussian E)) l
      (nhds (normalProfileClosed (∫ y, f y ∂stdGaussian E))) := by
    rw [show (fun e : ℝ => normalProfileClosed
        (∫ y, bobkovTruncation e (f y) ∂stdGaussian E)) =
        normalProfileClosed ∘ fun e : ℝ =>
          bobkovTruncation e (∫ y, f y ∂stdGaussian E) by
      funext e
      simp only [Function.comp_apply, hint]]
    exact continuous_normalProfileClosed.continuousAt.tendsto.comp
      ((tendsto_bobkovTruncation_zero _).comp hl0)
  have hright : Tendsto (fun e : ℝ =>
      ∫ y, Real.sqrt
        (normalProfileClosed (bobkovTruncation e (f y)) ^ 2 +
          ‖(1 - 2 * e) • Df y‖ ^ 2) ∂stdGaussian E) l
      (nhds (∫ y, Real.sqrt
        (normalProfileClosed (f y) ^ 2 + ‖Df y‖ ^ 2) ∂stdGaussian E)) := by
    apply tendsto_integral_filter_of_norm_le_const
    · exact Filter.Eventually.of_forall fun e =>
        (show Continuous (fun y : E => Real.sqrt
          (normalProfileClosed (bobkovTruncation e (f y)) ^ 2 +
            ‖(1 - 2 * e) • Df y‖ ^ 2)) by
          have htr : Continuous (fun y : E => bobkovTruncation e (f y)) := by
            unfold bobkovTruncation
            fun_prop
          have hp := continuous_normalProfileClosed.comp htr
          have hD : Continuous (fun y : E => (1 - 2 * e) • Df y) := by
            fun_prop
          exact Real.continuous_sqrt.comp ((hp.pow 2).add (hD.norm.pow 2))
          ).aestronglyMeasurable
    · refine ⟨Real.sqrt (((Real.sqrt (2 * Real.pi))⁻¹) ^ 2 + ‖Df‖ ^ 2), ?_⟩
      filter_upwards [self_mem_nhdsWithin] with e he
      exact Filter.Eventually.of_forall fun y => by
        have hc0 : 0 ≤ 1 - 2 * e := by linarith [he.2]
        have hc1 : 1 - 2 * e ≤ 1 := by linarith [he.1]
        have hp0 := normalProfileClosed_nonneg (bobkovTruncation e (f y))
        have hp := normalProfileClosed_le_inv_sqrt_two_pi
          (bobkovTruncation e (f y))
        have hpsq : normalProfileClosed (bobkovTruncation e (f y)) ^ 2 ≤
            ((Real.sqrt (2 * Real.pi))⁻¹) ^ 2 := by
          exact (sq_le_sq₀ hp0 (inv_nonneg.mpr (Real.sqrt_nonneg _))).2 hp
        have hscale : ‖(1 - 2 * e) • Df y‖ ≤ ‖Df‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
          calc
            (1 - 2 * e) * ‖Df y‖ ≤ 1 * ‖Df y‖ :=
              mul_le_mul_of_nonneg_right hc1 (norm_nonneg _)
            _ = ‖Df y‖ := one_mul _
            _ ≤ ‖Df‖ := Df.norm_coe_le_norm y
        have hscaleSq : ‖(1 - 2 * e) • Df y‖ ^ 2 ≤ ‖Df‖ ^ 2 := by
          simpa only [pow_two] using
            mul_self_le_mul_self (norm_nonneg ((1 - 2 * e) • Df y)) hscale
        have hrad := add_le_add hpsq hscaleSq
        simpa [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using
          Real.sqrt_le_sqrt hrad
    · exact Filter.Eventually.of_forall fun y => by
        have htr := (tendsto_bobkovTruncation_zero (f y)).comp hl0
        have hp := continuous_normalProfileClosed.continuousAt.tendsto.comp htr
        have hc : Tendsto (fun e : ℝ => 1 - 2 * e) l (nhds 1) := by
          convert (tendsto_const_nhds.sub
            (tendsto_const_nhds.mul hl0)) using 1 <;> ring
        have hD : Tendsto (fun e : ℝ => (1 - 2 * e) • Df y) l
            (nhds (Df y)) := by
          simpa using hc.smul (tendsto_const_nhds : Tendsto
            (fun _ : ℝ => Df y) l (nhds (Df y)))
        have hrad := (hp.pow 2).add (hD.norm.pow 2)
        exact Real.continuous_sqrt.continuousAt.tendsto.comp hrad
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin] with e he
  have hmeanIcc := integral_mem_Icc_of_mem_Icc f hf
  have hmeanTrunc := bobkovTruncation_mem_Ioo he.1 he.2 hmeanIcc
  have hmeanTrunc' :
      (∫ y, bobkovTruncation e (f y) ∂stdGaussian E) ∈
        Set.Ioo (0 : ℝ) 1 := by
    rw [hint]
    exact hmeanTrunc
  have hpoint : ∀ y, bobkovTruncation e (f y) ∈ Set.Ioo (0 : ℝ) 1 :=
    fun y => bobkovTruncation_mem_Ioo he.1 he.2 (hf y)
  simpa only [normalProfileClosed_eq_normalProfile hmeanTrunc',
    normalProfileClosed_eq_normalProfile (hpoint _)] using
      htrunc e he.1 he.2

/-- G3-to-G4 endpoint bridge.  Local OU inequalities for every interior
affine truncation imply the endpoint-complete functional inequality. -/
theorem gaussianBobkov_functionalClosed_of_localTruncations
    (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (hf : ∀ y, f y ∈ Set.Icc (0 : ℝ) 1)
    (x : E)
    (hlocal : ∀ (e : ℝ) (he0 : 0 < e) (he1 : e < 1 / 2)
      (t : ℝ), 0 ≤ t →
      normalProfile
          (gaussianOUSemigroup t (bobkovTruncationBCF e f) x) ≤
        gaussianBobkovOUIntegral t
          (normalProfileCompBCF (bobkovTruncationBCF e f) e he0
            (bobkovTruncationBCF_mem_Icc e f hf he1))
          ((1 - 2 * e) • Df) x) :
    normalProfileClosed (∫ y, f y ∂stdGaussian E) ≤
      ∫ y, Real.sqrt (normalProfileClosed (f y) ^ 2 + ‖Df y‖ ^ 2)
        ∂stdGaussian E := by
  apply gaussianBobkov_functionalClosed_of_truncations f Df hf
  intro e he0 he1
  have h := gaussianBobkov_functional_of_local_uniformInterior
    (E := E) (f := bobkovTruncationBCF e f) (Df := (1 - 2 * e) • Df)
    e he0 (bobkovTruncationBCF_mem_Icc e f hf he1) x
    (hlocal e he0 he1)
  simpa only [bobkovTruncationBCF_apply,
    BoundedContinuousFunction.smul_apply] using h

end Concrete

end

end UniformRandomMALA
