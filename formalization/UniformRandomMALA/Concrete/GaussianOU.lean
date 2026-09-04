import UniformRandomMALA.Concrete.GaussianNormalProfile
import UniformRandomMALA.DiscreteTime.GaussianLawBridge
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The Gaussian Ornstein--Uhlenbeck semigroup

This file gives the finite-dimensional Mehler representation

`P_t f(x) = E[f(exp(-t) x + sqrt(1-exp(-2t)) Z)]`

and proves its elementary coefficient identities, the time-zero law, and
invariance of the standard Gaussian measure.  The invariance proof is at the
measure level and uses characteristic functions, so it can be reused without
additional integrability hypotheses on test functions.
-/

namespace UniformRandomMALA

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace Concrete

/-- The deterministic coefficient in the Mehler representation. -/
def ouDriftCoeff (t : ℝ) : ℝ := Real.exp (-t)

/-- The fresh-noise coefficient in the Mehler representation. -/
def ouNoiseCoeff (t : ℝ) : ℝ := Real.sqrt (1 - Real.exp (-2 * t))

lemma ouDriftCoeff_pos (t : ℝ) : 0 < ouDriftCoeff t := by
  exact Real.exp_pos _

lemma ouNoiseCoeff_nonneg (t : ℝ) : 0 ≤ ouNoiseCoeff t :=
  Real.sqrt_nonneg _

lemma one_sub_exp_neg_two_mul_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ 1 - Real.exp (-2 * t) := by
  rw [sub_nonneg]
  exact Real.exp_le_one_iff.mpr (by linarith)

/-- The two Mehler coefficients have squared norm one. -/
theorem ouDriftCoeff_sq_add_ouNoiseCoeff_sq {t : ℝ} (ht : 0 ≤ t) :
    ouDriftCoeff t ^ 2 + ouNoiseCoeff t ^ 2 = 1 := by
  rw [ouDriftCoeff, ouNoiseCoeff,
    Real.sq_sqrt (one_sub_exp_neg_two_mul_nonneg ht)]
  rw [← Real.exp_nat_mul]
  ring_nf

/-- Multiplicativity of the deterministic Mehler coefficient. -/
theorem ouDriftCoeff_add (s t : ℝ) :
    ouDriftCoeff (s + t) = ouDriftCoeff s * ouDriftCoeff t := by
  rw [ouDriftCoeff, ouDriftCoeff, ouDriftCoeff, ← Real.exp_add]
  congr 1
  ring

/-- The noise created by two successive OU steps has the one-step variance. -/
theorem ouNoiseCoeff_composition_sq {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (ouDriftCoeff t * ouNoiseCoeff s) ^ 2 + ouNoiseCoeff t ^ 2 =
      ouNoiseCoeff (s + t) ^ 2 := by
  simp only [ouDriftCoeff, ouNoiseCoeff]
  rw [mul_pow,
    Real.sq_sqrt (one_sub_exp_neg_two_mul_nonneg hs),
    Real.sq_sqrt (one_sub_exp_neg_two_mul_nonneg ht),
    Real.sq_sqrt (one_sub_exp_neg_two_mul_nonneg (add_nonneg hs ht))]
  rw [← Real.exp_nat_mul]
  ring_nf
  have hexp : Real.exp (-(t * 2) - s * 2) =
      Real.exp (-(t * 2)) * Real.exp (-(s * 2)) := by
    rw [show -(t * 2) - s * 2 = -(t * 2) + -(s * 2) by ring,
      Real.exp_add]
  rw [hexp]

/-- The deterministic Mehler coefficient vanishes at long times. -/
theorem tendsto_ouDriftCoeff_atTop : Tendsto ouDriftCoeff atTop (𝓝 0) := by
  change Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 0)
  exact Real.tendsto_exp_neg_atTop_nhds_zero

/-- The Mehler noise coefficient tends to one at long times. -/
theorem tendsto_ouNoiseCoeff_atTop : Tendsto ouNoiseCoeff atTop (𝓝 1) := by
  have harg : Tendsto (fun t : ℝ => 1 - Real.exp (-2 * t)) atTop (𝓝 1) := by
    have hneg : Tendsto (fun t : ℝ => -2 * t) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg (by norm_num)
    have hexp : Tendsto (fun t : ℝ => Real.exp (-2 * t)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp hneg
    simpa using tendsto_const_nhds.sub hexp
  change Tendsto (fun t : ℝ => Real.sqrt (1 - Real.exp (-2 * t)))
    atTop (𝓝 1)
  convert (Real.continuous_sqrt.tendsto 1).comp harg using 1
  · rfl
  · rw [Real.sqrt_one]

@[simp] lemma ouDriftCoeff_zero : ouDriftCoeff 0 = 1 := by
  simp [ouDriftCoeff]

@[simp] lemma ouNoiseCoeff_zero : ouNoiseCoeff 0 = 0 := by
  simp [ouNoiseCoeff]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- One Mehler update, with the current state and fresh Gaussian innovation. -/
def gaussianOUTransition (t : ℝ) (x z : E) : E :=
  ouDriftCoeff t • x + ouNoiseCoeff t • z

/-- At long times a Mehler update forgets its deterministic initial state. -/
theorem tendsto_gaussianOUTransition_atTop (x z : E) :
    Tendsto (fun t : ℝ => gaussianOUTransition t x z) atTop (𝓝 z) := by
  have h := (tendsto_ouDriftCoeff_atTop.smul_const x).add
    (tendsto_ouNoiseCoeff_atTop.smul_const z)
  simpa [gaussianOUTransition] using h

/-- The stationary two-Gaussian presentation of one OU state. -/
def gaussianOUMap (t : ℝ) (p : E × E) : E :=
  gaussianOUTransition t p.1 p.2

/-- The OU semigroup in its Mehler integral representation. -/
def gaussianOUSemigroup [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E]
    (t : ℝ) (f : E → ℝ) (x : E) : ℝ :=
  ∫ z, f (gaussianOUTransition t x z) ∂stdGaussian E

@[simp] theorem gaussianOUTransition_zero (x z : E) :
    gaussianOUTransition 0 x z = x := by
  simp [gaussianOUTransition]

@[simp] theorem gaussianOUSemigroup_zero [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (f : E → ℝ) (x : E) :
    gaussianOUSemigroup 0 f x = f x := by
  simp [gaussianOUSemigroup]

section Invariance

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [SecondCountableTopology E]

lemma measurable_gaussianOUTransition (t : ℝ) (x : E) :
    Measurable (gaussianOUTransition t x) := by
  unfold gaussianOUTransition
  fun_prop

lemma measurable_gaussianOUMap (t : ℝ) : Measurable (gaussianOUMap (E := E) t) := by
  unfold gaussianOUMap gaussianOUTransition
  fun_prop

/-- A linear combination of two independent standard Gaussians is a scaled
standard Gaussian when the squared coefficients agree. -/
theorem map_gaussianLinearCombination_prod_stdGaussian
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a ^ 2 + b ^ 2 = c ^ 2) :
    Measure.map (fun p : E × E => a • p.1 + b • p.2)
        ((stdGaussian E).prod (stdGaussian E)) =
      (stdGaussian E).map (fun z : E => c • z) := by
  let μa := (stdGaussian E).map (fun x : E => a • x)
  let μb := (stdGaussian E).map (fun x : E => b • x)
  letI : IsProbabilityMeasure μa := by
    dsimp only [μa]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure μb := by
    dsimp only [μb]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hsum :
      Measure.map (fun p : E × E => p.1 + p.2) (μa.prod μb) =
        (stdGaussian E).map (fun z : E => c • z) := by
    apply Measure.ext_of_charFun
    funext ξ
    rw [ProbabilityTheory.charFun_map_add_prod_eq_mul]
    change charFun ((stdGaussian E).map (fun x : E => a • x)) ξ *
        charFun ((stdGaussian E).map (fun x : E => b • x)) ξ = _
    rw [charFun_map_smul, charFun_map_smul, charFun_map_smul,
      charFun_stdGaussian, charFun_stdGaussian, charFun_stdGaussian]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha,
      abs_of_nonneg hb, abs_of_nonneg hc]
    norm_cast
    rw [← Real.exp_add]
    congr 1
    calc
      -(a * ‖ξ‖) ^ 2 / 2 + (-(b * ‖ξ‖) ^ 2 / 2) =
          -(a ^ 2 + b ^ 2) * ‖ξ‖ ^ 2 / 2 := by ring
      _ = -(c * ‖ξ‖) ^ 2 / 2 := by rw [habc]; ring
  calc
    Measure.map (fun p : E × E => a • p.1 + b • p.2)
        ((stdGaussian E).prod (stdGaussian E)) =
        Measure.map (fun p : E × E => p.1 + p.2) (μa.prod μb) := by
      rw [Measure.map_prod_map (stdGaussian E) (stdGaussian E)
        (by fun_prop : Measurable fun x : E => a • x)
        (by fun_prop : Measurable fun x : E => b • x)]
      rw [Measure.map_map]
      · rfl
      · fun_prop
      · fun_prop
    _ = (stdGaussian E).map (fun z : E => c • z) := hsum

/-- A standard Gaussian is invariant under the Mehler rotation. -/
theorem map_gaussianOUMap_prod_stdGaussian {t : ℝ} (ht : 0 ≤ t) :
    Measure.map (gaussianOUMap (E := E) t)
        ((stdGaussian E).prod (stdGaussian E)) =
      stdGaussian E := by
  have h := map_gaussianLinearCombination_prod_stdGaussian (E := E)
    (a := ouDriftCoeff t) (b := ouNoiseCoeff t) (c := 1)
    (ouDriftCoeff_pos t).le (ouNoiseCoeff_nonneg t) (by norm_num)
    (by simpa using ouDriftCoeff_sq_add_ouNoiseCoeff_sq ht)
  change Measure.map
      (fun p : E × E => ouDriftCoeff t • p.1 + ouNoiseCoeff t • p.2)
        ((stdGaussian E).prod (stdGaussian E)) = stdGaussian E
  simpa using h

/-- Distributional semigroup law for two successive Mehler updates. -/
theorem map_gaussianOUTransition_comp_prod_stdGaussian
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : E) :
    Measure.map
        (fun p : E × E =>
          gaussianOUTransition t (gaussianOUTransition s x p.1) p.2)
        ((stdGaussian E).prod (stdGaussian E)) =
      Measure.map (gaussianOUTransition (s + t) x) (stdGaussian E) := by
  let a := ouDriftCoeff t * ouNoiseCoeff s
  let b := ouNoiseCoeff t
  let c := ouNoiseCoeff (s + t)
  let d := ouDriftCoeff (s + t) • x
  have hnoise :
      Measure.map (fun p : E × E => a • p.1 + b • p.2)
          ((stdGaussian E).prod (stdGaussian E)) =
        (stdGaussian E).map (fun z : E => c • z) := by
    apply map_gaussianLinearCombination_prod_stdGaussian (E := E)
    · exact mul_nonneg (ouDriftCoeff_pos t).le (ouNoiseCoeff_nonneg s)
    · exact ouNoiseCoeff_nonneg t
    · exact ouNoiseCoeff_nonneg (s + t)
    · simpa [a, b, c] using ouNoiseCoeff_composition_sq hs ht
  calc
    Measure.map
        (fun p : E × E =>
          gaussianOUTransition t (gaussianOUTransition s x p.1) p.2)
        ((stdGaussian E).prod (stdGaussian E)) =
        Measure.map (fun y : E => d + y)
          (Measure.map (fun p : E × E => a • p.1 + b • p.2)
            ((stdGaussian E).prod (stdGaussian E))) := by
      rw [Measure.map_map]
      · congr 1
        funext p
        simp only [Function.comp_apply, gaussianOUTransition, a, b, d,
          smul_add, smul_smul, ouDriftCoeff_add]
        module
      · fun_prop
      · fun_prop
    _ = Measure.map (fun y : E => d + y)
          ((stdGaussian E).map (fun z : E => c • z)) := by rw [hnoise]
    _ = Measure.map (gaussianOUTransition (s + t) x) (stdGaussian E) := by
      rw [Measure.map_map]
      · rfl
      · fun_prop
      · fun_prop

/-- Semigroup law `P_s (P_t f) = P_{s+t} f` for bounded continuous tests. -/
theorem gaussianOUSemigroup_comp
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (f : BoundedContinuousFunction E ℝ) (x : E) :
    gaussianOUSemigroup s (gaussianOUSemigroup t f) x =
      gaussianOUSemigroup (s + t) f x := by
  let g : E × E → ℝ := fun p =>
    f (gaussianOUTransition t (gaussianOUTransition s x p.1) p.2)
  have hcomp : Continuous (fun p : E × E =>
      gaussianOUTransition t (gaussianOUTransition s x p.1) p.2) := by
    unfold gaussianOUTransition
    fun_prop
  have hg : Integrable g ((stdGaussian E).prod (stdGaussian E)) := by
    refine Integrable.of_bound (f.continuous.comp hcomp).aestronglyMeasurable
      ‖f‖ ?_
    exact Filter.Eventually.of_forall fun p => f.norm_coe_le_norm _
  change (∫ z, ∫ w,
      f (gaussianOUTransition t (gaussianOUTransition s x z) w)
        ∂stdGaussian E ∂stdGaussian E) =
    ∫ z, f (gaussianOUTransition (s + t) x z) ∂stdGaussian E
  rw [← integral_prod g hg]
  have hmap := map_gaussianOUTransition_comp_prod_stdGaussian
    (E := E) hs ht x
  calc
    (∫ p, g p ∂(stdGaussian E).prod (stdGaussian E)) =
        ∫ y, f y ∂Measure.map
          (fun p : E × E =>
            gaussianOUTransition t (gaussianOUTransition s x p.1) p.2)
          ((stdGaussian E).prod (stdGaussian E)) := by
      simpa [g] using (integral_map hcomp.measurable.aemeasurable
        f.continuous.aestronglyMeasurable).symm
    _ = ∫ y, f y ∂Measure.map (gaussianOUTransition (s + t) x)
          (stdGaussian E) := by rw [hmap]
    _ = ∫ z, f (gaussianOUTransition (s + t) x z) ∂stdGaussian E := by
      apply integral_map
      · exact measurable_gaussianOUTransition (s + t) x |>.aemeasurable
      · exact f.continuous.aestronglyMeasurable

/-- Invariance of the Gaussian integral under the OU semigroup. -/
theorem integral_gaussianOUSemigroup
    {t : ℝ} (ht : 0 ≤ t) (f : BoundedContinuousFunction E ℝ) :
    ∫ x, gaussianOUSemigroup t f x ∂stdGaussian E =
      ∫ x, f x ∂stdGaussian E := by
  let g : E × E → ℝ := fun p => f (gaussianOUMap t p)
  have hmapContinuous : Continuous (gaussianOUMap (E := E) t) := by
    unfold gaussianOUMap gaussianOUTransition
    fun_prop
  have hg : Integrable g ((stdGaussian E).prod (stdGaussian E)) := by
    refine Integrable.of_bound
      (f.continuous.comp hmapContinuous).aestronglyMeasurable ‖f‖ ?_
    exact Filter.Eventually.of_forall fun p => f.norm_coe_le_norm _
  change (∫ x, ∫ z, g (x, z) ∂stdGaussian E ∂stdGaussian E) =
    ∫ x, f x ∂stdGaussian E
  rw [← integral_prod g hg]
  calc
    (∫ p, g p ∂(stdGaussian E).prod (stdGaussian E)) =
        ∫ y, f y ∂Measure.map (gaussianOUMap (E := E) t)
          ((stdGaussian E).prod (stdGaussian E)) := by
      simpa [g] using (integral_map hmapContinuous.measurable.aemeasurable
        f.continuous.aestronglyMeasurable).symm
    _ = ∫ y, f y ∂stdGaussian E := by
      rw [map_gaussianOUMap_prod_stdGaussian ht]

/-- Fréchet-derivative commutation for the OU semigroup.  The bounded
continuous map `Df` records the derivative of `f`; the conclusion is the
covector form of `∇ P_t f = exp(-t) P_t (∇ f)`. -/
theorem hasFDerivAt_gaussianOUSemigroup
    (t : ℝ) (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (hDf : ∀ y, HasFDerivAt f (Df y) y) (x : E) :
    HasFDerivAt (gaussianOUSemigroup t f)
      (ouDriftCoeff t • ∫ z, Df (gaussianOUTransition t x z) ∂stdGaussian E) x := by
  let F : E → E → ℝ := fun y z => f (gaussianOUTransition t y z)
  let F' : E → E → E →L[ℝ] ℝ := fun y z =>
    ouDriftCoeff t • Df (gaussianOUTransition t y z)
  have hcore : HasFDerivAt (fun y : E => ∫ z, F y z ∂stdGaussian E)
      (∫ z, F' x z ∂stdGaussian E) x := by
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
        simp [F']
  change HasFDerivAt (fun y : E => ∫ z, F y z ∂stdGaussian E) _ x
  convert hcore using 1
  rw [integral_smul]

/-- The explicit derivative identity associated with
`hasFDerivAt_gaussianOUSemigroup`. -/
theorem fderiv_gaussianOUSemigroup
    (t : ℝ) (f : BoundedContinuousFunction E ℝ)
    (Df : BoundedContinuousFunction E (E →L[ℝ] ℝ))
    (hDf : ∀ y, HasFDerivAt f (Df y) y) (x : E) :
    fderiv ℝ (gaussianOUSemigroup t f) x =
      ouDriftCoeff t • ∫ z, Df (gaussianOUTransition t x z) ∂stdGaussian E :=
  (hasFDerivAt_gaussianOUSemigroup t f Df hDf x).fderiv

/-- Long-time convergence of `P_t f(x)` to the Gaussian mean for bounded
continuous tests. -/
theorem tendsto_gaussianOUSemigroup_atTop
    (f : BoundedContinuousFunction E ℝ) (x : E) :
    Tendsto (fun t : ℝ => gaussianOUSemigroup t f x) atTop
      (𝓝 (∫ z, f z ∂stdGaussian E)) := by
  apply tendsto_integral_filter_of_norm_le_const
  · exact Filter.Eventually.of_forall fun t =>
      (f.continuous.comp (by
        unfold gaussianOUTransition
        fun_prop)).aestronglyMeasurable
  · refine ⟨‖f‖, Filter.Eventually.of_forall fun _ =>
      Filter.Eventually.of_forall fun z => ?_⟩
    exact f.norm_coe_le_norm _
  · exact Filter.Eventually.of_forall fun z =>
      f.continuous.continuousAt.tendsto.comp
        (tendsto_gaussianOUTransition_atTop x z)

end Invariance

end Concrete

end

end UniformRandomMALA
