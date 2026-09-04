import UniformRandomMALA.Concrete.EuclideanTarget
import UniformRandomMALA.DiscreteTime.GaussianMGF
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Moments.ComplexMGF

/-!
# A finite Gaussian likelihood on an explicit innovation space

This file constructs the finite Euler recursion directly on the finite
product space `Fin n → State d`.  All path coordinates and the scalar
likelihood summaries are proved measurable before any integration is used.

For the exact mean-one identity we use a second, equivalent recursive
presentation of the likelihood.  Splitting `Fin (n+1)` into its first
coordinate and its tail turns the proof into ordinary Tonelli integration
and the one-dimensional Gaussian square-completion identity from
`GaussianMGF`.  No filtration, conditional expectation, martingale, or
infinite product space occurs.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace DiscreteTime

open Concrete

section StandardGaussianShift

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The normalized density which translates a standard Gaussian by `a`.
This auxiliary definition is independent of the Euler recursion. -/
def gaussianShiftLikelihood (a z : E) : ℝ :=
  Real.exp (inner ℝ a z - ‖a‖ ^ 2 / 2)

lemma measurable_gaussianShiftLikelihood (a : E) :
    Measurable (gaussianShiftLikelihood a) := by
  unfold gaussianShiftLikelihood
  fun_prop

lemma gaussianShiftLikelihood_pos (a z : E) :
    0 < gaussianShiftLikelihood a z :=
  Real.exp_pos _

lemma integral_gaussianShiftLikelihood (a : E) :
    (∫ z, gaussianShiftLikelihood a z ∂stdGaussian E) = 1 := by
  let L : StrongDual ℝ E := innerSL ℝ a
  have h := integral_exp_add_mul_strongDual_stdGaussian L 1 (-‖a‖ ^ 2 / 2)
  rw [show gaussianShiftLikelihood a =
      fun z => Real.exp (-‖a‖ ^ 2 / 2 + 1 * L z) by
    funext z
    simp [gaussianShiftLikelihood, L]
    ring]
  rw [h]
  simp [L]
  ring

lemma lintegral_gaussianShiftLikelihood (a : E) :
    (∫⁻ z, ENNReal.ofReal (gaussianShiftLikelihood a z) ∂stdGaussian E) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · simp [integral_gaussianShiftLikelihood]
  · exact integrable_exp_add_mul_strongDual_stdGaussian
      (innerSL ℝ a) 1 (-‖a‖ ^ 2 / 2) |>.congr
        (ae_of_all _ fun z => by simp [gaussianShiftLikelihood]; ring)
  · exact ae_of_all _ fun z => (gaussianShiftLikelihood_pos a z).le

private lemma gaussianShift_withDensity_univ (a : E) :
    (stdGaussian E).withDensity
        (fun z => ENNReal.ofReal (gaussianShiftLikelihood a z)) Set.univ = 1 := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  simpa using lintegral_gaussianShiftLikelihood a

/-- The real MGF under the exponentially tilted standard Gaussian.  The
proof only combines two real linear Gaussian exponents; complex Gaussian
integration is not needed. -/
private lemma mgf_gaussianShift_withDensity
    (a : E) (L : StrongDual ℝ E) (t : ℝ) :
    mgf L ((stdGaussian E).withDensity
      (fun z => ENNReal.ofReal (gaussianShiftLikelihood a z))) t =
      Real.exp (t * L a + ‖L‖ ^ 2 * t ^ 2 / 2) := by
  let y : E := (InnerProductSpace.toDual ℝ E).symm L
  rw [mgf, integral_withDensity_eq_integral_toReal_smul
    ((measurable_gaussianShiftLikelihood a).ennreal_ofReal)
      (ae_of_all _ fun z => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (gaussianShiftLikelihood_pos a _).le,
    smul_eq_mul]
  rw [show (fun z : E => gaussianShiftLikelihood a z * Real.exp (t * L z)) =
      fun z => Real.exp (-‖a‖ ^ 2 / 2 +
        1 * (innerSL ℝ (a + t • y)) z) by
    funext z
    rw [gaussianShiftLikelihood, ← Real.exp_add]
    congr 1
    simp only [innerSL_apply_apply, inner_add_left, inner_smul_left]
    rw [show inner ℝ y z = L z by
      exact InnerProductSpace.toDual_symm_apply]
    simp
    ring]
  rw [integral_exp_add_mul_strongDual_stdGaussian]
  simp only [innerSL_apply_norm]
  rw [norm_add_sq_real]
  have hy : ‖y‖ = ‖L‖ := by
    simpa [y] using (map_norm (InnerProductSpace.toDual ℝ E).symm L)
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, y]
  rw [show inner ℝ a ((InnerProductSpace.toDual ℝ E).symm L) = L a by
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply]
  rw [show ‖(InnerProductSpace.toDual ℝ E).symm L‖ = ‖L‖ by
    simpa [y] using hy]
  rw [mul_pow, sq_abs]
  congr 1
  ring

/-- Elementary finite-dimensional Gaussian change of variables: weighting
the standard Gaussian by `exp (⟨a,z⟩ - ‖a‖²/2)` gives the translate by
`a`.  Equality of real MGFs is converted to equality of characteristic
functions only at the final uniqueness step. -/
theorem stdGaussian_withDensity_gaussianShiftLikelihood (a : E) :
    (stdGaussian E).withDensity
        (fun z => ENNReal.ofReal (gaussianShiftLikelihood a z)) =
      (stdGaussian E).map (fun z => z + a) := by
  let ν : Measure E := (stdGaussian E).withDensity
    (fun z => ENNReal.ofReal (gaussianShiftLikelihood a z))
  letI : IsProbabilityMeasure ν :=
    ⟨by simpa [ν] using gaussianShift_withDensity_univ a⟩
  apply Measure.ext_of_charFunDual
  funext L
  let μ : Measure E := (stdGaussian E).map (fun z => z + a)
  letI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (by fun_prop)
  have hmgf : mgf L ν = mgf L μ := by
    funext t
    rw [mgf_gaussianShift_withDensity]
    simp only [μ, mgf]
    rw [integral_map (by fun_prop) (by fun_prop)]
    rw [show (fun z : E => Real.exp (t * L (z + a))) =
        fun z => Real.exp (t * L a) * Real.exp (t * L z) by
      funext z
      rw [map_add, mul_add, Real.exp_add]
      ring]
    rw [integral_const_mul, integral_exp_mul_strongDual_stdGaussian]
    rw [← Real.exp_add]
  have hall : integrableExpSet L ν = Set.univ := by
    ext t
    simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    let y : E := (InnerProductSpace.toDual ℝ E).symm L
    change Integrable (fun w => Real.exp (t * L w))
      ((stdGaussian E).withDensity
        (fun z => ENNReal.ofReal (gaussianShiftLikelihood a z)))
    rw [integrable_withDensity_iff_integrable_smul'
      ((measurable_gaussianShiftLikelihood a).ennreal_ofReal)
      (ae_of_all _ fun z => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (gaussianShiftLikelihood_pos a _).le,
      smul_eq_mul]
    apply (integrable_exp_add_mul_strongDual_stdGaussian
      (innerSL ℝ (a + t • y)) 1 (-‖a‖ ^ 2 / 2)).congr
    exact ae_of_all _ fun z => by
      simp only [gaussianShiftLikelihood]
      rw [← Real.exp_add]
      congr 1
      simp only [innerSL_apply_apply, inner_add_left, inner_smul_left]
      rw [show inner ℝ y z = L z by
        exact InnerProductSpace.toDual_symm_apply]
      simp
      ring
  have heq := eqOn_complexMGF_of_mgf hmgf
  have hat : Complex.I.re ∈ interior (integrableExpSet L ν) := by
    simp [hall]
  specialize heq hat
  simp only [complexMGF, ν, μ] at heq
  rw [charFunDual_apply, charFunDual_apply]
  simpa [mul_comm] using heq

/-- Lintegral form of the one-coordinate shift, convenient for finite
Tonelli induction. -/
theorem lintegral_gaussianShiftLikelihood_comp_sub
    (a : E) {f : E → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z, ENNReal.ofReal (gaussianShiftLikelihood a z) * f (z - a)
        ∂stdGaussian E) =
      ∫⁻ z, f z ∂stdGaussian E := by
  have hd : Measurable
      (fun z => ENNReal.ofReal (gaussianShiftLikelihood a z)) :=
    (measurable_gaussianShiftLikelihood a).ennreal_ofReal
  let g : E → ℝ≥0∞ := fun z => f (z - a)
  have hg : Measurable g := by
    exact hf.comp (measurable_id.sub measurable_const)
  change (∫⁻ z, ENNReal.ofReal (gaussianShiftLikelihood a z) * g z
      ∂stdGaussian E) = _
  calc
    _ = ∫⁻ z, g z ∂((stdGaussian E).withDensity
        (fun z => ENNReal.ofReal (gaussianShiftLikelihood a z))) := by
      exact (lintegral_withDensity_eq_lintegral_mul (stdGaussian E) hd hg).symm
    _ = ∫⁻ z, g z ∂((stdGaussian E).map (fun z => z + a)) := by
      rw [stdGaussian_withDensity_gaussianShiftLikelihood a]
    _ = _ := by
      rw [lintegral_map]
      · simp [g]
      · exact hg
      · fun_prop

end StandardGaussianShift

section EulerPath

variable {d n : ℕ} (V : FirstOrderPotential d)

/-- One explicit Euler step driven by a standard-Gaussian innovation. -/
def finiteEulerStep (delta : ℝ) (x z : State d) : State d :=
  x - delta • V.gradU x + Real.sqrt (2 * delta) • z

lemma continuous_finiteEulerStep (delta : ℝ) :
    Continuous (fun p : State d × State d =>
      finiteEulerStep V delta p.1 p.2) := by
  unfold finiteEulerStep
  exact (continuous_fst.sub
    ((continuous_const : Continuous fun _ : State d × State d => delta).smul
      (V.continuous_gradU.comp continuous_fst))).add
      ((continuous_const : Continuous fun _ : State d × State d =>
        Real.sqrt (2 * delta)).smul continuous_snd)

lemma measurable_finiteEulerStep (delta : ℝ) :
    Measurable (fun p : State d × State d =>
      finiteEulerStep V delta p.1 p.2) :=
  (continuous_finiteEulerStep V delta).measurable

/-- Euler state after `k` steps.  When `k > n`, missing innovations are
filled by zero.  The intended path only evaluates this function for
`k ≤ n`; totalizing the definition makes induction and measurability
elementary. -/
def finiteEulerState (delta : ℝ) (x0 : State d)
    (z : Fin n → State d) : ℕ → State d
  | 0 => x0
  | k + 1 =>
      finiteEulerStep V delta (finiteEulerState delta x0 z k)
        (if hk : k < n then z ⟨k, hk⟩ else 0)

@[simp] lemma finiteEulerState_zero (delta : ℝ) (x0 : State d)
    (z : Fin n → State d) :
    finiteEulerState V delta x0 z 0 = x0 := rfl

lemma finiteEulerState_succ_of_lt (delta : ℝ) (x0 : State d)
    (z : Fin n → State d) {k : ℕ} (hk : k < n) :
    finiteEulerState V delta x0 z (k + 1) =
      finiteEulerStep V delta (finiteEulerState V delta x0 z k) (z ⟨k, hk⟩) := by
  simp [finiteEulerState, hk]

/-- The finite Euler path, including its initial point. -/
def finiteEulerPath (delta : ℝ) (x0 : State d)
    (z : Fin n → State d) (k : Fin (n + 1)) : State d :=
  finiteEulerState V delta x0 z k

@[simp] lemma finiteEulerPath_zero (delta : ℝ) (x0 : State d)
    (z : Fin n → State d) :
    finiteEulerPath V delta x0 z 0 = x0 := rfl

lemma measurable_finiteEulerState (delta : ℝ) (x0 : State d) (k : ℕ) :
    Measurable (fun z : Fin n → State d =>
      finiteEulerState V delta x0 z k) := by
  induction k with
  | zero => simp [finiteEulerState]
  | succ k ih =>
      rw [show (fun z : Fin n → State d =>
          finiteEulerState V delta x0 z (k + 1)) =
        fun z => finiteEulerStep V delta (finiteEulerState V delta x0 z k)
          (if hk : k < n then z ⟨k, hk⟩ else 0) by
            funext z
            rw [finiteEulerState]]
      have hz : Measurable (fun z : Fin n → State d =>
          if hk : k < n then z ⟨k, hk⟩ else 0) := by
        by_cases hk : k < n
        · simpa [hk] using (measurable_pi_apply (⟨k, hk⟩ : Fin n))
        · simp [hk]
      change Measurable
        ((fun p : State d × State d => finiteEulerStep V delta p.1 p.2) ∘
          fun z => (finiteEulerState V delta x0 z k,
            if hk : k < n then z ⟨k, hk⟩ else 0))
      exact (measurable_finiteEulerStep V delta).comp (ih.prodMk hz)

lemma measurable_finiteEulerPath (delta : ℝ) (x0 : State d)
    (k : Fin (n + 1)) :
    Measurable (fun z : Fin n → State d =>
      finiteEulerPath V delta x0 z k) :=
  measurable_finiteEulerState V delta x0 k

/-- Predictable Gaussian shift at step `k` in the finite Euler path. -/
def finiteEulerTheta (delta : ℝ) (x0 : State d)
    (z : Fin n → State d) (k : Fin n) : State d :=
  (1 / Real.sqrt 2) •
    (V.gradU (finiteEulerState V delta x0 z k) - V.gradU x0)

lemma measurable_finiteEulerTheta (delta : ℝ) (x0 : State d)
    (k : Fin n) :
    Measurable (fun z : Fin n → State d =>
      finiteEulerTheta V delta x0 z k) := by
  unfold finiteEulerTheta
  exact (measurable_const : Measurable fun _ : Fin n → State d =>
      (1 / Real.sqrt 2 : ℝ)).smul
    ((V.continuous_gradU.measurable.comp
      (measurable_finiteEulerState V delta x0 k)).sub measurable_const)

/-- Linear Gaussian term in the finite likelihood exponent. -/
def finiteEulerM (delta : ℝ) (x0 : State d)
    (z : Fin n → State d) : ℝ :=
  Real.sqrt delta * ∑ k, @inner ℝ (State d) _
    (finiteEulerTheta V delta x0 z k) (z k)

/-- Quadratic compensator in the finite likelihood exponent. -/
def finiteEulerV (delta : ℝ) (x0 : State d)
    (z : Fin n → State d) : ℝ :=
  delta * ∑ k, ‖finiteEulerTheta V delta x0 z k‖ ^ 2

/-- Discrete path energy used in the Lean replacement for Appendix B. -/
def finiteEulerEnergy (delta : ℝ) (x0 : State d)
    (z : Fin n → State d) : ℝ :=
  delta * ∑ k : Fin n, ‖finiteEulerState V delta x0 z k - x0‖ ^ 2

/-- Normalized finite Gaussian likelihood. -/
def finiteEulerD (delta : ℝ) (x0 : State d)
    (z : Fin n → State d) : ℝ :=
  Real.exp (finiteEulerM V delta x0 z -
    finiteEulerV V delta x0 z / 2)

lemma measurable_finiteEulerM (delta : ℝ) (x0 : State d) :
    Measurable (finiteEulerM V delta x0 : (Fin n → State d) → ℝ) := by
  unfold finiteEulerM
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro k hk
  exact continuous_inner.measurable.comp
    ((measurable_finiteEulerTheta V delta x0 k).prodMk
      (measurable_pi_apply k))

lemma measurable_finiteEulerV (delta : ℝ) (x0 : State d) :
    Measurable (finiteEulerV V delta x0 : (Fin n → State d) → ℝ) := by
  unfold finiteEulerV
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro k hk
  exact ((continuous_norm.measurable.comp
    (measurable_finiteEulerTheta V delta x0 k)).pow_const 2)

lemma measurable_finiteEulerEnergy (delta : ℝ) (x0 : State d) :
    Measurable (finiteEulerEnergy V delta x0 :
      (Fin n → State d) → ℝ) := by
  unfold finiteEulerEnergy
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro k hk
  exact ((continuous_norm.measurable.comp
    ((measurable_finiteEulerState V delta x0 k).sub measurable_const)).pow_const 2)

/-- Lipschitzness of the gradient controls each predictable Gaussian shift. -/
lemma finiteEulerTheta_norm_sq_le (delta : ℝ) (x0 : State d)
    (z : Fin n → State d) (k : Fin n) :
    ‖finiteEulerTheta V delta x0 z k‖ ^ 2 ≤
      (V.L ^ 2 / 2) * ‖finiteEulerState V delta x0 z k - x0‖ ^ 2 := by
  have hgrad :
      ‖V.gradU (finiteEulerState V delta x0 z k) - V.gradU x0‖ ≤
        V.L * ‖finiteEulerState V delta x0 z k - x0‖ := by
    have hg := V.grad_lipschitz.norm_sub_le
      (finiteEulerState V delta x0 z k) x0
    change ‖V.gradU (finiteEulerState V delta x0 z k) - V.gradU x0‖ ≤
      V.L * ‖finiteEulerState V delta x0 z k - x0‖ at hg
    exact hg
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have htheta : ‖finiteEulerTheta V delta x0 z k‖ =
      (1 / Real.sqrt 2) *
        ‖V.gradU (finiteEulerState V delta x0 z k) - V.gradU x0‖ := by
    rw [finiteEulerTheta, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos (by norm_num) hsqrt)]
  rw [htheta]
  have hL0 : 0 ≤ V.L := V.hL.le
  have hx0 : 0 ≤ ‖finiteEulerState V delta x0 z k - x0‖ := norm_nonneg _
  have hg0 : 0 ≤
      ‖V.gradU (finiteEulerState V delta x0 z k) - V.gradU x0‖ := norm_nonneg _
  have hs0 : 0 ≤ 1 / Real.sqrt 2 := (div_pos (by norm_num) hsqrt).le
  have hinv_sq : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
    rw [div_pow, one_pow, hsqrt_sq]
  have hsq :
      ‖V.gradU (finiteEulerState V delta x0 z k) - V.gradU x0‖ ^ 2 ≤
        (V.L * ‖finiteEulerState V delta x0 z k - x0‖) ^ 2 :=
    (sq_le_sq₀ hg0 (mul_nonneg hL0 hx0)).2 hgrad
  calc
    (1 / Real.sqrt 2 *
        ‖V.gradU (finiteEulerState V delta x0 z k) - V.gradU x0‖) ^ 2 =
        (1 / 2) *
          ‖V.gradU (finiteEulerState V delta x0 z k) - V.gradU x0‖ ^ 2 := by
      rw [mul_pow, hinv_sq]
    _ ≤ (1 / 2) *
        (V.L * ‖finiteEulerState V delta x0 z k - x0‖) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = (V.L ^ 2 / 2) *
        ‖finiteEulerState V delta x0 z k - x0‖ ^ 2 := by ring

/-- Pathwise bridge from the Euler energy to the Gaussian compensator. -/
lemma finiteEulerV_le_energy (delta : ℝ) (hdelta : 0 ≤ delta)
    (x0 : State d) (z : Fin n → State d) :
    finiteEulerV V delta x0 z ≤
      (V.L ^ 2 / 2) * finiteEulerEnergy V delta x0 z := by
  unfold finiteEulerV finiteEulerEnergy
  calc
    delta * ∑ k : Fin n, ‖finiteEulerTheta V delta x0 z k‖ ^ 2 ≤
        delta * ∑ k : Fin n,
          (V.L ^ 2 / 2) *
            ‖finiteEulerState V delta x0 z k - x0‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hdelta
      exact Finset.sum_le_sum fun k hk =>
        finiteEulerTheta_norm_sq_le V delta x0 z k
    _ = (V.L ^ 2 / 2) *
        (delta * ∑ k : Fin n,
          ‖finiteEulerState V delta x0 z k - x0‖ ^ 2) := by
      rw [← Finset.mul_sum]
      ring

lemma measurable_finiteEulerD (delta : ℝ) (x0 : State d) :
    Measurable (finiteEulerD V delta x0 : (Fin n → State d) → ℝ) := by
  unfold finiteEulerD
  exact Real.continuous_exp.measurable.comp
    ((measurable_finiteEulerM V delta x0).sub
      ((measurable_finiteEulerV V delta x0).div_const (2 : ℝ)))

lemma finiteEulerD_pos (delta : ℝ) (x0 : State d)
    (z : Fin n → State d) :
    0 < finiteEulerD V delta x0 z :=
  Real.exp_pos _

/-- After consuming the first innovation, the remaining explicit Euler
states are exactly the states generated from `Fin.tail z`. -/
lemma finiteEulerState_succ_eq_tail (delta : ℝ) (x : State d)
    (z : Fin (n + 1) → State d) {k : ℕ} (hk : k < n) :
    finiteEulerState V delta x z (k + 1) =
      finiteEulerState V delta (finiteEulerStep V delta x (z 0))
        (Fin.tail z) k := by
  induction k with
  | zero =>
      rw [finiteEulerState_succ_of_lt V delta x z (by omega)]
      rfl
  | succ k ih =>
      have hk' : k < n := by omega
      rw [finiteEulerState_succ_of_lt V delta x z (by omega)]
      rw [finiteEulerState_succ_of_lt V delta
        (finiteEulerStep V delta x (z 0)) (Fin.tail z) hk']
      rw [ih hk']
      rfl

end EulerPath

section OneStep

variable {d : ℕ}

/-- One normalized Gaussian factor.  Writing the compensator with
`(beta * sqrt delta)^2` makes normalization exact even before the eventual
assumption `0 ≤ delta` is introduced. -/
def finiteGaussianStepLikelihood (beta delta : ℝ)
    (theta z : State d) : ℝ :=
  Real.exp ((beta * Real.sqrt delta) * @inner ℝ (State d) _ theta z -
    (beta * Real.sqrt delta) ^ 2 * ‖theta‖ ^ 2 / 2)

lemma continuous_finiteGaussianStepLikelihood (beta delta : ℝ) :
    Continuous (fun p : State d × State d =>
      finiteGaussianStepLikelihood beta delta p.1 p.2) := by
  unfold finiteGaussianStepLikelihood
  apply Real.continuous_exp.comp
  exact (continuous_const.mul continuous_inner).sub
    ((continuous_const.mul ((continuous_norm.comp continuous_fst).pow 2)).div_const 2)

lemma measurable_finiteGaussianStepLikelihood (beta delta : ℝ) :
    Measurable (fun p : State d × State d =>
      finiteGaussianStepLikelihood beta delta p.1 p.2) :=
  (continuous_finiteGaussianStepLikelihood beta delta).measurable

lemma finiteGaussianStepLikelihood_pos (beta delta : ℝ)
    (theta z : State d) :
    0 < finiteGaussianStepLikelihood beta delta theta z :=
  Real.exp_pos _

lemma integrable_finiteGaussianStepLikelihood (beta delta : ℝ)
    (theta : State d) :
    Integrable (finiteGaussianStepLikelihood beta delta theta)
      (stdGaussian (State d)) := by
  let L : StrongDual ℝ (State d) := innerSL ℝ theta
  let t : ℝ := beta * Real.sqrt delta
  have h := integrable_exp_add_mul_strongDual_stdGaussian L t
    (-(t ^ 2 * ‖theta‖ ^ 2 / 2))
  apply h.congr
  exact ae_of_all _ fun z => by
    unfold finiteGaussianStepLikelihood
    simp only [L, t, innerSL_apply_apply]
    congr 1
    ring

/-- Completing one finite-dimensional Gaussian square: every one-step
factor has exactly unit mass. -/
lemma integral_finiteGaussianStepLikelihood (beta delta : ℝ)
    (theta : State d) :
    (∫ z, finiteGaussianStepLikelihood beta delta theta z
        ∂stdGaussian (State d)) = 1 := by
  let L : StrongDual ℝ (State d) := innerSL ℝ theta
  let t : ℝ := beta * Real.sqrt delta
  have h := integral_exp_add_mul_strongDual_stdGaussian L t
    (-(t ^ 2 * ‖theta‖ ^ 2 / 2))
  rw [show (fun z => finiteGaussianStepLikelihood beta delta theta z) =
      fun z => Real.exp (-(t ^ 2 * ‖theta‖ ^ 2 / 2) + t * L z) by
    funext z
    unfold finiteGaussianStepLikelihood
    simp only [L, t, innerSL_apply_apply]
    congr 1
    ring]
  rw [h]
  simp only [L, t, innerSL_apply_norm]
  rw [show -(t ^ 2 * ‖theta‖ ^ 2 / 2) + ‖theta‖ ^ 2 * t ^ 2 / 2 = 0 by ring]
  exact Real.exp_zero

lemma lintegral_finiteGaussianStepLikelihood (beta delta : ℝ)
    (theta : State d) :
    (∫⁻ z, ENNReal.ofReal (finiteGaussianStepLikelihood beta delta theta z)
        ∂stdGaussian (State d)) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_finiteGaussianStepLikelihood beta delta theta)
    (ae_of_all _ fun z => (finiteGaussianStepLikelihood_pos beta delta theta z).le)]
  simp [integral_finiteGaussianStepLikelihood beta delta theta]

/-- A one-step factor is the abstract Gaussian translation density with
translation vector `beta * sqrt delta • theta`. -/
lemma finiteGaussianStepLikelihood_eq_gaussianShiftLikelihood
    (beta delta : ℝ) (theta z : State d) :
    finiteGaussianStepLikelihood beta delta theta z =
      gaussianShiftLikelihood ((beta * Real.sqrt delta) • theta) z := by
  unfold finiteGaussianStepLikelihood gaussianShiftLikelihood
  congr 1
  simp only [inner_smul_left, norm_smul, Real.norm_eq_abs]
  rw [show (|beta * Real.sqrt delta| * ‖theta‖) ^ 2 =
      (beta * Real.sqrt delta) ^ 2 * ‖theta‖ ^ 2 by
    rw [mul_pow, sq_abs]]
  simp only [starRingEnd_apply, star_trivial]

/-- Coordinatewise change of measure for the exact one-step likelihood. -/
theorem stdGaussian_withDensity_finiteGaussianStepLikelihood
    (beta delta : ℝ) (theta : State d) :
    (stdGaussian (State d)).withDensity
        (fun z => ENNReal.ofReal
          (finiteGaussianStepLikelihood beta delta theta z)) =
      (stdGaussian (State d)).map
        (fun z => z + (beta * Real.sqrt delta) • theta) := by
  simpa only [finiteGaussianStepLikelihood_eq_gaussianShiftLikelihood] using
    (stdGaussian_withDensity_gaussianShiftLikelihood
      ((beta * Real.sqrt delta) • theta : State d))

/-- Lintegral change-of-variables form used by chronological induction. -/
theorem lintegral_finiteGaussianStepLikelihood_comp_sub
    (beta delta : ℝ) (theta : State d)
    {f : State d → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z, ENNReal.ofReal
          (finiteGaussianStepLikelihood beta delta theta z) *
        f (z - (beta * Real.sqrt delta) • theta)
        ∂stdGaussian (State d)) =
      ∫⁻ z, f z ∂stdGaussian (State d) := by
  simpa only [finiteGaussianStepLikelihood_eq_gaussianShiftLikelihood] using
    (lintegral_gaussianShiftLikelihood_comp_sub
      ((beta * Real.sqrt delta) • theta : State d) hf)

end OneStep

section RecursiveProduct

variable {d : ℕ} (V : FirstOrderPotential d)

/-- The predictable shift used in the paper, with the initial point kept as
an explicit frozen reference. -/
def frozenGradientShift (xRef x : State d) : State d :=
  (1 / Real.sqrt 2) • (V.gradU x - V.gradU xRef)

lemma continuous_frozenGradientShift :
    Continuous (fun p : State d × State d =>
      frozenGradientShift V p.1 p.2) := by
  unfold frozenGradientShift
  exact (continuous_const : Continuous fun _ : State d × State d =>
    (1 / Real.sqrt 2 : ℝ)).smul
      ((V.continuous_gradU.comp continuous_snd).sub
        (V.continuous_gradU.comp continuous_fst))

/-- Euler step with the drift frozen at the deterministic reference point. -/
def finiteFrozenEulerStep (delta : ℝ) (xRef x z : State d) : State d :=
  x - delta • V.gradU xRef + Real.sqrt (2 * delta) • z

lemma continuous_finiteFrozenEulerStep (delta : ℝ) (xRef : State d) :
    Continuous (fun p : State d × State d =>
      finiteFrozenEulerStep V delta xRef p.1 p.2) := by
  unfold finiteFrozenEulerStep
  fun_prop

lemma measurable_finiteFrozenEulerStep (delta : ℝ) (xRef : State d) :
    Measurable (fun p : State d × State d =>
      finiteFrozenEulerStep V delta xRef p.1 p.2) :=
  (continuous_finiteFrozenEulerStep V delta xRef).measurable

/-- Pathwise square-root cancellation behind the change of innovations.
This is the elementary algebraic replacement for the continuous-time
change-of-measure argument. -/
lemma finiteEulerStep_eq_finiteFrozenEulerStep_centered
    (delta : ℝ) (hdelta : 0 ≤ delta) (xRef x z : State d) :
    finiteEulerStep V delta x z =
      finiteFrozenEulerStep V delta xRef x
        (z - Real.sqrt delta • frozenGradientShift V xRef x) := by
  have hsqrt2 : Real.sqrt (2 * delta) =
      Real.sqrt 2 * Real.sqrt delta := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrt2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqd : Real.sqrt delta ^ 2 = delta := Real.sq_sqrt hdelta
  have hcoef : Real.sqrt (2 * delta) * Real.sqrt delta *
      (1 / Real.sqrt 2) = delta := by
    rw [hsqrt2]
    field_simp [ne_of_gt hsqrt2pos]
    nlinarith
  unfold finiteEulerStep finiteFrozenEulerStep frozenGradientShift
  rw [smul_sub, smul_smul, smul_smul]
  rw [hcoef]
  module

/-- Triangular centering of a finite innovation tuple.  Each shift uses
only the state generated by earlier, uncentered coordinates. -/
def finiteCenteredInnovations (delta : ℝ) (xRef : State d) :
    {n : ℕ} → State d → (Fin n → State d) → (Fin n → State d)
  | 0, _x, z => z
  | _n + 1, x, z =>
      Fin.cons
        (z 0 - Real.sqrt delta • frozenGradientShift V xRef x)
        (finiteCenteredInnovations delta xRef
          (finiteEulerStep V delta x (z 0)) (Fin.tail z))

@[simp] lemma finiteCenteredInnovations_zero
    (delta : ℝ) (xRef x : State d) (z : Fin 0 → State d) :
    finiteCenteredInnovations V delta xRef x z = z := rfl

@[simp] lemma finiteCenteredInnovations_succ_zero
    (delta : ℝ) (xRef x : State d) (z : Fin (n + 1) → State d) :
    finiteCenteredInnovations V delta xRef x z 0 =
      z 0 - Real.sqrt delta • frozenGradientShift V xRef x := by
  simp [finiteCenteredInnovations]

@[simp] lemma finiteCenteredInnovations_succ_succ
    (delta : ℝ) (xRef x : State d) (z : Fin (n + 1) → State d)
    (k : Fin n) :
    finiteCenteredInnovations V delta xRef x z k.succ =
      finiteCenteredInnovations V delta xRef
        (finiteEulerStep V delta x (z 0)) (Fin.tail z) k := by
  simp [finiteCenteredInnovations]

@[simp] lemma finiteCenteredInnovations_cons
    (delta : ℝ) (xRef x z0 : State d) (ztail : Fin n → State d) :
    finiteCenteredInnovations V delta xRef x (Fin.cons z0 ztail) =
      Fin.cons (z0 - Real.sqrt delta • frozenGradientShift V xRef x)
        (finiteCenteredInnovations V delta xRef
          (finiteEulerStep V delta x z0) ztail) := rfl

lemma measurable_finiteCenteredInnovations_joint
    (delta : ℝ) (xRef : State d) :
    ∀ n : ℕ, Measurable (fun p : State d × (Fin n → State d) =>
      finiteCenteredInnovations V delta xRef p.1 p.2) := by
  intro n
  induction n with
  | zero =>
      apply measurable_pi_iff.mpr
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      have hz0 : Measurable
          (fun p : State d × (Fin (n + 1) → State d) => p.2 0) :=
        (measurable_pi_apply (0 : Fin (n + 1))).comp measurable_snd
      have hshift : Measurable
          (fun p : State d × (Fin (n + 1) → State d) =>
            frozenGradientShift V xRef p.1) :=
        continuous_frozenGradientShift V |>.measurable |>.comp
          (measurable_const.prodMk measurable_fst)
      have hstep : Measurable
          (fun p : State d × (Fin (n + 1) → State d) =>
            finiteEulerStep V delta p.1 (p.2 0)) :=
        (measurable_finiteEulerStep V delta).comp (measurable_fst.prodMk hz0)
      have htail : Measurable
          (fun p : State d × (Fin (n + 1) → State d) => Fin.tail p.2) := by
        apply measurable_pi_iff.mpr
        intro k
        exact (measurable_pi_apply k.succ).comp measurable_snd
      have hfuture : Measurable
          (fun p : State d × (Fin (n + 1) → State d) =>
            finiteCenteredInnovations V delta xRef
              (finiteEulerStep V delta p.1 (p.2 0)) (Fin.tail p.2)) := by
        exact ih.comp (hstep.prodMk htail)
      apply measurable_pi_iff.mpr
      intro i
      refine Fin.cases ?_ (fun k => ?_) i
      · change Measurable (fun p : State d × (Fin (n + 1) → State d) =>
          p.2 0 - Real.sqrt delta • frozenGradientShift V xRef p.1)
        exact hz0.sub ((measurable_const : Measurable fun _ :
          State d × (Fin (n + 1) → State d) => Real.sqrt delta).smul hshift)
      · change Measurable
          ((fun q : Fin n → State d => q k) ∘
            fun p : State d × (Fin (n + 1) → State d) =>
              finiteCenteredInnovations V delta xRef
                (finiteEulerStep V delta p.1 (p.2 0)) (Fin.tail p.2))
        exact (measurable_pi_apply k).comp hfuture

lemma measurable_finiteCenteredInnovations
    (delta : ℝ) (xRef x : State d) (n : ℕ) :
    Measurable (finiteCenteredInnovations V delta xRef x :
      (Fin n → State d) → (Fin n → State d)) := by
  exact (measurable_finiteCenteredInnovations_joint V delta xRef n).comp
    (measurable_const.prodMk measurable_id)

/-- Frozen-drift endpoint after finitely many centered innovations. -/
def finiteFrozenEndpointRec (delta : ℝ) (xRef : State d) :
    {n : ℕ} → State d → (Fin n → State d) → State d
  | 0, x, _z => x
  | _n + 1, x, z =>
      finiteFrozenEndpointRec delta xRef
        (finiteFrozenEulerStep V delta xRef x (z 0)) (Fin.tail z)

/-- Usual Euler endpoint in the same chronological recursion format. -/
def finiteEulerEndpointRec (delta : ℝ) :
    {n : ℕ} → State d → (Fin n → State d) → State d
  | 0, x, _z => x
  | _n + 1, x, z =>
      finiteEulerEndpointRec delta
        (finiteEulerStep V delta x (z 0)) (Fin.tail z)

lemma measurable_finiteEulerEndpointRec_joint (delta : ℝ) :
    ∀ n : ℕ, Measurable (fun p : State d × (Fin n → State d) =>
      finiteEulerEndpointRec V delta p.1 p.2) := by
  intro n
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
      have hz0 : Measurable
          (fun p : State d × (Fin (n + 1) → State d) => p.2 0) :=
        (measurable_pi_apply (0 : Fin (n + 1))).comp measurable_snd
      have hstep : Measurable
          (fun p : State d × (Fin (n + 1) → State d) =>
            finiteEulerStep V delta p.1 (p.2 0)) :=
        (measurable_finiteEulerStep V delta).comp (measurable_fst.prodMk hz0)
      have htail : Measurable
          (fun p : State d × (Fin (n + 1) → State d) => Fin.tail p.2) := by
        apply measurable_pi_iff.mpr
        intro k
        exact (measurable_pi_apply k.succ).comp measurable_snd
      exact ih.comp (hstep.prodMk htail)

lemma measurable_finiteEulerEndpointRec
    (delta : ℝ) (x : State d) (n : ℕ) :
    Measurable (finiteEulerEndpointRec V delta x :
      (Fin n → State d) → State d) :=
  (measurable_finiteEulerEndpointRec_joint V delta n).comp
    (measurable_const.prodMk measurable_id)

lemma measurable_finiteFrozenEndpointRec_joint
    (delta : ℝ) (xRef : State d) :
    ∀ n : ℕ, Measurable (fun p : State d × (Fin n → State d) =>
      finiteFrozenEndpointRec V delta xRef p.1 p.2) := by
  intro n
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
      have hz0 : Measurable
          (fun p : State d × (Fin (n + 1) → State d) => p.2 0) :=
        (measurable_pi_apply (0 : Fin (n + 1))).comp measurable_snd
      have hstep : Measurable
          (fun p : State d × (Fin (n + 1) → State d) =>
            finiteFrozenEulerStep V delta xRef p.1 (p.2 0)) :=
        (measurable_finiteFrozenEulerStep V delta xRef).comp
          (measurable_fst.prodMk hz0)
      have htail : Measurable
          (fun p : State d × (Fin (n + 1) → State d) => Fin.tail p.2) := by
        apply measurable_pi_iff.mpr
        intro k
        exact (measurable_pi_apply k.succ).comp measurable_snd
      exact ih.comp (hstep.prodMk htail)

lemma measurable_finiteFrozenEndpointRec
    (delta : ℝ) (xRef x : State d) (n : ℕ) :
    Measurable (finiteFrozenEndpointRec V delta xRef x :
      (Fin n → State d) → State d) :=
  (measurable_finiteFrozenEndpointRec_joint V delta xRef n).comp
    (measurable_const.prodMk measurable_id)

/-- Closed form of the finite frozen-drift recursion. -/
lemma finiteFrozenEndpointRec_eq_closedForm (delta : ℝ) (xRef : State d) :
    ∀ {n : ℕ} (x : State d) (z : Fin n → State d),
      finiteFrozenEndpointRec V delta xRef x z =
        x - ((n : ℝ) * delta) • V.gradU xRef +
          Real.sqrt (2 * delta) • ∑ k, z k := by
  intro n
  induction n with
  | zero => intro x z; simp [finiteFrozenEndpointRec]
  | succ n ih =>
      intro x z
      rw [finiteFrozenEndpointRec]
      rw [ih]
      rw [Fin.sum_univ_succ]
      unfold finiteFrozenEulerStep
      push_cast
      simp only [Fin.tail]
      module

/-- Closed form at the initial frozen reference. -/
lemma finiteFrozenEndpointRec_initial_eq_closedForm
    (delta : ℝ) (x0 : State d) (z : Fin n → State d) :
    finiteFrozenEndpointRec V delta x0 x0 z =
      x0 - ((n : ℝ) * delta) • V.gradU x0 +
        Real.sqrt (2 * delta) • ∑ k, z k :=
  finiteFrozenEndpointRec_eq_closedForm V delta x0 x0 z

/-- The uncentered Euler endpoint is the frozen-drift endpoint driven by
the triangularly centered innovations. -/
lemma finiteEulerEndpointRec_eq_finiteFrozenEndpointRec_centered
    (delta : ℝ) (hdelta : 0 ≤ delta) (xRef : State d) :
    ∀ {n : ℕ} (x : State d) (z : Fin n → State d),
      finiteEulerEndpointRec V delta x z =
        finiteFrozenEndpointRec V delta xRef x
          (finiteCenteredInnovations V delta xRef x z) := by
  intro n
  induction n with
  | zero => intro x z; rfl
  | succ n ih =>
      intro x z
      rw [finiteEulerEndpointRec, finiteFrozenEndpointRec]
      simp only [finiteCenteredInnovations_succ_zero,
        finiteCenteredInnovations_succ_succ]
      rw [← finiteEulerStep_eq_finiteFrozenEulerStep_centered
        V delta hdelta xRef x (z 0)]
      exact ih (finiteEulerStep V delta x (z 0)) (Fin.tail z)

/-- Chronological likelihood recursion on a finite tuple.  At a successor
step, coordinate `0` is consumed and the recursion continues on `Fin.tail`.
The current Euler state and the frozen initial reference are separate
arguments, which is what makes the induction closed under one step. -/
def finiteGaussianLikelihoodRec (beta delta : ℝ) (xRef : State d) :
    {n : ℕ} → State d → (Fin n → State d) → ℝ
  | 0, _x, _z => 1
  | _n + 1, x, z =>
      finiteGaussianStepLikelihood beta delta
          (frozenGradientShift V xRef x) (z 0) *
        finiteGaussianLikelihoodRec beta delta xRef
          (finiteEulerStep V delta x (z 0)) (Fin.tail z)

/-- Chronological version of the linear term `M`.  Keeping the current state
as an argument makes the successor equation definitional. -/
def finiteGaussianMRec (delta : ℝ) (xRef : State d) :
    {n : ℕ} → State d → (Fin n → State d) → ℝ
  | 0, _x, _z => 0
  | _n + 1, x, z =>
      Real.sqrt delta * @inner ℝ (State d) _
          (frozenGradientShift V xRef x) (z 0) +
        finiteGaussianMRec delta xRef
          (finiteEulerStep V delta x (z 0)) (Fin.tail z)

/-- Chronological version of the quadratic compensator `V`. -/
def finiteGaussianVRec (delta : ℝ) (xRef : State d) :
    {n : ℕ} → State d → (Fin n → State d) → ℝ
  | 0, _x, _z => 0
  | _n + 1, x, z =>
      delta * ‖frozenGradientShift V xRef x‖ ^ 2 +
        finiteGaussianVRec delta xRef
          (finiteEulerStep V delta x (z 0)) (Fin.tail z)

/-- Chronological Euler path energy, aligned definitionally with
`finiteGaussianVRec`. -/
def finiteEulerEnergyRec (delta : ℝ) (xRef : State d) :
    {n : ℕ} → State d → (Fin n → State d) → ℝ
  | 0, _x, _z => 0
  | _n + 1, x, z =>
      delta * ‖x - xRef‖ ^ 2 +
        finiteEulerEnergyRec delta xRef
          (finiteEulerStep V delta x (z 0)) (Fin.tail z)

/-- The chronological energy is the same finite sum of explicit Euler
states as the direct path presentation, with the frozen reference kept
separate from the current initial state. -/
lemma finiteEulerEnergyRec_eq_sum (delta : ℝ) (xRef : State d) :
    ∀ {n : ℕ} (x : State d) (z : Fin n → State d),
      finiteEulerEnergyRec V delta xRef x z =
        delta * ∑ k : Fin n,
          ‖finiteEulerState V delta x z k - xRef‖ ^ 2 := by
  intro n
  induction n with
  | zero => intro x z; simp [finiteEulerEnergyRec]
  | succ n ih =>
      intro x z
      rw [finiteEulerEnergyRec]
      rw [ih]
      rw [Fin.sum_univ_succ]
      have htail : ∀ k : Fin n,
          finiteEulerState V delta x z (Fin.succ k) =
            finiteEulerState V delta
              (finiteEulerStep V delta x (z 0)) (Fin.tail z) k := by
        intro k
        exact finiteEulerState_succ_eq_tail V delta x z k.isLt
      simp_rw [htail]
      have hzero : finiteEulerState V delta x z
          ((0 : Fin (n + 1)) : ℕ) = x := rfl
      rw [hzero]
      ring

/-- At the actual initial state, the recursive energy used in likelihood
induction is definitionally the direct Euler energy used by the MGF bound. -/
lemma finiteEulerEnergyRec_initial_eq_finiteEulerEnergy
    (delta : ℝ) (x0 : State d) (z : Fin n → State d) :
    finiteEulerEnergyRec V delta x0 x0 z =
      finiteEulerEnergy V delta x0 z := by
  rw [finiteEulerEnergyRec_eq_sum]
  rfl

/-- The shift bound in a form independent of any path representation. -/
lemma frozenGradientShift_norm_sq_le (xRef x : State d) :
    ‖frozenGradientShift V xRef x‖ ^ 2 ≤
      (V.L ^ 2 / 2) * ‖x - xRef‖ ^ 2 := by
  have hgrad : ‖V.gradU x - V.gradU xRef‖ ≤ V.L * ‖x - xRef‖ := by
    have hg := V.grad_lipschitz.norm_sub_le x xRef
    change ‖V.gradU x - V.gradU xRef‖ ≤ V.L * ‖x - xRef‖ at hg
    exact hg
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hshift : ‖frozenGradientShift V xRef x‖ =
      (1 / Real.sqrt 2) * ‖V.gradU x - V.gradU xRef‖ := by
    rw [frozenGradientShift, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos (by norm_num) hsqrt)]
  rw [hshift]
  have hL0 : 0 ≤ V.L := V.hL.le
  have hx0 : 0 ≤ ‖x - xRef‖ := norm_nonneg _
  have hg0 : 0 ≤ ‖V.gradU x - V.gradU xRef‖ := norm_nonneg _
  have hinv_sq : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
    rw [div_pow, one_pow, hsqrt_sq]
  have hsq : ‖V.gradU x - V.gradU xRef‖ ^ 2 ≤
      (V.L * ‖x - xRef‖) ^ 2 :=
    (sq_le_sq₀ hg0 (mul_nonneg hL0 hx0)).2 hgrad
  calc
    (1 / Real.sqrt 2 * ‖V.gradU x - V.gradU xRef‖) ^ 2 =
        (1 / 2) * ‖V.gradU x - V.gradU xRef‖ ^ 2 := by
      rw [mul_pow, hinv_sq]
    _ ≤ (1 / 2) * (V.L * ‖x - xRef‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = (V.L ^ 2 / 2) * ‖x - xRef‖ ^ 2 := by ring

/-- Recursive pathwise bridge used directly by the finite likelihood proof. -/
lemma finiteGaussianVRec_le_energyRec
    (delta : ℝ) (hdelta : 0 ≤ delta) (xRef : State d) :
    ∀ {n : ℕ} (x : State d) (z : Fin n → State d),
      finiteGaussianVRec V delta xRef x z ≤
        (V.L ^ 2 / 2) * finiteEulerEnergyRec V delta xRef x z := by
  intro n
  induction n with
  | zero => intro x z; simp [finiteGaussianVRec, finiteEulerEnergyRec]
  | succ n ih =>
      intro x z
      simp only [finiteGaussianVRec, finiteEulerEnergyRec]
      have hone := mul_le_mul_of_nonneg_left
        (frozenGradientShift_norm_sq_le V xRef x) hdelta
      have htail := ih (finiteEulerStep V delta x (z 0)) (Fin.tail z)
      calc
        delta * ‖frozenGradientShift V xRef x‖ ^ 2 +
            finiteGaussianVRec V delta xRef
              (finiteEulerStep V delta x (z 0)) (Fin.tail z) ≤
            delta * ((V.L ^ 2 / 2) * ‖x - xRef‖ ^ 2) +
              (V.L ^ 2 / 2) * finiteEulerEnergyRec V delta xRef
                (finiteEulerStep V delta x (z 0)) (Fin.tail z) :=
          add_le_add hone htail
        _ = (V.L ^ 2 / 2) *
            (delta * ‖x - xRef‖ ^ 2 +
              finiteEulerEnergyRec V delta xRef
                (finiteEulerStep V delta x (z 0)) (Fin.tail z)) := by ring

/-- The exponential presentation of the recursive finite likelihood. -/
def finiteGaussianDRec (beta delta : ℝ) (xRef : State d)
    {n : ℕ} (x : State d) (z : Fin n → State d) : ℝ :=
  Real.exp (beta * finiteGaussianMRec V delta xRef x z -
    beta ^ 2 * finiteGaussianVRec V delta xRef x z / 2)

/-- Algebraic powered-likelihood identity used before Cauchy--Schwarz:
`D_1^q = D_q * exp((q^2-q)V/2)`. -/
lemma finiteGaussianDRec_rpow_eq
    (q delta : ℝ) (xRef : State d) {n : ℕ}
    (x : State d) (z : Fin n → State d) :
    (finiteGaussianDRec V 1 delta xRef x z) ^ q =
      finiteGaussianDRec V q delta xRef x z *
        Real.exp ((q ^ 2 - q) *
          finiteGaussianVRec V delta xRef x z / 2) := by
  unfold finiteGaussianDRec
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_add]
  congr 1
  ring

/-- Elementary Young bound for the second likelihood moment.  The first
term on the right is a normalized likelihood with parameter `4`; the second
is the only energy exponential that remains. -/
lemma finiteGaussianDRec_sq_le
    (delta : ℝ) (xRef : State d) {n : ℕ}
    (x : State d) (z : Fin n → State d) :
    finiteGaussianDRec V 1 delta xRef x z ^ 2 ≤
      (finiteGaussianDRec V 4 delta xRef x z +
        Real.exp (6 * finiteGaussianVRec V delta xRef x z)) / 2 := by
  let M := finiteGaussianMRec V delta xRef x z
  let W := finiteGaussianVRec V delta xRef x z
  simp only [finiteGaussianDRec, one_mul, one_pow]
  change Real.exp (M - W / 2) ^ 2 ≤
    (Real.exp (4 * M - 4 ^ 2 * W / 2) + Real.exp (6 * W)) / 2
  let a := Real.exp (2 * M - 4 * W)
  let b := Real.exp (3 * W)
  have hleft : Real.exp (M - W / 2) ^ 2 = a * b := by
    rw [show Real.exp (M - W / 2) ^ 2 =
        Real.exp (M - W / 2) * Real.exp (M - W / 2) by ring,
      ← Real.exp_add]
    change Real.exp ((M - W / 2) + (M - W / 2)) =
      Real.exp (2 * M - 4 * W) * Real.exp (3 * W)
    rw [← Real.exp_add]
    congr 1
    ring
  have ha : a ^ 2 = Real.exp (4 * M - 4 ^ 2 * W / 2) := by
    change Real.exp (2 * M - 4 * W) ^ 2 = _
    rw [show Real.exp (2 * M - 4 * W) ^ 2 =
        Real.exp (2 * M - 4 * W) * Real.exp (2 * M - 4 * W) by ring,
      ← Real.exp_add]
    congr 1
    ring
  have hb : b ^ 2 = Real.exp (6 * W) := by
    change Real.exp (3 * W) ^ 2 = _
    rw [show Real.exp (3 * W) ^ 2 =
        Real.exp (3 * W) * Real.exp (3 * W) by ring,
      ← Real.exp_add]
    congr 1
    ring
  rw [hleft, ← ha, ← hb]
  nlinarith [sq_nonneg (a - b)]

@[simp] lemma finiteGaussianLikelihoodRec_zero
    (beta delta : ℝ) (xRef x : State d) (z : Fin 0 → State d) :
    finiteGaussianLikelihoodRec V beta delta xRef x z = 1 := rfl

@[simp] lemma finiteGaussianLikelihoodRec_succ
    (beta delta : ℝ) (xRef x : State d)
    (z : Fin (n + 1) → State d) :
    finiteGaussianLikelihoodRec V beta delta xRef x z =
      finiteGaussianStepLikelihood beta delta
          (frozenGradientShift V xRef x) (z 0) *
        finiteGaussianLikelihoodRec V beta delta xRef
          (finiteEulerStep V delta x (z 0)) (Fin.tail z) := rfl

lemma measurable_finiteGaussianLikelihoodRec_joint
    (beta delta : ℝ) (xRef : State d) :
    ∀ n : ℕ, Measurable (fun p : State d × (Fin n → State d) =>
      finiteGaussianLikelihoodRec V beta delta xRef p.1 p.2) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hz0 : Measurable
          (fun p : State d × (Fin (n + 1) → State d) => p.2 0) :=
        (measurable_pi_apply (0 : Fin (n + 1))).comp measurable_snd
      have htheta : Measurable
          (fun p : State d × (Fin (n + 1) → State d) =>
            frozenGradientShift V xRef p.1) :=
        continuous_frozenGradientShift V |>.measurable |>.comp
          (measurable_const.prodMk measurable_fst)
      have hfactor : Measurable
          (fun p : State d × (Fin (n + 1) → State d) =>
            finiteGaussianStepLikelihood beta delta
              (frozenGradientShift V xRef p.1) (p.2 0)) :=
        by
          unfold finiteGaussianStepLikelihood
          apply Real.continuous_exp.measurable.comp
          apply Measurable.sub
          · exact measurable_const.mul
              (continuous_inner.measurable.comp (htheta.prodMk hz0))
          · exact (measurable_const.mul
              ((continuous_norm.measurable.comp htheta).pow_const 2)).div_const 2
      have hstep : Measurable
          (fun p : State d × (Fin (n + 1) → State d) =>
            finiteEulerStep V delta p.1 (p.2 0)) :=
        (measurable_finiteEulerStep V delta).comp (measurable_fst.prodMk hz0)
      have htail : Measurable
          (fun p : State d × (Fin (n + 1) → State d) => Fin.tail p.2) := by
        apply measurable_pi_iff.mpr
        intro k
        exact (measurable_pi_apply k.succ).comp measurable_snd
      have hfuture : Measurable
          (fun p : State d × (Fin (n + 1) → State d) =>
            finiteGaussianLikelihoodRec V beta delta xRef
              (finiteEulerStep V delta p.1 (p.2 0)) (Fin.tail p.2)) := by
        change Measurable
          ((fun q : State d × (Fin n → State d) =>
              finiteGaussianLikelihoodRec V beta delta xRef q.1 q.2) ∘
            fun p : State d × (Fin (n + 1) → State d) =>
              (finiteEulerStep V delta p.1 (p.2 0), Fin.tail p.2))
        exact ih.comp (hstep.prodMk htail)
      change Measurable
        ((fun p : State d × (Fin (n + 1) → State d) =>
            finiteGaussianStepLikelihood beta delta
              (frozenGradientShift V xRef p.1) (p.2 0)) *
          fun p => finiteGaussianLikelihoodRec V beta delta xRef
            (finiteEulerStep V delta p.1 (p.2 0)) (Fin.tail p.2))
      exact hfactor.mul hfuture

lemma measurable_finiteGaussianLikelihoodRec
    (beta delta : ℝ) (xRef x : State d) :
    Measurable (finiteGaussianLikelihoodRec V beta delta xRef x :
      (Fin n → State d) → ℝ) := by
  change Measurable
    ((fun p : State d × (Fin n → State d) =>
      finiteGaussianLikelihoodRec V beta delta xRef p.1 p.2) ∘
        fun z => (x, z))
  exact (measurable_finiteGaussianLikelihoodRec_joint V beta delta xRef n).comp
    (measurable_const.prodMk measurable_id)

/-- Joint measurability when the frozen reference and current state are both
variables.  This is the version needed to integrate the initial state after
the fixed-initial-state product identity has been proved. -/
lemma measurable_finiteGaussianLikelihoodRec_all
    (beta delta : ℝ) :
    ∀ n : ℕ, Measurable
      (fun p : (State d × State d) × (Fin n → State d) =>
        finiteGaussianLikelihoodRec V beta delta p.1.1 p.1.2 p.2) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have href : Measurable
          (fun p : (State d × State d) × (Fin (n + 1) → State d) => p.1.1) :=
        measurable_fst.comp measurable_fst
      have hcurrent : Measurable
          (fun p : (State d × State d) × (Fin (n + 1) → State d) => p.1.2) :=
        measurable_snd.comp measurable_fst
      have hz0 : Measurable
          (fun p : (State d × State d) × (Fin (n + 1) → State d) => p.2 0) :=
        (measurable_pi_apply (0 : Fin (n + 1))).comp measurable_snd
      have htheta : Measurable
          (fun p : (State d × State d) × (Fin (n + 1) → State d) =>
            frozenGradientShift V p.1.1 p.1.2) :=
        continuous_frozenGradientShift V |>.measurable |>.comp
          (href.prodMk hcurrent)
      have hfactor : Measurable
          (fun p : (State d × State d) × (Fin (n + 1) → State d) =>
            finiteGaussianStepLikelihood beta delta
              (frozenGradientShift V p.1.1 p.1.2) (p.2 0)) := by
        unfold finiteGaussianStepLikelihood
        apply Real.continuous_exp.measurable.comp
        apply Measurable.sub
        · exact measurable_const.mul
            (continuous_inner.measurable.comp (htheta.prodMk hz0))
        · exact (measurable_const.mul
            ((continuous_norm.measurable.comp htheta).pow_const 2)).div_const 2
      have hstep : Measurable
          (fun p : (State d × State d) × (Fin (n + 1) → State d) =>
            finiteEulerStep V delta p.1.2 (p.2 0)) :=
        (measurable_finiteEulerStep V delta).comp (hcurrent.prodMk hz0)
      have htail : Measurable
          (fun p : (State d × State d) × (Fin (n + 1) → State d) =>
            Fin.tail p.2) := by
        apply measurable_pi_iff.mpr
        intro k
        exact (measurable_pi_apply k.succ).comp measurable_snd
      have hfuture : Measurable
          (fun p : (State d × State d) × (Fin (n + 1) → State d) =>
            finiteGaussianLikelihoodRec V beta delta p.1.1
              (finiteEulerStep V delta p.1.2 (p.2 0)) (Fin.tail p.2)) := by
        change Measurable
          ((fun q : (State d × State d) × (Fin n → State d) =>
              finiteGaussianLikelihoodRec V beta delta q.1.1 q.1.2 q.2) ∘
            fun p : (State d × State d) × (Fin (n + 1) → State d) =>
              ((p.1.1, finiteEulerStep V delta p.1.2 (p.2 0)), Fin.tail p.2))
        exact ih.comp ((href.prodMk hstep).prodMk htail)
      change Measurable
        ((fun p : (State d × State d) × (Fin (n + 1) → State d) =>
            finiteGaussianStepLikelihood beta delta
              (frozenGradientShift V p.1.1 p.1.2) (p.2 0)) *
          fun p => finiteGaussianLikelihoodRec V beta delta p.1.1
            (finiteEulerStep V delta p.1.2 (p.2 0)) (Fin.tail p.2))
      exact hfactor.mul hfuture

lemma measurable_finiteGaussianLikelihoodRec_initial
    (beta delta : ℝ) (n : ℕ) :
    Measurable (fun p : State d × (Fin n → State d) =>
      finiteGaussianLikelihoodRec V beta delta p.1 p.1 p.2) := by
  change Measurable
    ((fun q : (State d × State d) × (Fin n → State d) =>
        finiteGaussianLikelihoodRec V beta delta q.1.1 q.1.2 q.2) ∘
      fun p : State d × (Fin n → State d) => ((p.1, p.1), p.2))
  exact (measurable_finiteGaussianLikelihoodRec_all V beta delta n).comp
    ((measurable_fst.prodMk measurable_fst).prodMk measurable_snd)

lemma measurable_finiteGaussianVRec_all (delta : ℝ) :
    ∀ n : ℕ, Measurable
      (fun p : (State d × State d) × (Fin n → State d) =>
        finiteGaussianVRec V delta p.1.1 p.1.2 p.2) := by
  intro n
  induction n with
  | zero => simp [finiteGaussianVRec]
  | succ n ih =>
      have href : Measurable
          (fun p : (State d × State d) × (Fin (n + 1) → State d) => p.1.1) :=
        measurable_fst.comp measurable_fst
      have hcurrent : Measurable
          (fun p : (State d × State d) × (Fin (n + 1) → State d) => p.1.2) :=
        measurable_snd.comp measurable_fst
      have hz0 : Measurable
          (fun p : (State d × State d) × (Fin (n + 1) → State d) => p.2 0) :=
        (measurable_pi_apply (0 : Fin (n + 1))).comp measurable_snd
      have htheta : Measurable
          (fun p : (State d × State d) × (Fin (n + 1) → State d) =>
            frozenGradientShift V p.1.1 p.1.2) :=
        continuous_frozenGradientShift V |>.measurable |>.comp
          (href.prodMk hcurrent)
      have hfirst : Measurable
          (fun p : (State d × State d) × (Fin (n + 1) → State d) =>
            delta * ‖frozenGradientShift V p.1.1 p.1.2‖ ^ 2) :=
        measurable_const.mul
          ((continuous_norm.measurable.comp htheta).pow_const 2)
      have hstep : Measurable
          (fun p : (State d × State d) × (Fin (n + 1) → State d) =>
            finiteEulerStep V delta p.1.2 (p.2 0)) :=
        (measurable_finiteEulerStep V delta).comp (hcurrent.prodMk hz0)
      have htail : Measurable
          (fun p : (State d × State d) × (Fin (n + 1) → State d) =>
            Fin.tail p.2) := by
        apply measurable_pi_iff.mpr
        intro k
        exact (measurable_pi_apply k.succ).comp measurable_snd
      have hfuture : Measurable
          (fun p : (State d × State d) × (Fin (n + 1) → State d) =>
            finiteGaussianVRec V delta p.1.1
              (finiteEulerStep V delta p.1.2 (p.2 0)) (Fin.tail p.2)) := by
        change Measurable
          ((fun q : (State d × State d) × (Fin n → State d) =>
              finiteGaussianVRec V delta q.1.1 q.1.2 q.2) ∘
            fun p : (State d × State d) × (Fin (n + 1) → State d) =>
              ((p.1.1, finiteEulerStep V delta p.1.2 (p.2 0)), Fin.tail p.2))
        exact ih.comp ((href.prodMk hstep).prodMk htail)
      change Measurable
        ((fun p : (State d × State d) × (Fin (n + 1) → State d) =>
            delta * ‖frozenGradientShift V p.1.1 p.1.2‖ ^ 2) +
          fun p => finiteGaussianVRec V delta p.1.1
            (finiteEulerStep V delta p.1.2 (p.2 0)) (Fin.tail p.2))
      exact hfirst.add hfuture

lemma measurable_finiteGaussianVRec_initial (delta : ℝ) (n : ℕ) :
    Measurable (fun p : State d × (Fin n → State d) =>
      finiteGaussianVRec V delta p.1 p.1 p.2) := by
  change Measurable
    ((fun q : (State d × State d) × (Fin n → State d) =>
        finiteGaussianVRec V delta q.1.1 q.1.2 q.2) ∘
      fun p : State d × (Fin n → State d) => ((p.1, p.1), p.2))
  exact (measurable_finiteGaussianVRec_all V delta n).comp
    ((measurable_fst.prodMk measurable_fst).prodMk measurable_snd)

lemma finiteGaussianLikelihoodRec_pos
    (beta delta : ℝ) (xRef : State d) :
    ∀ {n : ℕ} (x : State d) (z : Fin n → State d),
      0 < finiteGaussianLikelihoodRec V beta delta xRef x z := by
  intro n
  induction n with
  | zero => intro x z; simp
  | succ n ih =>
      intro x z
      rw [finiteGaussianLikelihoodRec_succ]
      exact mul_pos (finiteGaussianStepLikelihood_pos _ _ _ _) (ih _ _)

/-- The chronological product is exactly `exp(beta M - beta^2 V / 2)`.
This is only finite algebra.  The hypothesis `0 ≤ delta` is used once to
replace `(sqrt delta)^2` by `delta`. -/
lemma finiteGaussianLikelihoodRec_eq_DRec
    (beta delta : ℝ) (hdelta : 0 ≤ delta) (xRef : State d) :
    ∀ {n : ℕ} (x : State d) (z : Fin n → State d),
      finiteGaussianLikelihoodRec V beta delta xRef x z =
        finiteGaussianDRec V beta delta xRef x z := by
  intro n
  induction n with
  | zero =>
      intro x z
      simp [finiteGaussianLikelihoodRec, finiteGaussianDRec,
        finiteGaussianMRec, finiteGaussianVRec]
  | succ n ih =>
      intro x z
      rw [finiteGaussianLikelihoodRec_succ, ih]
      unfold finiteGaussianStepLikelihood finiteGaussianDRec
      rw [← Real.exp_add]
      congr 1
      simp only [finiteGaussianMRec, finiteGaussianVRec]
      rw [mul_pow, Real.sq_sqrt hdelta]
      ring

/-- Exact finite product normalization on the explicit innovation space.

The proof is an induction on `n`.  At the successor step, the measurable
equivalence `Fin (n+1) → E ≃ E × (Fin n → E)` exposes the first innovation.
Tonelli then integrates the tail by the induction hypothesis and the first
coordinate by `integral_finiteGaussianStepLikelihood`. -/
lemma lintegral_finiteGaussianLikelihoodRec
    (beta delta : ℝ) (xRef : State d) :
    ∀ (n : ℕ) (x : State d),
      (∫⁻ z, ENNReal.ofReal
          (finiteGaussianLikelihoodRec V beta delta xRef x z)
          ∂Measure.pi (fun _ : Fin n => stdGaussian (State d))) = 1 := by
  intro n
  induction n with
  | zero =>
      intro x
      simp [finiteGaussianLikelihoodRec]
  | succ n ih =>
      intro x
      let e : (Fin (n + 1) → State d) ≃ᵐ
          State d × (Fin n → State d) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => State d) 0
      let F : State d × (Fin n → State d) → ℝ≥0∞ := fun p =>
        ENNReal.ofReal (finiteGaussianLikelihoodRec V beta delta xRef x (e.symm p))
      have hF : Measurable F := by
        exact ENNReal.measurable_ofReal.comp
          ((measurable_finiteGaussianLikelihoodRec V beta delta xRef x).comp
            e.symm.measurable)
      have hmp := measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => stdGaussian (State d)) (0 : Fin (n + 1))
      calc
        (∫⁻ z, ENNReal.ofReal
            (finiteGaussianLikelihoodRec V beta delta xRef x z)
            ∂Measure.pi (fun _ : Fin (n + 1) => stdGaussian (State d))) =
            ∫⁻ z, F (e z)
              ∂Measure.pi (fun _ : Fin (n + 1) => stdGaussian (State d)) := by
                apply lintegral_congr
                intro z
                simp [F]
        _ = ∫⁻ p, F p ∂(stdGaussian (State d)).prod
              (Measure.pi (fun _ : Fin n => stdGaussian (State d))) := by
                exact hmp.lintegral_comp hF
        _ = ∫⁻ z0, ∫⁻ ztail, F (z0, ztail)
              ∂Measure.pi (fun _ : Fin n => stdGaussian (State d))
              ∂stdGaussian (State d) := by
                exact lintegral_prod F hF.aemeasurable
        _ = ∫⁻ z0,
              ENNReal.ofReal
                (finiteGaussianStepLikelihood beta delta
                  (frozenGradientShift V xRef x) z0)
              ∂stdGaussian (State d) := by
                apply lintegral_congr
                intro z0
                rw [show (∫⁻ ztail, F (z0, ztail)
                    ∂Measure.pi (fun _ : Fin n => stdGaussian (State d))) =
                    ENNReal.ofReal
                      (finiteGaussianStepLikelihood beta delta
                        (frozenGradientShift V xRef x) z0) by
                  simp only [F, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
                    Fin.insertNthEquiv, Fin.insertNth_zero, Equiv.coe_fn_mk,
                    finiteGaussianLikelihoodRec_succ, Fin.cons_zero, Fin.tail_cons,
                    Fin.zero_succAbove, cast_eq]
                  change (∫⁻ ztail,
                      ENNReal.ofReal
                        (finiteGaussianStepLikelihood beta delta
                            (frozenGradientShift V xRef x) z0 *
                          finiteGaussianLikelihoodRec V beta delta xRef
                            (finiteEulerStep V delta x z0) ztail)
                        ∂Measure.pi (fun _ : Fin n => stdGaussian (State d))) =
                    ENNReal.ofReal (finiteGaussianStepLikelihood beta delta
                      (frozenGradientShift V xRef x) z0)
                  rw [show (∫⁻ ztail,
                        ENNReal.ofReal
                          (finiteGaussianStepLikelihood beta delta
                              (frozenGradientShift V xRef x) z0 *
                            finiteGaussianLikelihoodRec V beta delta xRef
                              (finiteEulerStep V delta x z0) ztail)
                          ∂Measure.pi (fun _ : Fin n => stdGaussian (State d))) =
                      ∫⁻ ztail,
                        ENNReal.ofReal (finiteGaussianStepLikelihood beta delta
                            (frozenGradientShift V xRef x) z0) *
                          ENNReal.ofReal
                            (finiteGaussianLikelihoodRec V beta delta xRef
                              (finiteEulerStep V delta x z0) ztail)
                          ∂Measure.pi (fun _ : Fin n => stdGaussian (State d)) by
                    apply lintegral_congr
                    intro ztail
                    exact ENNReal.ofReal_mul
                      (finiteGaussianStepLikelihood_pos beta delta
                        (frozenGradientShift V xRef x) z0).le]
                  rw [lintegral_const_mul]
                  · rw [ih]
                    simp
                  · exact ENNReal.measurable_ofReal.comp
                      (measurable_finiteGaussianLikelihoodRec V beta delta xRef
                        (finiteEulerStep V delta x z0))]
        _ = 1 := lintegral_finiteGaussianStepLikelihood beta delta
          (frozenGradientShift V xRef x)

/-- The triangular centering map pushes the finite likelihood-tilted
innovation law back to the ordinary finite product Gaussian law.  This
functional form is proved by finite Tonelli induction and is equivalent to
the corresponding pushforward measure identity. -/
lemma lintegral_finiteGaussianLikelihoodRec_centered
    (delta : ℝ) (xRef : State d) :
    ∀ (n : ℕ) (x : State d) (f : (Fin n → State d) → ℝ≥0∞),
      Measurable f →
      (∫⁻ z, ENNReal.ofReal
            (finiteGaussianLikelihoodRec V 1 delta xRef x z) *
          f (finiteCenteredInnovations V delta xRef x z)
          ∂Measure.pi (fun _ : Fin n => stdGaussian (State d))) =
        ∫⁻ z, f z
          ∂Measure.pi (fun _ : Fin n => stdGaussian (State d)) := by
  intro n
  induction n with
  | zero =>
      intro x f hf
      simp [finiteGaussianLikelihoodRec]
  | succ n ih =>
      intro x f hf
      let e : (Fin (n + 1) → State d) ≃ᵐ
          State d × (Fin n → State d) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => State d) 0
      let c : State d × (Fin n → State d) →
          (Fin (n + 1) → State d) := fun p => Fin.cons p.1 p.2
      have hc : Measurable c := by
        apply measurable_pi_iff.mpr
        intro i
        refine Fin.cases ?_ (fun k => ?_) i
        · exact measurable_fst
        · exact (measurable_pi_apply k).comp measurable_snd
      have hc_eq : c = e.symm := by
        funext p
        simp [c, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv, Fin.insertNth_zero]
      let F : State d × (Fin n → State d) → ℝ≥0∞ := fun p =>
        ENNReal.ofReal
            (finiteGaussianLikelihoodRec V 1 delta xRef x (c p)) *
          f (finiteCenteredInnovations V delta xRef x (c p))
      let G : State d × (Fin n → State d) → ℝ≥0∞ :=
        fun p => f (c p)
      have hF : Measurable F := by
        apply Measurable.mul
        · exact ENNReal.measurable_ofReal.comp
            ((measurable_finiteGaussianLikelihoodRec V 1 delta xRef x).comp
              hc)
        · exact hf.comp
            ((measurable_finiteCenteredInnovations V delta xRef x (n + 1)).comp
              hc)
      have hG : Measurable G := hf.comp hc
      let g : State d → ℝ≥0∞ := fun w0 =>
        ∫⁻ wtail, G (w0, wtail)
          ∂Measure.pi (fun _ : Fin n => stdGaussian (State d))
      have hg : Measurable g := by
        exact hG.lintegral_prod_right
      have hmp := measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => stdGaussian (State d)) (0 : Fin (n + 1))
      have hinner (z0 : State d) :
          (∫⁻ ztail, F (z0, ztail)
              ∂Measure.pi (fun _ : Fin n => stdGaussian (State d))) =
            ENNReal.ofReal (finiteGaussianStepLikelihood 1 delta
                (frozenGradientShift V xRef x) z0) *
              g (z0 - Real.sqrt delta • frozenGradientShift V xRef x) := by
        let fTail : (Fin n → State d) → ℝ≥0∞ := fun wtail =>
          G (z0 - Real.sqrt delta • frozenGradientShift V xRef x, wtail)
        have hfTail : Measurable fTail :=
          hG.comp (measurable_const.prodMk measurable_id)
        simp only [F, c,
          Fin.insertNthEquiv, Fin.insertNth_zero, Equiv.coe_fn_mk,
          finiteGaussianLikelihoodRec_succ, Fin.cons_zero, Fin.tail_cons,
          Fin.zero_succAbove, cast_eq, finiteCenteredInnovations_succ_zero,
          finiteCenteredInnovations_succ_succ, finiteCenteredInnovations_cons]
        change (∫⁻ ztail,
            ENNReal.ofReal
                (finiteGaussianStepLikelihood 1 delta
                    (frozenGradientShift V xRef x) z0 *
                  finiteGaussianLikelihoodRec V 1 delta xRef
                    (finiteEulerStep V delta x z0) ztail) *
              fTail (finiteCenteredInnovations V delta xRef
                (finiteEulerStep V delta x z0) ztail)
              ∂Measure.pi (fun _ : Fin n => stdGaussian (State d))) = _
        rw [show (∫⁻ ztail,
              ENNReal.ofReal
                  (finiteGaussianStepLikelihood 1 delta
                      (frozenGradientShift V xRef x) z0 *
                    finiteGaussianLikelihoodRec V 1 delta xRef
                      (finiteEulerStep V delta x z0) ztail) *
                fTail (finiteCenteredInnovations V delta xRef
                  (finiteEulerStep V delta x z0) ztail)
                ∂Measure.pi (fun _ : Fin n => stdGaussian (State d))) =
            ∫⁻ ztail,
              ENNReal.ofReal (finiteGaussianStepLikelihood 1 delta
                  (frozenGradientShift V xRef x) z0) *
                (ENNReal.ofReal
                    (finiteGaussianLikelihoodRec V 1 delta xRef
                      (finiteEulerStep V delta x z0) ztail) *
                  fTail (finiteCenteredInnovations V delta xRef
                    (finiteEulerStep V delta x z0) ztail))
                ∂Measure.pi (fun _ : Fin n => stdGaussian (State d)) by
          apply lintegral_congr
          intro ztail
          rw [ENNReal.ofReal_mul
            (finiteGaussianStepLikelihood_pos 1 delta
              (frozenGradientShift V xRef x) z0).le]
          ac_rfl]
        rw [lintegral_const_mul]
        · rw [ih (finiteEulerStep V delta x z0) fTail hfTail]
        · exact (ENNReal.measurable_ofReal.comp
              (measurable_finiteGaussianLikelihoodRec V 1 delta xRef
                (finiteEulerStep V delta x z0))).mul
            (hfTail.comp
              (measurable_finiteCenteredInnovations V delta xRef
                (finiteEulerStep V delta x z0) n))
      calc
        (∫⁻ z, ENNReal.ofReal
              (finiteGaussianLikelihoodRec V 1 delta xRef x z) *
            f (finiteCenteredInnovations V delta xRef x z)
            ∂Measure.pi (fun _ : Fin (n + 1) => stdGaussian (State d))) =
            ∫⁻ z, F (e z)
              ∂Measure.pi (fun _ : Fin (n + 1) => stdGaussian (State d)) := by
                apply lintegral_congr
                intro z
                simp [F, hc_eq]
        _ = ∫⁻ p, F p ∂(stdGaussian (State d)).prod
              (Measure.pi (fun _ : Fin n => stdGaussian (State d))) := by
                exact hmp.lintegral_comp hF
        _ = ∫⁻ z0, ∫⁻ ztail, F (z0, ztail)
              ∂Measure.pi (fun _ : Fin n => stdGaussian (State d))
              ∂stdGaussian (State d) := by
                exact lintegral_prod F hF.aemeasurable
        _ = ∫⁻ z0,
              ENNReal.ofReal (finiteGaussianStepLikelihood 1 delta
                  (frozenGradientShift V xRef x) z0) *
                g (z0 - Real.sqrt delta • frozenGradientShift V xRef x)
              ∂stdGaussian (State d) := by
                apply lintegral_congr
                exact hinner
        _ = ∫⁻ w0, g w0 ∂stdGaussian (State d) := by
              simpa only [one_mul] using
                (lintegral_finiteGaussianStepLikelihood_comp_sub 1 delta
                  (frozenGradientShift V xRef x) hg)
        _ = ∫⁻ p, G p ∂(stdGaussian (State d)).prod
              (Measure.pi (fun _ : Fin n => stdGaussian (State d))) := by
                symm
                exact lintegral_prod G hG.aemeasurable
        _ = ∫⁻ z, G (e z)
              ∂Measure.pi (fun _ : Fin (n + 1) => stdGaussian (State d)) := by
                exact (hmp.lintegral_comp hG).symm
        _ = ∫⁻ z, f z
              ∂Measure.pi (fun _ : Fin (n + 1) => stdGaussian (State d)) := by
                apply lintegral_congr
                intro z
                simp [G, hc_eq]

/-- Measure-valued version of the preceding functional identity. -/
theorem map_finiteCenteredInnovations_likelihood_withDensity
    (delta : ℝ) (xRef x : State d) (n : ℕ) :
    Measure.map (finiteCenteredInnovations V delta xRef x)
        ((Measure.pi (fun _ : Fin n => stdGaussian (State d))).withDensity
          (fun z => ENNReal.ofReal
            (finiteGaussianLikelihoodRec V 1 delta xRef x z))) =
      Measure.pi (fun _ : Fin n => stdGaussian (State d)) := by
  let base : Measure (Fin n → State d) :=
    Measure.pi (fun _ : Fin n => stdGaussian (State d))
  let center : (Fin n → State d) → (Fin n → State d) :=
    finiteCenteredInnovations V delta xRef x
  let density : (Fin n → State d) → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (finiteGaussianLikelihoodRec V 1 delta xRef x z)
  have hcenter : Measurable center :=
    measurable_finiteCenteredInnovations V delta xRef x n
  have hdensity : Measurable density :=
    ENNReal.measurable_ofReal.comp
      (measurable_finiteGaussianLikelihoodRec V 1 delta xRef x)
  ext s hs
  rw [Measure.map_apply hcenter hs]
  have hpre : MeasurableSet (center ⁻¹' s) := hs.preimage hcenter
  let f : (Fin n → State d) → ℝ≥0∞ :=
    s.indicator (fun _ => 1)
  have hf : Measurable f := Measurable.indicator measurable_const hs
  calc
    (base.withDensity density) (center ⁻¹' s) =
        ∫⁻ z, f (center z) ∂(base.withDensity density) := by
      symm
      change (∫⁻ z, (center ⁻¹' s).indicator (fun _ => 1) z
        ∂(base.withDensity density)) = _
      exact lintegral_indicator_one hpre
    _ = ∫⁻ z, density z * f (center z) ∂base := by
      exact lintegral_withDensity_eq_lintegral_mul base hdensity
        (hf.comp hcenter)
    _ = ∫⁻ z, f z ∂base := by
      exact lintegral_finiteGaussianLikelihoodRec_centered
        V delta xRef n x f hf
    _ = base s := lintegral_indicator_one hs

/-- Endpoint law under the finite likelihood: the ordinary Euler endpoint
under the tilted innovation law is the frozen-drift endpoint under an
untitled product Gaussian law. -/
theorem map_finiteEulerEndpointRec_likelihood_withDensity
    (delta : ℝ) (hdelta : 0 ≤ delta) (xRef x : State d) (n : ℕ) :
    Measure.map (finiteEulerEndpointRec V delta x)
        ((Measure.pi (fun _ : Fin n => stdGaussian (State d))).withDensity
          (fun z => ENNReal.ofReal
            (finiteGaussianLikelihoodRec V 1 delta xRef x z))) =
      Measure.map (finiteFrozenEndpointRec V delta xRef x)
        (Measure.pi (fun _ : Fin n => stdGaussian (State d))) := by
  let tilted : Measure (Fin n → State d) :=
    (Measure.pi (fun _ : Fin n => stdGaussian (State d))).withDensity
      (fun z => ENNReal.ofReal
        (finiteGaussianLikelihoodRec V 1 delta xRef x z))
  let center : (Fin n → State d) → (Fin n → State d) :=
    finiteCenteredInnovations V delta xRef x
  let frozen : (Fin n → State d) → State d :=
    finiteFrozenEndpointRec V delta xRef x
  have hcenter : Measurable center :=
    measurable_finiteCenteredInnovations V delta xRef x n
  have hfrozen : Measurable frozen :=
    measurable_finiteFrozenEndpointRec V delta xRef x n
  have hend : finiteEulerEndpointRec V delta x = frozen ∘ center := by
    funext z
    exact finiteEulerEndpointRec_eq_finiteFrozenEndpointRec_centered
      V delta hdelta xRef x z
  rw [hend, ← Measure.map_map hfrozen hcenter]
  rw [show Measure.map center tilted =
      Measure.pi (fun _ : Fin n => stdGaussian (State d)) by
    exact map_finiteCenteredInnovations_likelihood_withDensity
      V delta xRef x n]

/-- The same endpoint-law identity with the exponential `DRec`
presentation used in the quantitative bounds. -/
theorem map_finiteEulerEndpointRec_DRec_withDensity
    (delta : ℝ) (hdelta : 0 ≤ delta) (xRef x : State d) (n : ℕ) :
    Measure.map (finiteEulerEndpointRec V delta x)
        ((Measure.pi (fun _ : Fin n => stdGaussian (State d))).withDensity
          (fun z => ENNReal.ofReal
            (finiteGaussianDRec V 1 delta xRef x z))) =
      Measure.map (finiteFrozenEndpointRec V delta xRef x)
        (Measure.pi (fun _ : Fin n => stdGaussian (State d))) := by
  rw [show (fun z : Fin n → State d => ENNReal.ofReal
      (finiteGaussianDRec V 1 delta xRef x z)) =
      fun z => ENNReal.ofReal
        (finiteGaussianLikelihoodRec V 1 delta xRef x z) by
    funext z
    rw [finiteGaussianLikelihoodRec_eq_DRec V 1 delta hdelta xRef x z]]
  exact map_finiteEulerEndpointRec_likelihood_withDensity
    V delta hdelta xRef x n

/-- Integrating the initial state under any probability law preserves exact
normalization.  This is ordinary Tonelli applied after the fixed-initial-state
identity; no conditional expectation is needed. -/
lemma lintegral_finiteGaussianLikelihoodRec_initial
    {mu : Measure (State d)} [IsProbabilityMeasure mu]
    (beta delta : ℝ) (n : ℕ) :
    (∫⁻ p, ENNReal.ofReal
        (finiteGaussianLikelihoodRec V beta delta p.1 p.1 p.2)
        ∂mu.prod (Measure.pi
          (fun _ : Fin n => stdGaussian (State d)))) = 1 := by
  have hf : Measurable
      (fun p : State d × (Fin n → State d) => ENNReal.ofReal
        (finiteGaussianLikelihoodRec V beta delta p.1 p.1 p.2)) :=
    ENNReal.measurable_ofReal.comp
      (measurable_finiteGaussianLikelihoodRec_initial V beta delta n)
  rw [lintegral_prod _ hf.aemeasurable]
  have hinner : ∀ x0 : State d,
      (∫⁻ z, ENNReal.ofReal
          (finiteGaussianLikelihoodRec V beta delta x0 x0 z)
          ∂Measure.pi (fun _ : Fin n => stdGaussian (State d))) = 1 :=
    fun x0 => lintegral_finiteGaussianLikelihoodRec
      V beta delta x0 n x0
  simp_rw [hinner]
  simp

/-- Real-integral form of the exact finite Gaussian product identity. -/
lemma integral_finiteGaussianLikelihoodRec
    (beta delta : ℝ) (xRef : State d) (n : ℕ) (x : State d) :
    (∫ z, finiteGaussianLikelihoodRec V beta delta xRef x z
        ∂Measure.pi (fun _ : Fin n => stdGaussian (State d))) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun z =>
      (finiteGaussianLikelihoodRec_pos V beta delta xRef x z).le)
    (measurable_finiteGaussianLikelihoodRec V beta delta xRef x).aestronglyMeasurable]
  rw [lintegral_finiteGaussianLikelihoodRec V beta delta xRef n x]
  simp

lemma integral_finiteGaussianLikelihoodRec_initial
    {mu : Measure (State d)} [IsProbabilityMeasure mu]
    (beta delta : ℝ) (n : ℕ) :
    (∫ p, finiteGaussianLikelihoodRec V beta delta p.1 p.1 p.2
        ∂mu.prod (Measure.pi
          (fun _ : Fin n => stdGaussian (State d)))) = 1 := by
  calc
    (∫ p, finiteGaussianLikelihoodRec V beta delta p.1 p.1 p.2
        ∂mu.prod (Measure.pi
          (fun _ : Fin n => stdGaussian (State d)))) =
        (∫⁻ p, ENNReal.ofReal
          (finiteGaussianLikelihoodRec V beta delta p.1 p.1 p.2)
          ∂mu.prod (Measure.pi
            (fun _ : Fin n => stdGaussian (State d)))).toReal :=
      integral_eq_lintegral_of_nonneg_ae
        (ae_of_all _ fun p =>
          (finiteGaussianLikelihoodRec_pos V beta delta p.1 p.1 p.2).le)
        (measurable_finiteGaussianLikelihoodRec_initial
          V beta delta n).aestronglyMeasurable
    _ = 1 := by
      rw [lintegral_finiteGaussianLikelihoodRec_initial V beta delta n]
      simp

/-- Normalized finite Gaussian product in the paper's displayed
`exp(beta M - beta^2 V/2)` form. -/
lemma integral_finiteGaussianDRec
    (beta delta : ℝ) (hdelta : 0 ≤ delta)
    (xRef : State d) (n : ℕ) (x : State d) :
    (∫ z, finiteGaussianDRec V beta delta xRef x z
        ∂Measure.pi (fun _ : Fin n => stdGaussian (State d))) = 1 := by
  calc
    (∫ z, finiteGaussianDRec V beta delta xRef x z
        ∂Measure.pi (fun _ : Fin n => stdGaussian (State d))) =
        ∫ z, finiteGaussianLikelihoodRec V beta delta xRef x z
          ∂Measure.pi (fun _ : Fin n => stdGaussian (State d)) := by
      apply integral_congr_ae
      exact ae_of_all _ fun z =>
        (finiteGaussianLikelihoodRec_eq_DRec V beta delta hdelta xRef x z).symm
    _ = 1 := integral_finiteGaussianLikelihoodRec V beta delta xRef n x

/-- Fully unconditioned finite product identity: the initial point may have
any probability distribution, in particular the target `V.target`. -/
lemma integral_finiteGaussianDRec_initial
    {mu : Measure (State d)} [IsProbabilityMeasure mu]
    (beta delta : ℝ) (hdelta : 0 ≤ delta) (n : ℕ) :
    (∫ p, finiteGaussianDRec V beta delta p.1 p.1 p.2
        ∂mu.prod (Measure.pi
          (fun _ : Fin n => stdGaussian (State d)))) = 1 := by
  calc
    (∫ p, finiteGaussianDRec V beta delta p.1 p.1 p.2
        ∂mu.prod (Measure.pi
          (fun _ : Fin n => stdGaussian (State d)))) =
        ∫ p, finiteGaussianLikelihoodRec V beta delta p.1 p.1 p.2
          ∂mu.prod (Measure.pi
            (fun _ : Fin n => stdGaussian (State d))) := by
      apply integral_congr_ae
      exact ae_of_all _ fun p =>
        (finiteGaussianLikelihoodRec_eq_DRec
          V beta delta hdelta p.1 p.1 p.2).symm
    _ = 1 := integral_finiteGaussianLikelihoodRec_initial
      V beta delta n

lemma measurable_finiteGaussianDRec_initial
    (beta delta : ℝ) (hdelta : 0 ≤ delta) (n : ℕ) :
    Measurable (fun p : State d × (Fin n → State d) =>
      finiteGaussianDRec V beta delta p.1 p.1 p.2) := by
  have hfun : (fun p : State d × (Fin n → State d) =>
      finiteGaussianDRec V beta delta p.1 p.1 p.2) =
      fun p => finiteGaussianLikelihoodRec V beta delta p.1 p.1 p.2 := by
    funext p
    exact (finiteGaussianLikelihoodRec_eq_DRec
      V beta delta hdelta p.1 p.1 p.2).symm
  rw [hfun]
  exact measurable_finiteGaussianLikelihoodRec_initial V beta delta n

lemma measurable_finiteGaussianDRec
    (beta delta : ℝ) (hdelta : 0 ≤ delta)
    (xRef : State d) (n : ℕ) (x : State d) :
    Measurable (finiteGaussianDRec V beta delta xRef x :
      (Fin n → State d) → ℝ) := by
  have hfun : (finiteGaussianDRec V beta delta xRef x :
      (Fin n → State d) → ℝ) =
      finiteGaussianLikelihoodRec V beta delta xRef x := by
    funext z
    exact (finiteGaussianLikelihoodRec_eq_DRec
      V beta delta hdelta xRef x z).symm
  rw [hfun]
  exact measurable_finiteGaussianLikelihoodRec V beta delta xRef x

/-- The normalized finite product is integrable; this is derived from its
nonnegative lower integral, rather than proved by a separate recursive
domination argument. -/
lemma integrable_finiteGaussianLikelihoodRec
    (beta delta : ℝ) (xRef : State d) (n : ℕ) (x : State d) :
    Integrable (finiteGaussianLikelihoodRec V beta delta xRef x)
      (Measure.pi (fun _ : Fin n => stdGaussian (State d))) := by
  constructor
  · exact (measurable_finiteGaussianLikelihoodRec V beta delta xRef x).aestronglyMeasurable
  · rw [hasFiniteIntegral_iff_ofReal
      (ae_of_all _ fun z =>
        (finiteGaussianLikelihoodRec_pos V beta delta xRef x z).le)]
    rw [lintegral_finiteGaussianLikelihoodRec V beta delta xRef n x]
    exact ENNReal.one_lt_top

lemma integrable_finiteGaussianLikelihoodRec_initial
    {mu : Measure (State d)} [IsProbabilityMeasure mu]
    (beta delta : ℝ) (n : ℕ) :
    Integrable (fun p : State d × (Fin n → State d) =>
        finiteGaussianLikelihoodRec V beta delta p.1 p.1 p.2)
      (mu.prod (Measure.pi
        (fun _ : Fin n => stdGaussian (State d)))) := by
  constructor
  · exact (measurable_finiteGaussianLikelihoodRec_initial
      V beta delta n).aestronglyMeasurable
  · apply (hasFiniteIntegral_iff_ofReal
      (ae_of_all _ fun p : State d × (Fin n → State d) =>
        (finiteGaussianLikelihoodRec_pos V beta delta p.1 p.1 p.2).le)).2
    rw [lintegral_finiteGaussianLikelihoodRec_initial V beta delta n]
    exact ENNReal.one_lt_top

lemma integrable_finiteGaussianDRec
    (beta delta : ℝ) (hdelta : 0 ≤ delta)
    (xRef : State d) (n : ℕ) (x : State d) :
    Integrable (finiteGaussianDRec V beta delta xRef x)
      (Measure.pi (fun _ : Fin n => stdGaussian (State d))) := by
  have hfun : (finiteGaussianDRec V beta delta xRef x :
      (Fin n → State d) → ℝ) =
      finiteGaussianLikelihoodRec V beta delta xRef x := by
    funext z
    exact (finiteGaussianLikelihoodRec_eq_DRec
      V beta delta hdelta xRef x z).symm
  rw [hfun]
  exact integrable_finiteGaussianLikelihoodRec V beta delta xRef n x

lemma integrable_finiteGaussianDRec_initial
    {mu : Measure (State d)} [IsProbabilityMeasure mu]
    (beta delta : ℝ) (hdelta : 0 ≤ delta) (n : ℕ) :
    Integrable (fun p : State d × (Fin n → State d) =>
        finiteGaussianDRec V beta delta p.1 p.1 p.2)
      (mu.prod (Measure.pi
        (fun _ : Fin n => stdGaussian (State d)))) := by
  have hfun : (fun p : State d × (Fin n → State d) =>
      finiteGaussianDRec V beta delta p.1 p.1 p.2) =
      fun p => finiteGaussianLikelihoodRec V beta delta p.1 p.1 p.2 := by
    funext p
    exact (finiteGaussianLikelihoodRec_eq_DRec
      V beta delta hdelta p.1 p.1 p.2).symm
  rw [hfun]
  exact integrable_finiteGaussianLikelihoodRec_initial V beta delta n

/-- Second-moment likelihood estimate under a single abstract exponential
energy hypothesis.  This is the finite-dimensional Young-inequality
replacement for stochastic-exponential Hölder arguments.

The only analytic input is the displayed integrability and bound for
`exp(3 L^2 J)`. -/
lemma finiteGaussianDRec_sq_integrable_and_integral_le_of_energy_exp
    {mu : Measure (State d)} [IsProbabilityMeasure mu]
    (delta : ℝ) (hdelta : 0 ≤ delta) (n : ℕ) (B : ℝ)
    (hEnergyInt : Integrable
      (fun p : State d × (Fin n → State d) =>
        Real.exp (3 * V.L ^ 2 *
          finiteEulerEnergyRec V delta p.1 p.1 p.2))
      (mu.prod (Measure.pi
        (fun _ : Fin n => stdGaussian (State d)))))
    (hEnergyBound :
      (∫ p : State d × (Fin n → State d),
        Real.exp (3 * V.L ^ 2 *
          finiteEulerEnergyRec V delta p.1 p.1 p.2)
        ∂mu.prod (Measure.pi
          (fun _ : Fin n => stdGaussian (State d)))) ≤ B) :
    Integrable
        (fun p : State d × (Fin n → State d) =>
          finiteGaussianDRec V 1 delta p.1 p.1 p.2 ^ 2)
        (mu.prod (Measure.pi
          (fun _ : Fin n => stdGaussian (State d)))) ∧
      (∫ p : State d × (Fin n → State d),
        finiteGaussianDRec V 1 delta p.1 p.1 p.2 ^ 2
        ∂mu.prod (Measure.pi
          (fun _ : Fin n => stdGaussian (State d)))) ≤ (1 + B) / 2 := by
  let P : Measure (State d × (Fin n → State d)) :=
    mu.prod (Measure.pi (fun _ : Fin n => stdGaussian (State d)))
  let dOne : State d × (Fin n → State d) → ℝ := fun p =>
    finiteGaussianDRec V 1 delta p.1 p.1 p.2
  let dFour : State d × (Fin n → State d) → ℝ := fun p =>
    finiteGaussianDRec V 4 delta p.1 p.1 p.2
  let expV : State d × (Fin n → State d) → ℝ := fun p =>
    Real.exp (6 * finiteGaussianVRec V delta p.1 p.1 p.2)
  let expJ : State d × (Fin n → State d) → ℝ := fun p =>
    Real.exp (3 * V.L ^ 2 * finiteEulerEnergyRec V delta p.1 p.1 p.2)
  have hExpVMeas : Measurable expV := by
    exact Real.continuous_exp.measurable.comp
      (measurable_const.mul
        (measurable_finiteGaussianVRec_initial V delta n))
  have hExpVLe : ∀ p, expV p ≤ expJ p := by
    intro p
    apply Real.exp_le_exp.mpr
    have hv := finiteGaussianVRec_le_energyRec V delta hdelta
      p.1 p.1 p.2
    nlinarith
  have hExpVInt : Integrable expV P := by
    apply hEnergyInt.mono hExpVMeas.aestronglyMeasurable
    exact ae_of_all _ fun p => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hExpVLe p
  have hExpVBound : (∫ p, expV p ∂P) ≤ B := by
    exact (integral_mono hExpVInt hEnergyInt hExpVLe).trans hEnergyBound
  have hD4Int : Integrable dFour P := by
    exact integrable_finiteGaussianDRec_initial V 4 delta hdelta n
  have hRhsInt : Integrable (fun p => (dFour p + expV p) / 2) P :=
    (hD4Int.add hExpVInt).div_const 2
  have hD1SqMeas : Measurable (fun p => dOne p ^ 2) := by
    exact (measurable_finiteGaussianDRec_initial V 1 delta hdelta n).pow_const 2
  have hPoint : ∀ p, dOne p ^ 2 ≤ (dFour p + expV p) / 2 := by
    intro p
    exact finiteGaussianDRec_sq_le V delta p.1 p.1 p.2
  have hD1SqInt : Integrable (fun p => dOne p ^ 2) P := by
    apply integrable_of_le_of_le hD1SqMeas.aestronglyMeasurable
      (ae_of_all _ fun p => sq_nonneg (dOne p))
      (ae_of_all _ hPoint)
      (integrable_zero _ ℝ P) hRhsInt
  constructor
  · exact hD1SqInt
  · calc
      (∫ p, dOne p ^ 2 ∂P) ≤ ∫ p, (dFour p + expV p) / 2 ∂P :=
        integral_mono hD1SqInt hRhsInt hPoint
      _ = ((∫ p, dFour p ∂P) + ∫ p, expV p ∂P) / 2 := by
        rw [integral_div, integral_add hD4Int hExpVInt]
      _ ≤ (1 + B) / 2 := by
        have hD4Mean : (∫ p, dFour p ∂P) = 1 := by
          exact integral_finiteGaussianDRec_initial V 4 delta hdelta n
        rw [hD4Mean]
        linarith

/-- Centered second-moment consequence of the same energy hypothesis.  The
subtraction of `1` uses only the already-proved exact mean-one identity. -/
lemma finiteGaussianDRec_centered_sq_integrable_and_integral_le_of_energy_exp
    {mu : Measure (State d)} [IsProbabilityMeasure mu]
    (delta : ℝ) (hdelta : 0 ≤ delta) (n : ℕ) (B : ℝ)
    (hEnergyInt : Integrable
      (fun p : State d × (Fin n → State d) =>
        Real.exp (3 * V.L ^ 2 *
          finiteEulerEnergyRec V delta p.1 p.1 p.2))
      (mu.prod (Measure.pi
        (fun _ : Fin n => stdGaussian (State d)))))
    (hEnergyBound :
      (∫ p : State d × (Fin n → State d),
        Real.exp (3 * V.L ^ 2 *
          finiteEulerEnergyRec V delta p.1 p.1 p.2)
        ∂mu.prod (Measure.pi
          (fun _ : Fin n => stdGaussian (State d)))) ≤ B) :
    Integrable
        (fun p : State d × (Fin n → State d) =>
          (finiteGaussianDRec V 1 delta p.1 p.1 p.2 - 1) ^ 2)
        (mu.prod (Measure.pi
          (fun _ : Fin n => stdGaussian (State d)))) ∧
      (∫ p : State d × (Fin n → State d),
        (finiteGaussianDRec V 1 delta p.1 p.1 p.2 - 1) ^ 2
        ∂mu.prod (Measure.pi
          (fun _ : Fin n => stdGaussian (State d)))) ≤ (B - 1) / 2 := by
  let P : Measure (State d × (Fin n → State d)) :=
    mu.prod (Measure.pi (fun _ : Fin n => stdGaussian (State d)))
  let D : State d × (Fin n → State d) → ℝ := fun p =>
    finiteGaussianDRec V 1 delta p.1 p.1 p.2
  obtain ⟨hDsqInt, hDsqBound⟩ :=
    finiteGaussianDRec_sq_integrable_and_integral_le_of_energy_exp
      V delta hdelta n B hEnergyInt hEnergyBound
  have hDsqIntP : Integrable (fun p => D p ^ 2) P := by
    simpa [D, P] using hDsqInt
  have hDsqBoundP : (∫ p, D p ^ 2 ∂P) ≤ (1 + B) / 2 := by
    simpa [D, P] using hDsqBound
  have hDInt : Integrable D P :=
    integrable_finiteGaussianDRec_initial V 1 delta hdelta n
  have hTwoDInt : Integrable (fun p => 2 * D p) P := hDInt.const_mul 2
  have hCenteredEq : (fun p => (D p - 1) ^ 2) =
      fun p => D p ^ 2 - 2 * D p + 1 := by
    funext p
    ring
  have hCenteredInt : Integrable (fun p => (D p - 1) ^ 2) P := by
    rw [hCenteredEq]
    exact (hDsqIntP.sub hTwoDInt).add (integrable_const 1)
  constructor
  · exact hCenteredInt
  · have hDMean : (∫ p, D p ∂P) = 1 :=
      integral_finiteGaussianDRec_initial V 1 delta hdelta n
    calc
      (∫ p, (D p - 1) ^ 2 ∂P) =
          (∫ p, D p ^ 2 ∂P) - 2 * (∫ p, D p ∂P) + 1 := by
        rw [hCenteredEq]
        calc
          (∫ p, D p ^ 2 - 2 * D p + 1 ∂P) =
              (∫ p, D p ^ 2 - 2 * D p ∂P) + ∫ _p, (1 : ℝ) ∂P := by
            simpa only [Pi.add_apply, Pi.sub_apply] using
              integral_add (hDsqIntP.sub hTwoDInt) (integrable_const 1)
          _ = ((∫ p, D p ^ 2 ∂P) - ∫ p, 2 * D p ∂P) +
              ∫ _p, (1 : ℝ) ∂P := by
            rw [integral_sub hDsqIntP hTwoDInt]
          _ = (∫ p, D p ^ 2 ∂P) - 2 * (∫ p, D p ∂P) + 1 := by
            rw [integral_const_mul]
            simp [P]
      _ = (∫ p, D p ^ 2 ∂P) - 1 := by rw [hDMean]; ring
      _ ≤ (1 + B) / 2 - 1 := sub_le_sub_right hDsqBoundP 1
      _ = (B - 1) / 2 := by ring

/-- Scalar truncation/Young inequality used to turn a centered second moment
into an `L¹` (hence total-variation) estimate. -/
lemma abs_le_eta_add_sq_div (x eta : ℝ) (heta : 0 < eta) :
    |x| ≤ eta + x ^ 2 / (4 * eta) := by
  have hden : 0 < 4 * eta := mul_pos (by norm_num) heta
  have habssq : |x| ^ 2 = x ^ 2 := sq_abs x
  rw [show eta + x ^ 2 / (4 * eta) =
      (4 * eta ^ 2 + x ^ 2) / (4 * eta) by
    field_simp]
  apply (le_div_iff₀ hden).2
  nlinarith [sq_nonneg (|x| - 2 * eta)]

/-- `L¹`/TV-proxy bound under the abstract finite Euler energy MGF.  The
free parameter `eta` avoids introducing a square-root optimization theorem;
choosing `eta` later gives the usual square-root estimate. -/
lemma finiteGaussianDRec_centered_abs_integrable_and_integral_le_of_energy_exp
    {mu : Measure (State d)} [IsProbabilityMeasure mu]
    (delta : ℝ) (hdelta : 0 ≤ delta) (n : ℕ) (B eta : ℝ)
    (heta : 0 < eta)
    (hEnergyInt : Integrable
      (fun p : State d × (Fin n → State d) =>
        Real.exp (3 * V.L ^ 2 *
          finiteEulerEnergyRec V delta p.1 p.1 p.2))
      (mu.prod (Measure.pi
        (fun _ : Fin n => stdGaussian (State d)))))
    (hEnergyBound :
      (∫ p : State d × (Fin n → State d),
        Real.exp (3 * V.L ^ 2 *
          finiteEulerEnergyRec V delta p.1 p.1 p.2)
        ∂mu.prod (Measure.pi
          (fun _ : Fin n => stdGaussian (State d)))) ≤ B) :
    Integrable
        (fun p : State d × (Fin n → State d) =>
          |finiteGaussianDRec V 1 delta p.1 p.1 p.2 - 1|)
        (mu.prod (Measure.pi
          (fun _ : Fin n => stdGaussian (State d)))) ∧
      (∫ p : State d × (Fin n → State d),
        |finiteGaussianDRec V 1 delta p.1 p.1 p.2 - 1|
        ∂mu.prod (Measure.pi
          (fun _ : Fin n => stdGaussian (State d)))) ≤
        eta + (B - 1) / (8 * eta) := by
  let P : Measure (State d × (Fin n → State d)) :=
    mu.prod (Measure.pi (fun _ : Fin n => stdGaussian (State d)))
  let D : State d × (Fin n → State d) → ℝ := fun p =>
    finiteGaussianDRec V 1 delta p.1 p.1 p.2
  obtain ⟨hCenteredSqInt, hCenteredSqBound⟩ :=
    finiteGaussianDRec_centered_sq_integrable_and_integral_le_of_energy_exp
      V delta hdelta n B hEnergyInt hEnergyBound
  have hCenteredSqIntP : Integrable (fun p => (D p - 1) ^ 2) P := by
    simpa [D, P] using hCenteredSqInt
  have hCenteredSqBoundP : (∫ p, (D p - 1) ^ 2 ∂P) ≤ (B - 1) / 2 := by
    simpa [D, P] using hCenteredSqBound
  have hAbsMeas : Measurable (fun p => |D p - 1|) :=
    ((measurable_finiteGaussianDRec_initial V 1 delta hdelta n).sub
      measurable_const).abs
  have hRhsInt : Integrable
      (fun p => eta + (D p - 1) ^ 2 / (4 * eta)) P :=
    (integrable_const eta).add (hCenteredSqIntP.div_const (4 * eta))
  have hPoint : ∀ p, |D p - 1| ≤
      eta + (D p - 1) ^ 2 / (4 * eta) :=
    fun p => abs_le_eta_add_sq_div (D p - 1) eta heta
  have hAbsInt : Integrable (fun p => |D p - 1|) P := by
    apply integrable_of_le_of_le hAbsMeas.aestronglyMeasurable
      (ae_of_all _ fun p => abs_nonneg (D p - 1))
      (ae_of_all _ hPoint)
      (integrable_zero _ ℝ P) hRhsInt
  constructor
  · exact hAbsInt
  · have hden0 : 0 ≤ 4 * eta := (mul_pos (by norm_num) heta).le
    calc
      (∫ p, |D p - 1| ∂P) ≤
          ∫ p, eta + (D p - 1) ^ 2 / (4 * eta) ∂P :=
        integral_mono hAbsInt hRhsInt hPoint
      _ = eta + (∫ p, (D p - 1) ^ 2 ∂P) / (4 * eta) := by
        rw [integral_add (integrable_const eta)
          (hCenteredSqIntP.div_const (4 * eta)), integral_div]
        simp [P]
      _ ≤ eta + ((B - 1) / 2) / (4 * eta) := by
        gcongr
      _ = eta + (B - 1) / (8 * eta) := by
        field_simp
        ring

/-- Elementary Markov tail bound for the finite likelihood.  The proof is
written directly with restricted integrals, avoiding a conditional
expectation or a specialized probability-tail API. -/
lemma finiteGaussianDRec_centered_tail_le_of_energy_exp
    {mu : Measure (State d)} [IsProbabilityMeasure mu]
    (delta : ℝ) (hdelta : 0 ≤ delta) (n : ℕ) (B t : ℝ)
    (ht : 0 < t)
    (hEnergyInt : Integrable
      (fun p : State d × (Fin n → State d) =>
        Real.exp (3 * V.L ^ 2 *
          finiteEulerEnergyRec V delta p.1 p.1 p.2))
      (mu.prod (Measure.pi
        (fun _ : Fin n => stdGaussian (State d)))))
    (hEnergyBound :
      (∫ p : State d × (Fin n → State d),
        Real.exp (3 * V.L ^ 2 *
          finiteEulerEnergyRec V delta p.1 p.1 p.2)
        ∂mu.prod (Measure.pi
          (fun _ : Fin n => stdGaussian (State d)))) ≤ B) :
    (mu.prod (Measure.pi
      (fun _ : Fin n => stdGaussian (State d)))).real
        {p | t ≤ |finiteGaussianDRec V 1 delta p.1 p.1 p.2 - 1|} ≤
      ((B - 1) / 2) / t ^ 2 := by
  let P : Measure (State d × (Fin n → State d)) :=
    mu.prod (Measure.pi (fun _ : Fin n => stdGaussian (State d)))
  let D : State d × (Fin n → State d) → ℝ := fun p =>
    finiteGaussianDRec V 1 delta p.1 p.1 p.2
  let S : Set (State d × (Fin n → State d)) := {p | t ≤ |D p - 1|}
  obtain ⟨hCenteredSqInt, hCenteredSqBound⟩ :=
    finiteGaussianDRec_centered_sq_integrable_and_integral_le_of_energy_exp
      V delta hdelta n B hEnergyInt hEnergyBound
  have hCenteredSqIntP : Integrable (fun p => (D p - 1) ^ 2) P := by
    simpa [D, P] using hCenteredSqInt
  have hCenteredSqBoundP : (∫ p, (D p - 1) ^ 2 ∂P) ≤ (B - 1) / 2 := by
    simpa [D, P] using hCenteredSqBound
  have hAbsMeas : Measurable (fun p => |D p - 1|) :=
    ((measurable_finiteGaussianDRec_initial V 1 delta hdelta n).sub
      measurable_const).abs
  have hS : MeasurableSet S := by
    exact measurableSet_le measurable_const hAbsMeas
  have hOnS : ∀ p ∈ S, t ^ 2 ≤ (D p - 1) ^ 2 := by
    intro p hp
    simpa only [sq_abs] using
      (sq_le_sq₀ ht.le (abs_nonneg (D p - 1))).2 hp
  have hMarkov : t ^ 2 * P.real S ≤ ∫ p, (D p - 1) ^ 2 ∂P := by
    calc
      t ^ 2 * P.real S = ∫ _p in S, t ^ 2 ∂P := by
        simp [mul_comm]
      _ ≤ ∫ p in S, (D p - 1) ^ 2 ∂P := by
        apply integral_mono_ae (integrable_const _)
          (hCenteredSqIntP.mono_measure Measure.restrict_le_self)
        filter_upwards [ae_restrict_mem₀ hS.nullMeasurableSet] with p hp
        exact hOnS p hp
      _ ≤ ∫ p, (D p - 1) ^ 2 ∂P :=
        integral_mono_measure Measure.restrict_le_self
          (ae_of_all _ fun p => sq_nonneg (D p - 1)) hCenteredSqIntP
  change P.real S ≤ ((B - 1) / 2) / t ^ 2
  apply (le_div_iff₀ (sq_pos_of_pos ht)).2
  simpa only [mul_comm] using hMarkov.trans hCenteredSqBoundP

/-- The exact finite-product identity with the initial Euler state also used
as the frozen drift reference, matching the paper's construction. -/
lemma integral_finiteEulerGaussianProduct
    (beta delta : ℝ) (hdelta : 0 ≤ delta)
    (x0 : State d) (n : ℕ) :
    (∫ z, finiteGaussianDRec V beta delta x0 x0 z
        ∂Measure.pi (fun _ : Fin n => stdGaussian (State d))) = 1 :=
  integral_finiteGaussianDRec V beta delta hdelta x0 n x0

end RecursiveProduct

end DiscreteTime

end

end UniformRandomMALA
