import UniformRandomMALA.Concrete.FiniteEulerEnergyMGF

/-!
# Concrete likelihood bounds from the finite Euler energy estimate

This file composes the elementary finite-grid energy MGF with the finite
Gaussian likelihood estimates.  The only small-step assumption is a scalar
inequality; in particular, all exponential integrability obligations are
discharged here rather than retained as abstract hypotheses.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace DiscreteTime

open Concrete Finset

section ScalarSimplification

/-- On the unit interval, the exponential remainder is bounded by its
largest derivative.  The proof uses the elementary unit-ball remainder
estimate for `exp`, not a mean-value or convex-analysis API. -/
lemma exp_sub_one_le_exp_one_mul {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x - 1 ≤ Real.exp 1 * x := by
  have hxNorm : ‖x‖ ≤ 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hx0]
  have hrem := Real.norm_exp_sub_one_sub_id_le hxNorm
  have hupper : Real.exp x - 1 - x ≤ x ^ 2 := by
    calc
      Real.exp x - 1 - x ≤ |Real.exp x - 1 - x| := le_abs_self _
      _ = ‖Real.exp x - 1 - x‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖x‖ ^ 2 := hrem
      _ = x ^ 2 := by rw [Real.norm_eq_abs, abs_of_nonneg hx0]
  have htwoExp : (2 : ℝ) ≤ Real.exp 1 := by
    convert Real.add_one_le_exp (1 : ℝ) using 1 <;> norm_num
  calc
    Real.exp x - 1 ≤ x + x ^ 2 := by linarith
    _ ≤ 2 * x := by nlinarith
    _ ≤ Real.exp 1 * x := mul_le_mul_of_nonneg_right htwoExp hx0

end ScalarSimplification

section EnergyAtLikelihoodScale

variable {d n : ℕ} (V : FirstOrderPotential d)

/-- The single small-step condition at the likelihood exponent `3 L²`
implies the deterministic Euler stability condition `L h ≤ 1`. -/
lemma euler_stable_of_likelihood_small
    (h : ℝ) (hh : 0 ≤ h)
    (hsmall : 192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 ≤ 1) :
    V.L * h ≤ 1 := by
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have heSq : (1 : ℝ) ≤ (Real.exp 1) ^ 2 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) he 2
  have hLh0 : 0 ≤ V.L * h := mul_nonneg V.hL.le hh
  have hsq : (V.L * h) ^ 2 ≤ 1 := by
    calc
      (V.L * h) ^ 2 ≤
          192 * (Real.exp 1) ^ 2 * (V.L * h) ^ 2 := by
        have hc : (1 : ℝ) ≤ 192 * (Real.exp 1) ^ 2 := by nlinarith
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hc (sq_nonneg (V.L * h))
      _ = 192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 := by ring
      _ ≤ 1 := hsmall
  nlinarith

/-- A dimension-aware likelihood smallness condition implies the
dimension-free condition needed for the energy MGF whenever `d > 0`. -/
lemma likelihood_small_of_dimension_small
    (hd : 0 < d) (h : ℝ)
    (hsmallDim :
      192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 * d ≤ 1) :
    192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 ≤ 1 := by
  have hq0 : 0 ≤ 192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 := by
    positivity
  have hdOne : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  calc
    192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 =
        (192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2) * 1 := by ring
    _ ≤ (192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2) * d :=
      mul_le_mul_of_nonneg_left hdOne hq0
    _ ≤ 1 := hsmallDim

/-- Concrete exponential integrability and MGF bound at the exponent used
by the finite Gaussian likelihood comparison. -/
theorem finiteEuler_energy_exp_three_L_sq_integrable_and_integral_le
    (hn : 0 < n) (delta h : ℝ)
    (hdelta : 0 ≤ delta)
    (hhorizon : (n : ℝ) * delta = h)
    (hsmall : 192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 ≤ 1) :
    Integrable (fun p : State d × (Fin n → State d) =>
      Real.exp (3 * V.L ^ 2 * finiteEulerEnergy V delta p.1 p.2))
      ((V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) ∧
    (∫ p : State d × (Fin n → State d),
      Real.exp (3 * V.L ^ 2 * finiteEulerEnergy V delta p.1 p.2)
      ∂(V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) ≤
      Real.exp
        (192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 * d) := by
  have hh : 0 ≤ h := by
    rw [← hhorizon]
    positivity
  have hEuler := euler_stable_of_likelihood_small V h hh hsmall
  have hlambda : 0 ≤ 3 * V.L ^ 2 := by positivity
  have hmgfSmall :
      64 * (Real.exp 1) ^ 2 * (3 * V.L ^ 2) * h ^ 2 ≤ 1 := by
    convert hsmall using 1 <;> ring
  constructor
  · exact integrable_exp_finiteEulerEnergy V hn delta h (3 * V.L ^ 2)
      hdelta hlambda hhorizon hEuler hmgfSmall
  · convert integral_exp_finiteEulerEnergy_le_exp V hn delta h
      (3 * V.L ^ 2) hdelta hlambda hhorizon hEuler hmgfSmall using 1 <;> ring

/-- Transport the concrete energy package to the chronological energy used
by the likelihood recursion.  The equality argument is kept explicit in this
internal lemma so the probabilistic composition is independent of the path
indexing proof. -/
private theorem finiteEulerEnergyRec_exp_three_L_sq_package_of_eq
    (hn : 0 < n) (delta h : ℝ)
    (hdelta : 0 ≤ delta)
    (hhorizon : (n : ℝ) * delta = h)
    (hsmall : 192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 ≤ 1)
    (hEnergyEq : ∀ (x0 : State d) (z : Fin n → State d),
      finiteEulerEnergyRec V delta x0 x0 z =
        finiteEulerEnergy V delta x0 z) :
    Integrable (fun p : State d × (Fin n → State d) =>
      Real.exp (3 * V.L ^ 2 *
        finiteEulerEnergyRec V delta p.1 p.1 p.2))
      ((V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) ∧
    (∫ p : State d × (Fin n → State d),
      Real.exp (3 * V.L ^ 2 *
        finiteEulerEnergyRec V delta p.1 p.1 p.2)
      ∂(V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) ≤
      Real.exp
        (192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 * d) := by
  obtain ⟨hInt, hBound⟩ :=
    finiteEuler_energy_exp_three_L_sq_integrable_and_integral_le
      V hn delta h hdelta hhorizon hsmall
  have hfun : (fun p : State d × (Fin n → State d) =>
      Real.exp (3 * V.L ^ 2 *
        finiteEulerEnergyRec V delta p.1 p.1 p.2)) =
      fun p => Real.exp (3 * V.L ^ 2 *
        finiteEulerEnergy V delta p.1 p.2) := by
    funext p
    rw [hEnergyEq p.1 p.2]
  rw [hfun]
  exact ⟨hInt, hBound⟩

end EnergyAtLikelihoodScale

section CompositionWithEnergyEquality

variable {d n : ℕ} (V : FirstOrderPotential d)

/-- Centered `L²` likelihood estimate, separated from the path-indexing
equality. -/
private theorem finiteEulerLikelihood_centered_sq_package_of_energy_eq
    (hn : 0 < n) (delta h : ℝ)
    (hdelta : 0 ≤ delta)
    (hhorizon : (n : ℝ) * delta = h)
    (hsmall : 192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 ≤ 1)
    (hEnergyEq : ∀ (x0 : State d) (z : Fin n → State d),
      finiteEulerEnergyRec V delta x0 x0 z =
        finiteEulerEnergy V delta x0 z) :
    Integrable (fun p : State d × (Fin n → State d) =>
      (finiteGaussianDRec V 1 delta p.1 p.1 p.2 - 1) ^ 2)
      ((V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) ∧
    (∫ p : State d × (Fin n → State d),
      (finiteGaussianDRec V 1 delta p.1 p.1 p.2 - 1) ^ 2
      ∂(V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) ≤
      (Real.exp
        (192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 * d) - 1) / 2 := by
  obtain ⟨hEnergyInt, hEnergyBound⟩ :=
    finiteEulerEnergyRec_exp_three_L_sq_package_of_eq V hn delta h hdelta
      hhorizon hsmall hEnergyEq
  exact
    finiteGaussianDRec_centered_sq_integrable_and_integral_le_of_energy_exp
      V delta hdelta n
        (Real.exp (192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 * d))
        hEnergyInt hEnergyBound

/-- Centered `L¹` likelihood estimate, separated from the path-indexing
equality. -/
private theorem finiteEulerLikelihood_centered_abs_package_of_energy_eq
    (hn : 0 < n) (delta h eta : ℝ)
    (hdelta : 0 ≤ delta) (heta : 0 < eta)
    (hhorizon : (n : ℝ) * delta = h)
    (hsmall : 192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 ≤ 1)
    (hEnergyEq : ∀ (x0 : State d) (z : Fin n → State d),
      finiteEulerEnergyRec V delta x0 x0 z =
        finiteEulerEnergy V delta x0 z) :
    Integrable (fun p : State d × (Fin n → State d) =>
      |finiteGaussianDRec V 1 delta p.1 p.1 p.2 - 1|)
      ((V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) ∧
    (∫ p : State d × (Fin n → State d),
      |finiteGaussianDRec V 1 delta p.1 p.1 p.2 - 1|
      ∂(V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) ≤
      eta +
        (Real.exp
          (192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 * d) - 1) /
            (8 * eta) := by
  obtain ⟨hEnergyInt, hEnergyBound⟩ :=
    finiteEulerEnergyRec_exp_three_L_sq_package_of_eq V hn delta h hdelta
      hhorizon hsmall hEnergyEq
  exact
    finiteGaussianDRec_centered_abs_integrable_and_integral_le_of_energy_exp
      V delta hdelta n
        (Real.exp (192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 * d)) eta
        heta hEnergyInt hEnergyBound

/-- Centered likelihood tail estimate, separated from the path-indexing
equality. -/
private theorem finiteEulerLikelihood_centered_tail_of_energy_eq
    (hn : 0 < n) (delta h t : ℝ)
    (hdelta : 0 ≤ delta) (ht : 0 < t)
    (hhorizon : (n : ℝ) * delta = h)
    (hsmall : 192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 ≤ 1)
    (hEnergyEq : ∀ (x0 : State d) (z : Fin n → State d),
      finiteEulerEnergyRec V delta x0 x0 z =
        finiteEulerEnergy V delta x0 z) :
    ((V.target : Measure (State d)).prod
      (Measure.pi (fun _ : Fin n => stdGaussian (State d)))).real
        {p | t ≤ |finiteGaussianDRec V 1 delta p.1 p.1 p.2 - 1|} ≤
      ((Real.exp
        (192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 * d) - 1) / 2) /
          t ^ 2 := by
  obtain ⟨hEnergyInt, hEnergyBound⟩ :=
    finiteEulerEnergyRec_exp_three_L_sq_package_of_eq V hn delta h hdelta
      hhorizon hsmall hEnergyEq
  exact finiteGaussianDRec_centered_tail_le_of_energy_exp
    V delta hdelta n
      (Real.exp (192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 * d)) t ht
      hEnergyInt hEnergyBound

/-- Concrete centered `L²` estimate for the finite Euler Gaussian
likelihood.  All energy-integrability hypotheses have been discharged by the
single scalar small-step condition. -/
theorem finiteEulerLikelihood_centered_sq_integrable_and_integral_le
    (hn : 0 < n) (delta h : ℝ)
    (hdelta : 0 ≤ delta)
    (hhorizon : (n : ℝ) * delta = h)
    (hsmall : 192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 ≤ 1) :
    Integrable (fun p : State d × (Fin n → State d) =>
      (finiteGaussianDRec V 1 delta p.1 p.1 p.2 - 1) ^ 2)
      ((V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) ∧
    (∫ p : State d × (Fin n → State d),
      (finiteGaussianDRec V 1 delta p.1 p.1 p.2 - 1) ^ 2
      ∂(V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) ≤
      (Real.exp
        (192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 * d) - 1) / 2 := by
  exact finiteEulerLikelihood_centered_sq_package_of_energy_eq V hn delta h
    hdelta hhorizon hsmall fun x0 z =>
      finiteEulerEnergyRec_initial_eq_finiteEulerEnergy V delta x0 z

/-- Concrete centered `L¹` estimate for the finite Euler Gaussian
likelihood.  The positive parameter `eta` is the elementary Young-inequality
tradeoff and can be optimized downstream for the desired TV scale. -/
theorem finiteEulerLikelihood_centered_abs_integrable_and_integral_le
    (hn : 0 < n) (delta h eta : ℝ)
    (hdelta : 0 ≤ delta) (heta : 0 < eta)
    (hhorizon : (n : ℝ) * delta = h)
    (hsmall : 192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 ≤ 1) :
    Integrable (fun p : State d × (Fin n → State d) =>
      |finiteGaussianDRec V 1 delta p.1 p.1 p.2 - 1|)
      ((V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) ∧
    (∫ p : State d × (Fin n → State d),
      |finiteGaussianDRec V 1 delta p.1 p.1 p.2 - 1|
      ∂(V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) ≤
      eta +
        (Real.exp
          (192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 * d) - 1) /
            (8 * eta) := by
  exact finiteEulerLikelihood_centered_abs_package_of_energy_eq V hn delta h eta
    hdelta heta hhorizon hsmall fun x0 z =>
      finiteEulerEnergyRec_initial_eq_finiteEulerEnergy V delta x0 z

/-- Concrete Markov tail estimate for the centered finite Euler Gaussian
likelihood. -/
theorem finiteEulerLikelihood_centered_tail_le
    (hn : 0 < n) (delta h t : ℝ)
    (hdelta : 0 ≤ delta) (ht : 0 < t)
    (hhorizon : (n : ℝ) * delta = h)
    (hsmall : 192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 ≤ 1) :
    ((V.target : Measure (State d)).prod
      (Measure.pi (fun _ : Fin n => stdGaussian (State d)))).real
        {p | t ≤ |finiteGaussianDRec V 1 delta p.1 p.1 p.2 - 1|} ≤
      ((Real.exp
        (192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 * d) - 1) / 2) /
          t ^ 2 := by
  exact finiteEulerLikelihood_centered_tail_of_energy_eq V hn delta h t
    hdelta ht hhorizon hsmall fun x0 z =>
      finiteEulerEnergyRec_initial_eq_finiteEulerEnergy V delta x0 z

/-- Paper-readable linearized centered `L²` estimate.  The strengthened
dimension-aware scalar condition is precisely what permits replacing
`exp(x) - 1` by a constant times `x`. -/
theorem finiteEulerLikelihood_centered_sq_integrable_and_integral_le_linear
    (hd : 0 < d) (hn : 0 < n) (delta h : ℝ)
    (hdelta : 0 ≤ delta)
    (hhorizon : (n : ℝ) * delta = h)
    (hsmallDim :
      192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 * d ≤ 1) :
    Integrable (fun p : State d × (Fin n → State d) =>
      (finiteGaussianDRec V 1 delta p.1 p.1 p.2 - 1) ^ 2)
      ((V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) ∧
    (∫ p : State d × (Fin n → State d),
      (finiteGaussianDRec V 1 delta p.1 p.1 p.2 - 1) ^ 2
      ∂(V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) ≤
      96 * (Real.exp 1) ^ 3 * V.L ^ 2 * h ^ 2 * d := by
  let x : ℝ := 192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 * d
  have hsmall := likelihood_small_of_dimension_small V hd h hsmallDim
  obtain ⟨hInt, hBound⟩ :=
    finiteEulerLikelihood_centered_sq_integrable_and_integral_le
      V hn delta h hdelta hhorizon hsmall
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hx1 : x ≤ 1 := by simpa only [x] using hsmallDim
  have hExp := exp_sub_one_le_exp_one_mul hx0 hx1
  constructor
  · exact hInt
  · calc
      (∫ p : State d × (Fin n → State d),
        (finiteGaussianDRec V 1 delta p.1 p.1 p.2 - 1) ^ 2
        ∂(V.target : Measure (State d)).prod
          (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) ≤
          (Real.exp x - 1) / 2 := by simpa only [x] using hBound
      _ ≤ (Real.exp 1 * x) / 2 :=
        div_le_div_of_nonneg_right hExp (by norm_num)
      _ = 96 * (Real.exp 1) ^ 3 * V.L ^ 2 * h ^ 2 * d := by
        dsimp [x]
        ring

/-- Linearized version of the centered likelihood tail bound. -/
theorem finiteEulerLikelihood_centered_tail_le_linear
    (hd : 0 < d) (hn : 0 < n) (delta h t : ℝ)
    (hdelta : 0 ≤ delta) (ht : 0 < t)
    (hhorizon : (n : ℝ) * delta = h)
    (hsmallDim :
      192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 * d ≤ 1) :
    ((V.target : Measure (State d)).prod
      (Measure.pi (fun _ : Fin n => stdGaussian (State d)))).real
        {p | t ≤ |finiteGaussianDRec V 1 delta p.1 p.1 p.2 - 1|} ≤
      (96 * (Real.exp 1) ^ 3 * V.L ^ 2 * h ^ 2 * d) / t ^ 2 := by
  let x : ℝ := 192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 * d
  have hsmall := likelihood_small_of_dimension_small V hd h hsmallDim
  have hTail := finiteEulerLikelihood_centered_tail_le
    V hn delta h t hdelta ht hhorizon hsmall
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hx1 : x ≤ 1 := by simpa only [x] using hsmallDim
  have hExp := exp_sub_one_le_exp_one_mul hx0 hx1
  calc
    ((V.target : Measure (State d)).prod
      (Measure.pi (fun _ : Fin n => stdGaussian (State d)))).real
        {p | t ≤ |finiteGaussianDRec V 1 delta p.1 p.1 p.2 - 1|} ≤
        ((Real.exp x - 1) / 2) / t ^ 2 := by simpa only [x] using hTail
    _ ≤ ((Real.exp 1 * x) / 2) / t ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg t)
      exact div_le_div_of_nonneg_right hExp (by norm_num)
    _ = (96 * (Real.exp 1) ^ 3 * V.L ^ 2 * h ^ 2 * d) /
        t ^ 2 := by
      dsimp [x]
      ring

/-- Paper-readable centered `L¹` estimate obtained from the explicit Young
parameter `eta = 4 e² L h √d`.  This avoids a separate square-root
optimization theorem while retaining the expected `L h √d` scale. -/
theorem finiteEulerLikelihood_centered_abs_integrable_and_integral_le_sqrt
    (hd : 0 < d) (hn : 0 < n) (delta h : ℝ)
    (hdelta : 0 < delta)
    (hhorizon : (n : ℝ) * delta = h)
    (hsmallDim :
      192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 * d ≤ 1) :
    Integrable (fun p : State d × (Fin n → State d) =>
      |finiteGaussianDRec V 1 delta p.1 p.1 p.2 - 1|)
      ((V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) ∧
    (∫ p : State d × (Fin n → State d),
      |finiteGaussianDRec V 1 delta p.1 p.1 p.2 - 1|
      ∂(V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) ≤
      8 * (Real.exp 1) ^ 2 * V.L * h * Real.sqrt d := by
  let x : ℝ := 192 * (Real.exp 1) ^ 2 * V.L ^ 2 * h ^ 2 * d
  let eta : ℝ := 4 * (Real.exp 1) ^ 2 * V.L * h * Real.sqrt d
  have hh : 0 < h := by
    rw [← hhorizon]
    positivity
  have hsmall := likelihood_small_of_dimension_small V hd h hsmallDim
  have hsqrtd : 0 < Real.sqrt (d : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.mpr hd)
  have heta : 0 < eta := by
    dsimp [eta]
    exact mul_pos
      (mul_pos (mul_pos (mul_pos (by norm_num)
        (sq_pos_of_pos (Real.exp_pos 1))) V.hL) hh) hsqrtd
  obtain ⟨hInt, hBound⟩ :=
    finiteEulerLikelihood_centered_abs_integrable_and_integral_le
      V hn delta h eta hdelta.le heta hhorizon hsmall
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hx1 : x ≤ 1 := by simpa only [x] using hsmallDim
  have hExp : Real.exp x - 1 ≤ Real.exp 1 * x :=
    exp_sub_one_le_exp_one_mul hx0 hx1
  have htwoExp : (2 : ℝ) ≤ Real.exp 1 := by
    convert Real.add_one_le_exp (1 : ℝ) using 1 <;> norm_num
  have hcoeff :
      192 * (Real.exp 1) ^ 3 ≤ 128 * (Real.exp 1) ^ 4 := by
    calc
      192 * (Real.exp 1) ^ 3 =
          64 * (Real.exp 1) ^ 3 * 3 := by ring
      _ ≤ 64 * (Real.exp 1) ^ 3 * (2 * Real.exp 1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      _ = 128 * (Real.exp 1) ^ 4 := by ring
  have hExpEta : Real.exp x - 1 ≤ 8 * eta ^ 2 := by
    calc
      Real.exp x - 1 ≤ Real.exp 1 * x := hExp
      _ = 192 * (Real.exp 1) ^ 3 *
          (V.L ^ 2 * h ^ 2 * (d : ℝ)) := by
        dsimp [x]
        ring
      _ ≤ 128 * (Real.exp 1) ^ 4 *
          (V.L ^ 2 * h ^ 2 * (d : ℝ)) :=
        mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ = 8 * eta ^ 2 := by
        dsimp [eta]
        rw [show
          (4 * Real.exp 1 ^ 2 * V.L * h * Real.sqrt ↑d) ^ 2 =
            16 * Real.exp 1 ^ 4 * V.L ^ 2 * h ^ 2 *
              (Real.sqrt (d : ℝ)) ^ 2 by ring,
          Real.sq_sqrt (Nat.cast_nonneg d)]
        ring
  have hfrac : (Real.exp x - 1) / (8 * eta) ≤ eta := by
    apply (div_le_iff₀ (mul_pos (by norm_num) heta)).2
    calc
      Real.exp x - 1 ≤ 8 * eta ^ 2 := hExpEta
      _ = eta * (8 * eta) := by ring
  constructor
  · exact hInt
  · calc
      (∫ p : State d × (Fin n → State d),
        |finiteGaussianDRec V 1 delta p.1 p.1 p.2 - 1|
        ∂(V.target : Measure (State d)).prod
          (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) ≤
          eta + (Real.exp x - 1) / (8 * eta) := by
        simpa only [x] using hBound
      _ ≤ eta + eta := by linarith
      _ = 8 * (Real.exp 1) ^ 2 * V.L * h * Real.sqrt d := by
        dsimp [eta]
        ring

end CompositionWithEnergyEquality

end DiscreteTime

end

end UniformRandomMALA
