import UniformRandomMALA.Concrete.FiniteEulerEnergyMGF
import UniformRandomMALA.DiscreteTime.ElementaryMGFTail
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Real-order moments for the finite Euler likelihood martingale term

This file applies the elementary two-sided-MGF theory to the chronological
linear likelihood term `finiteGaussianMRec`.  The application remains on the
explicit finite product probability space.  Its only analytic input is the
already formalized finite Euler energy MGF.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory

noncomputable section

namespace DiscreteTime

open Concrete

variable {d n : Nat} (V : FirstOrderPotential d)

/-- Real version of the elementary two-term powered-sum estimate. -/
lemma add_rpow_le_two_sub_one_mul_add {a b r : Real}
    (ha : 0 <= a) (hb : 0 <= b) (hr : 1 <= r) :
    (a + b) ^ r <= 2 ^ (r - 1) * (a ^ r + b ^ r) := by
  let A : NNReal := ⟨a, ha⟩
  let B : NNReal := ⟨b, hb⟩
  have h := NNReal.rpow_add_le_mul_rpow_add_rpow A B hr
  exact_mod_cast h

/-- A deliberately lightweight two-term moment triangle inequality.  Its
factor two is looser than Minkowski but follows from a pointwise powered-sum
bound and ordinary integral monotonicity. -/
lemma integral_add_rpow_root_le_two
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (f g : Omega -> Real) {r : Real}
    (hr : 1 <= r) (hf0 : forall x, 0 <= f x)
    (hg0 : forall x, 0 <= g x)
    (hfMeas : Measurable f) (hgMeas : Measurable g)
    (hf : Integrable (fun x => (f x) ^ r) mu)
    (hg : Integrable (fun x => (g x) ^ r) mu) :
    Integrable (fun x => (f x + g x) ^ r) mu /\
      (∫ x, (f x + g x) ^ r ∂mu) ^ (1 / r) <=
        2 * ((∫ x, (f x) ^ r ∂mu) ^ (1 / r) +
          (∫ x, (g x) ^ r ∂mu) ^ (1 / r)) := by
  let c : Real := 2 ^ (r - 1)
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hc0 : 0 <= c := Real.rpow_nonneg (by norm_num) _
  have hmajorInt : Integrable
      (fun x => c * ((f x) ^ r + (g x) ^ r)) mu :=
    (hf.add hg).const_mul c
  have hsumMeas : Measurable (fun x => (f x + g x) ^ r) := by
    exact (Real.continuous_rpow_const hr0.le).measurable.comp
      (hfMeas.add hgMeas)
  have hpoint : forall x, (f x + g x) ^ r <=
      c * ((f x) ^ r + (g x) ^ r) := by
    intro x
    exact add_rpow_le_two_sub_one_mul_add (hf0 x) (hg0 x) hr
  have hsumInt : Integrable (fun x => (f x + g x) ^ r) mu := by
    apply integrable_of_le_of_le hsumMeas.aestronglyMeasurable
      (ae_of_all _ fun x => Real.rpow_nonneg (add_nonneg (hf0 x) (hg0 x)) r)
      (ae_of_all _ hpoint) (integrable_zero _ Real mu) hmajorInt
  have hA0 : 0 <= ∫ x, (f x) ^ r ∂mu :=
    integral_nonneg_of_ae (ae_of_all _ fun x => Real.rpow_nonneg (hf0 x) r)
  have hB0 : 0 <= ∫ x, (g x) ^ r ∂mu :=
    integral_nonneg_of_ae (ae_of_all _ fun x => Real.rpow_nonneg (hg0 x) r)
  have hI0 : 0 <= ∫ x, (f x + g x) ^ r ∂mu :=
    integral_nonneg_of_ae (ae_of_all _ fun x =>
      Real.rpow_nonneg (add_nonneg (hf0 x) (hg0 x)) r)
  have hI : (∫ x, (f x + g x) ^ r ∂mu) <=
      c * ((∫ x, (f x) ^ r ∂mu) + ∫ x, (g x) ^ r ∂mu) := by
    calc
      (∫ x, (f x + g x) ^ r ∂mu) <=
          ∫ x, c * ((f x) ^ r + (g x) ^ r) ∂mu :=
        integral_mono hsumInt hmajorInt hpoint
      _ = c * ((∫ x, (f x) ^ r ∂mu) +
          ∫ x, (g x) ^ r ∂mu) := by
        rw [integral_const_mul, integral_add hf hg]
  have hroot := Real.rpow_le_rpow hI0 hI (by positivity : 0 <= 1 / r)
  have hcroot : c ^ (1 / r) <= 2 := by
    have hexp : (r - 1) * (1 / r) <= 1 := by
      rw [show (r - 1) * (1 / r) = (r - 1) / r by ring]
      exact (div_le_one hr0).2 (by linarith)
    dsimp [c]
    rw [<- Real.rpow_mul (by norm_num : (0 : Real) <= 2)]
    exact Real.rpow_le_self_of_one_le (by norm_num) hexp
  have hABroot := Real.rpow_add_le_add_rpow hA0 hB0
    (by positivity : 0 <= 1 / r) ((div_le_one hr0).2 hr)
  constructor
  · exact hsumInt
  · calc
      (∫ x, (f x + g x) ^ r ∂mu) ^ (1 / r) <=
          (c * ((∫ x, (f x) ^ r ∂mu) +
            ∫ x, (g x) ^ r ∂mu)) ^ (1 / r) := hroot
      _ = c ^ (1 / r) *
          ((∫ x, (f x) ^ r ∂mu) +
            ∫ x, (g x) ^ r ∂mu) ^ (1 / r) := by
        rw [Real.mul_rpow hc0 (add_nonneg hA0 hB0)]
      _ <= 2 *
          ((∫ x, (f x) ^ r ∂mu) +
            ∫ x, (g x) ^ r ∂mu) ^ (1 / r) := by
        gcongr
      _ <= 2 * ((∫ x, (f x) ^ r ∂mu) ^ (1 / r) +
          (∫ x, (g x) ^ r ∂mu) ^ (1 / r)) := by
        gcongr

/-- Measurability of the initial-reference version of the linear likelihood
term.  We recover `M` from the measurable positive likelihood and its
quadratic compensator, avoiding a second recursion-measurability induction. -/
lemma measurable_finiteGaussianMRec_initial_of_nonneg
    (delta : Real) (hdelta : 0 <= delta) (n : Nat) :
    Measurable (fun p : State d × (Fin n -> State d) =>
      finiteGaussianMRec V delta p.1 p.1 p.2) := by
  have hD := measurable_finiteGaussianDRec_initial V 1 delta hdelta n
  have hW := measurable_finiteGaussianVRec_initial V delta n
  have hfun : (fun p : State d × (Fin n -> State d) =>
      finiteGaussianMRec V delta p.1 p.1 p.2) =
      fun p => Real.log (finiteGaussianDRec V 1 delta p.1 p.1 p.2) +
        finiteGaussianVRec V delta p.1 p.1 p.2 / 2 := by
    funext p
    unfold finiteGaussianDRec
    rw [Real.log_exp]
    ring
  rw [hfun]
  exact (Real.measurable_log.comp hD).add (hW.div_const 2)

/-- At a scalar parameter `a`, the normalized likelihood and a single
Young inequality reduce the MGF of `a M` to the Euler energy MGF at
`lambda = a^2 L^2`.

The admissible range is expressed by `|a| <= s0`; the one scalar hypothesis
at `s0` then discharges all smaller energy-integrability obligations. -/
theorem finiteGaussianMRec_exp_integrable_and_integral_le
    (hn : 0 < n) (delta tau s0 a : Real)
    (hdelta : 0 <= delta) (hs0 : 0 <= s0)
    (hhorizon : (n : Real) * delta = tau)
    (hEuler : V.L * tau <= 1)
    (hsmall :
      64 * (Real.exp 1) ^ 2 * (s0 ^ 2 * V.L ^ 2) * tau ^ 2 <= 1)
    (ha : |a| <= s0) :
    Integrable (fun p : State d × (Fin n -> State d) =>
      Real.exp (a * finiteGaussianMRec V delta p.1 p.1 p.2))
      ((V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) /\
    (∫ p : State d × (Fin n -> State d),
      Real.exp (a * finiteGaussianMRec V delta p.1 p.1 p.2)
      ∂(V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) <=
      Real.exp
        ((64 * (Real.exp 1) ^ 2 * V.L ^ 2 * tau ^ 2 * d) * a ^ 2) := by
  let P : Measure (State d × (Fin n -> State d)) :=
    (V.target : Measure (State d)).prod
      (Measure.pi (fun _ : Fin n => stdGaussian (State d)))
  let M : State d × (Fin n -> State d) -> Real := fun p =>
    finiteGaussianMRec V delta p.1 p.1 p.2
  let W : State d × (Fin n -> State d) -> Real := fun p =>
    finiteGaussianVRec V delta p.1 p.1 p.2
  let J : State d × (Fin n -> State d) -> Real := fun p =>
    finiteEulerEnergy V delta p.1 p.2
  let lambda : Real := a ^ 2 * V.L ^ 2
  let C : Real := 64 * (Real.exp 1) ^ 2 * V.L ^ 2 * tau ^ 2 * d
  have haSq : a ^ 2 <= s0 ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg a) hs0).2 ha
  have hlambda : 0 <= lambda := by
    dsimp [lambda]
    positivity
  have hsmallA : 64 * (Real.exp 1) ^ 2 * lambda * tau ^ 2 <= 1 := by
    calc
      64 * (Real.exp 1) ^ 2 * lambda * tau ^ 2 =
          (64 * (Real.exp 1) ^ 2 * tau ^ 2) *
            (a ^ 2 * V.L ^ 2) := by
        dsimp [lambda]
        ring
      _ <= (64 * (Real.exp 1) ^ 2 * tau ^ 2) *
          (s0 ^ 2 * V.L ^ 2) := by
        gcongr
      _ = 64 * (Real.exp 1) ^ 2 * (s0 ^ 2 * V.L ^ 2) * tau ^ 2 := by
        ring
      _ <= 1 := hsmall
  have hEnergyInt : Integrable (fun p => Real.exp (lambda * J p)) P := by
    simpa only [P, J] using
      integrable_exp_finiteEulerEnergy V hn delta tau lambda hdelta hlambda
        hhorizon hEuler hsmallA
  have hEnergyBound :
      (∫ p, Real.exp (lambda * J p) ∂P) <= Real.exp (C * a ^ 2) := by
    have hbound := integral_exp_finiteEulerEnergy_le_exp
      V hn delta tau lambda hdelta hlambda hhorizon hEuler hsmallA
    have hexponent :
        64 * (Real.exp 1) ^ 2 * lambda * tau ^ 2 * d = C * a ^ 2 := by
      dsimp [lambda, C]
      ring
    rw [hexponent] at hbound
    simpa only [P, J] using hbound
  have hDInt : Integrable (fun p =>
      finiteGaussianDRec V (2 * a) delta p.1 p.1 p.2) P := by
    simpa only [P] using
      integrable_finiteGaussianDRec_initial V (2 * a) delta hdelta n
  have hDIntegral :
      (∫ p, finiteGaussianDRec V (2 * a) delta p.1 p.1 p.2 ∂P) = 1 := by
    simpa only [P] using
      integral_finiteGaussianDRec_initial V (2 * a) delta hdelta n
  have hMMeas : Measurable M := by
    simpa only [M] using
      measurable_finiteGaussianMRec_initial_of_nonneg V delta hdelta n
  have hmajorInt : Integrable (fun p =>
      (finiteGaussianDRec V (2 * a) delta p.1 p.1 p.2 +
        Real.exp (lambda * J p)) / 2) P :=
    (hDInt.add hEnergyInt).div_const 2
  have hpoint : forall p, Real.exp (a * M p) <=
      (finiteGaussianDRec V (2 * a) delta p.1 p.1 p.2 +
        Real.exp (lambda * J p)) / 2 := by
    intro p
    let u : Real := Real.exp (a * M p - a ^ 2 * W p)
    let v : Real := Real.exp (a ^ 2 * W p)
    have hprod : Real.exp (a * M p) = u * v := by
      dsimp [u, v]
      rw [<- Real.exp_add]
      congr 1
      ring
    have huSq : u ^ 2 =
        finiteGaussianDRec V (2 * a) delta p.1 p.1 p.2 := by
      dsimp [u, M, W]
      unfold finiteGaussianDRec
      rw [pow_two, <- Real.exp_add]
      congr 1
      ring
    have hvSq : v ^ 2 = Real.exp (2 * a ^ 2 * W p) := by
      dsimp [v]
      rw [pow_two, <- Real.exp_add]
      congr 1
      ring
    have hYoung : u * v <= (u ^ 2 + v ^ 2) / 2 := by
      nlinarith [sq_nonneg (u - v)]
    have hW := finiteGaussianVRec_le_energyRec
      V delta hdelta p.1 p.1 p.2
    rw [finiteEulerEnergyRec_initial_eq_finiteEulerEnergy V delta p.1 p.2]
      at hW
    have hscaled : 2 * a ^ 2 * W p <= lambda * J p := by
      have hs := mul_le_mul_of_nonneg_left hW
        (by positivity : 0 <= 2 * a ^ 2)
      dsimp [W, J, lambda] at hs ⊢
      nlinarith
    calc
      Real.exp (a * M p) = u * v := hprod
      _ <= (u ^ 2 + v ^ 2) / 2 := hYoung
      _ = (finiteGaussianDRec V (2 * a) delta p.1 p.1 p.2 +
          Real.exp (2 * a ^ 2 * W p)) / 2 := by rw [huSq, hvSq]
      _ <= (finiteGaussianDRec V (2 * a) delta p.1 p.1 p.2 +
          Real.exp (lambda * J p)) / 2 := by
        gcongr
  have hMExpInt : Integrable (fun p => Real.exp (a * M p)) P := by
    apply integrable_of_le_of_le
      ((Real.continuous_exp.measurable.comp
        (measurable_const.mul hMMeas)).aestronglyMeasurable)
      (ae_of_all _ fun p => (Real.exp_pos (a * M p)).le)
      (ae_of_all _ hpoint) (integrable_zero _ Real P) hmajorInt
  constructor
  · simpa only [P, M] using hMExpInt
  · change (∫ p, Real.exp (a * M p) ∂P) <= Real.exp (C * a ^ 2)
    calc
      (∫ p, Real.exp (a * M p) ∂P) <=
          ∫ p, (finiteGaussianDRec V (2 * a) delta p.1 p.1 p.2 +
            Real.exp (lambda * J p)) / 2 ∂P :=
        integral_mono hMExpInt hmajorInt hpoint
      _ = (1 + (∫ p, Real.exp (lambda * J p) ∂P)) / 2 := by
        rw [integral_div, integral_add hDInt hEnergyInt, hDIntegral]
      _ <= (1 + Real.exp (C * a ^ 2)) / 2 := by
        gcongr
      _ <= Real.exp (C * a ^ 2) := by
        have hC0 : 0 <= C := by
          dsimp [C]
          positivity
        have hone := Real.one_le_exp (mul_nonneg hC0 (sq_nonneg a))
        linarith

/-- Application-level two-sided MGF package for the finite linear
likelihood term.  Its quadratic coefficient is
`64 e^2 L^2 tau^2 d`, and its MGF prefactor is exactly one. -/
theorem finiteGaussianMRec_twoSidedMGFBound
    (hn : 0 < n) (delta tau s0 : Real)
    (hdelta : 0 <= delta) (hs0 : 0 <= s0)
    (hhorizon : (n : Real) * delta = tau)
    (hEuler : V.L * tau <= 1)
    (hsmall :
      64 * (Real.exp 1) ^ 2 * (s0 ^ 2 * V.L ^ 2) * tau ^ 2 <= 1) :
    TwoSidedMGFBound
      ((V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d))))
      (fun p : State d × (Fin n -> State d) =>
        finiteGaussianMRec V delta p.1 p.1 p.2)
      1 (64 * (Real.exp 1) ^ 2 * V.L ^ 2 * tau ^ 2 * d) s0 := by
  let P : Measure (State d × (Fin n -> State d)) :=
    (V.target : Measure (State d)).prod
      (Measure.pi (fun _ : Fin n => stdGaussian (State d)))
  let M : State d × (Fin n -> State d) -> Real := fun p =>
    finiteGaussianMRec V delta p.1 p.1 p.2
  let C : Real := 64 * (Real.exp 1) ^ 2 * V.L ^ 2 * tau ^ 2 * d
  change TwoSidedMGFBound P M 1 C s0
  refine
    { measurable_X := by
        simpa only [M] using
          measurable_finiteGaussianMRec_initial_of_nonneg V delta hdelta n
      integrable_pos := ?_
      integrable_neg := ?_
      integral_pos_le := ?_
      integral_neg_le := ?_ }
  · intro s hs hss0
    have has : |s| <= s0 := by simpa [abs_of_nonneg hs]
    simpa only [P, M] using
      (finiteGaussianMRec_exp_integrable_and_integral_le
        V hn delta tau s0 s hdelta hs0 hhorizon hEuler hsmall has).1
  · intro s hs hss0
    have has : |-s| <= s0 := by simpa [abs_of_nonneg hs]
    simpa only [P, M] using
      (finiteGaussianMRec_exp_integrable_and_integral_le
        V hn delta tau s0 (-s) hdelta hs0 hhorizon hEuler hsmall has).1
  · intro s hs hss0
    have has : |s| <= s0 := by simpa [abs_of_nonneg hs]
    have hb :=
      (finiteGaussianMRec_exp_integrable_and_integral_le
        V hn delta tau s0 s hdelta hs0 hhorizon hEuler hsmall has).2
    simpa only [P, M, C, one_mul] using hb
  · intro s hs hss0
    have has : |-s| <= s0 := by simpa [abs_of_nonneg hs]
    have hb :=
      (finiteGaussianMRec_exp_integrable_and_integral_le
        V hn delta tau s0 (-s) hdelta hs0 hhorizon hEuler hsmall has).2
    simpa only [P, M, C, one_mul, neg_sq] using hb

/-- Concrete real-order moment estimate for the finite linear likelihood
term.  The right side has the sub-gamma scale
`sqrt(64 e^2 L^2 tau^2 d r) + r / s0`. -/
theorem finiteGaussianMRec_realMomentRoot_le
    (hn : 0 < n) (hd : 0 < d) (delta tau s0 r : Real)
    (hdelta : 0 <= delta) (htau : 0 < tau) (hs0 : 0 < s0)
    (hr : 1 <= r)
    (hhorizon : (n : Real) * delta = tau)
    (hEuler : V.L * tau <= 1)
    (hsmall :
      64 * (Real.exp 1) ^ 2 * (s0 ^ 2 * V.L ^ 2) * tau ^ 2 <= 1) :
    TwoSidedMGFBound.realMomentRoot
      ((V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d))))
      (fun p : State d × (Fin n -> State d) =>
        finiteGaussianMRec V delta p.1 p.1 p.2) r <=
      2 * Real.exp 1 *
        (Real.sqrt
          ((64 * (Real.exp 1) ^ 2 * V.L ^ 2 * tau ^ 2 * d) * r) +
          r / s0) := by
  let P : Measure (State d × (Fin n -> State d)) :=
    (V.target : Measure (State d)).prod
      (Measure.pi (fun _ : Fin n => stdGaussian (State d)))
  let M : State d × (Fin n -> State d) -> Real := fun p =>
    finiteGaussianMRec V delta p.1 p.1 p.2
  let C : Real := 64 * (Real.exp 1) ^ 2 * V.L ^ 2 * tau ^ 2 * d
  have hmgf : TwoSidedMGFBound P M 1 C s0 := by
    simpa only [P, M, C] using
      finiteGaussianMRec_twoSidedMGFBound
        V hn delta tau s0 hdelta hs0.le hhorizon hEuler hsmall
  have hC : 0 < C := by
    have hdR : (0 : Real) < d := by exact_mod_cast hd
    dsimp [C]
    exact mul_pos
      (mul_pos
        (mul_pos
          (mul_pos (by norm_num) (sq_pos_of_pos (Real.exp_pos 1)))
          (sq_pos_of_pos V.hL))
        (sq_pos_of_pos htau))
      hdR
  have hm := hmgf.realMomentRoot_le_subgamma_scale hr hC hs0
  simpa only [P, M, C, one_mul, mul_one] using hm

/-- Real-order moment bound for the finite Euler path energy from one
ordinary exponential moment.  This is the one-sided analogue needed for the
nonnegative compensator; no layer-cake formula is used. -/
theorem finiteEulerEnergy_rpow_integrable_and_integral_le
    (hn : 0 < n) (delta tau lambda r : Real)
    (hdelta : 0 <= delta) (hlambda : 0 < lambda) (hr : 0 < r)
    (hhorizon : (n : Real) * delta = tau)
    (hEuler : V.L * tau <= 1)
    (hsmall : 64 * (Real.exp 1) ^ 2 * lambda * tau ^ 2 <= 1) :
    Integrable (fun p : State d × (Fin n -> State d) =>
      (finiteEulerEnergy V delta p.1 p.2) ^ r)
      ((V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) /\
    (∫ p : State d × (Fin n -> State d),
      (finiteEulerEnergy V delta p.1 p.2) ^ r
      ∂(V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) <=
      (r / lambda) ^ r *
        Real.exp
          ((64 * (Real.exp 1) ^ 2 * tau ^ 2 * d) * lambda) := by
  let P : Measure (State d × (Fin n -> State d)) :=
    (V.target : Measure (State d)).prod
      (Measure.pi (fun _ : Fin n => stdGaussian (State d)))
  let J : State d × (Fin n -> State d) -> Real := fun p =>
    finiteEulerEnergy V delta p.1 p.2
  let c : Real := (r / lambda) ^ r
  let K : Real := 64 * (Real.exp 1) ^ 2 * tau ^ 2 * d
  have hJ0 : forall p, 0 <= J p := by
    intro p
    dsimp [J]
    unfold finiteEulerEnergy
    exact mul_nonneg hdelta (Finset.sum_nonneg fun k _ => sq_nonneg _)
  have hc0 : 0 <= c :=
    Real.rpow_nonneg (div_pos hr hlambda).le r
  have hEnergyInt : Integrable (fun p => Real.exp (lambda * J p)) P := by
    simpa only [P, J] using
      integrable_exp_finiteEulerEnergy V hn delta tau lambda hdelta
        hlambda.le hhorizon hEuler hsmall
  have hEnergyBound :
      (∫ p, Real.exp (lambda * J p) ∂P) <= Real.exp (K * lambda) := by
    have hb := integral_exp_finiteEulerEnergy_le_exp
      V hn delta tau lambda hdelta hlambda.le hhorizon hEuler hsmall
    have hexponent :
        64 * (Real.exp 1) ^ 2 * lambda * tau ^ 2 * d = K * lambda := by
      dsimp [K]
      ring
    rw [hexponent] at hb
    simpa only [P, J] using hb
  have hmajorInt : Integrable
      (fun p => c * Real.exp (lambda * J p)) P :=
    hEnergyInt.const_mul c
  have hJrMeas : Measurable (fun p => (J p) ^ r) :=
    (Real.continuous_rpow_const hr.le).measurable.comp
      (measurable_finiteEulerEnergy_uncurry V delta)
  have hpoint : forall p, (J p) ^ r <=
      c * Real.exp (lambda * J p) := by
    intro p
    exact rpow_le_scale_rpow_mul_exp (hJ0 p) hr hlambda
  have hJrInt : Integrable (fun p => (J p) ^ r) P := by
    apply integrable_of_le_of_le hJrMeas.aestronglyMeasurable
      (ae_of_all _ fun p => Real.rpow_nonneg (hJ0 p) r)
      (ae_of_all _ hpoint) (integrable_zero _ Real P) hmajorInt
  constructor
  · simpa only [P, J] using hJrInt
  · change (∫ p, (J p) ^ r ∂P) <= c * Real.exp (K * lambda)
    calc
      (∫ p, (J p) ^ r ∂P) <=
          ∫ p, c * Real.exp (lambda * J p) ∂P :=
        integral_mono hJrInt hmajorInt hpoint
      _ = c * (∫ p, Real.exp (lambda * J p) ∂P) := by
        rw [integral_const_mul]
      _ <= c * Real.exp (K * lambda) :=
        mul_le_mul_of_nonneg_left hEnergyBound hc0

/-- The recursive quadratic compensator is nonnegative when the Euler step
is nonnegative. -/
lemma finiteGaussianVRec_nonneg (delta : Real) (hdelta : 0 <= delta)
    (xRef : State d) : forall {m : Nat} (x : State d)
      (z : Fin m -> State d),
      0 <= finiteGaussianVRec V delta xRef x z := by
  intro m
  induction m with
  | zero =>
      intro x z
      simp [finiteGaussianVRec]
  | succ m ih =>
      intro x z
      simp only [finiteGaussianVRec]
      exact add_nonneg (mul_nonneg hdelta (sq_nonneg _))
        (ih (finiteEulerStep V delta x (z 0)) (Fin.tail z))

/-- Global elementary exponential increment bound used to turn a log-density
moment into a centered density moment. -/
lemma abs_exp_sub_one_le_one_add_exp_mul_abs (w : Real) :
    |Real.exp w - 1| <= (1 + Real.exp w) * |w| := by
  rcases le_total 0 w with hw | hw
  · rw [abs_of_nonneg hw,
      abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp hw))]
    have hneg := Real.add_one_le_exp (-w)
    have hmul := mul_le_mul_of_nonneg_left hneg (Real.exp_pos w).le
    have hexp : Real.exp w * Real.exp (-w) = 1 := by
      rw [<- Real.exp_add]
      simp
    rw [hexp] at hmul
    nlinarith [mul_nonneg hw (Real.exp_pos w).le]
  · rw [abs_of_nonpos hw,
      abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_one_iff.mpr hw))]
    have hbase := Real.add_one_le_exp w
    have hfac : -w <= (1 + Real.exp w) * (-w) := by
      have hone : 1 <= 1 + Real.exp w := by
        linarith [Real.exp_pos w]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hone (neg_nonneg.mpr hw)
    linarith

/-- Powered likelihood estimate.  Exact normalization at parameter `2q`
and one Young inequality leave only the energy exponential at
`lambda = (2q^2-q)L^2/2`. -/
theorem finiteGaussianDRec_rpow_integrable_and_integral_le
    (hn : 0 < n) (delta tau q : Real)
    (hdelta : 0 <= delta) (hq : 1 <= q)
    (hhorizon : (n : Real) * delta = tau)
    (hEuler : V.L * tau <= 1)
    (hsmall :
      64 * (Real.exp 1) ^ 2 *
        (((2 * q ^ 2 - q) * V.L ^ 2 / 2)) * tau ^ 2 <= 1) :
    Integrable (fun p : State d × (Fin n -> State d) =>
      (finiteGaussianDRec V 1 delta p.1 p.1 p.2) ^ q)
      ((V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) /\
    (∫ p : State d × (Fin n -> State d),
      (finiteGaussianDRec V 1 delta p.1 p.1 p.2) ^ q
      ∂(V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) <=
      Real.exp
        ((64 * (Real.exp 1) ^ 2 * tau ^ 2 * d) *
          ((2 * q ^ 2 - q) * V.L ^ 2 / 2)) := by
  let P : Measure (State d × (Fin n -> State d)) :=
    (V.target : Measure (State d)).prod
      (Measure.pi (fun _ : Fin n => stdGaussian (State d)))
  let D : State d × (Fin n -> State d) -> Real := fun p =>
    finiteGaussianDRec V 1 delta p.1 p.1 p.2
  let W : State d × (Fin n -> State d) -> Real := fun p =>
    finiteGaussianVRec V delta p.1 p.1 p.2
  let J : State d × (Fin n -> State d) -> Real := fun p =>
    finiteEulerEnergy V delta p.1 p.2
  let lambda : Real := (2 * q ^ 2 - q) * V.L ^ 2 / 2
  let K : Real := 64 * (Real.exp 1) ^ 2 * tau ^ 2 * d
  have hq0 : 0 <= q := zero_le_one.trans hq
  have hcoef : 0 <= 2 * q ^ 2 - q := by nlinarith [sq_nonneg q]
  have hlambda : 0 <= lambda := by
    dsimp [lambda]
    positivity
  have hEnergyInt : Integrable (fun p => Real.exp (lambda * J p)) P := by
    simpa only [P, J] using
      integrable_exp_finiteEulerEnergy V hn delta tau lambda hdelta hlambda
        hhorizon hEuler hsmall
  have hEnergyBound :
      (∫ p, Real.exp (lambda * J p) ∂P) <= Real.exp (K * lambda) := by
    have hb := integral_exp_finiteEulerEnergy_le_exp
      V hn delta tau lambda hdelta hlambda hhorizon hEuler hsmall
    have hexponent :
        64 * (Real.exp 1) ^ 2 * lambda * tau ^ 2 * d = K * lambda := by
      dsimp [K]
      ring
    rw [hexponent] at hb
    simpa only [P, J] using hb
  have hD2Int : Integrable (fun p =>
      finiteGaussianDRec V (2 * q) delta p.1 p.1 p.2) P := by
    simpa only [P] using
      integrable_finiteGaussianDRec_initial V (2 * q) delta hdelta n
  have hD2Integral :
      (∫ p, finiteGaussianDRec V (2 * q) delta p.1 p.1 p.2 ∂P) = 1 := by
    simpa only [P] using
      integral_finiteGaussianDRec_initial V (2 * q) delta hdelta n
  have hmajorInt : Integrable (fun p =>
      (finiteGaussianDRec V (2 * q) delta p.1 p.1 p.2 +
        Real.exp (lambda * J p)) / 2) P :=
    (hD2Int.add hEnergyInt).div_const 2
  have hpoint : forall p, (D p) ^ q <=
      (finiteGaussianDRec V (2 * q) delta p.1 p.1 p.2 +
        Real.exp (lambda * J p)) / 2 := by
    intro p
    let u : Real := Real.exp
      (q * finiteGaussianMRec V delta p.1 p.1 p.2 - q ^ 2 * W p)
    let v : Real := Real.exp ((q ^ 2 - q / 2) * W p)
    have hprod : (D p) ^ q = u * v := by
      dsimp [D, u, v, W]
      unfold finiteGaussianDRec
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
        <- Real.exp_add]
      congr 1
      ring
    have huSq : u ^ 2 =
        finiteGaussianDRec V (2 * q) delta p.1 p.1 p.2 := by
      dsimp [u, W]
      unfold finiteGaussianDRec
      rw [pow_two, <- Real.exp_add]
      congr 1
      ring
    have hvSq : v ^ 2 = Real.exp ((2 * q ^ 2 - q) * W p) := by
      dsimp [v]
      rw [pow_two, <- Real.exp_add]
      congr 1
      ring
    have hYoung : u * v <= (u ^ 2 + v ^ 2) / 2 := by
      nlinarith [sq_nonneg (u - v)]
    have hW := finiteGaussianVRec_le_energyRec
      V delta hdelta p.1 p.1 p.2
    rw [finiteEulerEnergyRec_initial_eq_finiteEulerEnergy V delta p.1 p.2]
      at hW
    have hscaled : (2 * q ^ 2 - q) * W p <= lambda * J p := by
      have hs := mul_le_mul_of_nonneg_left hW hcoef
      dsimp [W, J, lambda] at hs ⊢
      nlinarith
    calc
      (D p) ^ q = u * v := hprod
      _ <= (u ^ 2 + v ^ 2) / 2 := hYoung
      _ = (finiteGaussianDRec V (2 * q) delta p.1 p.1 p.2 +
          Real.exp ((2 * q ^ 2 - q) * W p)) / 2 := by rw [huSq, hvSq]
      _ <= (finiteGaussianDRec V (2 * q) delta p.1 p.1 p.2 +
          Real.exp (lambda * J p)) / 2 := by
        gcongr
  have hDqMeas : Measurable (fun p => (D p) ^ q) :=
    (Real.continuous_rpow_const hq0).measurable.comp
      (measurable_finiteGaussianDRec_initial V 1 delta hdelta n)
  have hDqInt : Integrable (fun p => (D p) ^ q) P := by
    have hDnonneg : forall p, 0 <= D p := by
      intro p
      dsimp [D]
      unfold finiteGaussianDRec
      exact (Real.exp_pos _).le
    apply integrable_of_le_of_le hDqMeas.aestronglyMeasurable
      (ae_of_all _ fun p => Real.rpow_nonneg
        (hDnonneg p) q)
      (ae_of_all _ hpoint) (integrable_zero _ Real P) hmajorInt
  constructor
  · simpa only [P, D] using hDqInt
  · change (∫ p, (D p) ^ q ∂P) <= Real.exp (K * lambda)
    calc
      (∫ p, (D p) ^ q ∂P) <=
          ∫ p, (finiteGaussianDRec V (2 * q) delta p.1 p.1 p.2 +
            Real.exp (lambda * J p)) / 2 ∂P :=
        integral_mono hDqInt hmajorInt hpoint
      _ = (1 + (∫ p, Real.exp (lambda * J p) ∂P)) / 2 := by
        rw [integral_div, integral_add hD2Int hEnergyInt, hD2Integral]
      _ <= (1 + Real.exp (K * lambda)) / 2 := by gcongr
      _ <= Real.exp (K * lambda) := by
        have hK0 : 0 <= K := by
          dsimp [K]
          positivity
        have hone := Real.one_le_exp (mul_nonneg hK0 hlambda)
        linarith

/-- Uniform `L^(2p)` root of the likelihood under the simpler paper-style
small-step condition with a quadratic dependence on `p`. -/
theorem finiteGaussianDRec_two_p_root_le
    (hn : 0 < n) (delta tau p : Real)
    (hdelta : 0 <= delta) (hp : 1 <= p)
    (hhorizon : (n : Real) * delta = tau)
    (hEuler : V.L * tau <= 1)
    (hsmall :
      256 * (Real.exp 1) ^ 2 * p ^ 2 * V.L ^ 2 * tau ^ 2 <= 1) :
    ((∫ x : State d × (Fin n -> State d),
      (finiteGaussianDRec V 1 delta x.1 x.1 x.2) ^ (2 * p)
      ∂(V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) ^
        (1 / (2 * p))) <=
      Real.exp
        (128 * (Real.exp 1) ^ 2 * V.L ^ 2 * tau ^ 2 * d * p) := by
  let P : Measure (State d × (Fin n -> State d)) :=
    (V.target : Measure (State d)).prod
      (Measure.pi (fun _ : Fin n => stdGaussian (State d)))
  let D : State d × (Fin n -> State d) -> Real := fun x =>
    finiteGaussianDRec V 1 delta x.1 x.1 x.2
  let q : Real := 2 * p
  let lambda : Real := (2 * q ^ 2 - q) * V.L ^ 2 / 2
  let K : Real := 64 * (Real.exp 1) ^ 2 * tau ^ 2 * d
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hq : 1 <= q := by dsimp [q]; nlinarith
  have hlambda : 0 <= lambda := by
    dsimp [lambda, q]
    have hcoef : 0 <= 4 * p ^ 2 - p := by nlinarith [sq_nonneg p]
    rw [show (2 * (2 * p) ^ 2 - 2 * p) * V.L ^ 2 / 2 =
        (4 * p ^ 2 - p) * V.L ^ 2 by ring]
    exact mul_nonneg hcoef (sq_nonneg V.L)
  have hlambdaLe : lambda <= 4 * p ^ 2 * V.L ^ 2 := by
    dsimp [lambda, q]
    have hLsq : 0 <= V.L ^ 2 := sq_nonneg _
    nlinarith
  have hsmallQ : 64 * (Real.exp 1) ^ 2 * lambda * tau ^ 2 <= 1 := by
    calc
      64 * (Real.exp 1) ^ 2 * lambda * tau ^ 2 <=
          64 * (Real.exp 1) ^ 2 * (4 * p ^ 2 * V.L ^ 2) * tau ^ 2 := by
        gcongr
      _ = 256 * (Real.exp 1) ^ 2 * p ^ 2 * V.L ^ 2 * tau ^ 2 := by ring
      _ <= 1 := hsmall
  obtain ⟨hDqInt, hDqBound⟩ :=
    finiteGaussianDRec_rpow_integrable_and_integral_le
      V hn delta tau q hdelta hq hhorizon hEuler hsmallQ
  have hDqIntP : Integrable (fun x => (D x) ^ q) P := by
    simpa only [P, D, q] using hDqInt
  have hDqBoundP : (∫ x, (D x) ^ q ∂P) <= Real.exp (K * lambda) := by
    simpa only [P, D, K, lambda] using hDqBound
  have hDnonneg : forall x, 0 <= D x := by
    intro x
    dsimp [D]
    unfold finiteGaussianDRec
    exact (Real.exp_pos _).le
  have hIntegral0 : 0 <= ∫ x, (D x) ^ q ∂P :=
    integral_nonneg_of_ae (ae_of_all _ fun x =>
      Real.rpow_nonneg (hDnonneg x) q)
  have hroot := Real.rpow_le_rpow hIntegral0 hDqBoundP
    (by positivity : 0 <= 1 / (2 * p))
  have hexpRoot :
      (Real.exp (K * lambda)) ^ (1 / (2 * p)) =
        Real.exp (K * lambda / (2 * p)) := by
    rw [<- Real.exp_mul]
    congr 1
    ring
  have hexponent : K * lambda / (2 * p) <=
      128 * (Real.exp 1) ^ 2 * V.L ^ 2 * tau ^ 2 * d * p := by
    have hK0 : 0 <= K := by dsimp [K]; positivity
    have hmul := mul_le_mul_of_nonneg_left hlambdaLe hK0
    apply (div_le_iff₀ (mul_pos (by norm_num) hp0)).2
    dsimp [K] at hmul ⊢
    nlinarith
  change (∫ x, (D x) ^ q ∂P) ^ (1 / (2 * p)) <= _
  calc
    (∫ x, (D x) ^ q ∂P) ^ (1 / (2 * p)) <=
        (Real.exp (K * lambda)) ^ (1 / (2 * p)) := by
      simpa only [q] using hroot
    _ = Real.exp (K * lambda / (2 * p)) := hexpRoot
    _ <= Real.exp
        (128 * (Real.exp 1) ^ 2 * V.L ^ 2 * tau ^ 2 * d * p) :=
      Real.exp_le_exp.mpr hexponent

/-- Real-order moment bound for the quadratic compensator `V`, transported
from the path-energy moment by the deterministic inequality
`V <= (L^2/2) J`. -/
theorem finiteGaussianVRec_rpow_integrable_and_integral_le
    (hn : 0 < n) (delta tau lambda r : Real)
    (hdelta : 0 <= delta) (hlambda : 0 < lambda) (hr : 0 < r)
    (hhorizon : (n : Real) * delta = tau)
    (hEuler : V.L * tau <= 1)
    (hsmall : 64 * (Real.exp 1) ^ 2 * lambda * tau ^ 2 <= 1) :
    Integrable (fun p : State d × (Fin n -> State d) =>
      (finiteGaussianVRec V delta p.1 p.1 p.2) ^ r)
      ((V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) /\
    (∫ p : State d × (Fin n -> State d),
      (finiteGaussianVRec V delta p.1 p.1 p.2) ^ r
      ∂(V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) <=
      (V.L ^ 2 / 2) ^ r *
        ((r / lambda) ^ r *
          Real.exp
            ((64 * (Real.exp 1) ^ 2 * tau ^ 2 * d) * lambda)) := by
  let P : Measure (State d × (Fin n -> State d)) :=
    (V.target : Measure (State d)).prod
      (Measure.pi (fun _ : Fin n => stdGaussian (State d)))
  let W : State d × (Fin n -> State d) -> Real := fun p =>
    finiteGaussianVRec V delta p.1 p.1 p.2
  let J : State d × (Fin n -> State d) -> Real := fun p =>
    finiteEulerEnergy V delta p.1 p.2
  let c : Real := (V.L ^ 2 / 2) ^ r
  obtain ⟨hJrInt, hJrBound⟩ :=
    finiteEulerEnergy_rpow_integrable_and_integral_le
      V hn delta tau lambda r hdelta hlambda hr hhorizon hEuler hsmall
  have hJrIntP : Integrable (fun p => (J p) ^ r) P := by
    simpa only [P, J] using hJrInt
  have hJrBoundP : (∫ p, (J p) ^ r ∂P) <=
      (r / lambda) ^ r *
        Real.exp ((64 * (Real.exp 1) ^ 2 * tau ^ 2 * d) * lambda) := by
    simpa only [P, J] using hJrBound
  have hcoef0 : 0 <= V.L ^ 2 / 2 := by positivity
  have hc0 : 0 <= c := Real.rpow_nonneg hcoef0 r
  have hW0 : forall p, 0 <= W p := by
    intro p
    exact finiteGaussianVRec_nonneg V delta hdelta p.1 p.1 p.2
  have hJ0 : forall p, 0 <= J p := by
    intro p
    dsimp [J]
    unfold finiteEulerEnergy
    exact mul_nonneg hdelta (Finset.sum_nonneg fun k _ => sq_nonneg _)
  have hWle : forall p, W p <= (V.L ^ 2 / 2) * J p := by
    intro p
    have hbound := finiteGaussianVRec_le_energyRec
      V delta hdelta p.1 p.1 p.2
    rw [finiteEulerEnergyRec_initial_eq_finiteEulerEnergy V delta p.1 p.2]
      at hbound
    exact hbound
  have hpoint : forall p, (W p) ^ r <= c * (J p) ^ r := by
    intro p
    calc
      (W p) ^ r <= ((V.L ^ 2 / 2) * J p) ^ r :=
        Real.rpow_le_rpow (hW0 p) (hWle p) hr.le
      _ = c * (J p) ^ r := by
        dsimp [c]
        rw [Real.mul_rpow hcoef0 (hJ0 p)]
  have hmajorInt : Integrable (fun p => c * (J p) ^ r) P :=
    hJrIntP.const_mul c
  have hWrMeas : Measurable (fun p => (W p) ^ r) :=
    (Real.continuous_rpow_const hr.le).measurable.comp
      (measurable_finiteGaussianVRec_initial V delta n)
  have hWrInt : Integrable (fun p => (W p) ^ r) P := by
    apply integrable_of_le_of_le hWrMeas.aestronglyMeasurable
      (ae_of_all _ fun p => Real.rpow_nonneg (hW0 p) r)
      (ae_of_all _ hpoint) (integrable_zero _ Real P) hmajorInt
  constructor
  · simpa only [P, W] using hWrInt
  · change (∫ p, (W p) ^ r ∂P) <= c *
      ((r / lambda) ^ r *
        Real.exp ((64 * (Real.exp 1) ^ 2 * tau ^ 2 * d) * lambda))
    calc
      (∫ p, (W p) ^ r ∂P) <= ∫ p, c * (J p) ^ r ∂P :=
        integral_mono hWrInt hmajorInt hpoint
      _ = c * (∫ p, (J p) ^ r ∂P) := by rw [integral_const_mul]
      _ <= c * ((r / lambda) ^ r *
          Real.exp ((64 * (Real.exp 1) ^ 2 * tau ^ 2 * d) * lambda)) :=
        mul_le_mul_of_nonneg_left hJrBoundP hc0

/-- Root form of the compensator moment estimate. -/
theorem finiteGaussianVRec_rpow_root_le
    (hn : 0 < n) (delta tau lambda r : Real)
    (hdelta : 0 <= delta) (hlambda : 0 < lambda) (hr : 0 < r)
    (hhorizon : (n : Real) * delta = tau)
    (hEuler : V.L * tau <= 1)
    (hsmall : 64 * (Real.exp 1) ^ 2 * lambda * tau ^ 2 <= 1) :
    ((∫ x : State d × (Fin n -> State d),
      (finiteGaussianVRec V delta x.1 x.1 x.2) ^ r
      ∂(V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) ^ (1 / r)) <=
      (V.L ^ 2 / 2) * (r / lambda) *
        Real.exp
          ((64 * (Real.exp 1) ^ 2 * tau ^ 2 * d) * lambda / r) := by
  let P : Measure (State d × (Fin n -> State d)) :=
    (V.target : Measure (State d)).prod
      (Measure.pi (fun _ : Fin n => stdGaussian (State d)))
  let W : State d × (Fin n -> State d) -> Real := fun x =>
    finiteGaussianVRec V delta x.1 x.1 x.2
  let a : Real := V.L ^ 2 / 2
  let b : Real := r / lambda
  let z : Real := (64 * (Real.exp 1) ^ 2 * tau ^ 2 * d) * lambda
  obtain ⟨hInt, hBound⟩ :=
    finiteGaussianVRec_rpow_integrable_and_integral_le
      V hn delta tau lambda r hdelta hlambda hr hhorizon hEuler hsmall
  have hBoundP : (∫ x, (W x) ^ r ∂P) <= a ^ r * (b ^ r * Real.exp z) := by
    simpa only [P, W, a, b, z] using hBound
  have hW0 : forall x, 0 <= W x := fun x =>
    finiteGaussianVRec_nonneg V delta hdelta x.1 x.1 x.2
  have hI0 : 0 <= ∫ x, (W x) ^ r ∂P :=
    integral_nonneg_of_ae (ae_of_all _ fun x => Real.rpow_nonneg (hW0 x) r)
  have ha0 : 0 <= a := by dsimp [a]; positivity
  have hb0 : 0 <= b := (div_pos hr hlambda).le
  have hroot := Real.rpow_le_rpow hI0 hBoundP (by positivity : 0 <= 1 / r)
  have haroot : (a ^ r) ^ (1 / r) = a := by
    rw [<- Real.rpow_mul ha0]
    rw [show r * (1 / r) = 1 by field_simp, Real.rpow_one]
  have hbroot : (b ^ r) ^ (1 / r) = b := by
    rw [<- Real.rpow_mul hb0]
    rw [show r * (1 / r) = 1 by field_simp, Real.rpow_one]
  have hzroot : (Real.exp z) ^ (1 / r) = Real.exp (z / r) := by
    rw [<- Real.exp_mul]
    congr 1
    ring
  change (∫ x, (W x) ^ r ∂P) ^ (1 / r) <=
    a * b * Real.exp (z / r)
  calc
    (∫ x, (W x) ^ r ∂P) ^ (1 / r) <=
        (a ^ r * (b ^ r * Real.exp z)) ^ (1 / r) := hroot
    _ = a * b * Real.exp (z / r) := by
      rw [Real.mul_rpow (Real.rpow_nonneg ha0 r)
          (mul_nonneg (Real.rpow_nonneg hb0 r) (Real.exp_nonneg _)),
        Real.mul_rpow (Real.rpow_nonneg hb0 r) (Real.exp_nonneg _),
        haroot, hbroot, hzroot]
      ring

/-- Scalar Cauchy--Schwarz assembly for the centered likelihood.  The three
inputs are exactly the `2p` moments of `D`, `M`, and `V`.  The factor four
comes from two uses of the elementary powered-sum estimate, in place of a
general real-`Lp` Minkowski theorem. -/
theorem finiteGaussianDRec_centered_rpow_root_le_of_moments
    (delta p : Real) (hdelta : 0 <= delta) (hp : 1 <= p)
    (hD : Integrable (fun x : State d × (Fin n -> State d) =>
      (finiteGaussianDRec V 1 delta x.1 x.1 x.2) ^ (2 * p))
      ((V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))))
    (hM : Integrable (fun x : State d × (Fin n -> State d) =>
      |finiteGaussianMRec V delta x.1 x.1 x.2| ^ (2 * p))
      ((V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))))
    (hW : Integrable (fun x : State d × (Fin n -> State d) =>
      (finiteGaussianVRec V delta x.1 x.1 x.2) ^ (2 * p))
      ((V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d))))) :
    Integrable (fun x : State d × (Fin n -> State d) =>
      |finiteGaussianDRec V 1 delta x.1 x.1 x.2 - 1| ^ p)
      ((V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) /\
    ((∫ x : State d × (Fin n -> State d),
      |finiteGaussianDRec V 1 delta x.1 x.1 x.2 - 1| ^ p
      ∂(V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) ^ (1 / p)) <=
      4 *
        (1 + ((∫ x : State d × (Fin n -> State d),
          (finiteGaussianDRec V 1 delta x.1 x.1 x.2) ^ (2 * p)
          ∂(V.target : Measure (State d)).prod
            (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) ^
              (1 / (2 * p)))) *
        (((∫ x : State d × (Fin n -> State d),
          |finiteGaussianMRec V delta x.1 x.1 x.2| ^ (2 * p)
          ∂(V.target : Measure (State d)).prod
            (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) ^
              (1 / (2 * p))) +
         ((∫ x : State d × (Fin n -> State d),
          (finiteGaussianVRec V delta x.1 x.1 x.2) ^ (2 * p)
          ∂(V.target : Measure (State d)).prod
            (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) ^
              (1 / (2 * p)))) := by
  let P : Measure (State d × (Fin n -> State d)) :=
    (V.target : Measure (State d)).prod
      (Measure.pi (fun _ : Fin n => stdGaussian (State d)))
  let D : State d × (Fin n -> State d) -> Real := fun x =>
    finiteGaussianDRec V 1 delta x.1 x.1 x.2
  let M : State d × (Fin n -> State d) -> Real := fun x =>
    finiteGaussianMRec V delta x.1 x.1 x.2
  let W : State d × (Fin n -> State d) -> Real := fun x =>
    finiteGaussianVRec V delta x.1 x.1 x.2
  let r : Real := 2 * p
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hr : 1 <= r := by dsimp [r]; nlinarith
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hD0 : forall x, 0 <= D x := by
    intro x
    dsimp [D]
    unfold finiteGaussianDRec
    exact (Real.exp_pos _).le
  have hW0 : forall x, 0 <= W x := by
    intro x
    exact finiteGaussianVRec_nonneg V delta hdelta x.1 x.1 x.2
  have hDMeas : Measurable D := by
    simpa only [D] using
      measurable_finiteGaussianDRec_initial V 1 delta hdelta n
  have hMMeas : Measurable M := by
    simpa only [M] using
      measurable_finiteGaussianMRec_initial_of_nonneg V delta hdelta n
  have hWMeas : Measurable W := by
    simpa only [W] using measurable_finiteGaussianVRec_initial V delta n
  have hDP : Integrable (fun x => (D x) ^ r) P := by
    simpa only [P, D, r] using hD
  have hMP : Integrable (fun x => |M x| ^ r) P := by
    simpa only [P, M, r] using hM
  have hWP : Integrable (fun x => (W x) ^ r) P := by
    simpa only [P, W, r] using hW
  obtain ⟨hFInt, hFroot⟩ := integral_add_rpow_root_le_two P
    (fun _ => 1) D hr (fun _ => zero_le_one) hD0 measurable_const hDMeas
    (by simpa using (integrable_const (1 : Real) :
      Integrable (fun _ : State d × (Fin n -> State d) => (1 : Real)) P)) hDP
  have hFroot' :
      (∫ x, (1 + D x) ^ r ∂P) ^ (1 / r) <=
        2 * (1 + (∫ x, (D x) ^ r ∂P) ^ (1 / r)) := by
    simpa using hFroot
  obtain ⟨hGInt, hGroot⟩ := integral_add_rpow_root_le_two P
    (fun x => |M x|) W hr (fun x => abs_nonneg (M x)) hW0
    hMMeas.abs hWMeas hMP hWP
  let f : State d × (Fin n -> State d) -> Real := fun x =>
    (1 + D x) ^ p
  let g : State d × (Fin n -> State d) -> Real := fun x =>
    (|M x| + W x) ^ p
  have hf0 : forall x, 0 <= f x := fun x =>
    Real.rpow_nonneg (add_nonneg zero_le_one (hD0 x)) p
  have hg0 : forall x, 0 <= g x := fun x =>
    Real.rpow_nonneg (add_nonneg (abs_nonneg _) (hW0 x)) p
  have hfMeas : Measurable f :=
    (Real.continuous_rpow_const hp0.le).measurable.comp
      (measurable_const.add hDMeas)
  have hgMeas : Measurable g :=
    (Real.continuous_rpow_const hp0.le).measurable.comp
      (hMMeas.abs.add hWMeas)
  have hfSq : (fun x => (f x) ^ 2) = fun x => (1 + D x) ^ r := by
    funext x
    dsimp [f, r]
    rw [<- Real.rpow_two, <- Real.rpow_mul (add_nonneg zero_le_one (hD0 x))]
    congr 1
    ring
  have hgSq : (fun x => (g x) ^ 2) = fun x => (|M x| + W x) ^ r := by
    funext x
    dsimp [g, r]
    rw [<- Real.rpow_two,
      <- Real.rpow_mul (add_nonneg (abs_nonneg (M x)) (hW0 x))]
    congr 1
    ring
  have hfSqR : (fun x => (f x) ^ (2 : Real)) =
      fun x => (1 + D x) ^ r := by
    funext x
    dsimp [f, r]
    rw [<- Real.rpow_mul (add_nonneg zero_le_one (hD0 x))]
    congr 1
    ring
  have hgSqR : (fun x => (g x) ^ (2 : Real)) =
      fun x => (|M x| + W x) ^ r := by
    funext x
    dsimp [g, r]
    rw [<- Real.rpow_mul (add_nonneg (abs_nonneg (M x)) (hW0 x))]
    congr 1
    ring
  have hfMem : MemLp f 2 P :=
    (memLp_two_iff_integrable_sq hfMeas.aestronglyMeasurable).2 (by
      rw [hfSq]
      exact hFInt)
  have hgMem : MemLp g 2 P :=
    (memLp_two_iff_integrable_sq hgMeas.aestronglyMeasurable).2 (by
      rw [hgSq]
      exact hGInt)
  have hfgInt : Integrable (fun x => f x * g x) P := by
    change Integrable (f * g) P
    exact hfMem.integrable_mul hgMem
  have hcenterPoint : forall x, |D x - 1| ^ p <= f x * g x := by
    intro x
    have hDexp : D x = Real.exp (M x - W x / 2) := by
      dsimp [D, M, W]
      unfold finiteGaussianDRec
      ring_nf
    have hbase : |D x - 1| <= (1 + D x) * (|M x| + W x) := by
      rw [hDexp]
      calc
        |Real.exp (M x - W x / 2) - 1| <=
            (1 + Real.exp (M x - W x / 2)) * |M x - W x / 2| :=
          abs_exp_sub_one_le_one_add_exp_mul_abs _
        _ <= (1 + Real.exp (M x - W x / 2)) * (|M x| + W x) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc
            |M x - W x / 2| <= |M x| + |W x / 2| := abs_sub _ _
            _ <= |M x| + W x := by
              rw [abs_of_nonneg (div_nonneg (hW0 x) (by norm_num))]
              linarith [hW0 x]
    calc
      |D x - 1| ^ p <= ((1 + D x) * (|M x| + W x)) ^ p :=
        Real.rpow_le_rpow (abs_nonneg _) hbase hp0.le
      _ = f x * g x := by
        dsimp [f, g]
        rw [Real.mul_rpow (add_nonneg zero_le_one (hD0 x))
          (add_nonneg (abs_nonneg _) (hW0 x))]
  have hcenterMeas : Measurable (fun x => |D x - 1| ^ p) :=
    (Real.continuous_rpow_const hp0.le).measurable.comp
      ((hDMeas.sub measurable_const).abs)
  have hcenterInt : Integrable (fun x => |D x - 1| ^ p) P := by
    apply integrable_of_le_of_le hcenterMeas.aestronglyMeasurable
      (ae_of_all _ fun x => Real.rpow_nonneg (abs_nonneg _) p)
      (ae_of_all _ hcenterPoint) (integrable_zero _ Real P) hfgInt
  have hfMem' : MemLp f (ENNReal.ofReal (2 : Real)) P := by
    norm_num
    exact hfMem
  have hgMem' : MemLp g (ENNReal.ofReal (2 : Real)) P := by
    norm_num
    exact hgMem
  have hCS0 := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := P) (p := 2) (q := 2) Real.HolderConjugate.two_two
    (ae_of_all _ hf0) (ae_of_all _ hg0) hfMem' hgMem'
  have hCS : (∫ x, f x * g x ∂P) <=
      (∫ x, (1 + D x) ^ r ∂P) ^ (1 / 2 : Real) *
        (∫ x, (|M x| + W x) ^ r ∂P) ^ (1 / 2 : Real) := by
    have hfIntEq : (∫ x, f x ^ (2 : Real) ∂P) =
        ∫ x, (1 + D x) ^ r ∂P := by
      exact integral_congr_ae (ae_of_all _ fun x => congrFun hfSqR x)
    have hgIntEq : (∫ x, g x ^ (2 : Real) ∂P) =
        ∫ x, (|M x| + W x) ^ r ∂P := by
      exact integral_congr_ae (ae_of_all _ fun x => congrFun hgSqR x)
    rw [hfIntEq, hgIntEq] at hCS0
    exact hCS0
  have hcenterBound : (∫ x, |D x - 1| ^ p ∂P) <=
      (∫ x, (1 + D x) ^ r ∂P) ^ (1 / 2 : Real) *
        (∫ x, (|M x| + W x) ^ r ∂P) ^ (1 / 2 : Real) :=
    (integral_mono hcenterInt hfgInt hcenterPoint).trans hCS
  have hcenter0 : 0 <= ∫ x, |D x - 1| ^ p ∂P :=
    integral_nonneg_of_ae (ae_of_all _ fun x =>
      Real.rpow_nonneg (abs_nonneg _) p)
  have hFI0 : 0 <= ∫ x, (1 + D x) ^ r ∂P :=
    integral_nonneg_of_ae (ae_of_all _ fun x =>
      Real.rpow_nonneg (add_nonneg zero_le_one (hD0 x)) r)
  have hGI0 : 0 <= ∫ x, (|M x| + W x) ^ r ∂P :=
    integral_nonneg_of_ae (ae_of_all _ fun x =>
      Real.rpow_nonneg (add_nonneg (abs_nonneg _) (hW0 x)) r)
  have hDI0 : 0 <= ∫ x, (D x) ^ r ∂P :=
    integral_nonneg_of_ae (ae_of_all _ fun x => Real.rpow_nonneg (hD0 x) r)
  have hroot := Real.rpow_le_rpow hcenter0 hcenterBound
    (by positivity : 0 <= 1 / p)
  have hrootProduct :
      (((∫ x, (1 + D x) ^ r ∂P) ^ (1 / 2 : Real) *
          (∫ x, (|M x| + W x) ^ r ∂P) ^ (1 / 2 : Real)) ^ (1 / p)) =
        (∫ x, (1 + D x) ^ r ∂P) ^ (1 / r) *
          (∫ x, (|M x| + W x) ^ r ∂P) ^ (1 / r) := by
    calc
      (((∫ x, (1 + D x) ^ r ∂P) ^ ((1 / 2 : Real)) *
          (∫ x, (|M x| + W x) ^ r ∂P) ^ ((1 / 2 : Real))) ^ (1 / p)) =
          ((∫ x, (1 + D x) ^ r ∂P) ^ ((1 / 2 : Real))) ^ (1 / p) *
            ((∫ x, (|M x| + W x) ^ r ∂P) ^ ((1 / 2 : Real))) ^ (1 / p) :=
        Real.mul_rpow (Real.rpow_nonneg hFI0 _) (Real.rpow_nonneg hGI0 _)
      _ = (∫ x, (1 + D x) ^ r ∂P) ^ (1 / r) *
          (∫ x, (|M x| + W x) ^ r ∂P) ^ (1 / r) := by
        rw [<- Real.rpow_mul hFI0, <- Real.rpow_mul hGI0]
        congr 2 <;> dsimp [r] <;> field_simp
  constructor
  · simpa only [P, D] using hcenterInt
  · change (∫ x, |D x - 1| ^ p ∂P) ^ (1 / p) <= _
    calc
      (∫ x, |D x - 1| ^ p ∂P) ^ (1 / p) <=
          (((∫ x, (1 + D x) ^ r ∂P) ^ (1 / 2 : Real) *
            (∫ x, (|M x| + W x) ^ r ∂P) ^ (1 / 2 : Real)) ^ (1 / p)) :=
        hroot
      _ = (∫ x, (1 + D x) ^ r ∂P) ^ (1 / r) *
          (∫ x, (|M x| + W x) ^ r ∂P) ^ (1 / r) := hrootProduct
      _ <= (2 * (1 + (∫ x, (D x) ^ r ∂P) ^ (1 / r))) *
          (2 * ((∫ x, |M x| ^ r ∂P) ^ (1 / r) +
            (∫ x, (W x) ^ r ∂P) ^ (1 / r))) := by
        apply mul_le_mul hFroot' hGroot
        · exact Real.rpow_nonneg hGI0 _
        · positivity
      _ = 4 * (1 + (∫ x, (D x) ^ r ∂P) ^ (1 / r)) *
          ((∫ x, |M x| ^ r ∂P) ^ (1 / r) +
            (∫ x, (W x) ^ r ∂P) ^ (1 / r)) := by ring
      _ = _ := by rfl

set_option maxHeartbeats 800000 in
/-- Paper-scale centered likelihood moment.  The scalar hypothesis is the
squared form of `L*tau*sqrt(p*(d+p)) <= 1/(16e)`.  Constants are kept
deliberately generous so that the proof consists only of monotonicity and
polynomial arithmetic after the three moment checkpoints above. -/
theorem finiteGaussianDRec_centered_rpow_root_le_paper_scale
    (hn : 0 < n) (hd : 0 < d) (delta tau p : Real)
    (hdelta : 0 <= delta) (htau : 0 < tau) (hp : 1 <= p)
    (hhorizon : (n : Real) * delta = tau)
    (hEuler : V.L * tau <= 1)
    (hsmall :
      256 * (Real.exp 1) ^ 2 * V.L ^ 2 * tau ^ 2 *
        (p * ((d : Real) + p)) <= 1) :
    Integrable (fun x : State d × (Fin n -> State d) =>
      |finiteGaussianDRec V 1 delta x.1 x.1 x.2 - 1| ^ p)
      ((V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) /\
    ((∫ x : State d × (Fin n -> State d),
      |finiteGaussianDRec V 1 delta x.1 x.1 x.2 - 1| ^ p
      ∂(V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) ^ (1 / p)) <=
      1024 * (Real.exp 1) ^ 3 * V.L * tau *
        Real.sqrt (p * ((d : Real) + p)) := by
  let P : Measure (State d × (Fin n -> State d)) :=
    (V.target : Measure (State d)).prod
      (Measure.pi (fun _ : Fin n => stdGaussian (State d)))
  let D : State d × (Fin n -> State d) -> Real := fun x =>
    finiteGaussianDRec V 1 delta x.1 x.1 x.2
  let M : State d × (Fin n -> State d) -> Real := fun x =>
    finiteGaussianMRec V delta x.1 x.1 x.2
  let W : State d × (Fin n -> State d) -> Real := fun x =>
    finiteGaussianVRec V delta x.1 x.1 x.2
  let r : Real := 2 * p
  let S : Real := V.L * tau * Real.sqrt (p * ((d : Real) + p))
  let s0 : Real := 1 / (8 * Real.exp 1 * V.L * tau)
  let lambda : Real :=
    p / (64 * (Real.exp 1) ^ 2 * tau ^ 2 * ((d : Real) + p))
  have hdR : (0 : Real) < d := by exact_mod_cast hd
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hdp : 0 < p * ((d : Real) + p) := by positivity
  have hsqrt : 0 < Real.sqrt (p * ((d : Real) + p)) := Real.sqrt_pos.2 hdp
  have hsqrtSq : (Real.sqrt (p * ((d : Real) + p))) ^ 2 =
      p * ((d : Real) + p) := Real.sq_sqrt hdp.le
  have hS : 0 < S := by
    dsimp [S]
    exact mul_pos (mul_pos V.hL htau) hsqrt
  have hsmallS : 256 * (Real.exp 1) ^ 2 * S ^ 2 <= 1 := by
    dsimp [S]
    rw [mul_pow, mul_pow, hsqrtSq]
    simpa only [mul_assoc] using hsmall
  have heOne : 1 <= Real.exp 1 := Real.one_le_exp (by norm_num)
  have hscaledS : 16 * Real.exp 1 * S <= 1 := by
    have hsquare : (16 * Real.exp 1 * S) ^ 2 <= 1 := by
      calc
        (16 * Real.exp 1 * S) ^ 2 =
            256 * (Real.exp 1) ^ 2 * S ^ 2 := by ring
        _ <= 1 := hsmallS
    have hnonneg : 0 <= 16 * Real.exp 1 * S := by positivity
    nlinarith
  have hSle : S <= 1 := by
    have hcoef : 1 <= 16 * Real.exp 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hcoef hS.le]
  have hs0 : 0 < s0 := by
    dsimp [s0]
    apply one_div_pos.mpr
    exact mul_pos (mul_pos (by positivity) V.hL) htau
  have hlambda : 0 < lambda := by dsimp [lambda]; positivity
  have hr : 1 <= r := by dsimp [r]; nlinarith
  have hr0 : 0 < r := zero_lt_one.trans_le hr

  have hpSqLe : p ^ 2 <= p * ((d : Real) + p) := by nlinarith
  have hDsmall :
      256 * (Real.exp 1) ^ 2 * p ^ 2 * V.L ^ 2 * tau ^ 2 <= 1 := by
    calc
      256 * (Real.exp 1) ^ 2 * p ^ 2 * V.L ^ 2 * tau ^ 2 <=
          256 * (Real.exp 1) ^ 2 * (p * ((d : Real) + p)) *
            V.L ^ 2 * tau ^ 2 := by gcongr
      _ = 256 * (Real.exp 1) ^ 2 * V.L ^ 2 * tau ^ 2 *
          (p * ((d : Real) + p)) := by ring
      _ <= 1 := hsmall
  have hDroot := finiteGaussianDRec_two_p_root_le
    V hn delta tau p hdelta hp hhorizon hEuler hDsmall
  have hDexpLe :
      128 * (Real.exp 1) ^ 2 * V.L ^ 2 * tau ^ 2 * d * p <= 1 := by
    have hdpLe : (d : Real) * p <= p * ((d : Real) + p) := by nlinarith
    have hc0 : 0 <= 128 * (Real.exp 1) ^ 2 * V.L ^ 2 * tau ^ 2 := by
      positivity
    calc
      128 * (Real.exp 1) ^ 2 * V.L ^ 2 * tau ^ 2 * d * p =
          (128 * (Real.exp 1) ^ 2 * V.L ^ 2 * tau ^ 2) *
            ((d : Real) * p) := by ring
      _ <= (128 * (Real.exp 1) ^ 2 * V.L ^ 2 * tau ^ 2) *
          (p * ((d : Real) + p)) :=
        mul_le_mul_of_nonneg_left hdpLe hc0
      _ <= 256 * (Real.exp 1) ^ 2 * V.L ^ 2 * tau ^ 2 *
          (p * ((d : Real) + p)) := by
        have htail : 0 <= p * ((d : Real) + p) := hdp.le
        nlinarith [mul_nonneg hc0 htail]
      _ <= 1 := hsmall
  have hDrootSimple : (∫ x, (D x) ^ r ∂P) ^ (1 / r) <=
      Real.exp 1 := by
    have hrootP : (∫ x, (D x) ^ r ∂P) ^ (1 / r) <=
        Real.exp
          (128 * (Real.exp 1) ^ 2 * V.L ^ 2 * tau ^ 2 * d * p) := by
      simpa only [P, D, r] using hDroot
    exact hrootP.trans (Real.exp_le_exp.mpr hDexpLe)

  have hMsmall :
      64 * (Real.exp 1) ^ 2 * (s0 ^ 2 * V.L ^ 2) * tau ^ 2 <= 1 := by
    dsimp [s0]
    field_simp [V.hL.ne', htau.ne', Real.exp_ne_zero]
    norm_num
  have hmgf : TwoSidedMGFBound P M 1
      (64 * (Real.exp 1) ^ 2 * V.L ^ 2 * tau ^ 2 * d) s0 := by
    simpa only [P, M] using finiteGaussianMRec_twoSidedMGFBound
      V hn delta tau s0 hdelta hs0.le hhorizon hEuler hMsmall
  obtain ⟨hMInt, _hMraw⟩ :=
    hmgf.rpow_moment_integrable_and_integral_le hr0 hs0 le_rfl
  have hMroot := finiteGaussianMRec_realMomentRoot_le
    V hn hd delta tau s0 r hdelta htau hs0 hr hhorizon hEuler hMsmall
  have hpLeSqrt : p <= Real.sqrt (p * ((d : Real) + p)) := by
    exact (Real.le_sqrt hp0.le hdp.le).2 hpSqLe
  have hsqrtTerm :
      Real.sqrt
        ((64 * (Real.exp 1) ^ 2 * V.L ^ 2 * tau ^ 2 * d) * r) <=
      12 * Real.exp 1 * S := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hnum : 128 * (d : Real) * p <=
          144 * (p * ((d : Real) + p)) := by nlinarith
      have hc : 0 <= (Real.exp 1) ^ 2 * V.L ^ 2 * tau ^ 2 := by positivity
      calc
        (64 * (Real.exp 1) ^ 2 * V.L ^ 2 * tau ^ 2 * d) * r =
            ((Real.exp 1) ^ 2 * V.L ^ 2 * tau ^ 2) *
              (128 * (d : Real) * p) := by dsimp [r]; ring
        _ <= ((Real.exp 1) ^ 2 * V.L ^ 2 * tau ^ 2) *
            (144 * (p * ((d : Real) + p))) :=
          mul_le_mul_of_nonneg_left hnum hc
        _ = (12 * Real.exp 1 * S) ^ 2 := by
          dsimp [S]
          rw [mul_pow, mul_pow, mul_pow, hsqrtSq]
          ring
  have hrOver : r / s0 <= 16 * Real.exp 1 * S := by
    have hmulp := mul_le_mul_of_nonneg_left hpLeSqrt
      (mul_nonneg V.hL.le htau.le)
    dsimp [r, s0, S]
    field_simp [V.hL.ne', htau.ne', Real.exp_ne_zero]
    nlinarith
  have hMrootSimple : (∫ x, |M x| ^ r ∂P) ^ (1 / r) <=
      64 * (Real.exp 1) ^ 2 * S := by
    have hrootP : (∫ x, |M x| ^ r ∂P) ^ (1 / r) <=
        2 * Real.exp 1 *
          (Real.sqrt
            ((64 * (Real.exp 1) ^ 2 * V.L ^ 2 * tau ^ 2 * d) * r) +
            r / s0) := by
      simpa only [P, M, TwoSidedMGFBound.realMomentRoot] using hMroot
    calc
      (∫ x, |M x| ^ r ∂P) ^ (1 / r) <= _ := hrootP
      _ <= 2 * Real.exp 1 *
          (12 * Real.exp 1 * S + 16 * Real.exp 1 * S) := by gcongr
      _ <= 64 * (Real.exp 1) ^ 2 * S := by
        have hnonneg : 0 <= (Real.exp 1) ^ 2 * S :=
          mul_nonneg (sq_nonneg _) hS.le
        ring_nf
        gcongr
        norm_num

  have hVsmall : 64 * (Real.exp 1) ^ 2 * lambda * tau ^ 2 <= 1 := by
    dsimp [lambda]
    rw [show 64 * Real.exp 1 ^ 2 *
        (p / (64 * Real.exp 1 ^ 2 * tau ^ 2 * ((d : Real) + p))) *
          tau ^ 2 = p / ((d : Real) + p) by field_simp]
    exact (div_le_one (by positivity)).2 (by linarith)
  obtain ⟨hWInt, _hWraw⟩ := finiteGaussianVRec_rpow_integrable_and_integral_le
    V hn delta tau lambda r hdelta hlambda hr0 hhorizon hEuler hVsmall
  have hWroot := finiteGaussianVRec_rpow_root_le
    V hn delta tau lambda r hdelta hlambda hr0 hhorizon hEuler hVsmall
  have hVexp :
      (64 * (Real.exp 1) ^ 2 * tau ^ 2 * d) * lambda / r <= 1 := by
    dsimp [lambda, r]
    rw [show (64 * Real.exp 1 ^ 2 * tau ^ 2 * (d : Real)) *
        (p / (64 * Real.exp 1 ^ 2 * tau ^ 2 * ((d : Real) + p))) /
          (2 * p) = (d : Real) / (2 * ((d : Real) + p)) by field_simp]
    exact (div_le_one (by positivity)).2 (by linarith)
  have hVprefactor : (V.L ^ 2 / 2) * (r / lambda) =
      64 * (Real.exp 1) ^ 2 * V.L ^ 2 * tau ^ 2 * ((d : Real) + p) := by
    dsimp [r, lambda]
    field_simp
  have henergyScale : V.L ^ 2 * tau ^ 2 * ((d : Real) + p) <=
      S / (16 * Real.exp 1) := by
    have hident : V.L ^ 2 * tau ^ 2 * ((d : Real) + p) = S ^ 2 / p := by
      dsimp [S]
      rw [mul_pow, mul_pow, hsqrtSq]
      field_simp
    rw [hident]
    rw [div_le_div_iff₀ hp0 (by positivity : 0 < 16 * Real.exp 1)]
    have hscaled := mul_le_mul_of_nonneg_left hscaledS hS.le
    have hpScaled := mul_le_mul_of_nonneg_left hp hS.le
    calc
      S ^ 2 * (16 * Real.exp 1) = S * (16 * Real.exp 1 * S) := by ring
      _ <= S * 1 := hscaled
      _ <= S * p := hpScaled
  have hWrootSimple : (∫ x, (W x) ^ r ∂P) ^ (1 / r) <=
      4 * (Real.exp 1) ^ 2 * S := by
    have hrootP : (∫ x, (W x) ^ r ∂P) ^ (1 / r) <=
        (V.L ^ 2 / 2) * (r / lambda) *
          Real.exp
            ((64 * (Real.exp 1) ^ 2 * tau ^ 2 * d) * lambda / r) := by
      simpa only [P, W] using hWroot
    calc
      (∫ x, (W x) ^ r ∂P) ^ (1 / r) <= _ := hrootP
      _ <= (64 * (Real.exp 1) ^ 2 * V.L ^ 2 * tau ^ 2 *
          ((d : Real) + p)) * Real.exp 1 := by
        rw [hVprefactor]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hVexp) (by positivity)
      _ <= 4 * (Real.exp 1) ^ 2 * S := by
        have hc : 0 <= 64 * (Real.exp 1) ^ 2 := by positivity
        have he0 : 0 <= Real.exp 1 := (Real.exp_pos 1).le
        have hmul := mul_le_mul_of_nonneg_left henergyScale hc
        calc
          (64 * (Real.exp 1) ^ 2 * V.L ^ 2 * tau ^ 2 *
              ((d : Real) + p)) * Real.exp 1 =
              (64 * (Real.exp 1) ^ 2) *
                (V.L ^ 2 * tau ^ 2 * ((d : Real) + p)) * Real.exp 1 := by ring
          _ <= (64 * (Real.exp 1) ^ 2) *
              (S / (16 * Real.exp 1)) * Real.exp 1 :=
            mul_le_mul_of_nonneg_right hmul he0
          _ = 4 * (Real.exp 1) ^ 2 * S := by
            field_simp [Real.exp_ne_zero]
            ring

  have hDInt : Integrable (fun x => (D x) ^ r) P := by
    let q : Real := r
    let lambdaD : Real := (2 * q ^ 2 - q) * V.L ^ 2 / 2
    have hq : 1 <= q := by simpa only [q] using hr
    have hlambdaD : lambdaD <= 4 * p ^ 2 * V.L ^ 2 := by
      dsimp [lambdaD, q, r]
      calc
        (2 * (2 * p) ^ 2 - 2 * p) * V.L ^ 2 / 2 =
            (4 * p ^ 2 - p) * V.L ^ 2 := by ring
        _ <= 4 * p ^ 2 * V.L ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg V.L)
          nlinarith
    have hsmallD : 64 * (Real.exp 1) ^ 2 * lambdaD * tau ^ 2 <= 1 := by
      calc
        64 * (Real.exp 1) ^ 2 * lambdaD * tau ^ 2 <=
            64 * (Real.exp 1) ^ 2 * (4 * p ^ 2 * V.L ^ 2) * tau ^ 2 := by
          gcongr
        _ = 256 * (Real.exp 1) ^ 2 * p ^ 2 * V.L ^ 2 * tau ^ 2 := by ring
        _ <= 1 := hDsmall
    exact (finiteGaussianDRec_rpow_integrable_and_integral_le
      V hn delta tau q hdelta hq hhorizon hEuler hsmallD).1
  obtain ⟨hcenterInt, hcenterRoot⟩ :=
    finiteGaussianDRec_centered_rpow_root_le_of_moments
      V delta p hdelta hp (by simpa only [P, D, r] using hDInt)
        (by simpa only [P, M, r] using hMInt)
        (by simpa only [P, W, r] using hWInt)
  constructor
  · exact hcenterInt
  · have hcombined :
        4 * (1 + (∫ x, (D x) ^ r ∂P) ^ (1 / r)) *
          ((∫ x, |M x| ^ r ∂P) ^ (1 / r) +
            (∫ x, (W x) ^ r ∂P) ^ (1 / r)) <=
        1024 * (Real.exp 1) ^ 3 * S := by
      have hMintNonneg : 0 <= ∫ x, |M x| ^ r ∂P :=
        integral_nonneg (fun x => Real.rpow_nonneg (abs_nonneg (M x)) r)
      have hMnonneg : 0 <= (∫ x, |M x| ^ r ∂P) ^ (1 / r) :=
        Real.rpow_nonneg hMintNonneg _
      have hWintNonneg : 0 <= ∫ x, (W x) ^ r ∂P :=
        integral_nonneg (fun x => Real.rpow_nonneg
          (by
            dsimp [W]
            exact finiteGaussianVRec_nonneg V delta hdelta x.1 x.1 x.2) r)
      have hWnonneg : 0 <= (∫ x, (W x) ^ r ∂P) ^ (1 / r) :=
        Real.rpow_nonneg hWintNonneg _
      have hsumNonneg : 0 <=
          (∫ x, |M x| ^ r ∂P) ^ (1 / r) +
            (∫ x, (W x) ^ r ∂P) ^ (1 / r) :=
        add_nonneg hMnonneg hWnonneg
      have hfac :
          4 * (1 + (∫ x, (D x) ^ r ∂P) ^ (1 / r)) <=
            4 * (1 + Real.exp 1) := by gcongr
      have hsum :
          (∫ x, |M x| ^ r ∂P) ^ (1 / r) +
              (∫ x, (W x) ^ r ∂P) ^ (1 / r) <=
            64 * (Real.exp 1) ^ 2 * S + 4 * (Real.exp 1) ^ 2 * S :=
        add_le_add hMrootSimple hWrootSimple
      have hcoefNonneg : 0 <= 4 * (1 + Real.exp 1) := by positivity
      calc
        _ <= 4 * (1 + Real.exp 1) *
            ((∫ x, |M x| ^ r ∂P) ^ (1 / r) +
              (∫ x, (W x) ^ r ∂P) ^ (1 / r)) :=
          mul_le_mul_of_nonneg_right hfac hsumNonneg
        _ <= 4 * (1 + Real.exp 1) *
            (64 * (Real.exp 1) ^ 2 * S +
              4 * (Real.exp 1) ^ 2 * S) :=
          mul_le_mul_of_nonneg_left hsum hcoefNonneg
        _ <= 1024 * (Real.exp 1) ^ 3 * S := by
          have honeAdd : 1 + Real.exp 1 <= 2 * Real.exp 1 := by
            linarith
          calc
            _ <= 4 * (2 * Real.exp 1) *
                (64 * (Real.exp 1) ^ 2 * S +
                  4 * (Real.exp 1) ^ 2 * S) := by gcongr
            _ = 544 * (Real.exp 1) ^ 3 * S := by ring
            _ <= 1024 * (Real.exp 1) ^ 3 * S := by
              gcongr
              norm_num
    have hrootP : (∫ x, |D x - 1| ^ p ∂P) ^ (1 / p) <=
        4 * (1 + (∫ x, (D x) ^ r ∂P) ^ (1 / r)) *
          ((∫ x, |M x| ^ r ∂P) ^ (1 / r) +
            (∫ x, (W x) ^ r ∂P) ^ (1 / r)) := by
      simpa only [P, D, M, W, r] using hcenterRoot
    exact hrootP.trans (by simpa only [S, mul_assoc] using hcombined)

end DiscreteTime

end

end UniformRandomMALA
