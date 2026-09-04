import UniformRandomMALA.Prelude
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Elementary consequences of a two-sided MGF estimate

This file packages the probability estimates needed in the finite likelihood
argument.  The proofs use only restricted Bochner integrals, monotonicity, and
elementary real inequalities.  In particular, they do not use filtrations,
conditional expectations, martingales, or a layer-cake representation.
-/

namespace UniformRandomMALA

open MeasureTheory

noncomputable section

namespace DiscreteTime

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Elementary pointwise substitute for layer-cake integration.  The constant
is intentionally slightly looser than the optimal factor `Real.exp 1`: the
inequality `u <= exp u` makes the proof especially robust. -/
lemma rpow_le_scale_rpow_mul_exp {x r s : Real}
    (hx : 0 <= x) (hr : 0 < r) (hs : 0 < s) :
    x ^ r <= (r / s) ^ r * Real.exp (s * x) := by
  let u : Real := s * x / r
  have hu0 : 0 <= u := by
    dsimp [u]
    positivity
  have hule : u <= Real.exp u :=
    (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp u)
  have hpow : u ^ r <= (Real.exp u) ^ r :=
    Real.rpow_le_rpow hu0 hule hr.le
  have hscale0 : 0 <= r / s := (div_pos hr hs).le
  have hscale : x = (r / s) * u := by
    dsimp [u]
    field_simp
  calc
    x ^ r = ((r / s) * u) ^ r := by rw [hscale]
    _ = (r / s) ^ r * u ^ r := Real.mul_rpow hscale0 hu0
    _ <= (r / s) ^ r * (Real.exp u) ^ r :=
      mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hscale0 r)
    _ = (r / s) ^ r * Real.exp (s * x) := by
      rw [<- Real.exp_mul]
      congr 2
      dsimp [u]
      field_simp

/-- The exponential of an absolute value is bounded by the sum of the two
one-sided exponentials. -/
lemma exp_mul_abs_le_exp_add_exp_neg (s x : Real) :
    Real.exp (s * |x|) <= Real.exp (s * x) + Real.exp (-s * x) := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact le_add_of_nonneg_right (Real.exp_nonneg _)
  · rw [abs_of_nonpos hx]
    have heq : s * -x = -s * x := by ring
    rw [heq]
    exact le_add_of_nonneg_left (Real.exp_nonneg _)

/-- A two-sided quadratic MGF estimate, including the integrability data which
is essential when the estimate is used with the Bochner integral. -/
structure TwoSidedMGFBound (mu : Measure Omega) (X : Omega -> Real)
    (A B s0 : Real) : Prop where
  measurable_X : Measurable X
  integrable_pos : forall s, 0 <= s -> s <= s0 ->
    Integrable (fun omega => Real.exp (s * X omega)) mu
  integrable_neg : forall s, 0 <= s -> s <= s0 ->
    Integrable (fun omega => Real.exp (-s * X omega)) mu
  integral_pos_le : forall s, 0 <= s -> s <= s0 ->
    (∫ omega, Real.exp (s * X omega) ∂mu) <=
      A * Real.exp (B * s ^ 2)
  integral_neg_le : forall s, 0 <= s -> s <= s0 ->
    (∫ omega, Real.exp (-s * X omega) ∂mu) <=
      A * Real.exp (B * s ^ 2)

namespace TwoSidedMGFBound

variable {mu : Measure Omega} [IsProbabilityMeasure mu]
  {X : Omega -> Real} {A B s0 : Real}

/-- The MGF estimate at zero forces its prefactor to be at least one. -/
lemma one_le_A (h : TwoSidedMGFBound mu X A B s0) (hs0 : 0 <= s0) :
    1 <= A := by
  have hzero := h.integral_pos_le 0 le_rfl hs0
  simpa using hzero

/-- Direct Chernoff bound for the upper tail at any admissible parameter. -/
lemma upper_tail_le (h : TwoSidedMGFBound mu X A B s0)
    {s t : Real} (hs : 0 < s) (hss0 : s <= s0) :
    mu.real {omega | t <= X omega} <=
      A * Real.exp (B * s ^ 2 - s * t) := by
  let S : Set Omega := {omega | t <= X omega}
  have hS : MeasurableSet S := measurableSet_le measurable_const h.measurable_X
  have hInt := h.integrable_pos s hs.le hss0
  have hMarkov :
      Real.exp (s * t) * mu.real S <=
        ∫ omega, Real.exp (s * X omega) ∂mu := by
    calc
      Real.exp (s * t) * mu.real S =
          ∫ _omega, Real.exp (s * t) ∂(mu.restrict S) := by
        simp [mul_comm]
      _ <= ∫ omega, Real.exp (s * X omega) ∂(mu.restrict S) := by
        apply integral_mono_ae (integrable_const _)
          (hInt.mono_measure Measure.restrict_le_self)
        filter_upwards [ae_restrict_mem hS] with omega homega
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left homega hs.le)
      _ <= ∫ omega, Real.exp (s * X omega) ∂mu :=
        integral_mono_measure Measure.restrict_le_self
          (ae_of_all _ fun omega => (Real.exp_pos (s * X omega)).le) hInt
  change mu.real S <= A * Real.exp (B * s ^ 2 - s * t)
  calc
    mu.real S <= (A * Real.exp (B * s ^ 2)) / Real.exp (s * t) := by
      apply (le_div_iff₀ (Real.exp_pos (s * t))).2
      simpa only [mul_comm] using
        hMarkov.trans (h.integral_pos_le s hs.le hss0)
    _ = A * Real.exp (B * s ^ 2 - s * t) := by
      rw [Real.exp_sub]
      ring

/-- Direct Chernoff bound for the lower tail at any admissible parameter. -/
lemma lower_tail_le (h : TwoSidedMGFBound mu X A B s0)
    {s t : Real} (hs : 0 < s) (hss0 : s <= s0) :
    mu.real {omega | X omega <= -t} <=
      A * Real.exp (B * s ^ 2 - s * t) := by
  let S : Set Omega := {omega | X omega <= -t}
  have hS : MeasurableSet S := measurableSet_le h.measurable_X measurable_const
  have hInt := h.integrable_neg s hs.le hss0
  have hMarkov :
      Real.exp (s * t) * mu.real S <=
        ∫ omega, Real.exp (-s * X omega) ∂mu := by
    calc
      Real.exp (s * t) * mu.real S =
          ∫ _omega, Real.exp (s * t) ∂(mu.restrict S) := by
        simp [mul_comm]
      _ <= ∫ omega, Real.exp (-s * X omega) ∂(mu.restrict S) := by
        apply integral_mono_ae (integrable_const _)
          (hInt.mono_measure Measure.restrict_le_self)
        filter_upwards [ae_restrict_mem hS] with omega homega
        apply Real.exp_le_exp.mpr
        change X omega <= -t at homega
        nlinarith
      _ <= ∫ omega, Real.exp (-s * X omega) ∂mu :=
        integral_mono_measure Measure.restrict_le_self
          (ae_of_all _ fun omega => (Real.exp_pos (-s * X omega)).le) hInt
  change mu.real S <= A * Real.exp (B * s ^ 2 - s * t)
  calc
    mu.real S <= (A * Real.exp (B * s ^ 2)) / Real.exp (s * t) := by
      apply (le_div_iff₀ (Real.exp_pos (s * t))).2
      simpa only [mul_comm] using
        hMarkov.trans (h.integral_neg_le s hs.le hss0)
    _ = A * Real.exp (B * s ^ 2 - s * t) := by
      rw [Real.exp_sub]
      ring

/-- Two-sided Chernoff bound, obtained by a literal union bound. -/
lemma abs_tail_le (h : TwoSidedMGFBound mu X A B s0)
    {s t : Real} (hs : 0 < s) (hss0 : s <= s0) :
    mu.real {omega | t <= |X omega|} <=
      2 * A * Real.exp (B * s ^ 2 - s * t) := by
  let U : Set Omega := {omega | t <= X omega}
  let L : Set Omega := {omega | X omega <= -t}
  have hsub : {omega | t <= |X omega|} <= U ∪ L := by
    intro omega homega
    change t <= |X omega| at homega
    change t <= X omega ∨ X omega <= -t
    rcases le_total 0 (X omega) with hx | hx
    · left
      simpa [abs_of_nonneg hx] using homega
    · right
      rw [abs_of_nonpos hx] at homega
      linarith
  calc
    mu.real {omega | t <= |X omega|} <= mu.real (U ∪ L) :=
      measureReal_mono hsub
    _ <= mu.real U + mu.real L := measureReal_union_le U L
    _ <= A * Real.exp (B * s ^ 2 - s * t) +
        A * Real.exp (B * s ^ 2 - s * t) := by
      gcongr
      · exact h.upper_tail_le hs hss0
      · exact h.lower_tail_le hs hss0
    _ = 2 * A * Real.exp (B * s ^ 2 - s * t) := by ring

/-- Gaussian part of the sub-gamma tail.  This is the choice
`s = t / (2 B)` in `abs_tail_le`. -/
lemma abs_tail_gaussian_regime_le
    (h : TwoSidedMGFBound mu X A B s0)
    {t : Real} (hB : 0 < B) (ht : 0 < t) (hreg : t <= 2 * B * s0) :
    mu.real {omega | t <= |X omega|} <=
      2 * A * Real.exp (-(t ^ 2 / (4 * B))) := by
  have hs : 0 < t / (2 * B) := div_pos ht (by positivity)
  have hss0 : t / (2 * B) <= s0 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * B)).2
    simpa [mul_assoc, mul_comm, mul_left_comm] using hreg
  calc
    mu.real {omega | t <= |X omega|} <=
        2 * A * Real.exp
          (B * (t / (2 * B)) ^ 2 - (t / (2 * B)) * t) :=
      h.abs_tail_le hs hss0
    _ = 2 * A * Real.exp (-(t ^ 2 / (4 * B))) := by
      congr 2
      field_simp
      ring

/-- Exponential part of the sub-gamma tail.  This is the endpoint choice
`s = s0` in `abs_tail_le`. -/
lemma abs_tail_exponential_regime_le
    (h : TwoSidedMGFBound mu X A B s0)
    {t : Real} (hs0 : 0 < s0) (hreg : 2 * B * s0 <= t) :
    mu.real {omega | t <= |X omega|} <=
      2 * A * Real.exp (-(s0 * t / 2)) := by
  have hA0 : 0 <= A := (h.one_le_A hs0.le).trans' zero_le_one
  calc
    mu.real {omega | t <= |X omega|} <=
        2 * A * Real.exp (B * s0 ^ 2 - s0 * t) :=
      h.abs_tail_le hs0 le_rfl
    _ <= 2 * A * Real.exp (-(s0 * t / 2)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hA0)
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hs0.le (sub_nonneg.mpr hreg)]

omit [IsProbabilityMeasure mu] in
/-- Raw real-order moment estimate.  This is the moment consequence of the
two-sided MGF bound before choosing the parameter `s`; it avoids both
layer-cake integration and any `Lp` infrastructure. -/
lemma rpow_moment_integrable_and_integral_le
    (h : TwoSidedMGFBound mu X A B s0)
    {r s : Real} (hr : 0 < r) (hs : 0 < s) (hss0 : s <= s0) :
    Integrable (fun omega => |X omega| ^ r) mu /\
      ((∫ omega, |X omega| ^ r ∂mu) <=
        2 * A * (r / s) ^ r * Real.exp (B * s ^ 2)) := by
  let c : Real := (r / s) ^ r
  have hrs0 : 0 <= r / s := (div_pos hr hs).le
  have hc0 : 0 <= c := Real.rpow_nonneg hrs0 r
  have hpos := h.integrable_pos s hs.le hss0
  have hneg := h.integrable_neg s hs.le hss0
  have hdomInt : Integrable
      (fun omega => c *
        (Real.exp (s * X omega) + Real.exp (-s * X omega))) mu :=
    (hpos.add hneg).const_mul c
  have hmomentMeas : Measurable (fun omega => |X omega| ^ r) := by
    exact (Real.continuous_rpow_const hr.le).measurable.comp h.measurable_X.abs
  have hpoint : forall omega, |X omega| ^ r <= c *
      (Real.exp (s * X omega) + Real.exp (-s * X omega)) := by
    intro omega
    calc
      |X omega| ^ r <= c * Real.exp (s * |X omega|) :=
        rpow_le_scale_rpow_mul_exp (abs_nonneg _) hr hs
      _ <= c * (Real.exp (s * X omega) + Real.exp (-s * X omega)) :=
        mul_le_mul_of_nonneg_left (exp_mul_abs_le_exp_add_exp_neg _ _) hc0
  have hmomentInt : Integrable (fun omega => |X omega| ^ r) mu := by
    apply integrable_of_le_of_le hmomentMeas.aestronglyMeasurable
      (ae_of_all _ fun omega => Real.rpow_nonneg (abs_nonneg (X omega)) r)
      (ae_of_all _ hpoint)
      (integrable_zero _ Real mu) hdomInt
  constructor
  · exact hmomentInt
  · calc
      (∫ omega, |X omega| ^ r ∂mu) <=
          ∫ omega, c *
            (Real.exp (s * X omega) + Real.exp (-s * X omega)) ∂mu :=
        integral_mono hmomentInt hdomInt hpoint
      _ = c * ((∫ omega, Real.exp (s * X omega) ∂mu) +
          ∫ omega, Real.exp (-s * X omega) ∂mu) := by
        rw [integral_const_mul, integral_add hpos hneg]
      _ <= c * (A * Real.exp (B * s ^ 2) +
          A * Real.exp (B * s ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hc0
        exact add_le_add (h.integral_pos_le s hs.le hss0)
          (h.integral_neg_le s hs.le hss0)
      _ = 2 * A * (r / s) ^ r * Real.exp (B * s ^ 2) := by
        dsimp [c]
        ring

/-- A lightweight real-order moment norm.  This is deliberately defined in
terms of the ordinary real Bochner integral, rather than through `Lp`. -/
def realMomentRoot (mu : Measure Omega) (X : Omega -> Real) (r : Real) : Real :=
  (∫ omega, |X omega| ^ r ∂mu) ^ (1 / r)

/-- Taking the real `r`-th root of `rpow_moment_integral_le`.  Keeping `s`
explicit makes the result reusable; later arguments may choose either the
quadratic optimum or the endpoint `s0`. -/
lemma realMomentRoot_le
    (h : TwoSidedMGFBound mu X A B s0)
    {r s : Real} (hr : 0 < r) (hs : 0 < s) (hss0 : s <= s0) :
    realMomentRoot mu X r <=
      (2 * A) ^ (1 / r) * (r / s) * Real.exp (B * s ^ 2 / r) := by
  obtain ⟨hmomentInt, hmoment⟩ :=
    h.rpow_moment_integrable_and_integral_le hr hs hss0
  have hmoment0 : 0 <= ∫ omega, |X omega| ^ r ∂mu :=
    integral_nonneg_of_ae
      (ae_of_all _ fun omega => Real.rpow_nonneg (abs_nonneg (X omega)) r)
  have hs00 : 0 <= s0 := hs.le.trans hss0
  have hA0 : 0 <= A := (h.one_le_A hs00).trans' zero_le_one
  have hp0 : 0 <= 2 * A := mul_nonneg (by norm_num) hA0
  have hb0 : 0 <= r / s := (div_pos hr hs).le
  have hroot := Real.rpow_le_rpow hmoment0 hmoment
    (one_div_nonneg.mpr hr.le)
  have hbroot : ((r / s) ^ r) ^ (1 / r) = r / s := by
    rw [<- Real.rpow_mul hb0]
    rw [show r * (1 / r) = 1 by field_simp, Real.rpow_one]
  have hexproot : (Real.exp (B * s ^ 2)) ^ (1 / r) =
      Real.exp (B * s ^ 2 / r) := by
    rw [<- Real.exp_mul]
    congr 1
    ring
  change (∫ omega, |X omega| ^ r ∂mu) ^ (1 / r) <= _
  calc
    (∫ omega, |X omega| ^ r ∂mu) ^ (1 / r) <=
        (2 * A * (r / s) ^ r * Real.exp (B * s ^ 2)) ^ (1 / r) := hroot
    _ = (2 * A) ^ (1 / r) * (r / s) *
        Real.exp (B * s ^ 2 / r) := by
      rw [Real.mul_rpow (mul_nonneg hp0 (Real.rpow_nonneg hb0 r))
          (Real.exp_nonneg _),
        Real.mul_rpow hp0 (Real.rpow_nonneg hb0 r), hbroot, hexproot]

/-- Optimized sub-gamma moment scale.  The constant is elementary and
explicit.  The proof splits according to whether the quadratic optimizer
`r / sqrt (B r)` is admissible, and otherwise uses the endpoint `s0`. -/
lemma realMomentRoot_le_subgamma_scale
    (h : TwoSidedMGFBound mu X A B s0)
    {r : Real} (hr : 1 <= r) (hB : 0 < B) (hs0 : 0 < s0) :
    realMomentRoot mu X r <=
      2 * A * Real.exp 1 * (Real.sqrt (B * r) + r / s0) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  let q : Real := Real.sqrt (B * r)
  have hq0 : 0 <= q := Real.sqrt_nonneg _
  have hq : 0 < q := Real.sqrt_pos.2 (mul_pos hB hr0)
  have hq2 : q ^ 2 = B * r := by
    dsimp [q]
    exact Real.sq_sqrt (mul_nonneg hB.le hr0.le)
  have hAone : 1 <= A := h.one_le_A hs0.le
  have htwoAone : 1 <= 2 * A := by nlinarith
  have hinvr : 1 / r <= 1 := (div_le_one hr0).2 hr
  have hpref : (2 * A) ^ (1 / r) <= 2 * A :=
    Real.rpow_le_self_of_one_le htwoAone hinvr
  have hquot : r / (r / q) = q := by field_simp
  have harg : B * (r / q) ^ 2 / r = 1 := by
    field_simp
    nlinarith [hq2]
  by_cases hadm : r / q <= s0
  · have hs : 0 < r / q := div_pos hr0 hq
    calc
      realMomentRoot mu X r <=
          (2 * A) ^ (1 / r) * (r / (r / q)) *
            Real.exp (B * (r / q) ^ 2 / r) :=
        h.realMomentRoot_le hr0 hs hadm
      _ = (2 * A) ^ (1 / r) * q * Real.exp 1 := by
        rw [hquot, harg]
      _ <= 2 * A * q * Real.exp 1 := by
        gcongr
      _ <= 2 * A * Real.exp 1 * (q + r / s0) := by
        have hfac0 : 0 <= 2 * A * Real.exp 1 := by positivity
        calc
          2 * A * q * Real.exp 1 = (2 * A * Real.exp 1) * q := by ring
          _ <= (2 * A * Real.exp 1) * (q + r / s0) := by
            apply mul_le_mul_of_nonneg_left _ hfac0
            exact le_add_of_nonneg_right (div_nonneg hr0.le hs0.le)
      _ = 2 * A * Real.exp 1 * (Real.sqrt (B * r) + r / s0) := by
        rfl
  · have hlt : s0 < r / q := lt_of_not_ge hadm
    have hmul : s0 * q < r := (lt_div_iff₀ hq).1 hlt
    have hsq : (s0 * q) ^ 2 < r ^ 2 :=
      (sq_lt_sq₀ (mul_nonneg hs0.le hq0) hr0.le).2 hmul
    rw [mul_pow, hq2] at hsq
    have hBr : B * s0 ^ 2 <= r := by
      nlinarith [mul_pos hr0 (sub_pos.mpr (by nlinarith : B * s0 ^ 2 < r))]
    have hendpointArg : B * s0 ^ 2 / r <= 1 :=
      (div_le_one hr0).2 hBr
    have hrootEndpoint := h.realMomentRoot_le hr0 hs0 le_rfl
    calc
      realMomentRoot mu X r <=
          (2 * A) ^ (1 / r) * (r / s0) *
            Real.exp (B * s0 ^ 2 / r) := hrootEndpoint
      _ <= 2 * A * (r / s0) * Real.exp 1 := by
        gcongr
      _ <= 2 * A * Real.exp 1 * (q + r / s0) := by
        have hfac0 : 0 <= 2 * A * Real.exp 1 := by positivity
        calc
          2 * A * (r / s0) * Real.exp 1 =
              (2 * A * Real.exp 1) * (r / s0) := by ring
          _ <= (2 * A * Real.exp 1) * (q + r / s0) := by
            apply mul_le_mul_of_nonneg_left _ hfac0
            exact le_add_of_nonneg_left hq0
      _ = 2 * A * Real.exp 1 * (Real.sqrt (B * r) + r / s0) := by
        rfl

end TwoSidedMGFBound

end DiscreteTime

end

end UniformRandomMALA
