import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Elementary weak-limit steps for moving reference measures

The moving-reference argument needed by the discrete-time proof compares
probability measures `mu n = F n * nu n` while both `mu n` and `nu n` vary.
Instead of invoking an abstract compactness theorem for varying `L^p` spaces,
we first pass the Holder test-function inequality through weak convergence.
The eventual Radon--Nikodym and truncation argument can then be carried out
against the fixed limiting measure.

This file isolates the first, purely topological step.  It contains no path
space, stochastic process, or continuous-time probability.
-/

namespace UniformRandomMALA

open Filter MeasureTheory

noncomputable section

namespace DiscreteTime

section MovingReference

/-- The scalar endgame of the truncated-duality argument.  If `p` and `q`
are conjugate and a truncated `p`-moment `A` satisfies
`A <= C * A^(1/q)`, then its `p`-root is at most `C`.  Isolating this
calculation keeps divisions by a possibly zero moment out of the later
measure-theoretic proof. -/
theorem rpow_conjugate_bound
    {A C p q : ℝ}
    (hp : 1 < p) (_hq : 0 < q)
    (hconj : 1 / p + 1 / q = 1)
    (hA : 0 ≤ A)
    (hC : 0 ≤ C)
    (hbound : A ≤ C * A ^ (1 / q)) :
    A ^ (1 / p) ≤ C := by
  rcases hA.eq_or_lt with rfl | hApos
  · have hp0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
    rw [Real.zero_rpow (div_ne_zero one_ne_zero hp0)]
    exact hC
  have hpowpos : 0 < A ^ (1 / q) := Real.rpow_pos_of_pos hApos _
  have hdiv : A / A ^ (1 / q) ≤ C := by
    rw [div_le_iff₀ hpowpos]
    simpa only [mul_comm] using hbound
  calc
    A ^ (1 / p) = A ^ (1 - 1 / q) := by rw [show 1 / p = 1 - 1 / q by linarith]
    _ = A ^ 1 / A ^ (1 / q) := Real.rpow_sub hApos 1 (1 / q)
    _ = A / A ^ (1 / q) := by rw [Real.rpow_one]
    _ ≤ C := hdiv

/-- Elementary truncated dual power.  Using `u * |u|^(p-2)` instead of a
sign function keeps the test measurable by continuity when `p >= 2`. -/
def truncatedDualPower (p R u : ℝ) : ℝ :=
  if |u| ≤ R then u * |u| ^ (p - 2) else 0

/-- Absolute value of the untruncated dual power. -/
theorem abs_mul_abs_rpow_sub_two
    {p u : ℝ} (hp : 2 ≤ p) :
    |u * |u| ^ (p - 2)| = |u| ^ (p - 1) := by
  by_cases hu : u = 0
  · subst u
    rw [abs_zero, zero_mul, abs_zero]
    rw [Real.zero_rpow (by linarith)]
  · have habs : 0 < |u| := abs_pos.mpr hu
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg u) _)]
    calc
      |u| * |u| ^ (p - 2) = |u| ^ 1 * |u| ^ (p - 2) := by rw [Real.rpow_one]
      _ = |u| ^ (1 + (p - 2)) := (Real.rpow_add habs 1 (p - 2)).symm
      _ = |u| ^ (p - 1) := by ring_nf

/-- Multiplying by the truncated dual power produces the truncated
`p`-moment pointwise. -/
theorem mul_truncatedDualPower
    {p R u : ℝ} (hp : 2 ≤ p) :
    u * truncatedDualPower p R u =
      if |u| ≤ R then |u| ^ p else 0 := by
  unfold truncatedDualPower
  split_ifs
  · by_cases hu : u = 0
    · subst u
      simp [Real.zero_rpow (by linarith : p ≠ 0)]
    · have habs : 0 < |u| := abs_pos.mpr hu
      calc
        u * (u * |u| ^ (p - 2)) = u ^ 2 * |u| ^ (p - 2) := by ring
        _ = |u| ^ 2 * |u| ^ (p - 2) := by rw [sq_abs]
        _ = |u| ^ (2 : ℝ) * |u| ^ (p - 2) := by rw [Real.rpow_two]
        _ = |u| ^ ((2 : ℝ) + (p - 2)) := (Real.rpow_add habs 2 (p - 2)).symm
        _ = |u| ^ p := by ring_nf
  · simp

/-- The conjugate `q`-moment of the truncated dual power is the same
truncated `p`-moment. -/
theorem abs_truncatedDualPower_rpow
    {p q R u : ℝ} (hp : 2 ≤ p) (hexp : (p - 1) * q = p) :
    |truncatedDualPower p R u| ^ q =
      if |u| ≤ R then |u| ^ p else 0 := by
  have hq0 : q ≠ 0 := by
    intro hq
    rw [hq, mul_zero] at hexp
    linarith
  unfold truncatedDualPower
  split_ifs
  · rw [abs_mul_abs_rpow_sub_two hp]
    rw [← Real.rpow_mul (abs_nonneg u), hexp]
  · simp [Real.zero_rpow hq0]

/-- Measurability of the truncated dual test follows only from continuity of
absolute value, multiplication, and nonnegative real powers. -/
theorem measurable_truncatedDualPower
    {Alpha : Type*} [MeasurableSpace Alpha]
    {u : Alpha → ℝ} (hu : Measurable u)
    {p R : ℝ} (hp : 2 ≤ p) :
    Measurable (fun x => truncatedDualPower p R (u x)) := by
  have huabs : Measurable (fun x => |u x|) := continuous_abs.measurable.comp hu
  unfold truncatedDualPower
  apply Measurable.ite
  · exact measurableSet_le huabs measurable_const
  · exact hu.mul ((Real.continuous_rpow_const (by linarith)).measurable.comp huabs)
  · exact measurable_const

/-- A truncated dual test belongs to every finite-measure `L^q` space. -/
theorem truncatedDualPower_memLp
    {Alpha : Type*} [MeasurableSpace Alpha]
    {rho : Measure Alpha} [IsFiniteMeasure rho]
    {u : Alpha → ℝ} (hu : Measurable u)
    {p R : ℝ} (hp : 2 ≤ p) (hR : 0 ≤ R)
    (q : ENNReal) :
    MemLp (fun x => truncatedDualPower p R (u x)) q rho := by
  apply MemLp.of_bound (measurable_truncatedDualPower hu hp).aestronglyMeasurable
    (R ^ (p - 1))
  apply Filter.Eventually.of_forall
  intro x
  unfold truncatedDualPower
  split_ifs with hx
  · rw [Real.norm_eq_abs, abs_mul_abs_rpow_sub_two hp]
    exact Real.rpow_le_rpow (abs_nonneg _) hx (by linarith)
  · simpa using Real.rpow_nonneg hR (p - 1)

variable {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
  [OpensMeasurableSpace E]

/-- Integration of a fixed bounded continuous real-valued function passes
through weak convergence of probability measures.  This named wrapper keeps
the later moving-reference proof independent of the implementation of the
weak topology on `ProbabilityMeasure`. -/
theorem boundedContinuous_integral_tendsto
    {mu : ℕ → ProbabilityMeasure E} {muLimit : ProbabilityMeasure E}
    (hmu : Tendsto mu atTop (nhds muLimit))
    (f : BoundedContinuousFunction E ℝ) :
    Tendsto
      (fun n => ∫ x, f x ∂(mu n : Measure E))
      atTop
      (nhds (∫ x, f x ∂(muLimit : Measure E))) :=
  (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hmu) f

/-- The bounded continuous function `x ↦ |f x| ^ q`, for a nonnegative real
exponent.  It is introduced explicitly because weak convergence only tests
against bundled bounded continuous functions. -/
def boundedContinuousAbsRpow
    (f : BoundedContinuousFunction E ℝ) (q : ℝ) (hq : 0 ≤ q) :
    BoundedContinuousFunction E ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => |f x| ^ q,
      (Real.continuous_rpow_const hq).comp f.continuous.abs⟩
    (2 * ‖f‖ ^ q) (by
      intro x y
      have hx : |f x| ^ q ≤ ‖f‖ ^ q := by
        apply Real.rpow_le_rpow (abs_nonneg _) _ hq
        simpa [Real.norm_eq_abs] using f.norm_coe_le_norm x
      have hy : |f y| ^ q ≤ ‖f‖ ^ q := by
        apply Real.rpow_le_rpow (abs_nonneg _) _ hq
        simpa [Real.norm_eq_abs] using f.norm_coe_le_norm y
      rw [Real.dist_eq]
      calc
        |(|f x| ^ q) - (|f y| ^ q)| ≤
            |(|f x| ^ q)| + |(|f y| ^ q)| := abs_sub _ _
        _ = |f x| ^ q + |f y| ^ q := by
          rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
            abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
        _ ≤ 2 * ‖f‖ ^ q := by linarith)

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
@[simp] theorem boundedContinuousAbsRpow_apply
    (f : BoundedContinuousFunction E ℝ) (q : ℝ) (hq : 0 ≤ q) (x : E) :
    boundedContinuousAbsRpow f q hq x = |f x| ^ q :=
  rfl

/-- The `q`-th absolute moment of a bounded continuous test function is
continuous under weak convergence. -/
theorem boundedContinuous_integral_abs_rpow_tendsto
    {nu : ℕ → ProbabilityMeasure E} {nuLimit : ProbabilityMeasure E}
    (hnu : Tendsto nu atTop (nhds nuLimit))
    (f : BoundedContinuousFunction E ℝ) {q : ℝ} (hq : 0 ≤ q) :
    Tendsto
      (fun n => ∫ x, |f x| ^ q ∂(nu n : Measure E))
      atTop
      (nhds (∫ x, |f x| ^ q ∂(nuLimit : Measure E))) := by
  simpa only [boundedContinuousAbsRpow_apply] using
    boundedContinuous_integral_tendsto hnu
      (boundedContinuousAbsRpow f q hq)

/-- For `q > 0`, the usual real-valued `L^q` expression of a bounded
continuous function also passes through weak convergence. -/
theorem boundedContinuous_lqScale_tendsto
    {nu : ℕ → ProbabilityMeasure E} {nuLimit : ProbabilityMeasure E}
    (hnu : Tendsto nu atTop (nhds nuLimit))
    (f : BoundedContinuousFunction E ℝ) {q : ℝ} (hq : 0 < q) :
    Tendsto
      (fun n => (∫ x, |f x| ^ q ∂(nu n : Measure E)) ^ (1 / q))
      atTop
      (nhds ((∫ x, |f x| ^ q ∂(nuLimit : Measure E)) ^ (1 / q))) := by
  exact (Real.continuous_rpow_const (by positivity : 0 ≤ 1 / q)).continuousAt.tendsto.comp
    (boundedContinuous_integral_abs_rpow_tendsto hnu f hq.le)

/-- Elementary weak-limit transfer for a test-function estimate.

In the application, `scale n` is the `L^q(nu n)` norm of `f`, and `C` is a
uniform bound for the centered likelihood in `L^p(nu n)`.  Keeping the scale
abstract here separates the weak-convergence argument from the later proof
that bounded continuous `L^q` norms also converge. -/
theorem boundedContinuous_test_bound_of_weakLimit
    {mu nu : ℕ → ProbabilityMeasure E}
    {muLimit nuLimit : ProbabilityMeasure E}
    (hmu : Tendsto mu atTop (nhds muLimit))
    (hnu : Tendsto nu atTop (nhds nuLimit))
    (f : BoundedContinuousFunction E ℝ)
    {scale : ℕ → ℝ} {scaleLimit C : ℝ}
    (hscale : Tendsto scale atTop (nhds scaleLimit))
    (hbound : ∀ n,
      |(∫ x, f x ∂(mu n : Measure E)) -
        ∫ x, f x ∂(nu n : Measure E)| ≤ C * scale n) :
    |(∫ x, f x ∂(muLimit : Measure E)) -
      ∫ x, f x ∂(nuLimit : Measure E)| ≤ C * scaleLimit := by
  apply le_of_tendsto_of_tendsto'
    ((boundedContinuous_integral_tendsto hmu f).sub
      (boundedContinuous_integral_tendsto hnu f) |>.abs)
    (tendsto_const_nhds.mul hscale)
  exact hbound

/-- The exact bounded-continuous Holder estimate needed in the
moving-reference argument.  Both measures may vary, but the limiting bound
uses only the fixed limiting reference measure. -/
theorem boundedContinuous_holder_bound_of_weakLimit
    {mu nu : ℕ → ProbabilityMeasure E}
    {muLimit nuLimit : ProbabilityMeasure E}
    (hmu : Tendsto mu atTop (nhds muLimit))
    (hnu : Tendsto nu atTop (nhds nuLimit))
    (f : BoundedContinuousFunction E ℝ)
    {q C : ℝ} (hq : 0 < q)
    (hbound : ∀ n,
      |(∫ x, f x ∂(mu n : Measure E)) -
        ∫ x, f x ∂(nu n : Measure E)| ≤
        C * (∫ x, |f x| ^ q ∂(nu n : Measure E)) ^ (1 / q)) :
    |(∫ x, f x ∂(muLimit : Measure E)) -
      ∫ x, f x ∂(nuLimit : Measure E)| ≤
      C * (∫ x, |f x| ^ q ∂(nuLimit : Measure E)) ^ (1 / q) := by
  exact boundedContinuous_test_bound_of_weakLimit hmu hnu f
    (boundedContinuous_lqScale_tendsto hnu f hq) hbound

omit [OpensMeasurableSpace E] in
/-- Extend a Holder test estimate from bounded continuous functions to one
possibly merely measurable test function, once simultaneous approximants
have been supplied.  The approximants are required to converge for the two
linear integrals and for the `L^q(nu)` scale.  This is the exact interface
that the weak-regularity/density lemma must discharge; no duality theorem is
hidden in this step. -/
theorem holder_bound_of_boundedContinuous_approximants
    {mu nu : ProbabilityMeasure E}
    (phi : E → ℝ)
    (approx : ℕ → BoundedContinuousFunction E ℝ)
    {q C : ℝ}
    (hmu : Tendsto
      (fun n => ∫ x, approx n x ∂(mu : Measure E))
      atTop
      (nhds (∫ x, phi x ∂(mu : Measure E))))
    (hnu : Tendsto
      (fun n => ∫ x, approx n x ∂(nu : Measure E))
      atTop
      (nhds (∫ x, phi x ∂(nu : Measure E))))
    (hlq : Tendsto
      (fun n => (∫ x, |approx n x| ^ q ∂(nu : Measure E)) ^ (1 / q))
      atTop
      (nhds ((∫ x, |phi x| ^ q ∂(nu : Measure E)) ^ (1 / q))))
    (hbound : ∀ f : BoundedContinuousFunction E ℝ,
      |(∫ x, f x ∂(mu : Measure E)) -
        ∫ x, f x ∂(nu : Measure E)| ≤
        C * (∫ x, |f x| ^ q ∂(nu : Measure E)) ^ (1 / q)) :
    |(∫ x, phi x ∂(mu : Measure E)) -
      ∫ x, phi x ∂(nu : Measure E)| ≤
      C * (∫ x, |phi x| ^ q ∂(nu : Measure E)) ^ (1 / q) := by
  apply le_of_tendsto_of_tendsto'
    ((hmu.sub hnu).abs)
    (tendsto_const_nhds.mul hlq)
  exact fun n => hbound (approx n)

end MovingReference

section MetricApproximation

variable {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]

omit [PseudoMetricSpace E] [BorelSpace E] in
/-- Rewrite the real `L^q` scale used in the paper as the `eLpNorm` supplied
by Mathlib.  The real-valued formulation is convenient for the quantitative
inequality, while `eLpNorm` makes the density argument short and robust. -/
theorem toReal_eLpNorm_eq_integral_abs_rpow
    {mu : Measure E} {f : E → ℝ} {q : ℝ} (hq : 0 < q)
    (hf : MemLp f (ENNReal.ofReal q) mu) :
    ENNReal.toReal (eLpNorm f (ENNReal.ofReal q) mu) =
      (∫ x, |f x| ^ q ∂mu) ^ (1 / q) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm]
  · simp only [ENNReal.toReal_ofReal hq.le, Real.norm_eq_abs]
    rw [ENNReal.toReal_ofReal]
    · rw [one_div]
    · positivity
  · simpa using hq
  · exact ENNReal.ofReal_ne_top

/-- Simultaneous bounded-continuous approximation for two probability
measures.  Approximating in `L^q(mu + nu)` automatically approximates in
`L^q(mu)` and `L^q(nu)` by monotonicity of the seminorm. -/
theorem exists_boundedContinuous_eLpNorm_approximants
    (mu nu : ProbabilityMeasure E)
    {phi : E → ℝ} {q : ℝ}
    (hphi : MemLp phi (ENNReal.ofReal q)
      ((mu : Measure E) + (nu : Measure E))) :
    ∃ approx : ℕ → BoundedContinuousFunction E ℝ,
      Tendsto
        (fun n => eLpNorm ((approx n : E → ℝ) - phi)
          (ENNReal.ofReal q) (mu : Measure E))
        atTop (nhds 0) ∧
      Tendsto
        (fun n => eLpNorm ((approx n : E → ℝ) - phi)
          (ENNReal.ofReal q) (nu : Measure E))
        atTop (nhds 0) := by
  let epsilon : ℕ → ENNReal := fun n => ENNReal.ofReal (1 / (n + 1 : ℝ))
  have hepsilon_pos (n : ℕ) : epsilon n ≠ 0 := by
    simp only [epsilon, ENNReal.ofReal_ne_zero_iff]
    positivity
  have hex (n : ℕ) : ∃ g : BoundedContinuousFunction E ℝ,
      eLpNorm (phi - (g : E → ℝ)) (ENNReal.ofReal q)
        ((mu : Measure E) + (nu : Measure E)) ≤ epsilon n ∧
      MemLp g (ENNReal.ofReal q) ((mu : Measure E) + (nu : Measure E)) :=
    hphi.exists_boundedContinuous_eLpNorm_sub_le ENNReal.coe_ne_top (hepsilon_pos n)
  let approx : ℕ → BoundedContinuousFunction E ℝ := fun n => (hex n).choose
  have happrox (n : ℕ) :
      eLpNorm (phi - (approx n : E → ℝ)) (ENNReal.ofReal q)
        ((mu : Measure E) + (nu : Measure E)) ≤ epsilon n :=
    (hex n).choose_spec.1
  have hepsilon : Tendsto epsilon atTop (nhds 0) := by
    simpa only [epsilon, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
  have hsum : Tendsto
      (fun n => eLpNorm ((approx n : E → ℝ) - phi)
        (ENNReal.ofReal q) ((mu : Measure E) + (nu : Measure E)))
      atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hepsilon
    · exact fun n => bot_le
    · intro n
      change eLpNorm ((approx n : E → ℝ) - phi) (ENNReal.ofReal q)
        ((mu : Measure E) + (nu : Measure E)) ≤ epsilon n
      rw [eLpNorm_sub_comm]
      exact happrox n
  refine ⟨approx, ?_, ?_⟩
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    · exact fun n => bot_le
    · exact fun n => eLpNorm_mono_measure _ (Measure.le_add_right le_rfl)
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    · exact fun n => bot_le
    · exact fun n => eLpNorm_mono_measure _ (Measure.le_add_left le_rfl)

/-- The simultaneous approximation in precisely the three topologies used
by `holder_bound_of_boundedContinuous_approximants`: two `L^1` integral
limits and one `L^q`-norm limit.  The proof is only density, monotonicity of
`eLpNorm`, and continuity of the norm on the ordinary `Lp` space. -/
theorem exists_boundedContinuous_integral_approximants
    (mu nu : ProbabilityMeasure E)
    {phi : E → ℝ} {q : ℝ} (hq : 1 ≤ q)
    (hphi : MemLp phi (ENNReal.ofReal q)
      ((mu : Measure E) + (nu : Measure E))) :
    ∃ approx : ℕ → BoundedContinuousFunction E ℝ,
      Tendsto
        (fun n => ∫ x, approx n x ∂(mu : Measure E))
        atTop (nhds (∫ x, phi x ∂(mu : Measure E))) ∧
      Tendsto
        (fun n => ∫ x, approx n x ∂(nu : Measure E))
        atTop (nhds (∫ x, phi x ∂(nu : Measure E))) ∧
      Tendsto
        (fun n => (∫ x, |approx n x| ^ q ∂(nu : Measure E)) ^ (1 / q))
        atTop (nhds ((∫ x, |phi x| ^ q ∂(nu : Measure E)) ^ (1 / q))) := by
  have hqpos : 0 < q := zero_lt_one.trans_le hq
  have hqENN : 1 ≤ ENNReal.ofReal q := ENNReal.one_le_ofReal.mpr hq
  let _ : Fact (1 ≤ ENNReal.ofReal q) := ⟨hqENN⟩
  obtain ⟨approx, hmuq, hnuq⟩ :=
    exists_boundedContinuous_eLpNorm_approximants mu nu hphi
  have hmu_le : (mu : Measure E) ≤ (mu : Measure E) + (nu : Measure E) :=
    Measure.le_add_right le_rfl
  have hnu_le : (nu : Measure E) ≤ (mu : Measure E) + (nu : Measure E) :=
    Measure.le_add_left le_rfl
  have hphi_mu := hphi.mono_measure hmu_le
  have hphi_nu := hphi.mono_measure hnu_le
  have happrox_sum (n : ℕ) : MemLp (approx n : E → ℝ) (ENNReal.ofReal q)
      ((mu : Measure E) + (nu : Measure E)) := by
    apply MemLp.of_bound (approx n).continuous.aestronglyMeasurable ‖approx n‖
    exact Eventually.of_forall fun x => (approx n).norm_coe_le_norm x
  have happrox_mu (n : ℕ) :
      MemLp (approx n : E → ℝ) (ENNReal.ofReal q) (mu : Measure E) :=
    (happrox_sum n).mono_measure hmu_le
  have happrox_nu (n : ℕ) :
      MemLp (approx n : E → ℝ) (ENNReal.ofReal q) (nu : Measure E) :=
    (happrox_sum n).mono_measure hnu_le
  have hmu1 : Tendsto
      (fun n => eLpNorm ((approx n : E → ℝ) - phi) 1 (mu : Measure E))
      atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmuq
    · exact fun n => bot_le
    · intro n
      exact eLpNorm_le_eLpNorm_of_exponent_le hqENN
        ((happrox_mu n).1.sub hphi_mu.1)
  have hnu1 : Tendsto
      (fun n => eLpNorm ((approx n : E → ℝ) - phi) 1 (nu : Measure E))
      atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hnuq
    · exact fun n => bot_le
    · intro n
      exact eLpNorm_le_eLpNorm_of_exponent_le hqENN
        ((happrox_nu n).1.sub hphi_nu.1)
  have hmuIntegral : Tendsto
      (fun n => ∫ x, approx n x ∂(mu : Measure E))
      atTop (nhds (∫ x, phi x ∂(mu : Measure E))) := by
    exact tendsto_integral_of_L1' phi hphi_mu.1
      (Eventually.of_forall fun n => (happrox_mu n).integrable hqENN)
      hmu1
  have hnuIntegral : Tendsto
      (fun n => ∫ x, approx n x ∂(nu : Measure E))
      atTop (nhds (∫ x, phi x ∂(nu : Measure E))) := by
    exact tendsto_integral_of_L1' phi hphi_nu.1
      (Eventually.of_forall fun n => (happrox_nu n).integrable hqENN)
      hnu1
  have hLpNu : Tendsto
      (fun n => (happrox_nu n).toLp (approx n : E → ℝ))
      atTop (nhds (hphi_nu.toLp phi)) := by
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n => (approx n : E → ℝ)) happrox_nu phi hphi_nu).2 hnuq
  have hnormNu : Tendsto
      (fun n => ‖(happrox_nu n).toLp (approx n : E → ℝ)‖)
      atTop (nhds ‖hphi_nu.toLp phi‖) :=
    continuous_norm.continuousAt.tendsto.comp hLpNu
  refine ⟨approx, hmuIntegral, hnuIntegral, ?_⟩
  convert hnormNu using 1
  · funext n
    rw [Lp.norm_toLp,
      toReal_eLpNorm_eq_integral_abs_rpow hqpos (happrox_nu n)]
  · rw [Lp.norm_toLp,
      toReal_eLpNorm_eq_integral_abs_rpow hqpos hphi_nu]

/-- Fully discharge the bounded-continuous-to-measurable extension required
by the fixed-reference truncation argument.  The only hypothesis on the test
function is membership in `L^q(mu + nu)`; no `L^p` duality theorem is used. -/
theorem holder_bound_of_memLp
    (mu nu : ProbabilityMeasure E)
    (phi : E → ℝ)
    {q C : ℝ} (hq : 1 ≤ q)
    (hphi : MemLp phi (ENNReal.ofReal q)
      ((mu : Measure E) + (nu : Measure E)))
    (hbound : ∀ f : BoundedContinuousFunction E ℝ,
      |(∫ x, f x ∂(mu : Measure E)) -
        ∫ x, f x ∂(nu : Measure E)| ≤
        C * (∫ x, |f x| ^ q ∂(nu : Measure E)) ^ (1 / q)) :
    |(∫ x, phi x ∂(mu : Measure E)) -
      ∫ x, phi x ∂(nu : Measure E)| ≤
      C * (∫ x, |phi x| ^ q ∂(nu : Measure E)) ^ (1 / q) := by
  obtain ⟨approx, hmu, hnu, hlq⟩ :=
    exists_boundedContinuous_integral_approximants mu nu hq hphi
  exact holder_bound_of_boundedContinuous_approximants
    phi approx hmu hnu hlq hbound

/-- The test-function bound forces absolute continuity.  Apply the measurable
extension to an indicator of a measurable `nu`-null set; its `L^q(nu)` norm
is zero, hence the same set is also `mu`-null. -/
theorem absolutelyContinuous_of_boundedContinuous_holder
    (mu nu : ProbabilityMeasure E)
    {q C : ℝ} (hq : 1 ≤ q)
    (hbound : ∀ f : BoundedContinuousFunction E ℝ,
      |(∫ x, f x ∂(mu : Measure E)) -
        ∫ x, f x ∂(nu : Measure E)| ≤
        C * (∫ x, |f x| ^ q ∂(nu : Measure E)) ^ (1 / q)) :
    (mu : Measure E) ≪ (nu : Measure E) := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hnu
  let phi : E → ℝ := s.indicator fun _ => 1
  have hphi : MemLp phi (ENNReal.ofReal q)
      ((mu : Measure E) + (nu : Measure E)) := by
    apply memLp_indicator_const (ENNReal.ofReal q) hs 1
    right
    exact measure_ne_top _ _
  have htest := holder_bound_of_memLp mu nu phi hq hphi hbound
  have hnuReal : (nu : Measure E).real s = 0 := by simp [Measure.real, hnu]
  have hmoment : ∫ x, |phi x| ^ q ∂(nu : Measure E) = 0 := by
    apply integral_eq_zero_of_ae
    rw [measure_eq_zero_iff_ae_notMem] at hnu
    filter_upwards [hnu] with x hx
    simp [phi, Set.indicator_of_notMem hx,
      Real.zero_rpow (ne_of_gt (zero_lt_one.trans_le hq))]
  have hone : (fun _ : E => (1 : ℝ)) = (1 : E → ℝ) := by
    funext x
    rfl
  have hmuIntegral : ∫ x, phi x ∂(mu : Measure E) = (mu : Measure E).real s := by
    simp only [phi]
    rw [hone]
    exact integral_indicator_one (μ := (mu : Measure E)) hs
  have hnuIntegral : ∫ x, phi x ∂(nu : Measure E) = (nu : Measure E).real s := by
    simp only [phi]
    rw [hone]
    exact integral_indicator_one (μ := (nu : Measure E)) hs
  rw [hmuIntegral, hnuIntegral, hnuReal, hmoment] at htest
  have hmuReal : (mu : Measure E).real s = 0 := by
    have hnonneg : 0 ≤ (mu : Measure E).real s := ENNReal.toReal_nonneg
    have hqinv : 1 / q ≠ 0 := by positivity
    rw [sub_zero, abs_of_nonneg hnonneg, Real.zero_rpow hqinv, mul_zero] at htest
    exact le_antisymm htest hnonneg
  exact ((mu : Measure E) s).toReal_eq_zero_iff.mp hmuReal |>.resolve_right
    (measure_ne_top _ _)

/-- Real-valued centered Radon--Nikodym derivative. -/
def centeredRNDeriv (mu nu : Measure E) (x : E) : ℝ :=
  (mu.rnDeriv nu x).toReal - 1

/-- The complete finite-truncation estimate for the fixed-reference
Radon--Nikodym argument.  It uses indicator tests to obtain absolute
continuity, identifies the linear functional by the Radon--Nikodym integral
formula, and applies the elementary dual-power identities above. -/
theorem truncated_rnDeriv_moment_bound
    (mu nu : ProbabilityMeasure E)
    {p q C : ℝ} (hp : 2 ≤ p) (hq : 1 ≤ q)
    (hconj : 1 / p + 1 / q = 1) (hC : 0 ≤ C)
    (hbound : ∀ f : BoundedContinuousFunction E ℝ,
      |(∫ x, f x ∂(mu : Measure E)) -
        ∫ x, f x ∂(nu : Measure E)| ≤
        C * (∫ x, |f x| ^ q ∂(nu : Measure E)) ^ (1 / q)) :
    ∀ R : ℝ, 0 ≤ R →
      (∫ x, if |centeredRNDeriv (mu : Measure E) (nu : Measure E) x| ≤ R
        then |centeredRNDeriv (mu : Measure E) (nu : Measure E) x| ^ p else 0
        ∂(nu : Measure E)) ^ (1 / p) ≤ C := by
  have hp0 : p ≠ 0 := by linarith
  have hq0 : q ≠ 0 := by linarith
  have hexp : (p - 1) * q = p := by
    field_simp [hp0, hq0] at hconj
    nlinarith
  have hac : (mu : Measure E) ≪ (nu : Measure E) :=
    absolutelyContinuous_of_boundedContinuous_holder mu nu hq hbound
  let u : E → ℝ := centeredRNDeriv (mu : Measure E) (nu : Measure E)
  have hu : Measurable u := by
    exact (ENNReal.measurable_toReal.comp
      (Measure.measurable_rnDeriv (mu : Measure E) (nu : Measure E))).sub measurable_const
  intro R hR
  let phi : E → ℝ := fun x => truncatedDualPower p R (u x)
  have hphi : MemLp phi (ENNReal.ofReal q)
      ((mu : Measure E) + (nu : Measure E)) := by
    exact truncatedDualPower_memLp hu hp hR (ENNReal.ofReal q)
  have htest := holder_bound_of_memLp mu nu phi hq hphi hbound
  have hmu_le : (mu : Measure E) ≤ (mu : Measure E) + (nu : Measure E) :=
    Measure.le_add_right le_rfl
  have hnu_le : (nu : Measure E) ≤ (mu : Measure E) + (nu : Measure E) :=
    Measure.le_add_left le_rfl
  have hqENN : 1 ≤ ENNReal.ofReal q := ENNReal.one_le_ofReal.mpr hq
  have hphi_mu : Integrable phi (mu : Measure E) :=
    (hphi.mono_measure hmu_le).integrable hqENN
  have hphi_nu : Integrable phi (nu : Measure E) :=
    (hphi.mono_measure hnu_le).integrable hqENN
  have hFphi : Integrable
      (fun x => (((mu : Measure E).rnDeriv (nu : Measure E) x).toReal) * phi x)
      (nu : Measure E) :=
    (integrable_toReal_rnDeriv_mul_iff hac).2 hphi_mu
  let A : ℝ := ∫ x, if |u x| ≤ R then |u x| ^ p else 0 ∂(nu : Measure E)
  have hA : 0 ≤ A := by
    apply integral_nonneg
    intro x
    change 0 ≤ (if |u x| ≤ R then |u x| ^ p else 0)
    split_ifs
    · exact Real.rpow_nonneg (abs_nonneg _) _
    · exact le_rfl
  have hlinear :
      (∫ x, phi x ∂(mu : Measure E)) - ∫ x, phi x ∂(nu : Measure E) = A := by
    calc
      (∫ x, phi x ∂(mu : Measure E)) - ∫ x, phi x ∂(nu : Measure E) =
          (∫ x, ((mu : Measure E).rnDeriv (nu : Measure E) x).toReal * phi x
            ∂(nu : Measure E)) - ∫ x, phi x ∂(nu : Measure E) := by
              rw [integral_toReal_rnDeriv_mul hac]
      _ = ∫ x, (((mu : Measure E).rnDeriv (nu : Measure E) x).toReal * phi x) - phi x
            ∂(nu : Measure E) := (integral_sub hFphi hphi_nu).symm
      _ = ∫ x, u x * phi x ∂(nu : Measure E) := by
            apply integral_congr_ae
            apply Filter.Eventually.of_forall
            intro x
            simp only [u, centeredRNDeriv]
            ring
      _ = A := by
            apply integral_congr_ae
            apply Filter.Eventually.of_forall
            intro x
            simpa only [phi, A] using
              mul_truncatedDualPower (p := p) (R := R) (u := u x) hp
  have hmoment : ∫ x, |phi x| ^ q ∂(nu : Measure E) = A := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    simpa only [phi, A] using
      abs_truncatedDualPower_rpow (p := p) (q := q) (R := R) (u := u x) hp hexp
  rw [hlinear, hmoment, abs_of_nonneg hA] at htest
  simpa only [u] using rpow_conjugate_bound
    (lt_of_lt_of_le one_lt_two hp) (lt_of_lt_of_le zero_lt_one hq)
    hconj hA hC htest

/-- Letting the truncation level tend to infinity gives the actual centered
Radon--Nikodym derivative in `L^p`.  The passage to the limit is the monotone
convergence theorem for nonnegative scalar integrals, followed by the
definition of `MemLp`; it uses no weak compactness or Banach-space duality. -/
theorem full_rnDeriv_moment_bound
    (mu nu : ProbabilityMeasure E)
    {p q C : ℝ} (hp : 2 ≤ p) (hq : 1 ≤ q)
    (hconj : 1 / p + 1 / q = 1) (hC : 0 ≤ C)
    (hbound : ∀ f : BoundedContinuousFunction E ℝ,
      |(∫ x, f x ∂(mu : Measure E)) -
        ∫ x, f x ∂(nu : Measure E)| ≤
        C * (∫ x, |f x| ^ q ∂(nu : Measure E)) ^ (1 / q)) :
    let u := centeredRNDeriv (mu : Measure E) (nu : Measure E)
    MemLp u (ENNReal.ofReal p) (nu : Measure E) ∧
      (∫ x, |u x| ^ p ∂(nu : Measure E)) ^ (1 / p) ≤ C := by
  dsimp only
  let u : E → ℝ := centeredRNDeriv (mu : Measure E) (nu : Measure E)
  have hu : Measurable u := by
    exact (ENNReal.measurable_toReal.comp
      (Measure.measurable_rnDeriv (mu : Measure E) (nu : Measure E))).sub measurable_const
  have huabs : Measurable (fun x => |u x|) := continuous_abs.measurable.comp hu
  have hmomentMeas : Measurable (fun x => |u x| ^ p) :=
    (Real.continuous_rpow_const (by linarith)).measurable.comp huabs
  let moment : ℕ → E → ℝ := fun n x =>
    if |u x| ≤ (n : ℝ) then |u x| ^ p else 0
  have hmoment_meas (n : ℕ) : Measurable (moment n) := by
    exact Measurable.ite (measurableSet_le huabs measurable_const)
      hmomentMeas measurable_const
  have hmoment_nonneg (n : ℕ) : 0 ≤ moment n := by
    intro x
    change 0 ≤ (if |u x| ≤ (n : ℝ) then |u x| ^ p else 0)
    split_ifs
    · exact Real.rpow_nonneg (abs_nonneg _) _
    · exact le_rfl
  have hmoment_int (n : ℕ) : Integrable (moment n) (nu : Measure E) := by
    have hmem : MemLp (moment n) 1 (nu : Measure E) := by
      apply MemLp.of_bound (hmoment_meas n).aestronglyMeasurable ((n : ℝ) ^ p)
      apply Filter.Eventually.of_forall
      intro x
      change |(if |u x| ≤ (n : ℝ) then |u x| ^ p else 0)| ≤ (n : ℝ) ^ p
      split_ifs with hx
      · rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
        exact Real.rpow_le_rpow (abs_nonneg _) hx (by linarith)
      · simpa using Real.rpow_nonneg (Nat.cast_nonneg n) p
    exact hmem.integrable le_rfl
  have hp0 : p ≠ 0 := by linarith
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_two hp
  have hroot (n : ℕ) :
      (∫ x, moment n x ∂(nu : Measure E)) ^ (1 / p) ≤ C := by
    simpa only [moment, u] using
      truncated_rnDeriv_moment_bound mu nu hp hq hconj hC hbound (n : ℝ)
        (Nat.cast_nonneg n)
  have hrealBound (n : ℕ) :
      (∫ x, moment n x ∂(nu : Measure E)) ≤ C ^ p := by
    have hA : 0 ≤ ∫ x, moment n x ∂(nu : Measure E) :=
      integral_nonneg (hmoment_nonneg n)
    have hpow := (Real.rpow_le_rpow_iff
      (Real.rpow_nonneg hA (1 / p)) hC hp_pos).2 (hroot n)
    rw [← Real.rpow_mul hA, one_div, inv_mul_cancel₀ hp0, Real.rpow_one] at hpow
    exact hpow
  have hlinBound (n : ℕ) :
      (∫⁻ x, ENNReal.ofReal (moment n x) ∂(nu : Measure E)) ≤
        ENNReal.ofReal (C ^ p) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hmoment_int n)
      (Filter.Eventually.of_forall (hmoment_nonneg n))]
    exact ENNReal.ofReal_le_ofReal (hrealBound n)
  have hmono : ∀ᵐ x ∂(nu : Measure E),
      Monotone fun n => ENNReal.ofReal (moment n x) := by
    apply Filter.Eventually.of_forall
    intro x n m hnm
    dsimp only [moment]
    by_cases hn : |u x| ≤ (n : ℝ)
    · have hm : |u x| ≤ (m : ℝ) := hn.trans (Nat.cast_le.mpr hnm)
      simp [hn, hm]
    · simp [hn]
  have htendsto : ∀ᵐ x ∂(nu : Measure E), Tendsto
      (fun n => ENNReal.ofReal (moment n x)) atTop
      (nhds (ENNReal.ofReal (|u x| ^ p))) := by
    apply Filter.Eventually.of_forall
    intro x
    obtain ⟨N, hN⟩ := exists_nat_ge |u x|
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hxn : |u x| ≤ (n : ℝ) := hN.trans (Nat.cast_le.mpr hn)
    simp [moment, hxn]
  have hlinTendsto : Tendsto
      (fun n => ∫⁻ x, ENNReal.ofReal (moment n x) ∂(nu : Measure E)) atTop
      (nhds (∫⁻ x, ENNReal.ofReal (|u x| ^ p) ∂(nu : Measure E))) :=
    lintegral_tendsto_of_tendsto_of_monotone
      (fun n => (hmoment_meas n).ennreal_ofReal.aemeasurable) hmono htendsto
  have hfullLin : (∫⁻ x, ENNReal.ofReal (|u x| ^ p) ∂(nu : Measure E)) ≤
      ENNReal.ofReal (C ^ p) :=
    le_of_tendsto' hlinTendsto hlinBound
  have hfullNonneg : 0 ≤ᵐ[(nu : Measure E)] fun x => |u x| ^ p :=
    Filter.Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg _) _
  have hfullInt : Integrable (fun x => |u x| ^ p) (nu : Measure E) := by
    refine ⟨hmomentMeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hfullNonneg]
    exact lt_of_le_of_lt hfullLin ENNReal.ofReal_lt_top
  have huMem : MemLp u (ENNReal.ofReal p) (nu : Measure E) := by
    rw [← integrable_norm_rpow_iff hu.aestronglyMeasurable]
    · simpa only [ENNReal.toReal_ofReal hp_pos.le, Real.norm_eq_abs] using hfullInt
    · simpa using hp_pos
    · exact ENNReal.ofReal_ne_top
  have hfullReal : (∫ x, |u x| ^ p ∂(nu : Measure E)) ≤ C ^ p := by
    apply (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hC p)).mp
    rw [ofReal_integral_eq_lintegral_ofReal hfullInt hfullNonneg]
    exact hfullLin
  have hIntegralNonneg : 0 ≤ ∫ x, |u x| ^ p ∂(nu : Measure E) :=
    integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _
  have hrootFull := (Real.rpow_le_rpow_iff hIntegralNonneg
    (Real.rpow_nonneg hC p) (one_div_pos.mpr hp_pos)).2 hfullReal
  rw [← Real.rpow_mul hC, one_div, mul_inv_cancel₀ hp0, Real.rpow_one] at hrootFull
  constructor
  · simpa only [u] using huMem
  · simpa only [u, one_div] using hrootFull

/-- Moving-reference `L^p` closure under weak convergence.  This is the
elementary replacement for the varying-reference compactness theorem: pass
the Holder inequality on bounded continuous tests to the weak limit, extend
it by simultaneous `L^q(mu + nu)` approximation, identify the fixed-limit
Radon--Nikodym derivative, and use scalar truncation plus monotone
convergence. -/
theorem centeredRNDeriv_memLp_of_weakLimit
    {mu nu : ℕ → ProbabilityMeasure E}
    {muLimit nuLimit : ProbabilityMeasure E}
    {p q C : ℝ}
    (hp : 2 ≤ p) (hq : 1 ≤ q)
    (hconj : 1 / p + 1 / q = 1) (hC : 0 ≤ C)
    (hmu : Tendsto mu atTop (nhds muLimit))
    (hnu : Tendsto nu atTop (nhds nuLimit))
    (hbound : ∀ n, ∀ f : BoundedContinuousFunction E ℝ,
      |(∫ x, f x ∂(mu n : Measure E)) -
        ∫ x, f x ∂(nu n : Measure E)| ≤
        C * (∫ x, |f x| ^ q ∂(nu n : Measure E)) ^ (1 / q)) :
    let u := centeredRNDeriv (muLimit : Measure E) (nuLimit : Measure E)
    MemLp u (ENNReal.ofReal p) (nuLimit : Measure E) ∧
      (∫ x, |u x| ^ p ∂(nuLimit : Measure E)) ^ (1 / p) ≤ C := by
  apply full_rnDeriv_moment_bound muLimit nuLimit hp hq hconj hC
  intro f
  exact boundedContinuous_holder_bound_of_weakLimit hmu hnu f
    (lt_of_lt_of_le zero_lt_one hq) (fun n => hbound n f)

end MetricApproximation

end DiscreteTime

end

end UniformRandomMALA
