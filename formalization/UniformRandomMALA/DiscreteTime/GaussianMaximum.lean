import UniformRandomMALA.DiscreteTime.GaussianMGF
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Finite-grid exponential averaging

The discrete Euler estimate does not actually need a maximal inequality.
For a nonempty finite grid, convexity of the exponential gives

`exp ((1 / N) * sum_i q_i) <= (1 / N) * sum_i exp q_i`.

Applied with `q_k = lambda * (N * delta) * ‖S_k‖^2`, this bounds the
exponential moment of `lambda * delta * sum_k ‖S_k‖^2` by the average of
the one-time Gaussian exponential moments.  Thus no filtration, stopping
time, Doob inequality, or path maximum is needed.  The results below keep
the finite Jensen step separate from the later identification of each
Gaussian partial-sum marginal.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory

noncomputable section

namespace DiscreteTime

section FiniteJensen

variable {ι Ω : Type*} [MeasurableSpace Ω]

/-- Pointwise finite Jensen inequality for the exponential, written using
an ordinary arithmetic average over a nonempty finset. -/
theorem exp_finset_average_le_average_exp
    (s : Finset ι) (hs : s.Nonempty) (q : ι → ℝ) :
    Real.exp ((∑ i ∈ s, q i) / (s.card : ℝ)) ≤
      (∑ i ∈ s, Real.exp (q i)) / (s.card : ℝ) := by
  have hcard : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast hs.card_ne_zero
  have hweights : ∑ i ∈ s, ((s.card : ℝ)⁻¹) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp
  have hJensen := convexOn_exp.map_sum_le
    (t := s) (w := fun _ => (s.card : ℝ)⁻¹) (p := q)
    (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)) hweights
    (fun i _ => Set.mem_univ (q i))
  rw [Finset.sum_div, Finset.sum_div]
  simpa only [smul_eq_mul, div_eq_inv_mul] using hJensen

/-- Functional form of finite Jensen.  This is the exact pointwise
inequality used before integrating over the Gaussian path variables. -/
theorem exp_finset_average_apply_le_average_exp_apply
    (s : Finset ι) (hs : s.Nonempty) (q : ι → Ω → ℝ) (ω : Ω) :
    Real.exp ((∑ i ∈ s, q i ω) / (s.card : ℝ)) ≤
      (∑ i ∈ s, Real.exp (q i ω)) / (s.card : ℝ) :=
  exp_finset_average_le_average_exp s hs (fun i => q i ω)

/-- The exponential of a finite average is integrable whenever the
individual exponentials are integrable. -/
theorem integrable_exp_finset_average
    (μ : Measure Ω) (s : Finset ι) (hs : s.Nonempty)
    (q : ι → Ω → ℝ) (hq : ∀ i ∈ s, Measurable (q i))
    (hInt : ∀ i ∈ s, Integrable (fun ω => Real.exp (q i ω)) μ) :
    Integrable (fun ω =>
      Real.exp ((∑ i ∈ s, q i ω) / (s.card : ℝ))) μ := by
  have hcard0 : 0 ≤ ((s.card : ℝ)⁻¹) := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hUpper : Integrable (fun ω =>
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, Real.exp (q i ω)) μ := by
    refine (integrable_finsetSum s fun i hi => hInt i hi).const_mul _
  have hMeas : Measurable (fun ω =>
      Real.exp ((∑ i ∈ s, q i ω) / (s.card : ℝ))) := by
    fun_prop
  apply integrable_of_le_of_le hMeas.aestronglyMeasurable
    (ae_of_all _ fun ω => (Real.exp_pos _).le)
    (ae_of_all _ fun ω => ?_)
    (integrable_zero Ω ℝ μ) hUpper
  simpa only [div_eq_inv_mul] using
    exp_finset_average_apply_le_average_exp_apply s hs q ω

/-- Integrated finite-grid Jensen inequality.  It converts a path-level
exponential moment into an arithmetic average of one-time moments. -/
theorem integral_exp_finset_average_le_average_integral_exp
    (μ : Measure Ω) (s : Finset ι) (hs : s.Nonempty)
    (q : ι → Ω → ℝ) (hq : ∀ i ∈ s, Measurable (q i))
    (hInt : ∀ i ∈ s, Integrable (fun ω => Real.exp (q i ω)) μ) :
    (∫ ω, Real.exp ((∑ i ∈ s, q i ω) / (s.card : ℝ)) ∂μ) ≤
      (∑ i ∈ s, ∫ ω, Real.exp (q i ω) ∂μ) / (s.card : ℝ) := by
  have hLeft := integrable_exp_finset_average μ s hs q hq hInt
  have hRight : Integrable (fun ω =>
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, Real.exp (q i ω)) μ :=
    (integrable_finsetSum s fun i hi => hInt i hi).const_mul _
  calc
    (∫ ω, Real.exp ((∑ i ∈ s, q i ω) / (s.card : ℝ)) ∂μ) ≤
        ∫ ω, (s.card : ℝ)⁻¹ * ∑ i ∈ s, Real.exp (q i ω) ∂μ :=
      integral_mono hLeft hRight fun ω => by
        simpa only [div_eq_inv_mul] using
          exp_finset_average_apply_le_average_exp_apply s hs q ω
    _ = (s.card : ℝ)⁻¹ *
        ∑ i ∈ s, ∫ ω, Real.exp (q i ω) ∂μ := by
      rw [integral_const_mul, integral_finsetSum s hInt]
    _ = (∑ i ∈ s, ∫ ω, Real.exp (q i ω) ∂μ) / (s.card : ℝ) := by
      rw [div_eq_inv_mul]

/-- Uniform version: if every one-time exponential moment is bounded by
`B`, then the exponential moment of their arithmetic average is also at
most `B`, with no factor depending on the number of time points. -/
theorem integral_exp_finset_average_le
    (μ : Measure Ω) (s : Finset ι) (hs : s.Nonempty)
    (q : ι → Ω → ℝ) (hq : ∀ i ∈ s, Measurable (q i))
    (hInt : ∀ i ∈ s, Integrable (fun ω => Real.exp (q i ω)) μ)
    {B : ℝ} (hB : ∀ i ∈ s, (∫ ω, Real.exp (q i ω) ∂μ) ≤ B) :
    (∫ ω, Real.exp ((∑ i ∈ s, q i ω) / (s.card : ℝ)) ∂μ) ≤ B := by
  refine (integral_exp_finset_average_le_average_integral_exp
    μ s hs q hq hInt).trans ?_
  have hcardpos : 0 < (s.card : ℝ) := by exact_mod_cast hs.card_pos
  calc
    (∑ i ∈ s, ∫ ω, Real.exp (q i ω) ∂μ) / (s.card : ℝ) ≤
        (∑ _i ∈ s, B) / (s.card : ℝ) := by
      gcongr with i hi
      exact hB i hi
    _ = B := by
      rw [Finset.sum_const, nsmul_eq_mul]
      field_simp

/-- Euler-grid scaling of the pointwise Jensen bound.  The identity
`h = N * delta` is built into the formula: the left side is
`exp (lambda * delta * sum q_k)`, while each one-time term on the right is
`exp (lambda * (N * delta) * q_k)`. -/
theorem exp_mul_step_sum_le_average_exp_mul_horizon
    (n : ℕ) (hn : 0 < n) (lambda delta : ℝ) (q : Fin n → ℝ) :
    Real.exp (lambda * delta * ∑ k, q k) ≤
      (∑ k, Real.exp (lambda * ((n : ℝ) * delta) * q k)) / (n : ℝ) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hs : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty
  have hJ := exp_finset_average_le_average_exp
    (Finset.univ : Finset (Fin n)) hs
    (fun k => lambda * ((n : ℝ) * delta) * q k)
  simp only [Finset.card_univ, Fintype.card_fin] at hJ
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hscale :
      (∑ k, lambda * ((n : ℝ) * delta) * q k) / (n : ℝ) =
        lambda * delta * ∑ k, q k := by
    rw [← Finset.mul_sum]
    field_simp
  rwa [hscale] at hJ

/-- Integrated scaled-grid Jensen inequality with the arithmetic average of
the exact one-time moments retained on the right. -/
theorem integral_exp_mul_step_sum_le_average_one_time
    (μ : Measure Ω) (n : ℕ) (hn : 0 < n) (lambda delta : ℝ)
    (q : Fin n → Ω → ℝ) (hq : ∀ k, Measurable (q k))
    (hInt : ∀ k, Integrable
      (fun ω => Real.exp (lambda * ((n : ℝ) * delta) * q k ω)) μ) :
    (∫ ω, Real.exp (lambda * delta * ∑ k, q k ω) ∂μ) ≤
      (∑ k, ∫ ω,
        Real.exp (lambda * ((n : ℝ) * delta) * q k ω) ∂μ) / (n : ℝ) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hs : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty
  let qScaled : Fin n → Ω → ℝ := fun k ω =>
    lambda * ((n : ℝ) * delta) * q k ω
  have hScaledMeas : ∀ k ∈ (Finset.univ : Finset (Fin n)),
      Measurable (qScaled k) := by
    intro k _
    exact (hq k).const_mul (lambda * ((n : ℝ) * delta))
  have hScaledInt : ∀ k ∈ (Finset.univ : Finset (Fin n)),
      Integrable (fun ω => Real.exp (qScaled k ω)) μ := by
    intro k _
    exact hInt k
  have hJ := integral_exp_finset_average_le_average_integral_exp
    μ (Finset.univ : Finset (Fin n)) hs qScaled hScaledMeas hScaledInt
  simp only [Finset.card_univ, Fintype.card_fin] at hJ
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hscale : (fun ω =>
      (∑ k, qScaled k ω) / (n : ℝ)) =
      fun ω => lambda * delta * ∑ k, q k ω := by
    funext ω
    change (∑ k, lambda * ((n : ℝ) * delta) * q k ω) / (n : ℝ) = _
    rw [← Finset.mul_sum]
    field_simp
  have hexp : (fun ω => Real.exp ((∑ k, qScaled k ω) / (n : ℝ))) =
      fun ω => Real.exp (lambda * delta * ∑ k, q k ω) := by
    funext ω
    rw [congrFun hscale ω]
  rw [hexp] at hJ
  exact hJ

/-- Integrated Euler-grid version.  A uniform bound on the exponential
moment at each single time controls the exponential of the time sum with
the same constant, independently of the number `n` of grid points. -/
theorem integral_exp_mul_step_sum_le_of_one_time
    (μ : Measure Ω) (n : ℕ) (hn : 0 < n) (lambda delta : ℝ)
    (q : Fin n → Ω → ℝ) (hq : ∀ k, Measurable (q k))
    (hInt : ∀ k, Integrable
      (fun ω => Real.exp (lambda * ((n : ℝ) * delta) * q k ω)) μ)
    {B : ℝ} (hMoment : ∀ k,
      (∫ ω, Real.exp (lambda * ((n : ℝ) * delta) * q k ω) ∂μ) ≤ B) :
    (∫ ω, Real.exp (lambda * delta * ∑ k, q k ω) ∂μ) ≤ B := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hs : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty
  let qScaled : Fin n → Ω → ℝ := fun k ω =>
    lambda * ((n : ℝ) * delta) * q k ω
  have hScaledMeas : ∀ k ∈ (Finset.univ : Finset (Fin n)),
      Measurable (qScaled k) := by
    intro k _
    exact (hq k).const_mul (lambda * ((n : ℝ) * delta))
  have hScaledInt : ∀ k ∈ (Finset.univ : Finset (Fin n)),
      Integrable (fun ω => Real.exp (qScaled k ω)) μ := by
    intro k _
    exact hInt k
  have hScaledMoment : ∀ k ∈ (Finset.univ : Finset (Fin n)),
      (∫ ω, Real.exp (qScaled k ω) ∂μ) ≤ B := by
    intro k _
    exact hMoment k
  have hJ := integral_exp_finset_average_le μ
    (Finset.univ : Finset (Fin n)) hs qScaled
    hScaledMeas hScaledInt hScaledMoment
  simp only [Finset.card_univ, Fintype.card_fin] at hJ
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hscale : (fun ω =>
      (∑ k, qScaled k ω) / (n : ℝ)) =
      fun ω => lambda * delta * ∑ k, q k ω := by
    funext ω
    change (∑ k, lambda * ((n : ℝ) * delta) * q k ω) / (n : ℝ) = _
    rw [← Finset.mul_sum]
    field_simp
  have hexp : (fun ω => Real.exp ((∑ k, qScaled k ω) / (n : ℝ))) =
      fun ω => Real.exp (lambda * delta * ∑ k, q k ω) := by
    funext ω
    rw [congrFun hscale ω]
  rw [hexp] at hJ
  exact hJ

/-- Norm-square specialization used for Gaussian partial sums.  Once each
`S_k` has the expected Gaussian marginal bound at horizon
`h = n * delta`, Jensen supplies the required path-energy estimate without
any maximal-inequality infrastructure. -/
theorem integral_exp_mul_step_sum_norm_sq_le_of_one_time
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) (n : ℕ) (hn : 0 < n) (lambda delta : ℝ)
    (S : Fin n → Ω → E) (hS : ∀ k, Measurable (S k))
    (hInt : ∀ k, Integrable (fun ω =>
      Real.exp (lambda * ((n : ℝ) * delta) * ‖S k ω‖ ^ 2)) μ)
    {B : ℝ} (hMoment : ∀ k,
      (∫ ω, Real.exp (lambda * ((n : ℝ) * delta) * ‖S k ω‖ ^ 2) ∂μ) ≤ B) :
    (∫ ω, Real.exp (lambda * delta * ∑ k, ‖S k ω‖ ^ 2) ∂μ) ≤ B := by
  exact integral_exp_mul_step_sum_le_of_one_time μ n hn lambda delta
    (fun k ω => ‖S k ω‖ ^ 2) (fun k => by fun_prop) hInt hMoment

end FiniteJensen

section GaussianNormSquare

/-! The following lemmas provide the one-time input for the Jensen bypass.
They derive the quadratic exponential moment directly from the real Gaussian
density and the finite product presentation of `stdGaussian`. -/

/-- Integrability of the quadratic exponential under a real standard
Gaussian, up to its sharp threshold `a < 1/2`. -/
theorem integrable_exp_mul_sq_gaussianReal (a : ℝ) (ha : a < 1 / 2) :
    Integrable (fun x : ℝ => Real.exp (a * x ^ 2)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (v := 1) (by norm_num)]
  rw [integrable_withDensity_iff (measurable_gaussianPDF 0 1)
    (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp only [toReal_gaussianPDF]
  have hb : 0 < 1 / 2 - a := sub_pos.mpr ha
  have hbase :=
    (integrable_exp_neg_mul_sq hb).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  apply hbase.congr
  exact ae_of_all _ fun x => by
    simp only [gaussianPDFReal, NNReal.coe_one, sub_zero]
    norm_num
    have he : Real.exp ((a - 1 / 2) * x ^ 2) =
        Real.exp (-x ^ 2 / 2) * Real.exp (a * x ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    ring

/-- Exact quadratic exponential moment of a real standard Gaussian. -/
theorem integral_exp_mul_sq_gaussianReal (a : ℝ) (ha : a < 1 / 2) :
    (∫ x : ℝ, Real.exp (a * x ^ 2) ∂gaussianReal 0 1) =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.sqrt (Real.pi / (1 / 2 - a)) := by
  rw [gaussianReal_of_var_ne_zero 0 (v := 1) (by norm_num)]
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_gaussianPDF 0 1)
    (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp only [toReal_gaussianPDF, smul_eq_mul]
  have hb : 0 < 1 / 2 - a := sub_pos.mpr ha
  have heq :
      (fun x : ℝ => gaussianPDFReal 0 1 x * Real.exp (a * x ^ 2)) =
        fun x => (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.exp (-(1 / 2 - a) * x ^ 2) := by
    funext x
    simp only [gaussianPDFReal, NNReal.coe_one, sub_zero]
    norm_num
    have he : Real.exp ((a - 1 / 2) * x ^ 2) =
        Real.exp (-x ^ 2 / 2) * Real.exp (a * x ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    ring
  rw [heq, integral_const_mul, integral_gaussian (1 / 2 - a)]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Integrability of the norm-square exponential under an arbitrary
finite-dimensional standard Gaussian. -/
theorem integrable_exp_mul_norm_sq_stdGaussian (a : ℝ) (ha : a < 1 / 2) :
    Integrable (fun z : E => Real.exp (a * ‖z‖ ^ 2)) (stdGaussian E) := by
  let b := stdOrthonormalBasis ℝ E
  rw [stdGaussian_eq_map_pi_orthonormalBasis b]
  apply (integrable_map_measure (by fun_prop)
    (Measurable.aemeasurable (by fun_prop))).2
  have hnorm : ∀ x : Fin (Module.finrank ℝ E) → ℝ,
      ‖∑ i, x i • b i‖ ^ 2 = ∑ i, (x i) ^ 2 := by
    intro x
    rw [← b.sum_sq_inner_right]
    congr 1 with i
    rw [b.orthonormal.inner_right_fintype]
  have hprod : Integrable
      (fun x : Fin (Module.finrank ℝ E) → ℝ =>
        ∏ i, Real.exp (a * (x i) ^ 2))
      (Measure.pi fun _ => gaussianReal 0 1) :=
    Integrable.fintype_prod fun _ =>
      integrable_exp_mul_sq_gaussianReal a ha
  apply hprod.congr
  exact ae_of_all _ fun x => by
    simp only [Function.comp_apply, hnorm, Finset.mul_sum, Real.exp_sum]

/-- Exact finite-dimensional standard-Gaussian norm-square MGF, in a form
that avoids introducing real powers:

`E exp(a ‖Z‖²) = c(a)^(finrank E)`, `a < 1/2`.
-/
theorem integral_exp_mul_norm_sq_stdGaussian (a : ℝ) (ha : a < 1 / 2) :
    (∫ z : E, Real.exp (a * ‖z‖ ^ 2) ∂stdGaussian E) =
      ((Real.sqrt (2 * Real.pi))⁻¹ *
        Real.sqrt (Real.pi / (1 / 2 - a))) ^ (Module.finrank ℝ E) := by
  let b := stdOrthonormalBasis ℝ E
  rw [stdGaussian_eq_map_pi_orthonormalBasis b]
  rw [integral_map (Measurable.aemeasurable (by fun_prop)) (by fun_prop)]
  have hnorm : ∀ x : Fin (Module.finrank ℝ E) → ℝ,
      ‖∑ i, x i • b i‖ ^ 2 = ∑ i, (x i) ^ 2 := by
    intro x
    rw [← b.sum_sq_inner_right]
    congr 1 with i
    rw [b.orthonormal.inner_right_fintype]
  simp_rw [hnorm, Finset.mul_sum, Real.exp_sum]
  rw [integral_fintype_prod_eq_pow
    (ι := Fin (Module.finrank ℝ E))
    (μ := gaussianReal 0 1) (fun x : ℝ => Real.exp (a * x ^ 2)),
    Fintype.card_fin]
  congr 1
  exact integral_exp_mul_sq_gaussianReal a ha

/-- Scaled version of quadratic-exponential integrability. -/
theorem integrable_exp_mul_norm_sq_smul_stdGaussian
    (a c : ℝ) (ha : a * c ^ 2 < 1 / 2) :
    Integrable (fun z : E => Real.exp (a * ‖c • z‖ ^ 2))
      (stdGaussian E) := by
  have hbase := integrable_exp_mul_norm_sq_stdGaussian (E := E)
    (a * c ^ 2) ha
  apply hbase.congr
  exact ae_of_all _ fun z => by
    change Real.exp (a * c ^ 2 * ‖z‖ ^ 2) =
      Real.exp (a * ‖c • z‖ ^ 2)
    congr 1
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring

/-- Exact norm-square MGF after a deterministic scalar dilation of a
standard Gaussian.  This is the one-time formula for a Gaussian partial sum
once its marginal is written as `sqrt(t) • Z`. -/
theorem integral_exp_mul_norm_sq_smul_stdGaussian
    (a c : ℝ) (ha : a * c ^ 2 < 1 / 2) :
    (∫ z : E, Real.exp (a * ‖c • z‖ ^ 2) ∂stdGaussian E) =
      ((Real.sqrt (2 * Real.pi))⁻¹ *
        Real.sqrt (Real.pi / (1 / 2 - a * c ^ 2))) ^
          (Module.finrank ℝ E) := by
  have hbase := integral_exp_mul_norm_sq_stdGaussian (E := E)
    (a * c ^ 2) ha
  calc
    (∫ z : E, Real.exp (a * ‖c • z‖ ^ 2) ∂stdGaussian E) =
        ∫ z : E, Real.exp (a * c ^ 2 * ‖z‖ ^ 2) ∂stdGaussian E := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        change Real.exp (a * ‖c • z‖ ^ 2) =
          Real.exp (a * c ^ 2 * ‖z‖ ^ 2)
        congr 1
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        ring
    _ = _ := hbase

/-- Transfer quadratic-exponential integrability through a supplied
scaled-standard-Gaussian marginal identity.  This isolates the law
identification from the analytic estimate. -/
theorem integrable_exp_mul_norm_sq_of_map_eq_smul_stdGaussian
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : Ω → E) (hS : Measurable S) (a c : ℝ)
    (ha : a * c ^ 2 < 1 / 2)
    (hmap : Measure.map S μ =
      Measure.map (fun z : E => c • z) (stdGaussian E)) :
    Integrable (fun ω => Real.exp (a * ‖S ω‖ ^ 2)) μ := by
  let g : E → ℝ := fun x => Real.exp (a * ‖x‖ ^ 2)
  have hbase : Integrable (g ∘ fun z : E => c • z) (stdGaussian E) := by
    simpa [g, Function.comp_def] using
      integrable_exp_mul_norm_sq_smul_stdGaussian (E := E) a c ha
  have himage : Integrable g
      (Measure.map (fun z : E => c • z) (stdGaussian E)) :=
    (integrable_map_measure (by fun_prop)
      (Measurable.aemeasurable (by fun_prop))).2 hbase
  rw [← hmap] at himage
  have hpullback :=
    (integrable_map_measure (by fun_prop) hS.aemeasurable).1 himage
  simpa [g, Function.comp_def] using hpullback

/-- Exact quadratic-exponential moment under a supplied
scaled-standard-Gaussian marginal identity. -/
theorem integral_exp_mul_norm_sq_of_map_eq_smul_stdGaussian
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : Ω → E) (hS : Measurable S) (a c : ℝ)
    (ha : a * c ^ 2 < 1 / 2)
    (hmap : Measure.map S μ =
      Measure.map (fun z : E => c • z) (stdGaussian E)) :
    (∫ ω, Real.exp (a * ‖S ω‖ ^ 2) ∂μ) =
      ((Real.sqrt (2 * Real.pi))⁻¹ *
        Real.sqrt (Real.pi / (1 / 2 - a * c ^ 2))) ^
          (Module.finrank ℝ E) := by
  calc
    (∫ ω, Real.exp (a * ‖S ω‖ ^ 2) ∂μ) =
        ∫ x : E, Real.exp (a * ‖x‖ ^ 2) ∂Measure.map S μ := by
      rw [integral_map hS.aemeasurable (by fun_prop)]
    _ = ∫ x : E, Real.exp (a * ‖x‖ ^ 2)
        ∂Measure.map (fun z : E => c • z) (stdGaussian E) := by
      rw [hmap]
    _ = ∫ z : E, Real.exp (a * ‖c • z‖ ^ 2) ∂stdGaussian E := by
      rw [integral_map (Measurable.aemeasurable (by fun_prop)) (by fun_prop)]
    _ = _ := integral_exp_mul_norm_sq_smul_stdGaussian (E := E) a c ha

/-- Complete finite-grid Gaussian-energy estimate conditional only on the
elementary marginal identities.  For every grid time `k`, the caller supplies
that `S k` has the same law as `c k • Z`.  If the resulting explicit
one-time moments are bounded by `B`, then

`E exp(lambda * delta * sum_k ‖S_k‖²) <= B`,

uniformly in the number of grid points. -/
theorem integral_exp_mul_step_sum_norm_sq_le_of_scaledGaussian_marginals
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (n : ℕ) (hn : 0 < n) (lambda delta : ℝ)
    (S : Fin n → Ω → E) (hS : ∀ k, Measurable (S k))
    (c : Fin n → ℝ)
    (hmap : ∀ k, Measure.map (S k) μ =
      Measure.map (fun z : E => c k • z) (stdGaussian E))
    (hThreshold : ∀ k,
      (lambda * ((n : ℝ) * delta)) * (c k) ^ 2 < 1 / 2)
    {B : ℝ} (hMoment : ∀ k,
      ((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt
        (Real.pi / (1 / 2 -
          (lambda * ((n : ℝ) * delta)) * (c k) ^ 2))) ^
            (Module.finrank ℝ E) ≤ B) :
    (∫ ω, Real.exp
      (lambda * delta * ∑ k, ‖S k ω‖ ^ 2) ∂μ) ≤ B := by
  apply integral_exp_mul_step_sum_norm_sq_le_of_one_time
    μ n hn lambda delta S hS
  · intro k
    exact integrable_exp_mul_norm_sq_of_map_eq_smul_stdGaussian
      μ (S k) (hS k) (lambda * ((n : ℝ) * delta)) (c k)
      (hThreshold k) (hmap k)
  · intro k
    rw [integral_exp_mul_norm_sq_of_map_eq_smul_stdGaussian
      μ (S k) (hS k) (lambda * ((n : ℝ) * delta)) (c k)
      (hThreshold k) (hmap k)]
    exact hMoment k

end GaussianNormSquare

section GaussianPartialSum

variable {Ω E ι : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- A finite sum of independent standard Gaussian vectors has the law of a
standard Gaussian dilated by the square root of the number of summands.

The proof is a finite product of characteristic functions.  It uses neither
a stochastic process nor a limiting theorem. -/
theorem map_finsetSum_eq_map_sqrt_card_smul_stdGaussian
    (μ : Measure Ω) (Z : ι → Ω → E) (s : Finset ι)
    (hZ : ∀ i ∈ s, Measurable (Z i))
    (hIndep : iIndepFun (s.restrict Z) μ)
    (hLaw : ∀ i ∈ s, Measure.map (Z i) μ = stdGaussian E) :
    Measure.map (fun ω => ∑ i ∈ s, Z i ω) μ =
      Measure.map (fun z : E => Real.sqrt s.card • z) (stdGaussian E) := by
  letI := hIndep.isProbabilityMeasure
  let scale : E →L[ℝ] E :=
    (Real.sqrt s.card) • ContinuousLinearMap.id ℝ E
  have hscale : (scale : E → E) = fun z => Real.sqrt s.card • z := by
    funext z
    simp [scale]
  rw [← hscale]
  apply Measure.ext_of_charFunDual
  ext L
  rw [hIndep.charFunDual_map_fun_finsetSum_eq_prod
    (fun i hi => (hZ i hi).aemeasurable)]
  simp only [Finset.prod_apply]
  have hprod : (∏ i ∈ s, charFunDual (Measure.map (Z i) μ) L) =
      ∏ _i ∈ s, charFunDual (stdGaussian E) L := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [hLaw i hi]
  rw [hprod]
  simp_rw [charFunDual_stdGaussian]
  rw [charFunDual_map scale L, charFunDual_stdGaussian]
  have hcomp : L.comp scale = Real.sqrt s.card • L := by
    ext z
    simp [scale]
  rw [hcomp, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsqrt : (Real.sqrt (s.card : ℝ) * ‖L‖) ^ 2 =
      (s.card : ℝ) * ‖L‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hsqrtC : ((Real.sqrt (s.card : ℝ) * ‖L‖ : ℝ) : ℂ) ^ 2 =
      (s.card : ℂ) * (‖L‖ : ℂ) ^ 2 := by
    exact_mod_cast hsqrt
  rw [hsqrtC, Finset.prod_const, ← Complex.exp_nat_mul]
  congr 1
  ring

/-- Scaling the preceding finite sum by `sqrt delta` gives a Gaussian with
scalar dilation `sqrt delta * sqrt(card s)`. -/
theorem map_sqrt_smul_finsetSum_eq_scaled_stdGaussian
    (μ : Measure Ω) (Z : ι → Ω → E) (s : Finset ι) (delta : ℝ)
    (hZ : ∀ i ∈ s, Measurable (Z i))
    (hIndep : iIndepFun (s.restrict Z) μ)
    (hLaw : ∀ i ∈ s, Measure.map (Z i) μ = stdGaussian E) :
    Measure.map (fun ω => Real.sqrt delta • ∑ i ∈ s, Z i ω) μ =
      Measure.map (fun z : E =>
        (Real.sqrt delta * Real.sqrt s.card) • z) (stdGaussian E) := by
  have hsum := map_finsetSum_eq_map_sqrt_card_smul_stdGaussian
    μ Z s hZ hIndep hLaw
  calc
    Measure.map (fun ω => Real.sqrt delta • ∑ i ∈ s, Z i ω) μ =
        Measure.map (fun x : E => Real.sqrt delta • x)
          (Measure.map (fun ω => ∑ i ∈ s, Z i ω) μ) := by
      rw [Measure.map_map]
      · rfl
      · fun_prop
      · exact Finset.measurable_sum s fun i hi => hZ i hi
    _ = Measure.map (fun x : E => Real.sqrt delta • x)
          (Measure.map (fun z : E => Real.sqrt s.card • z)
            (stdGaussian E)) := by rw [hsum]
    _ = Measure.map (fun z : E =>
        (Real.sqrt delta * Real.sqrt s.card) • z) (stdGaussian E) := by
      rw [Measure.map_map]
      · congr 1
        funext z
        simp only [Function.comp_apply, smul_smul]
      · fun_prop
      · fun_prop

/-- Exact quadratic MGF of a scaled finite sum of independent standard
Gaussian vectors.  The variance parameter is `delta * card s`, as expected.
-/
theorem integral_exp_norm_sq_sqrt_smul_finsetSum
    (μ : Measure Ω) (Z : ι → Ω → E) (s : Finset ι)
    (delta a : ℝ) (hdelta : 0 ≤ delta)
    (hZ : ∀ i ∈ s, Measurable (Z i))
    (hIndep : iIndepFun (s.restrict Z) μ)
    (hLaw : ∀ i ∈ s, Measure.map (Z i) μ = stdGaussian E)
    (ha : a * (delta * (s.card : ℝ)) < 1 / 2) :
    (∫ ω, Real.exp
      (a * ‖Real.sqrt delta • ∑ i ∈ s, Z i ω‖ ^ 2) ∂μ) =
      ((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt
        (Real.pi / (1 / 2 - a * (delta * (s.card : ℝ))))) ^
          (Module.finrank ℝ E) := by
  have hmap := map_sqrt_smul_finsetSum_eq_scaled_stdGaussian
    μ Z s delta hZ hIndep hLaw
  have hc : (Real.sqrt delta * Real.sqrt (s.card : ℝ)) ^ 2 =
      delta * (s.card : ℝ) := by
    rw [mul_pow, Real.sq_sqrt hdelta,
      Real.sq_sqrt (Nat.cast_nonneg _)]
  have hthreshold :
      a * (Real.sqrt delta * Real.sqrt (s.card : ℝ)) ^ 2 < 1 / 2 := by
    rwa [hc]
  rw [integral_exp_mul_norm_sq_of_map_eq_smul_stdGaussian
    μ (fun ω => Real.sqrt delta • ∑ i ∈ s, Z i ω)
    (by fun_prop) a (Real.sqrt delta * Real.sqrt (s.card : ℝ))
    hthreshold hmap, hc]

/-- Unconditional finite-grid energy estimate for all partial sums of an
i.i.d. standard Gaussian sequence.  The right side is an arithmetic average
of explicit one-time Gaussian moments and hence has no factor growing with
the number of grid points.

This theorem is the direct replacement for the Doob/maximal-inequality line
in the paper. -/
theorem integral_exp_step_sum_gaussianPartialSums_le
    (μ : Measure Ω) (n : ℕ) (hn : 0 < n)
    (Z : Fin n → Ω → E) (hZ : ∀ i, Measurable (Z i))
    (hIndep : iIndepFun Z μ)
    (hLaw : ∀ i, Measure.map (Z i) μ = stdGaussian E)
    (delta lambda : ℝ) (hdelta : 0 ≤ delta)
    (hThreshold : ∀ k : Fin n,
      (lambda * ((n : ℝ) * delta)) *
        (delta * ((Finset.Iic k).card : ℝ)) < 1 / 2) :
    (∫ ω, Real.exp (lambda * delta * ∑ k : Fin n,
      ‖Real.sqrt delta • ∑ i ∈ Finset.Iic k, Z i ω‖ ^ 2) ∂μ) ≤
      (∑ k : Fin n,
        ((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt
          (Real.pi / (1 / 2 -
            (lambda * ((n : ℝ) * delta)) *
              (delta * ((Finset.Iic k).card : ℝ))))) ^
                (Module.finrank ℝ E)) / (n : ℝ) := by
  let S : Fin n → Ω → E := fun k ω =>
    Real.sqrt delta • ∑ i ∈ Finset.Iic k, Z i ω
  have hS : ∀ k, Measurable (S k) := by
    intro k
    exact (Finset.measurable_sum (Finset.Iic k)
      fun i _ => hZ i).const_smul _
  have hmap : ∀ k, Measure.map (S k) μ =
      Measure.map (fun z : E =>
        (Real.sqrt delta * Real.sqrt ((Finset.Iic k).card : ℝ)) • z)
          (stdGaussian E) := by
    intro k
    exact map_sqrt_smul_finsetSum_eq_scaled_stdGaussian
      μ Z (Finset.Iic k) delta (fun i _ => hZ i)
      (hIndep.restrict _) (fun i _ => hLaw i)
  have hc : ∀ k : Fin n,
      (Real.sqrt delta * Real.sqrt ((Finset.Iic k).card : ℝ)) ^ 2 =
        delta * ((Finset.Iic k).card : ℝ) := by
    intro k
    rw [mul_pow, Real.sq_sqrt hdelta,
      Real.sq_sqrt (Nat.cast_nonneg _)]
  have hInt : ∀ k, Integrable (fun ω =>
      Real.exp (lambda * ((n : ℝ) * delta) * ‖S k ω‖ ^ 2)) μ := by
    intro k
    apply integrable_exp_mul_norm_sq_of_map_eq_smul_stdGaussian
      μ (S k) (hS k) (lambda * ((n : ℝ) * delta))
      (Real.sqrt delta * Real.sqrt ((Finset.Iic k).card : ℝ))
    · rw [hc k]
      exact hThreshold k
    · exact hmap k
  have hJ := integral_exp_mul_step_sum_le_average_one_time
    μ n hn lambda delta (fun k ω => ‖S k ω‖ ^ 2)
    (fun k => by fun_prop) hInt
  change (∫ ω, Real.exp (lambda * delta * ∑ k : Fin n,
      ‖S k ω‖ ^ 2) ∂μ) ≤ _
  refine hJ.trans_eq ?_
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_exp_mul_norm_sq_of_map_eq_smul_stdGaussian
    μ (S k) (hS k) (lambda * ((n : ℝ) * delta))
    (Real.sqrt delta * Real.sqrt ((Finset.Iic k).card : ℝ))
    (by rw [hc k]; exact hThreshold k) (hmap k), hc k]

end GaussianPartialSum

end DiscreteTime

end

end UniformRandomMALA
