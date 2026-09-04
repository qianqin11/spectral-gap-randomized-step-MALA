import UniformRandomMALA.Concrete.RandomWalkMetropolis

/-!
# Equality of the explicit and density presentations of a Gaussian proposal

This file isolates the finite-dimensional measure-theoretic bridge between
the random variable `x + sqrt (2 * δ) • Z`, with `Z` standard Gaussian, and
the normalized Lebesgue density used to define the concrete RWM kernel.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace DiscreteTime

open Concrete Concrete.FirstOrderPotential

variable {d : ℕ}

section Centered

variable (V : FirstOrderPotential d)

private lemma ofReal_proposalNormalizer {δ : ℝ} (hδ : 0 < δ) :
    ((proposalNormalizer (d := d) δ : ℝ) : ℂ) =
      ((Real.pi : ℂ) / ((1 / (4 * δ) : ℝ) : ℂ)) ^
        ((Module.finrank ℝ (State d) : ℂ) / 2) := by
  unfold proposalNormalizer
  rw [← Complex.ofReal_div]
  rw [Complex.ofReal_cpow]
  · simp
  · positivity

lemma charFun_randomWalkProposal_zero {δ : ℝ} (hδ : 0 < δ)
    (t : State d) :
    charFun (V.randomWalkProposal δ 0) t =
      Complex.exp (-(δ : ℂ) * (‖t‖ : ℂ) ^ 2) := by
  letI : Fact (0 < δ) := ⟨hδ⟩
  rw [charFun_apply, randomWalkProposal,
    Kernel.withDensity_apply
      (Kernel.const (State d) (volume : Measure (State d)))
      (V.measurable_uncurry_randomWalkDensity δ) 0]
  rw [integral_withDensity_eq_integral_toReal_smul
    (Measurable.of_uncurry_left (V.measurable_uncurry_randomWalkDensity δ))
    (ae_of_all _ fun y => (V.randomWalkDensity_ne_top δ 0 y).lt_top)]
  simp only [Kernel.const_apply]
  simp_rw [randomWalkDensity, ENNReal.toReal_ofReal
    (V.randomWalkDensityReal_nonneg hδ 0 _)]
  unfold randomWalkDensityReal randomWalkBase randomWalkNormalizer
  simp only [sub_zero]
  have hint (y : State d) :
      (Real.exp (-(1 / (4 * δ)) * ‖y‖ ^ 2) /
          proposalNormalizer (d := d) δ) •
          Complex.exp ((inner ℝ y t : ℂ) * Complex.I) =
        ((proposalNormalizer (d := d) δ : ℝ) : ℂ)⁻¹ *
          Complex.exp
            (-((1 / (4 * δ) : ℝ) : ℂ) * (‖y‖ : ℂ) ^ 2 +
              Complex.I * (inner ℝ t y : ℂ)) := by
    rw [RCLike.real_smul_eq_coe_mul]
    change Complex.ofReal
        (Real.exp (-(1 / (4 * δ)) * ‖y‖ ^ 2) /
          proposalNormalizer (d := d) δ) * _ = _
    rw [Complex.ofReal_div, Complex.ofReal_exp,
      div_eq_mul_inv, mul_assoc]
    calc
      _ = ((proposalNormalizer (d := d) δ : ℝ) : ℂ)⁻¹ *
          (Complex.exp ((-(1 / (4 * δ)) * ‖y‖ ^ 2 : ℝ) : ℂ) *
            Complex.exp ((inner ℝ y t : ℂ) * Complex.I)) := by ring
      _ = _ := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        rw [real_inner_comm]
        ring
  simp_rw [hint]
  rw [integral_const_mul]
  have hb : 0 < (((1 / (4 * δ) : ℝ) : ℂ)).re := by
    exact one_div_pos.mpr (mul_pos (by norm_num) hδ)
  rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (V := State d) hb Complex.I t]
  rw [ofReal_proposalNormalizer (d := d) hδ]
  have hb0 : (1 / (4 * δ) : ℝ) ≠ 0 :=
    (one_div_pos.mpr (mul_pos (by norm_num) hδ)).ne'
  have hbase :
      (Real.pi : ℂ) / ((1 / (4 * δ) : ℝ) : ℂ) ≠ 0 :=
    div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
      (Complex.ofReal_ne_zero.mpr hb0)
  have hpow :
      ((Real.pi : ℂ) / ((1 / (4 * δ) : ℝ) : ℂ)) ^
          ((Module.finrank ℝ (State d) : ℂ) / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hbase)
  rw [← mul_assoc, inv_mul_cancel₀ hpow, one_mul]
  congr 1
  rw [Complex.I_sq]
  push_cast
  field_simp [ne_of_gt hδ]

/-- The centered density-defined RWM proposal is exactly the law of a
scaled standard Gaussian innovation. -/
theorem randomWalkProposal_zero_eq_map_stdGaussian {δ : ℝ} (hδ : 0 < δ) :
    V.randomWalkProposal δ 0 =
      (stdGaussian (State d)).map
        (fun z : State d => Real.sqrt (2 * δ) • z) := by
  letI : Fact (0 < δ) := ⟨hδ⟩
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_randomWalkProposal_zero V hδ t,
    charFun_map_smul, charFun_stdGaussian]
  congr 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  norm_cast
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  ring

/-- Characteristic function of a density-defined RWM proposal started from
an arbitrary deterministic point. -/
lemma charFun_randomWalkProposal {δ : ℝ} (hδ : 0 < δ)
    (x t : State d) :
    charFun (V.randomWalkProposal δ x) t =
      Complex.exp (-(δ : ℂ) * (‖t‖ : ℂ) ^ 2) *
        Complex.exp ((inner ℝ x t : ℂ) * Complex.I) := by
  letI : Fact (0 < δ) := ⟨hδ⟩
  rw [charFun_apply, randomWalkProposal,
    Kernel.withDensity_apply
      (Kernel.const (State d) (volume : Measure (State d)))
      (V.measurable_uncurry_randomWalkDensity δ) x]
  rw [integral_withDensity_eq_integral_toReal_smul
    (Measurable.of_uncurry_left (V.measurable_uncurry_randomWalkDensity δ))
    (ae_of_all _ fun y => (V.randomWalkDensity_ne_top δ x y).lt_top)]
  simp only [Kernel.const_apply]
  simp_rw [randomWalkDensity, ENNReal.toReal_ofReal
    (V.randomWalkDensityReal_nonneg hδ x _)]
  unfold randomWalkDensityReal randomWalkBase randomWalkNormalizer
  let F : State d → ℂ := fun y =>
    (Real.exp (-(1 / (4 * δ)) * ‖y‖ ^ 2) /
      proposalNormalizer (d := d) δ) •
        Complex.exp ((inner ℝ (y + x) t : ℂ) * Complex.I)
  have htranslate (y : State d) :
      (Real.exp (-(1 / (4 * δ)) * ‖y - x‖ ^ 2) /
        proposalNormalizer (d := d) δ) •
          Complex.exp ((inner ℝ y t : ℂ) * Complex.I) = F (y - x) := by
    simp only [F, sub_add_cancel]
  have hsplit (y : State d) :
      F y =
        ((Real.exp (-(1 / (4 * δ)) * ‖y‖ ^ 2) /
          proposalNormalizer (d := d) δ) •
            Complex.exp ((inner ℝ y t : ℂ) * Complex.I)) *
              Complex.exp ((inner ℝ x t : ℂ) * Complex.I) := by
    simp only [F, inner_add_left]
    push_cast
    rw [add_mul, Complex.exp_add]
    simp only [RCLike.real_smul_eq_coe_mul]
    ring
  have hcenter :
      (∫ y : State d,
        (Real.exp (-(1 / (4 * δ)) * ‖y‖ ^ 2) /
          proposalNormalizer (d := d) δ) •
            Complex.exp ((inner ℝ y t : ℂ) * Complex.I)) =
        Complex.exp (-(δ : ℂ) * (‖t‖ : ℂ) ^ 2) := by
    have hc := charFun_randomWalkProposal_zero V hδ t
    rw [charFun_apply, randomWalkProposal,
      Kernel.withDensity_apply
        (Kernel.const (State d) (volume : Measure (State d)))
        (V.measurable_uncurry_randomWalkDensity δ) 0] at hc
    rw [integral_withDensity_eq_integral_toReal_smul
      (Measurable.of_uncurry_left (V.measurable_uncurry_randomWalkDensity δ))
      (ae_of_all _ fun y => (V.randomWalkDensity_ne_top δ 0 y).lt_top)] at hc
    simp only [Kernel.const_apply] at hc
    simp_rw [randomWalkDensity, ENNReal.toReal_ofReal
      (V.randomWalkDensityReal_nonneg hδ 0 _)] at hc
    simpa only [randomWalkDensityReal, randomWalkBase,
      randomWalkNormalizer, sub_zero] using hc
  calc
    (∫ y : State d,
      (Real.exp (-(1 / (4 * δ)) * ‖y - x‖ ^ 2) /
        proposalNormalizer (d := d) δ) •
          Complex.exp ((inner ℝ y t : ℂ) * Complex.I)) =
        ∫ y, F (y - x) := integral_congr_ae (ae_of_all _ htranslate)
    _ = ∫ y, F y := integral_sub_right_eq_self F x
    _ = ∫ y : State d,
        ((Real.exp (-(1 / (4 * δ)) * ‖y‖ ^ 2) /
          proposalNormalizer (d := d) δ) •
            Complex.exp ((inner ℝ y t : ℂ) * Complex.I)) *
              Complex.exp ((inner ℝ x t : ℂ) * Complex.I) :=
      integral_congr_ae (ae_of_all _ hsplit)
    _ = (∫ y : State d,
        (Real.exp (-(1 / (4 * δ)) * ‖y‖ ^ 2) /
          proposalNormalizer (d := d) δ) •
            Complex.exp ((inner ℝ y t : ℂ) * Complex.I)) *
              Complex.exp ((inner ℝ x t : ℂ) * Complex.I) := by
      rw [integral_mul_const]
    _ = _ := by rw [hcenter]

/-- Full Gaussian proposal-law bridge.  For every starting point `x`, the
Lebesgue-density RWM proposal is the pushforward of `stdGaussian` by
`z ↦ x + sqrt (2 * δ) • z`. -/
theorem randomWalkProposal_eq_map_stdGaussian {δ : ℝ} (hδ : 0 < δ)
    (x : State d) :
    V.randomWalkProposal δ x =
      (stdGaussian (State d)).map
        (fun z : State d => x + Real.sqrt (2 * δ) • z) := by
  letI : Fact (0 < δ) := ⟨hδ⟩
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_randomWalkProposal V hδ x t]
  have hmap :
      (stdGaussian (State d)).map
          (fun z : State d => x + Real.sqrt (2 * δ) • z) =
        ((stdGaussian (State d)).map
          (fun z : State d => Real.sqrt (2 * δ) • z)).map (fun y => x + y) := by
    rw [Measure.map_map]
    · rfl
    · fun_prop
    · fun_prop
  rw [hmap, charFun_map_const_add, charFun_map_smul, charFun_stdGaussian]
  congr 2
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  norm_cast
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  ring

/-! ## Consequences for the two MALA proposal presentations -/

/-- At a fixed starting point, the density-defined MALA proposal is the RWM
proposal started from the deterministic Euler mean. -/
lemma gaussianDensityProposal_apply_eq_randomWalkProposal {h : ℝ}
    (x : State d) :
    V.gaussianDensityProposal h x =
      V.randomWalkProposal h (V.proposalMean h x) := by
  rw [gaussianDensityProposal,
    Kernel.withDensity_apply
      (Kernel.const (State d) (volume : Measure (State d)))
      (V.measurable_uncurry_proposalDensity h) x]
  rw [randomWalkProposal,
    Kernel.withDensity_apply
      (Kernel.const (State d) (volume : Measure (State d)))
      (V.measurable_uncurry_randomWalkDensity h) (V.proposalMean h x)]
  congr 1

/-- The pushforward-defined MALA proposal at `(h,x)` is literally the law of
the displayed affine function of a standard Gaussian innovation. -/
lemma gaussianProposal_apply_eq_map_stdGaussian (h : ℝ) (x : State d) :
    V.gaussianProposal h x =
      (stdGaussian (State d)).map
        (fun z : State d =>
          V.proposalMean h x + Real.sqrt (2 * h) • z) := by
  ext s hs
  have hg : Measurable (s.indicator fun _ : State d => (1 : ℝ≥0∞)) :=
    Measurable.indicator measurable_const hs
  have hi := V.lintegral_gaussianProposal h x hg
  rw [Measure.map_apply (by fun_prop) hs]
  have hleft :
      (∫⁻ y : State d,
        s.indicator (fun _ : State d => (1 : ℝ≥0∞)) y
          ∂V.gaussianProposal h x) = V.gaussianProposal h x s := by
    exact lintegral_indicator_one hs
  have hpre : MeasurableSet
      ((fun z : State d =>
        V.proposalMean h x + Real.sqrt (2 * h) • z) ⁻¹' s) :=
    hs.preimage (by fun_prop)
  have hright :
      (∫⁻ z : State d,
        s.indicator (fun _ : State d => (1 : ℝ≥0∞))
          (V.proposalMean h x + Real.sqrt (2 * h) • z)
          ∂stdGaussian (State d)) =
        (stdGaussian (State d))
          ((fun z : State d =>
            V.proposalMean h x + Real.sqrt (2 * h) • z) ⁻¹' s) := by
    change (∫⁻ z : State d,
      ((fun z : State d =>
        V.proposalMean h x + Real.sqrt (2 * h) • z) ⁻¹' s).indicator
          (fun _ : State d => (1 : ℝ≥0∞)) z ∂stdGaussian (State d)) = _
    exact lintegral_indicator_one hpre
  rw [hleft, hright] at hi
  exact hi

/-- For positive step size, the pushforward and Lebesgue-density definitions
of the MALA Gaussian proposal kernel coincide. -/
theorem gaussianProposal_eq_gaussianDensityProposal {h : ℝ} (hh : 0 < h) :
    V.gaussianProposal h = V.gaussianDensityProposal h := by
  ext x
  rw [gaussianProposal_apply_eq_map_stdGaussian V h x,
    gaussianDensityProposal_apply_eq_randomWalkProposal V x,
    randomWalkProposal_eq_map_stdGaussian V hh (V.proposalMean h x)]

/-- The density-defined MALA proposal is the same translated Gaussian
measure as the RWM proposal started from its Euler mean. -/
theorem gaussianDensityProposal_eq_randomWalkProposal
    (h : ℝ) (x : State d) :
    V.gaussianDensityProposal h x =
      V.randomWalkProposal h (V.proposalMean h x) := by
  ext s hs
  rw [V.gaussianDensityProposal_apply x s]
  rw [randomWalkProposal, Kernel.withDensity_apply'
    (Kernel.const (State d) (volume : Measure (State d)))
    (V.measurable_uncurry_randomWalkDensity h) (V.proposalMean h x) s]
  simp only [Kernel.const_apply]
  apply lintegral_congr
  intro y
  simp only [proposalDensity, proposalDensityReal, proposalBase,
    randomWalkDensity, randomWalkDensityReal, randomWalkBase,
    randomWalkNormalizer]

/-- Full MALA proposal-law bridge for the density presentation used in the
Metropolis kernel. -/
theorem gaussianDensityProposal_eq_map_stdGaussian
    {h : ℝ} (hh : 0 < h) (x : State d) :
    V.gaussianDensityProposal h x =
      (stdGaussian (State d)).map
        (fun z : State d =>
          V.proposalMean h x + Real.sqrt (2 * h) • z) := by
  rw [gaussianDensityProposal_eq_randomWalkProposal V h x,
    randomWalkProposal_eq_map_stdGaussian V hh (V.proposalMean h x)]

end Centered

end DiscreteTime

end

end UniformRandomMALA
