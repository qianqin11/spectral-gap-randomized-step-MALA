import UniformRandomMALA.Concrete.KernelLpCentering
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-! # Elementary `L²`--`L∞` interpolation at exponent four

The proof uses level-set truncation and the layer-cake formula. It does
not assume an interpolation theorem or an `L⁴` decay certificate.
-/

namespace UniformRandomMALA.Concrete.KernelLp
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
noncomputable section
variable {α : Type*} [MeasurableSpace α]

/-- The weighted layer-cake step in the elementary interpolation proof.
The input tail is weighted by the square of the original observable. -/
theorem lintegral_fourth_le_of_tail (μ : Measure α) {f g : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) (A : ℝ≥0∞) (hA : A ≠ ∞)
    (htail : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal (t ^ 2) * μ {x | t < |g x|} ≤
        A * (μ.withDensity (fun x => ENNReal.ofReal (f x ^ 2)))
          {x | t < 4 * |f x|}) :
    (∫⁻ x, ENNReal.ofReal (g x ^ 4) ∂μ) ≤
      32 * A * ∫⁻ x, ENNReal.ofReal (f x ^ 4) ∂μ := by
  let ν := μ.withDensity (fun x => ENNReal.ofReal (f x ^ 2))
  have hg4 := lintegral_rpow_eq_lintegral_meas_lt_mul μ
    (Filter.Eventually.of_forall fun x => abs_nonneg (g x)) hg.abs.aemeasurable
    (p := 4) (by norm_num)
  have hf2 := lintegral_rpow_eq_lintegral_meas_lt_mul ν
    (Filter.Eventually.of_forall fun x => mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
      (abs_nonneg (f x))) ((measurable_const.mul hf.abs).aemeasurable)
    (p := 2) (by norm_num)
  norm_num only [Real.rpow_ofNat, Real.rpow_one, show (4 : ℝ) - 1 = 3 by norm_num,
    show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.ofReal_ofNat] at hg4 hf2
  have habs4 (x : ℝ) : |x| ^ 4 = x ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
  have hg4' : (∫⁻ x, ENNReal.ofReal (g x ^ 4) ∂μ) =
      4 * ∫⁻ t in Ioi (0 : ℝ), μ {x | t < |g x|} * ENNReal.ofReal (t ^ 3) := by
    simpa only [habs4] using hg4
  have hineq : (∫⁻ t in Ioi (0 : ℝ), μ {x | t < |g x|} * ENNReal.ofReal (t ^ 3)) ≤
      A * ∫⁻ t in Ioi (0 : ℝ), ν {x | t < 4 * |f x|} * ENNReal.ofReal t := by
    rw [← lintegral_const_mul' A _ hA]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
      with t ht
    have heq : ENNReal.ofReal (t ^ 3) = ENNReal.ofReal (t ^ 2) * ENNReal.ofReal t := by
      rw [← ENNReal.ofReal_mul (sq_nonneg t)]
      congr 1
    rw [heq]
    calc
      _ = (ENNReal.ofReal (t ^ 2) * μ {x | t < |g x|}) * ENNReal.ofReal t := by ring
      _ ≤ (A * ν {x | t < 4 * |f x|}) * ENNReal.ofReal t :=
        mul_le_mul_left (htail t ht) _
      _ = _ := by ring
  have hweighted : (∫⁻ x, ENNReal.ofReal ((4 * |f x|) ^ 2) ∂ν) =
      16 * ∫⁻ x, ENNReal.ofReal (f x ^ 4) ∂μ := by
    rw [show ν = μ.withDensity (fun x => ENNReal.ofReal (f x ^ 2)) from rfl,
      lintegral_withDensity_eq_lintegral_mul μ (hf.pow_const 2).ennreal_ofReal
        (show Measurable (fun x => ENNReal.ofReal ((4 * |f x|) ^ 2)) by fun_prop)]
    change (∫⁻ x, ENNReal.ofReal (f x ^ 2) * ENNReal.ofReal ((4 * |f x|) ^ 2) ∂μ) = _
    simp_rw [← ENNReal.ofReal_mul (sq_nonneg (f _))]
    have heq (x : α) : f x ^ 2 * (4 * |f x|) ^ 2 = 16 * f x ^ 4 := by
      rw [mul_pow, sq_abs]
      ring
    simp_rw [heq, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    norm_num
  calc
    _ = 4 * ∫⁻ t in Ioi (0 : ℝ), μ {x | t < |g x|} * ENNReal.ofReal (t ^ 3) := hg4'
    _ ≤ 4 * (A * ∫⁻ t in Ioi (0 : ℝ), ν {x | t < 4 * |f x|} * ENNReal.ofReal t) :=
      mul_le_mul_right hineq _
    _ = 2 * A * (2 * ∫⁻ t in Ioi (0 : ℝ), ν {x | t < 4 * |f x|} * ENNReal.ofReal t) := by ring
    _ = 2 * A * (∫⁻ x, ENNReal.ofReal ((4 * |f x|) ^ 2) ∂ν) := by rw [← hf2]
    _ = _ := by rw [hweighted]; ring

/-- Level-set truncation converts a centered `L²` operator estimate into
the distributional estimate used by layer cake. -/
theorem centeredAverage_tail_bound (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : Kernel.Invariant K π)
    (a : ℝ)
    (hdecay : ∀ h : α → ℝ, MemLp h 2 π → (∫ x, h x ∂π) = 0 →
      (∫ x, average K h x ^ 2 ∂π) ≤ a ^ 2 * ∫ x, h x ^ 2 ∂π)
    {f : α → ℝ} (hm : Measurable f) (hf : MemLp f 2 π)
    (t : ℝ) (ht : 0 < t) :
    ENNReal.ofReal (t ^ 2) * π {x | t < |centeredAverage K π f x|} ≤
      ENNReal.ofReal (4 * a ^ 2) *
        (π.withDensity (fun x => ENNReal.ofReal (f x ^ 2))) {x | t < 4 * |f x|} := by
  classical
  let s : Set α := {x | t < 4 * |f x|}
  have hs : MeasurableSet s := measurableSet_lt measurable_const (measurable_const.mul hm.abs)
  let h := s.indicator f
  let l := sᶜ.indicator f
  have hh : MemLp h 2 π := hf.indicator hs
  have hl : MemLp l 2 π := hf.indicator hs.compl
  have hsplit : h + l = f := by
    funext x
    by_cases hx : x ∈ s <;> simp [h, l, hx]
  have hlbound (x : α) : |l x| ≤ t / 4 := by
    by_cases hx : x ∈ s
    · simp only [l, Set.indicator_of_notMem (notMem_compl_iff.mpr hx), abs_zero]
      positivity
    · have hx' : 4 * |f x| ≤ t := le_of_not_gt hx
      simp only [l, Set.indicator_of_mem (Set.mem_compl hx)]
      linarith
  have hlow (x : α) : |centeredAverage K π l x| ≤ t / 2 :=
    (abs_centeredAverage_le K π hlbound x).trans (by ring_nf; rfl)
  have hadd : centeredAverage K π f =ᵐ[π]
      fun x => centeredAverage K π h x + centeredAverage K π l x := by
    rw [← hsplit]
    exact centeredAverage_add_ae K π hπ (hh.integrable (by norm_num))
      (hl.integrable (by norm_num))
  have hmT : Measurable (centeredAverage K π f) := by
    exact (hm.stronglyMeasurable.integral_kernel.measurable).sub measurable_const
  let G : Set α := {x | t < |centeredAverage K π f x|}
  have hG : MeasurableSet G := measurableSet_lt measurable_const hmT.abs
  have hpoint : ∀ᵐ x ∂π,
      G.indicator (fun _ => ENNReal.ofReal (t ^ 2)) x ≤
        ENNReal.ofReal (4 * centeredAverage K π h x ^ 2) := by
    filter_upwards [hadd] with x hx
    by_cases hxG : x ∈ G
    · rw [Set.indicator_of_mem hxG]
      apply ENNReal.ofReal_le_ofReal
      have hgx : t < |centeredAverage K π f x| := hxG
      rw [hx] at hgx
      have hb := abs_add_le (centeredAverage K π h x) (centeredAverage K π l x)
      have hlx := hlow x
      have hn := abs_nonneg (centeredAverage K π h x)
      nlinarith [sq_abs (centeredAverage K π h x)]
    · rw [Set.indicator_of_notMem hxG]
      exact zero_le
  have hThi := (centeredAverage_memLp K π hπ (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (by norm_num) hh).integrable_sq
  have hinput : ENNReal.ofReal (∫ x, h x ^ 2 ∂π) =
      (π.withDensity (fun x => ENNReal.ofReal (f x ^ 2))) s := by
    rw [ofReal_integral_eq_lintegral_ofReal hh.integrable_sq
      (Filter.Eventually.of_forall fun x => sq_nonneg (h x)), withDensity_apply _ hs]
    rw [← lintegral_indicator hs]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ s <;> simp [h, hx]
  calc
    _ = ∫⁻ x, G.indicator (fun _ => ENNReal.ofReal (t ^ 2)) x ∂π :=
      (lintegral_indicator_const hG _).symm
    _ ≤ ∫⁻ x, ENNReal.ofReal (4 * centeredAverage K π h x ^ 2) ∂π :=
      lintegral_mono_ae hpoint
    _ = ENNReal.ofReal 4 * ENNReal.ofReal (∫ x, centeredAverage K π h x ^ 2 ∂π) := by
      simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ← ofReal_integral_eq_lintegral_ofReal hThi
          (Filter.Eventually.of_forall fun x => sq_nonneg _)]
    _ ≤ ENNReal.ofReal 4 * ENNReal.ofReal (a ^ 2 * ∫ x, h x ^ 2 ∂π) :=
      mul_le_mul_right (ENNReal.ofReal_le_ofReal
        (integral_sq_centeredAverage_le K π hπ a hdecay hh)) _
    _ = _ := by
      rw [ENNReal.ofReal_mul (sq_nonneg a), hinput,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      exact (mul_assoc _ _ _).symm

/-- Elementary interpolation: an `L²` contraction by `a` gives the
fourth-moment bound `128 a²`. -/
theorem lintegral_fourth_centeredAverage_le (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : Kernel.Invariant K π)
    (a : ℝ)
    (hdecay : ∀ h : α → ℝ, MemLp h 2 π → (∫ x, h x ∂π) = 0 →
      (∫ x, average K h x ^ 2 ∂π) ≤ a ^ 2 * ∫ x, h x ^ 2 ∂π)
    {f : α → ℝ} (hm : Measurable f) (hf : MemLp f 2 π) :
    (∫⁻ x, ENNReal.ofReal (centeredAverage K π f x ^ 4) ∂π) ≤
      ENNReal.ofReal (128 * a ^ 2) * ∫⁻ x, ENNReal.ofReal (f x ^ 4) ∂π := by
  have hmT : Measurable (centeredAverage K π f) :=
    hm.stronglyMeasurable.integral_kernel.measurable.sub measurable_const
  have hi := lintegral_fourth_le_of_tail π hm hmT
    (ENNReal.ofReal (4 * a ^ 2)) ENNReal.ofReal_ne_top
    (centeredAverage_tail_bound K π hπ a hdecay hm hf)
  have heq : 32 * ENNReal.ofReal (4 * a ^ 2) = ENNReal.ofReal (128 * a ^ 2) := by
    rw [← show ENNReal.ofReal (32 : ℝ) = 32 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 32)]
    congr 1
    ring
  rw [heq] at hi
  exact hi

theorem abs_pow_four (x : ℝ) : |x| ^ 4 = x ^ 4 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]

theorem integrable_fourth {μ : Measure α} {f : α → ℝ} (hf : MemLp f 4 μ) :
    Integrable (fun x => f x ^ 4) μ := by
  simpa only [Real.norm_eq_abs, abs_pow_four] using hf.integrable_norm_pow (by norm_num)

theorem lpNorm_fourth_pow {μ : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) :
    lpNorm f 4 μ ^ 4 = ∫ x, f x ^ 4 ∂μ := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hf]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_ofNat, Real.norm_eq_abs, abs_pow_four]
  rw [← Real.rpow_mul_natCast (integral_nonneg fun x => by positivity)]
  norm_num

theorem integral_fourth_centeredAverage_le_measurable
    (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : Kernel.Invariant K π)
    (a : ℝ)
    (hdecay : ∀ h : α → ℝ, MemLp h 2 π → (∫ x, h x ∂π) = 0 →
      (∫ x, average K h x ^ 2 ∂π) ≤ a ^ 2 * ∫ x, h x ^ 2 ∂π)
    {f : α → ℝ} (hm : Measurable f) (hf : MemLp f 4 π) :
    (∫ x, centeredAverage K π f x ^ 4 ∂π) ≤
      128 * a ^ 2 * ∫ x, f x ^ 4 ∂π := by
  have hf2 : MemLp f 2 π := hf.mono_exponent (by norm_num)
  have hT := centeredAverage_memLp K π hπ (by norm_num : (1 : ℝ≥0∞) ≤ 4)
    (by norm_num) hf
  have hi := lintegral_fourth_centeredAverage_le K π hπ a hdecay hm hf2
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_fourth hT)
      (Filter.Eventually.of_forall fun x => by positivity),
    ← ofReal_integral_eq_lintegral_ofReal (integrable_fourth hf)
      (Filter.Eventually.of_forall fun x => by positivity),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 128 * a ^ 2)] at hi
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hi

/-- Fourth-moment interpolation for arbitrary a.e. measurable observables. -/
theorem integral_fourth_centeredAverage_le
    (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : Kernel.Invariant K π)
    (a : ℝ)
    (hdecay : ∀ h : α → ℝ, MemLp h 2 π → (∫ x, h x ∂π) = 0 →
      (∫ x, average K h x ^ 2 ∂π) ≤ a ^ 2 * ∫ x, h x ^ 2 ∂π)
    {f : α → ℝ} (hf : MemLp f 4 π) :
    (∫ x, centeredAverage K π f x ^ 4 ∂π) ≤
      128 * a ^ 2 * ∫ x, f x ^ 4 ∂π := by
  let F := hf.toLp f
  have hF : F =ᵐ[π] f := hf.coeFn_toLp
  have hT : centeredAverage K π F =ᵐ[π] centeredAverage K π f := by
    have hm := integral_congr_ae hF
    filter_upwards [average_congr_ae K π hπ hF] with x hx
    simp only [centeredAverage, hx, hm]
  have hi := integral_fourth_centeredAverage_le_measurable K π hπ a hdecay
    (Lp.stronglyMeasurable F).measurable (Lp.memLp F)
  have hT4 : (∫ x, centeredAverage K π F x ^ 4 ∂π) =
      ∫ x, centeredAverage K π f x ^ 4 ∂π := by
    apply integral_congr_ae
    filter_upwards [hT] with x hx using congrArg (fun y : ℝ => y ^ 4) hx
  have hF4 : (∫ x, F x ^ 4 ∂π) = ∫ x, f x ^ 4 ∂π := by
    apply integral_congr_ae
    filter_upwards [hF] with x hx using congrArg (fun y : ℝ => y ^ 4) hx
  rwa [hT4, hF4] at hi

/-- A convenient real `L⁴` norm bound. The elementary interpolation
constant is rounded up to four. -/
theorem lpNorm_centeredAverage_le
    (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : Kernel.Invariant K π)
    {a : ℝ} (ha : 0 ≤ a)
    (hdecay : ∀ h : α → ℝ, MemLp h 2 π → (∫ x, h x ∂π) = 0 →
      (∫ x, average K h x ^ 2 ∂π) ≤ a ^ 2 * ∫ x, h x ^ 2 ∂π)
    {f : α → ℝ} (hf : MemLp f 4 π) :
    lpNorm (centeredAverage K π f) 4 π ≤ 4 * Real.sqrt a * lpNorm f 4 π := by
  have hT := centeredAverage_memLp K π hπ (by norm_num : (1 : ℝ≥0∞) ≤ 4)
    (by norm_num) hf
  have hi := integral_fourth_centeredAverage_le K π hπ a hdecay hf
  rw [← lpNorm_fourth_pow hT.1, ← lpNorm_fourth_pow hf.1] at hi
  apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0)
    (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg a)) lpNorm_nonneg)
  have hs : Real.sqrt a ^ 4 = a ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt ha]
  rw [mul_pow, mul_pow, hs]
  nlinarith [sq_nonneg (a * lpNorm f 4 π ^ 2)]

end
end UniformRandomMALA.Concrete.KernelLp
