import UniformRandomMALA.Concrete.KernelLpL2
import UniformRandomMALA.Concrete.LazyKernel
import UniformRandomMALA.Concrete.PositiveContraction

/-! # Exact full-`L²` spectral-gap contraction for positive kernels -/

namespace UniformRandomMALA.Concrete.KernelLp
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory InnerProductSpace
noncomputable section
variable {α : Type*} [MeasurableSpace α]

/-- Positivity is the nonnegativity of the genuine Markov quadratic form. -/
def Positive (K : Kernel α α) (π : Measure α) : Prop :=
  ∀ f : α → ℝ, MemLp f 2 π → 0 ≤ ∫ x, f x * average K f x ∂π

theorem norm_sq_operator_le_of_positive (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hrev : Kernel.IsReversible K π)
    (hpos : Positive K π) {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π K)
    (f : Lp ℝ 2 π) (hf : ∫ x, f x ∂π = 0) :
    ‖operator K π hrev.invariant 2 (by norm_num) f‖ ^ 2 ≤
      (1 - g) ^ 2 * ‖f‖ ^ 2 := by
  let T := operator K π hrev.invariant 2 (by norm_num)
  let u := T f
  have hs : ∀ x y, ⟪T x, y⟫_ℝ = ⟪x, T y⟫_ℝ := operator_isSymmetric K π hrev
  have hp : ∀ x : Lp ℝ 2 π, 0 ≤ ⟪x, T x⟫_ℝ := by
    intro x
    rw [show T = operator K π hrev.invariant 2 (by norm_num) from rfl, inner_operator]
    exact hpos x (Lp.memLp x)
  have hu : ∫ x, u x ∂π = 0 := by
    rw [show u = operator K π hrev.invariant 2 (by norm_num) f from rfl,
      integral_operator, hf]
  have hc : ⟪f, T u⟫_ℝ = ‖u‖ ^ 2 := by
    rw [← hs, show T f = u from rfl, real_inner_self_eq_norm_sq]
  have hCS : (‖u‖ ^ 2) ^ 2 ≤ ⟪f, T f⟫_ℝ * ⟪u, T u⟫_ℝ := by
    apply bilinear_cauchy_schwarz_of_quadratic_nonneg
    intro t
    have h := hp (f + t • u)
    simp only [map_add, map_smul, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right] at h
    rw [hc, show T f = u from rfl, real_inner_self_eq_norm_sq] at h
    nlinarith
  exact sq_norm_contraction_of_positive_form (sq_nonneg _) (sq_nonneg _)
    (sub_nonneg.mpr hg1) (hp f) (hp u) hCS
    (inner_operator_le_gap K π hrev.invariant hg0 hgap f hf)
    (inner_operator_le_gap K π hrev.invariant hg0 hgap u hu)

/-- The exact positive-kernel contraction applies to arbitrary `L²`
functions, with no boundedness premise. -/
theorem integral_sq_average_le_of_positive (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hrev : Kernel.IsReversible K π)
    (hpos : Positive K π) {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π K)
    {f : α → ℝ} (hf : MemLp f 2 π) (hf0 : ∫ x, f x ∂π = 0) :
    (∫ x, average K f x ^ 2 ∂π) ≤ (1 - g) ^ 2 * ∫ x, f x ^ 2 ∂π := by
  let F := hf.toLp f
  have hF : F =ᵐ[π] f := hf.coeFn_toLp
  have hF0 : ∫ x, F x ∂π = 0 := by rw [integral_congr_ae hF, hf0]
  have hi := norm_sq_operator_le_of_positive K π hrev hpos hg0 hg1 hgap F hF0
  rw [← integral_sq_eq_norm_sq, ← integral_sq_eq_norm_sq] at hi
  have hT : operator K π hrev.invariant 2 (by norm_num) F =ᵐ[π] average K f :=
    (operator_coeFn K π hrev.invariant 2 (by norm_num) F).trans
      (average_congr_ae K π hrev.invariant hF)
  have hT2 : (∫ x, operator K π hrev.invariant 2 (by norm_num) F x ^ 2 ∂π) =
      ∫ x, average K f x ^ 2 ∂π := by
    apply integral_congr_ae
    filter_upwards [hT] with x hx using congrArg (fun y : ℝ => y ^ 2) hx
  have hF2 : (∫ x, F x ^ 2 ∂π) = ∫ x, f x ^ 2 ∂π := by
    apply integral_congr_ae
    filter_upwards [hF] with x hx using congrArg (fun y : ℝ => y ^ 2) hx
  simpa only [hT2, hF2] using hi

theorem average_halfLazy_ae (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hrev : Kernel.IsReversible K π)
    {f : α → ℝ} (hf : MemLp f 2 π) :
    average (halfLazyKernel K) f =ᵐ[π] fun x => (f x + average K f x) / 2 := by
  let F := hf.toLp f
  have hπ := hrev.invariant
  have hF : F =ᵐ[π] f := hf.coeFn_toLp
  have hFi : Integrable F (K ∘ₘ π) := by
    rw [hπ]
    exact (Lp.memLp F).integrable (by norm_num)
  filter_upwards [average_congr_ae (halfLazyKernel K) π
    (halfLazyKernel_isReversible π K hrev).invariant hF,
    average_congr_ae K π hπ hF, hF,
    Measure.ae_integrable_of_integrable_comp hFi] with x hL hA hx hfx
  rw [← hL, ← hA, ← hx]
  have heq : halfLazyKernel K x = (2 : ℝ≥0∞)⁻¹ • (Measure.dirac x + K x) := by
    ext s hs
    rw [halfLazyKernel_apply K x s hs, Measure.smul_apply, Measure.add_apply]
    rfl
  change (∫ y, F y ∂halfLazyKernel K x) = _
  rw [heq, integral_smul_measure,
    integral_add_measure (integrable_dirac' (Lp.stronglyMeasurable F) (by finiteness)) hfx,
    integral_dirac' _ _ (Lp.stronglyMeasurable F)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul, average]
  ring

theorem halfLazy_positive (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hrev : Kernel.IsReversible K π) :
    Positive (halfLazyKernel K) π := by
  intro f hf
  have hπ := hrev.invariant
  have havg := average_memLp_of_ne_top K π hπ (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (by norm_num) hf
  have hfg : Integrable (fun x => f x * average K f x) π := hf.integrable_mul havg
  have heq : (∫ x, f x * average (halfLazyKernel K) f x ∂π) =
      ((∫ x, f x ^ 2 ∂π) + ∫ x, f x * average K f x ∂π) / 2 := by
    have hae : (fun x => f x * average (halfLazyKernel K) f x) =ᵐ[π]
        (fun x => f x * ((f x + average K f x) / 2)) := by
      filter_upwards [average_halfLazy_ae K π hrev hf] with x hx
      rw [hx]
    rw [integral_congr_ae hae]
    simp_rw [← mul_div_assoc, mul_add, ← pow_two]
    rw [integral_div, integral_add hf.integrable_sq hfg]
  have hn : 0 ≤ ∫ x, (f x + average K f x) ^ 2 ∂π :=
    integral_nonneg (fun x => sq_nonneg (f x + average K f x))
  have hs : (∫ x, (f x + average K f x) ^ 2 ∂π) =
      (∫ x, f x ^ 2 ∂π) + 2 * (∫ x, f x * average K f x ∂π) +
        ∫ x, average K f x ^ 2 ∂π := by
    simp_rw [add_sq, mul_assoc]
    have hadd : Integrable (fun x => f x ^ 2 + 2 * (f x * average K f x)) π :=
      hf.integrable_sq.add (hfg.const_mul 2)
    rw [integral_add hadd
      havg.integrable_sq, integral_add hf.integrable_sq
      (hfg.const_mul 2), integral_const_mul]
  rw [hs] at hn
  have hc := integral_sq_average_le π K hπ hf
  rw [heq]
  linarith

theorem integral_sq_average_halfLazy_le (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hrev : Kernel.IsReversible K π)
    {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π (halfLazyKernel K))
    {f : α → ℝ} (hf : MemLp f 2 π) (hf0 : ∫ x, f x ∂π = 0) :
    (∫ x, average (halfLazyKernel K) f x ^ 2 ∂π) ≤
      (1 - g) ^ 2 * ∫ x, f x ^ 2 ∂π :=
  integral_sq_average_le_of_positive π (halfLazyKernel K)
    (halfLazyKernel_isReversible π K hrev) (halfLazy_positive K π hrev)
    hg0 hg1 hgap hf hf0

end
end UniformRandomMALA.Concrete.KernelLp
