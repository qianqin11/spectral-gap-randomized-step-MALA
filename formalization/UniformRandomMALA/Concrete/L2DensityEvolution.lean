import UniformRandomMALA.Concrete.KernelLpContraction
import UniformRandomMALA.Concrete.L2MixingTV
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# Evolution of square-integrable Radon--Nikodym densities

The density is the actual Radon--Nikodym derivative of the iterated
transition law. Reversibility identifies its evolution with the Markov
operator; the spectral gap then contracts its centered `L²` norm.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory DiscreteTime
open scoped ENNReal ProbabilityTheory

noncomputable section

variable {α : Type*} [MeasurableSpace α]

theorem absolutelyContinuous_comp_of_invariant
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    (hμ : μ ≪ π) : K ∘ₘ μ ≪ π := by
  change K ∘ₘ π = π at hπ
  simpa only [hπ] using hμ.comp_right K

private theorem rnDeriv_comp_eq_average_of_pairing
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : μ ≪ π)
    (hDensity : MemLp (fun x => (μ.rnDeriv π x).toReal) 2 π)
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    (hpair : ∀ (f g : α → ℝ), MemLp f 2 π → MemLp g 2 π →
      (∫ x, f x * KernelLp.average K g x ∂π) =
        ∫ x, KernelLp.average K f x * g x ∂π) :
    (fun x => ((K ∘ₘ μ).rnDeriv π x).toReal) =ᵐ[π]
      KernelLp.average K (fun x => (μ.rnDeriv π x).toReal) := by
  have hμK := absolutelyContinuous_comp_of_invariant μ π K hπ hμ
  have havg := KernelLp.average_memLp_of_ne_top K π hπ (by norm_num)
    (by norm_num) hDensity
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    Measure.integrable_toReal_rnDeriv (havg.integrable (by norm_num))
  intro s hs _
  rw [Measure.setIntegral_toReal_rnDeriv hμK s]
  let f : α → ℝ := s.indicator (fun _ => 1)
  have hf : MemLp f 2 π := (memLp_const (1 : ℝ)).indicator hs
  have hfi : Integrable f (K ∘ₘ μ) := (integrable_const (1 : ℝ)).indicator hs
  have hset : (∫ x, KernelLp.average K (fun y => (μ.rnDeriv π y).toReal) x *
      f x ∂π) = ∫ x in s, KernelLp.average K
        (fun y => (μ.rnDeriv π y).toReal) x ∂π := by
    rw [← integral_indicator hs]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ s <;> simp [f, hx]
  calc
    (K ∘ₘ μ).real s = ∫ x, f x ∂(K ∘ₘ μ) := by
      simp [f, integral_indicator_const _ hs]
    _ = ∫ x, KernelLp.average K f x ∂μ :=
      (KernelLp.integral_average K μ hfi).symm
    _ = ∫ x, (μ.rnDeriv π x).toReal * KernelLp.average K f x ∂π :=
      (MeasureTheory.integral_toReal_rnDeriv_mul hμ).symm
    _ = ∫ x, KernelLp.average K (fun y => (μ.rnDeriv π y).toReal) x * f x ∂π :=
      hpair _ _ hDensity hf
    _ = _ := hset

theorem integral_centeredDensity_eq_zero
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : μ ≪ π) : ∫ x, centeredDensity μ π x ∂π = 0 := by
  change (∫ x, (μ.rnDeriv π x).toReal - 1 ∂π) = 0
  rw [integral_sub Measure.integrable_toReal_rnDeriv
    (integrable_const (1 : ℝ)), Measure.integral_toReal_rnDeriv hμ]
  simp

private theorem centeredDensity_comp_eq_average_of_pairing
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : μ ≪ π)
    (hDensity : MemLp (fun x => (μ.rnDeriv π x).toReal) 2 π)
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    (hpair : ∀ (f g : α → ℝ), MemLp f 2 π → MemLp g 2 π →
      (∫ x, f x * KernelLp.average K g x ∂π) =
        ∫ x, KernelLp.average K f x * g x ∂π) :
    centeredDensity (K ∘ₘ μ) π =ᵐ[π] KernelLp.average K (centeredDensity μ π) := by
  have hint : Integrable (fun x => (μ.rnDeriv π x).toReal) (K ∘ₘ π) := by
    rw [hπ]
    exact hDensity.integrable (by norm_num)
  filter_upwards [rnDeriv_comp_eq_average_of_pairing μ π hμ hDensity K hπ hpair,
    Measure.ae_integrable_of_integrable_comp hint] with x hx hxi
  simp only [centeredDensity, KernelLp.average] at hx ⊢
  rw [integral_sub hxi (integrable_const (1 : ℝ)), integral_const]
  simp [hx]

private theorem density_comp_memLp_of_pairing
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : μ ≪ π)
    (hDensity : MemLp (fun x => (μ.rnDeriv π x).toReal) 2 π)
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    (hpair : ∀ (f g : α → ℝ), MemLp f 2 π → MemLp g 2 π →
      (∫ x, f x * KernelLp.average K g x ∂π) =
        ∫ x, KernelLp.average K f x * g x ∂π) :
    MemLp (fun x => ((K ∘ₘ μ).rnDeriv π x).toReal) 2 π :=
  (KernelLp.average_memLp_of_ne_top K π hπ (by norm_num) (by norm_num) hDensity).ae_eq
    (rnDeriv_comp_eq_average_of_pairing μ π hμ hDensity K hπ hpair).symm

private theorem centeredDensityL2Norm_comp_le_of_pairing
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : μ ≪ π)
    (hDensity : MemLp (fun x => (μ.rnDeriv π x).toReal) 2 π)
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    (hpair : ∀ (f g : α → ℝ), MemLp f 2 π → MemLp g 2 π →
      (∫ x, f x * KernelLp.average K g x ∂π) =
        ∫ x, KernelLp.average K f x * g x ∂π)
    {a : ℝ} (ha : 0 ≤ a)
    (hcontract : ∀ f : α → ℝ, MemLp f 2 π → (∫ x, f x ∂π) = 0 →
      (∫ x, KernelLp.average K f x ^ 2 ∂π) ≤ a ^ 2 * ∫ x, f x ^ 2 ∂π) :
    centeredDensityL2Norm (K ∘ₘ μ) π ≤ centeredDensityL2Norm μ π * a := by
  have hc : MemLp (centeredDensity μ π) 2 π :=
    hDensity.sub (memLp_const (1 : ℝ))
  have hdecay := hcontract _ hc (integral_centeredDensity_eq_zero μ π hμ)
  have heq : (∫ x, centeredDensity (K ∘ₘ μ) π x ^ 2 ∂π) =
      ∫ x, KernelLp.average K (centeredDensity μ π) x ^ 2 ∂π := by
    apply integral_congr_ae
    filter_upwards [centeredDensity_comp_eq_average_of_pairing μ π hμ hDensity K hπ hpair]
      with x hx
    rw [hx]
  unfold centeredDensityL2Norm
  apply (Real.sqrt_le_left (mul_nonneg (Real.sqrt_nonneg _) ha)).2
  rw [heq, mul_pow, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _), mul_comm]
  exact hdecay

private theorem density_iterate_of_pairing
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : μ ≪ π)
    (hDensity : MemLp (fun x => (μ.rnDeriv π x).toReal) 2 π)
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    (hpair : ∀ (f g : α → ℝ), MemLp f 2 π → MemLp g 2 π →
      (∫ x, f x * KernelLp.average K g x ∂π) =
        ∫ x, KernelLp.average K f x * g x ∂π)
    {a : ℝ} (ha : 0 ≤ a)
    (hcontract : ∀ f : α → ℝ, MemLp f 2 π → (∫ x, f x ∂π) = 0 →
      (∫ x, KernelLp.average K f x ^ 2 ∂π) ≤ a ^ 2 * ∫ x, f x ^ 2 ∂π)
    (n : ℕ) :
    (finiteKernelIterate K n ∘ₘ μ) ≪ π ∧
    MemLp (fun x => ((finiteKernelIterate K n ∘ₘ μ).rnDeriv π x).toReal) 2 π ∧
    centeredDensityL2Norm (finiteKernelIterate K n ∘ₘ μ) π ≤
      centeredDensityL2Norm μ π * a ^ n := by
  induction n with
  | zero => simpa [finiteKernelIterate] using
      And.intro hμ (And.intro hDensity (le_refl (centeredDensityL2Norm μ π)))
  | succ n ih =>
    rw [finiteKernelIterate, ← Measure.comp_assoc]
    refine ⟨absolutelyContinuous_comp_of_invariant _ π K hπ ih.1,
      density_comp_memLp_of_pairing _ π ih.1 ih.2.1 K hπ hpair, ?_⟩
    calc
      centeredDensityL2Norm (K ∘ₘ (finiteKernelIterate K n ∘ₘ μ)) π ≤
          centeredDensityL2Norm (finiteKernelIterate K n ∘ₘ μ) π * a :=
        centeredDensityL2Norm_comp_le_of_pairing _ π ih.1 ih.2.1 K hπ hpair ha hcontract
      _ ≤ (centeredDensityL2Norm μ π * a ^ n) * a := mul_le_mul_of_nonneg_right ih.2.2 ha
      _ = centeredDensityL2Norm μ π * a ^ (n + 1) := by rw [pow_succ, mul_assoc]

/-- Reversibility evolves the actual RN density by kernel averaging. -/
theorem rnDeriv_comp_eq_average
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : μ ≪ π)
    (hDensity : MemLp (fun x => (μ.rnDeriv π x).toReal) 2 π)
    (K : Kernel α α) [IsMarkovKernel K] (hrev : Kernel.IsReversible K π) :
    (fun x => ((K ∘ₘ μ).rnDeriv π x).toReal) =ᵐ[π]
      KernelLp.average K (fun x => (μ.rnDeriv π x).toReal) :=
  rnDeriv_comp_eq_average_of_pairing μ π hμ hDensity K hrev.invariant
    (fun _ _ hf hg => KernelLp.integral_mul_average_symm π K hrev hf hg)

/-- The evolved RN density remains square integrable. -/
theorem rnDeriv_comp_memLp
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : μ ≪ π)
    (hDensity : MemLp (fun x => (μ.rnDeriv π x).toReal) 2 π)
    (K : Kernel α α) [IsMarkovKernel K] (hrev : Kernel.IsReversible K π) :
    MemLp (fun x => ((K ∘ₘ μ).rnDeriv π x).toReal) 2 π :=
  density_comp_memLp_of_pairing μ π hμ hDensity K hrev.invariant
    (fun _ _ hf hg => KernelLp.integral_mul_average_symm π K hrev hf hg)

/-- The centered RN density follows the same Markov operator. -/
theorem centeredDensity_comp_eq_average
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : μ ≪ π)
    (hDensity : MemLp (fun x => (μ.rnDeriv π x).toReal) 2 π)
    (K : Kernel α α) [IsMarkovKernel K] (hrev : Kernel.IsReversible K π) :
    centeredDensity (K ∘ₘ μ) π =ᵐ[π] KernelLp.average K (centeredDensity μ π) :=
  centeredDensity_comp_eq_average_of_pairing μ π hμ hDensity K hrev.invariant
    (fun _ _ hf hg => KernelLp.integral_mul_average_symm π K hrev hf hg)

private theorem densityTV_iterate_of_pairing
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : μ ≪ π)
    (hDensity : MemLp (fun x => (μ.rnDeriv π x).toReal) 2 π)
    (K : Kernel α α) [IsMarkovKernel K] (hrev : Kernel.IsReversible K π)
    {a : ℝ} (ha : 0 ≤ a)
    (hcontract : ∀ f : α → ℝ, MemLp f 2 π → (∫ x, f x ∂π) = 0 →
      (∫ x, KernelLp.average K f x ^ 2 ∂π) ≤ a ^ 2 * ∫ x, f x ^ 2 ∂π)
    (n : ℕ) :
    let ν := finiteKernelIterate K n ∘ₘ μ
    (ν ≪ π) ∧ MemLp (fun x => (ν.rnDeriv π x).toReal) 2 π ∧
      setwiseTV ν π ≤ centeredDensityL2Norm ν π / 2 ∧
      centeredDensityL2Norm ν π / 2 ≤ centeredDensityL2Norm μ π / 2 * a ^ n := by
  obtain ⟨hac, hLp, hnorm⟩ := density_iterate_of_pairing μ π hμ hDensity K
    hrev.invariant (fun _ _ hf hg => KernelLp.integral_mul_average_symm π K hrev hf hg)
    ha hcontract n
  refine ⟨hac, hLp, setwiseTV_le_half_centeredDensityL2Norm _ π hac hLp, ?_⟩
  calc
    centeredDensityL2Norm (finiteKernelIterate K n ∘ₘ μ) π / 2 ≤
        (centeredDensityL2Norm μ π * a ^ n) / 2 :=
      div_le_div_of_nonneg_right hnorm (by norm_num)
    _ = _ := by ring

private theorem centeredDensityL2Norm_eq_zero_of_gap_gt_one
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : μ ≪ π)
    (hDensity : MemLp (fun x => (μ.rnDeriv π x).toReal) 2 π)
    (K : Kernel α α) [IsMarkovKernel K] (hrev : Kernel.IsReversible K π)
    (hpos : ∀ f : α → ℝ, MemLp f 2 π →
      0 ≤ ∫ x, f x * KernelLp.average K f x ∂π)
    (hgt : 1 < (rayleighSpectralGap π K).toReal) : centeredDensityL2Norm μ π = 0 := by
  have hc : MemLp (centeredDensity μ π) 2 π := hDensity.sub (memLp_const (1 : ℝ))
  let F : Lp ℝ 2 π := hc.toLp (centeredDensity μ π)
  have hF : F =ᵐ[π] centeredDensity μ π := hc.coeFn_toLp
  have hmean : ∫ x, F x ∂π = 0 :=
    (integral_congr_ae hF).trans (integral_centeredDensity_eq_zero μ π hμ)
  have hquad := KernelLp.inner_operator_le_gap K π hrev.invariant ENNReal.toReal_nonneg
    ENNReal.ofReal_toReal_le F hmean
  have hpositive := hpos F (Lp.memLp F)
  rw [← KernelLp.inner_operator K π hrev.invariant] at hpositive
  have hnorm : ‖F‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖F‖]
  have hsquare : (∫ x, centeredDensity μ π x ^ 2 ∂π) = ∫ x, F x ^ 2 ∂π := by
    apply integral_congr_ae
    filter_upwards [hF] with x hx
    rw [hx]
  unfold centeredDensityL2Norm
  rw [hsquare, KernelLp.integral_sq_eq_norm_sq, hnorm, Real.sqrt_zero]

/-- Both density and total-variation inequalities from a positive reversible
kernel's gap bound, applied to its actual transition-law iterates. -/
theorem densityTV_iterate_of_positive_le
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : μ ≪ π)
    (hDensity : MemLp (fun x => (μ.rnDeriv π x).toReal) 2 π)
    (K : Kernel α α) [IsMarkovKernel K] (hrev : Kernel.IsReversible K π)
    (hpos : KernelLp.Positive K π) {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π K) (n : ℕ) :
    let ν := finiteKernelIterate K n ∘ₘ μ
    (ν ≪ π) ∧ MemLp (fun x => (ν.rnDeriv π x).toReal) 2 π ∧
      setwiseTV ν π ≤ centeredDensityL2Norm ν π / 2 ∧
      centeredDensityL2Norm ν π / 2 ≤
        centeredDensityL2Norm μ π / 2 * (1 - g) ^ n :=
  densityTV_iterate_of_pairing μ π hμ hDensity K hrev (sub_nonneg.mpr hg1)
    (fun _ hf hf0 => KernelLp.integral_sq_average_le_of_positive π K hrev hpos
      hg0 hg1 hgap hf hf0) n

/-- Equation `eq:TVbound` for any positive-semidefinite reversible Markov
kernel. The rate uses its actual Rayleigh gap, and the intermediate norm
uses the actual evolved RN density. No convergence premise is assumed. -/
theorem densityTV_iterate_of_positive_actualGap
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : μ ≪ π)
    (hDensity : MemLp (fun x => (μ.rnDeriv π x).toReal) 2 π)
    (K : Kernel α α) [IsMarkovKernel K] (hrev : Kernel.IsReversible K π)
    (hpos : KernelLp.Positive K π) (n : ℕ) :
    let ν := finiteKernelIterate K n ∘ₘ μ
    let gap := (rayleighSpectralGap π K).toReal
    (ν ≪ π) ∧ MemLp (fun x => (ν.rnDeriv π x).toReal) 2 π ∧
      setwiseTV ν π ≤ centeredDensityL2Norm ν π / 2 ∧
      centeredDensityL2Norm ν π / 2 ≤
        centeredDensityL2Norm μ π / 2 * (1 - gap) ^ n := by
  by_cases hg1 : (rayleighSpectralGap π K).toReal ≤ 1
  · exact densityTV_iterate_of_positive_le μ π hμ hDensity K hrev hpos
      ENNReal.toReal_nonneg hg1 ENNReal.ofReal_toReal_le n
  · have hzero := centeredDensityL2Norm_eq_zero_of_gap_gt_one μ π hμ hDensity K hrev
      hpos (lt_of_not_ge hg1)
    have h := densityTV_iterate_of_pairing μ π hμ hDensity K hrev
      (a := 1) zero_le_one (fun _ hf _ => by
        simpa only [one_pow, one_mul] using KernelLp.integral_sq_average_le π K hrev.invariant hf) n
    refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
    simpa only [hzero, zero_div, zero_mul] using h.2.2.2

/-- The density and TV bounds for a half-lazy reversible kernel and any
proved lower bound for its gap. -/
theorem densityTV_iterate_halfLazy_le
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : μ ≪ π)
    (hDensity : MemLp (fun x => (μ.rnDeriv π x).toReal) 2 π)
    (K : Kernel α α) [IsMarkovKernel K] (hrev : Kernel.IsReversible K π)
    {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π (halfLazyKernel K)) (n : ℕ) :
    let ν := finiteKernelIterate (halfLazyKernel K) n ∘ₘ μ
    (ν ≪ π) ∧ MemLp (fun x => (ν.rnDeriv π x).toReal) 2 π ∧
      setwiseTV ν π ≤ centeredDensityL2Norm ν π / 2 ∧
      centeredDensityL2Norm ν π / 2 ≤
        centeredDensityL2Norm μ π / 2 * (1 - g) ^ n :=
  densityTV_iterate_of_positive_le μ π hμ hDensity (halfLazyKernel K)
    (halfLazyKernel_isReversible π K hrev) (KernelLp.halfLazy_positive K π hrev)
    hg0 hg1 hgap n

/-- Equation `eq:TVbound` for half-lazy reversible kernels, with their
actual Rayleigh gaps and the actual evolved RN densities. -/
theorem densityTV_iterate_halfLazy_actualGap
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : μ ≪ π)
    (hDensity : MemLp (fun x => (μ.rnDeriv π x).toReal) 2 π)
    (K : Kernel α α) [IsMarkovKernel K] (hrev : Kernel.IsReversible K π) (n : ℕ) :
    let P := halfLazyKernel K
    let ν := finiteKernelIterate P n ∘ₘ μ
    let gap := (rayleighSpectralGap π P).toReal
    (ν ≪ π) ∧ MemLp (fun x => (ν.rnDeriv π x).toReal) 2 π ∧
      setwiseTV ν π ≤ centeredDensityL2Norm ν π / 2 ∧
      centeredDensityL2Norm ν π / 2 ≤
        centeredDensityL2Norm μ π / 2 * (1 - gap) ^ n :=
  densityTV_iterate_of_positive_actualGap μ π hμ hDensity (halfLazyKernel K)
    (halfLazyKernel_isReversible π K hrev) (KernelLp.halfLazy_positive K π hrev) n

end
end UniformRandomMALA.Concrete
