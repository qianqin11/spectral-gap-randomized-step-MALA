import UniformRandomMALA.Concrete.NonstationaryMSEMoments
import UniformRandomMALA.Concrete.KernelLpIterateContraction
import Mathlib.Data.Nat.Dist

/-! # Spectral estimates for the actual finite-path pair moments -/

namespace UniformRandomMALA.Concrete
open MeasureTheory ProbabilityTheory DiscreteTime
open scoped ENNReal ProbabilityTheory
noncomputable section
variable {α : Type*} [MeasurableSpace α]

theorem abs_integral_mul_average_iterate_le
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hrev : Kernel.IsReversible K π)
    (hpos : KernelLp.Positive K π) {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π K)
    {f : α → ℝ} (hf : MemLp f 2 π) (hf0 : ∫ x, f x ∂π = 0) (n : ℕ) :
    |∫ x, f x * KernelLp.average (finiteKernelIterate K n) f x ∂π| ≤
      (1 - g) ^ n * ∫ x, f x ^ 2 ∂π := by
  have hKn := finiteKernelIterate_invariant K π hrev.invariant n
  have havg := KernelLp.average_memLp_of_ne_top (finiteKernelIterate K n) π hKn
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hf
  have hi := KernelLp.integral_sq_average_iterate_le K π hrev.invariant (1 - g)
    (fun _ hh hh0 => KernelLp.integral_sq_average_le_of_positive π K hrev hpos
      hg0 hg1 hgap hh hh0) hf hf0 n
  have hs : Real.sqrt (∫ x, KernelLp.average (finiteKernelIterate K n) f x ^ 2 ∂π) ≤
      (1 - g) ^ n * Real.sqrt (∫ x, f x ^ 2 ∂π) := by
    have hs := Real.sqrt_le_sqrt hi
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg (sub_nonneg.mpr hg1) n)] at hs
    exact hs
  calc
    _ ≤ Real.sqrt (∫ x, f x ^ 2 ∂π) *
        Real.sqrt (∫ x, KernelLp.average (finiteKernelIterate K n) f x ^ 2 ∂π) :=
      abs_integral_mul_le_sqrt_integral_sq hf havg
    _ ≤ Real.sqrt (∫ x, f x ^ 2 ∂π) *
        ((1 - g) ^ n * Real.sqrt (∫ x, f x ^ 2 ∂π)) :=
      mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)
    _ = _ := by
      rw [mul_left_comm, ← pow_two, Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)]

theorem sqrt_pow_pair (ρ : ℝ) (hρ : 0 ≤ ρ) (i j : ℕ) (hij : i ≤ j) :
    ρ ^ i * (Real.sqrt ρ) ^ (j - i) = (Real.sqrt ρ) ^ (i + j) := by
  conv_lhs => lhs; rw [← Real.sq_sqrt hρ]
  rw [← pow_mul, ← pow_add]
  congr 1
  omega

theorem finitePath_pair_bound_of_le
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : μ ≪ π) (hDensity : MemLp (fun x => (μ.rnDeriv π x).toReal) 2 π)
    (K : Kernel α α) [IsMarkovKernel K] (hrev : Kernel.IsReversible K π)
    (hpos : KernelLp.Positive K π) {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π K)
    {f : α → ℝ} (hf : MemLp f 4 π) (hf0 : ∫ x, f x ∂π = 0)
    (n : ℕ) (i j : Fin n) (hij : i ≤ j) :
    Integrable (fun path => f (path i) * f (path j)) (finiteMarkovPathLaw μ K n) ∧
    (∫ path, f (path i) * f (path j) ∂finiteMarkovPathLaw μ K n) ≤
      (∫ x, f x ^ 2 ∂π) * (1 - g) ^ (j.val - i.val) +
        (4 * centeredDensityL2Norm μ π * lpNorm f 4 π ^ 2) *
          (Real.sqrt (1 - g)) ^ (i.val + j.val) := by
  have hpair := finitePath_pair_discrepancy_le_density_L4 μ π hμ hDensity K hrev hf hf n i j hij
  refine ⟨hpair.1, ?_⟩
  have hρ : 0 ≤ 1 - g := sub_nonneg.mpr hg1
  have hD := (densityTV_iterate_of_positive_le μ π hμ hDensity K hrev hpos
    hg0 hg1 hgap i.val).2.2.2
  have hD' : centeredDensityL2Norm (finiteKernelIterate K i.val ∘ₘ μ) π ≤
      centeredDensityL2Norm μ π * (1 - g) ^ i.val := by linarith
  have h4 := KernelLp.lpNorm_average_iterate_le K π hrev.invariant hρ
    (fun _ hh hh0 => KernelLp.integral_sq_average_le_of_positive π K hrev hpos
      hg0 hg1 hgap hh hh0) hf hf0 (j.val - i.val)
  have herror : |(∫ path, f (path i) * f (path j) ∂finiteMarkovPathLaw μ K n) -
      ∫ path, f (path i) * f (path j) ∂finiteMarkovPathLaw π K n| ≤
      (4 * centeredDensityL2Norm μ π * lpNorm f 4 π ^ 2) *
        (Real.sqrt (1 - g)) ^ (i.val + j.val) := by
    calc
      _ ≤ centeredDensityL2Norm (finiteKernelIterate K i.val ∘ₘ μ) π * lpNorm f 4 π *
          lpNorm (KernelLp.average (finiteKernelIterate K (j.val - i.val)) f) 4 π := hpair.2
      _ ≤ (centeredDensityL2Norm μ π * (1 - g) ^ i.val) * lpNorm f 4 π *
          (4 * (Real.sqrt (1 - g)) ^ (j.val - i.val) * lpNorm f 4 π) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right hD' lpNorm_nonneg
        · exact h4
        · exact lpNorm_nonneg
        · exact mul_nonneg (mul_nonneg (centeredDensityL2Norm_nonneg μ π)
            (pow_nonneg hρ _)) lpNorm_nonneg
      _ = (4 * centeredDensityL2Norm μ π * lpNorm f 4 π ^ 2) *
          ((1 - g) ^ i.val * (Real.sqrt (1 - g)) ^ (j.val - i.val)) := by ring
      _ = _ := by rw [sqrt_pow_pair _ hρ i.val j.val hij]
  have hf2 : MemLp f 2 π := hf.mono_exponent (by norm_num)
  have hstat : (∫ path, f (path i) * f (path j) ∂finiteMarkovPathLaw π K n) ≤
      (∫ x, f x ^ 2 ∂π) * (1 - g) ^ (j.val - i.val) := by
    rw [stationaryPathLaw_integral_mul_coordinates π K hrev.invariant hf2 hf2 n i j hij]
    exact (le_abs_self _).trans (by
      simpa only [mul_comm] using abs_integral_mul_average_iterate_le π K hrev hpos
        hg0 hg1 hgap hf2 hf0 (j.val - i.val))
  linarith [le_abs_self ((∫ path, f (path i) * f (path j) ∂finiteMarkovPathLaw μ K n) -
    ∫ path, f (path i) * f (path j) ∂finiteMarkovPathLaw π K n)]

/-- The complete pair estimate, valid for all coordinate orders. -/
theorem finitePath_pair_bound
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : μ ≪ π) (hDensity : MemLp (fun x => (μ.rnDeriv π x).toReal) 2 π)
    (K : Kernel α α) [IsMarkovKernel K] (hrev : Kernel.IsReversible K π)
    (hpos : KernelLp.Positive K π) {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π K)
    {f : α → ℝ} (hf : MemLp f 4 π) (hf0 : ∫ x, f x ∂π = 0)
    (n : ℕ) (i j : Fin n) :
    Integrable (fun path => f (path i) * f (path j)) (finiteMarkovPathLaw μ K n) ∧
    (∫ path, f (path i) * f (path j) ∂finiteMarkovPathLaw μ K n) ≤
      (∫ x, f x ^ 2 ∂π) * (1 - g) ^ (Nat.dist i.val j.val) +
        (4 * centeredDensityL2Norm μ π * lpNorm f 4 π ^ 2) *
          (Real.sqrt (1 - g)) ^ (i.val + j.val) := by
  rcases le_total i j with hij | hji
  · simpa only [Nat.dist_eq_sub_of_le hij] using
      finitePath_pair_bound_of_le μ π hμ hDensity K hrev hpos hg0 hg1 hgap hf hf0 n i j hij
  · have h := finitePath_pair_bound_of_le μ π hμ hDensity K hrev hpos hg0 hg1 hgap hf hf0 n j i hji
    simpa only [Nat.dist_eq_sub_of_le_right hji, add_comm j.val i.val, mul_comm (f _) (f _)] using h

end
end UniformRandomMALA.Concrete
