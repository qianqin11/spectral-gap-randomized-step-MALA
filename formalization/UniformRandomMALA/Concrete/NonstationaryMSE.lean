import UniformRandomMALA.Concrete.NonstationaryMSEExpansion
import UniformRandomMALA.Concrete.NonstationaryMSESum

/-!
# Nonstationary finite-sample mean-square error

The empirical mean contains exactly `X₀,...,Xₙ₋₁`, with no burn-in, and
expectation is taken under the recursively constructed finite Markov path
law. The proof combines genuine density evolution, `L⁴` interpolation,
the pair-coordinate laws, and the exact finite sum expansion.
-/

namespace UniformRandomMALA.Concrete
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators
noncomputable section
variable {α : Type*} [MeasurableSpace α]

/-- The finite-sample MSE estimate for a positive reversible kernel.
The second term is rounded up to the constant appearing in the paper. -/
theorem finiteMarkovMSE_le_of_positive
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : μ ≪ π) (hDensity : MemLp (fun x => (μ.rnDeriv π x).toReal) 2 π)
    (K : Kernel α α) [IsMarkovKernel K] (hrev : Kernel.IsReversible K π)
    (hpos : KernelLp.Positive K π) {g : ℝ} (hg0 : 0 < g) (hg1 : g ≤ 1)
    (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π K)
    {f : α → ℝ} (hf : MemLp f 4 π) {n : ℕ} (hn : 0 < n) :
    finiteMarkovMSE μ π K f n ≤
      (2 / g - 1) / n * variance f π +
        128 * centeredDensityL2Norm μ π * lpNorm (KernelLp.center π f) 4 π ^ 2 /
          ((n : ℝ) ^ 2 * g ^ 2) := by
  let f₀ := KernelLp.center π f
  have hf₀ : MemLp f₀ 4 π := KernelLp.center_memLp π hf
  have hf₀0 : ∫ x, f₀ x ∂π = 0 :=
    KernelLp.integral_center π (hf.integrable (by norm_num))
  have hpair := finitePath_pair_bound μ π hμ hDensity K hrev hpos hg0.le hg1 hgap hf₀ hf₀0 n
  let A : Fin n → Fin n → ℝ := fun i j =>
    ∫ path, f₀ (path i) * f₀ (path j) ∂finiteMarkovPathLaw μ K n
  have hsum := nonstationary_matrix_sum_le A (sub_nonneg.mpr hg1)
    (by linarith : 1 - g < 1)
    (integral_nonneg fun x => sq_nonneg (f₀ x))
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
      (centeredDensityL2Norm_nonneg μ π)) (sq_nonneg (lpNorm f₀ 4 π)))
    (fun i j => (hpair i j).2)
  have hδ : 1 - (1 - g) = g := by ring
  rw [hδ] at hsum
  have hvar : (∫ x, f₀ x ^ 2 ∂π) = variance f π := by
    rw [show f₀ = KernelLp.center π f from rfl,
      KernelLp.integral_sq_center π (hf.mono_exponent (by norm_num)),
      variance_eq_sub (hf.mono_exponent (by norm_num))]
    rfl
  rw [hvar] at hsum
  rw [finiteMarkovMSE_eq_pair_sum μ π K f (Nat.ne_of_gt hn)
    (fun i j => (hpair i j).1)]
  change (∑ i, ∑ j, A i j) / (n : ℝ) ^ 2 ≤ _
  calc
    _ ≤ ((n : ℝ) * (2 / g - 1) * variance f π +
        4 * (4 * centeredDensityL2Norm μ π * lpNorm f₀ 4 π ^ 2) / g ^ 2) /
          (n : ℝ) ^ 2 := div_le_div_of_nonneg_right hsum (sq_nonneg _)
    _ = (2 / g - 1) / n * variance f π +
        16 * centeredDensityL2Norm μ π * lpNorm f₀ 4 π ^ 2 /
          ((n : ℝ) ^ 2 * g ^ 2) := by
      field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn), hg0.ne']
      ring
    _ ≤ _ := by
      apply add_le_add le_rfl
      apply div_le_div_of_nonneg_right _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      have h := mul_nonneg (centeredDensityL2Norm_nonneg μ π) (sq_nonneg (lpNorm f₀ 4 π))
      dsimp only [f₀] at h ⊢
      nlinarith

/-- The lazy-kernel version used by the new nonstationary-MSE corollary. -/
theorem finiteMarkovMSE_halfLazy_le
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : μ ≪ π) (hDensity : MemLp (fun x => (μ.rnDeriv π x).toReal) 2 π)
    (K : Kernel α α) [IsMarkovKernel K] (hrev : Kernel.IsReversible K π)
    {g : ℝ} (hg0 : 0 < g) (hg1 : g ≤ 1)
    (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π (halfLazyKernel K))
    {f : α → ℝ} (hf : MemLp f 4 π) {n : ℕ} (hn : 0 < n) :
    finiteMarkovMSE μ π (halfLazyKernel K) f n ≤
      (2 / g - 1) / n * variance f π +
        128 * centeredDensityL2Norm μ π * lpNorm (KernelLp.center π f) 4 π ^ 2 /
          ((n : ℝ) ^ 2 * g ^ 2) :=
  finiteMarkovMSE_le_of_positive μ π hμ hDensity (halfLazyKernel K)
    (halfLazyKernel_isReversible π K hrev) (KernelLp.halfLazy_positive K π hrev)
    hg0 hg1 hgap hf hn

end
end UniformRandomMALA.Concrete
