import UniformRandomMALA.Concrete.NonstationaryMSEPairBounds

/-! # Exact finite-path expansion of empirical-mean square error -/

namespace UniformRandomMALA.Concrete
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators
noncomputable section
variable {α : Type*} [MeasurableSpace α]

theorem finiteMarkovSampleMean_center (π : Measure α) (f : α → ℝ)
    {n : ℕ} (hn : n ≠ 0) :
    finiteMarkovSampleMean (KernelLp.center π f) n =
      fun path => finiteMarkovSampleMean f n path - ∫ x, f x ∂π := by
  funext path
  simp only [finiteMarkovSampleMean, KernelLp.center, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sub_div]
  rw [mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn)]

theorem integral_sq_finiteMarkovSampleMean (μ : Measure α) (K : Kernel α α)
    (f : α → ℝ) (n : ℕ)
    (hpair : ∀ i j : Fin n, Integrable (fun path => f (path i) * f (path j))
      (finiteMarkovPathLaw μ K n)) :
    (∫ path, finiteMarkovSampleMean f n path ^ 2 ∂finiteMarkovPathLaw μ K n) =
      (∑ i : Fin n, ∑ j : Fin n,
        ∫ path, f (path i) * f (path j) ∂finiteMarkovPathLaw μ K n) / (n : ℝ) ^ 2 := by
  have heq (path : Fin n → α) : finiteMarkovSampleMean f n path ^ 2 =
      (∑ i : Fin n, ∑ j : Fin n, f (path i) * f (path j)) / (n : ℝ) ^ 2 := by
    rw [finiteMarkovSampleMean, div_pow, pow_two]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  simp_rw [heq]
  rw [integral_div]
  congr 1
  rw [integral_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hpair i j))]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_finsetSum Finset.univ (fun j _ => hpair i j)

/-- This is an exact identity under the actual path law, prior to any
spectral or interpolation estimates. -/
theorem finiteMarkovMSE_eq_pair_sum (μ π : Measure α) (K : Kernel α α)
    (f : α → ℝ) {n : ℕ} (hn : n ≠ 0)
    (hpair : ∀ i j : Fin n,
      Integrable (fun path => KernelLp.center π f (path i) * KernelLp.center π f (path j))
        (finiteMarkovPathLaw μ K n)) :
    finiteMarkovMSE μ π K f n =
      (∑ i : Fin n, ∑ j : Fin n,
        ∫ path, KernelLp.center π f (path i) * KernelLp.center π f (path j)
          ∂finiteMarkovPathLaw μ K n) / (n : ℝ) ^ 2 := by
  unfold finiteMarkovMSE
  have heq := finiteMarkovSampleMean_center π f hn
  simp_rw [← congrFun heq]
  exact integral_sq_finiteMarkovSampleMean μ K (KernelLp.center π f) n hpair

end
end UniformRandomMALA.Concrete
