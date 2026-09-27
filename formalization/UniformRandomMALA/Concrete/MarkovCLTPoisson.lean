import UniformRandomMALA.Concrete.StationaryVarianceGeneral

/-!
# The actual Poisson decomposition on finite Markov paths

This module proves the martingale-difference centering identity and the
vanishing normalized endpoint remainder. These are analytic ingredients
of the Markov central limit theorem, not a claim that the CLT has already
been established.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory Filter KernelLp
open scoped ENNReal ProbabilityTheory RealInnerProductSpace Topology

noncomputable section
variable {α : Type*} [MeasurableSpace α]

/-- The one-step Poisson increment along a Markov transition. -/
def poissonIncrement (K : Kernel α α) (u : α → ℝ) (x y : α) : ℝ :=
  u y - KernelLp.average K u x

theorem poissonIncrement_conditional_mean_zero
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {u : α → ℝ} (hu : MemLp u 2 π) :
    ∀ᵐ x ∂π, ∫ y, poissonIncrement K u x y ∂K x = 0 := by
  have hi : Integrable u (K ∘ₘ π) := by rw [hπ]; exact hu.integrable (by norm_num)
  filter_upwards [Measure.ae_integrable_of_integrable_comp hi] with x hx
  simp only [poissonIncrement]
  rw [integral_sub hx (integrable_const _)]
  simp [KernelLp.average]

/-- Sum of the conditionally centered one-step Poisson increments. -/
def finitePoissonIncrementSum (K : Kernel α α) (u : α → ℝ)
    (n : ℕ) (path : Fin (n + 1) → α) : ℝ :=
  ∑ i : Fin n, poissonIncrement K u (path i.castSucc) (path i.succ)

omit [MeasurableSpace α] in
theorem sum_fin_successive_differences (a : Fin (n + 1) → ℝ) :
    (∑ i : Fin n, (a i.castSucc - a i.succ)) = a 0 - a (Fin.last n) := by
  have hleft := Fin.sum_univ_castSucc a
  have hright := Fin.sum_univ_succ a
  rw [Finset.sum_sub_distrib]
  linarith

/-- A Poisson equation yields the exact additive-functional decomposition
on the actual stationary path law. -/
theorem finitePoisson_decomposition_ae
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {u f : α → ℝ}
    (hPoisson : (fun x => u x - KernelLp.average K u x) =ᵐ[π] f) (n : ℕ) :
    (fun path : Fin (n + 1) → α => ∑ i : Fin n, f (path i.castSucc))
      =ᵐ[finiteMarkovPathLaw π K (n + 1)]
    (fun path => finitePoissonIncrementSum K u n path + u (path 0) - u (path (Fin.last n))) := by
  have hi (i : Fin n) :
      (fun path : Fin (n + 1) → α => u (path i.castSucc) -
        KernelLp.average K u (path i.castSucc)) =ᵐ[finiteMarkovPathLaw π K (n + 1)]
        (fun path => f (path i.castSucc)) := by
    have hm := stationaryPathLaw_measurePreserving_coordinate π K hπ (n + 1) i.castSucc
    have hh := hm.quasiMeasurePreserving.ae_eq_comp hPoisson
    exact hh
  filter_upwards [ae_all_iff.2 hi] with path hpath
  have ht := sum_fin_successive_differences (fun i => u (path i))
  have hs : (∑ i : Fin n, f (path i.castSucc)) =
      (∑ i : Fin n, (u (path i.castSucc) - u (path i.succ))) +
        finitePoissonIncrementSum K u n path := by
    unfold finitePoissonIncrementSum
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hpath i]
    simp only [poissonIncrement]
    ring
  rw [hs, ht]
  ring

/-- The normalized boundary term in the Poisson decomposition. -/
def normalizedPoissonBoundary (u : α → ℝ) (n : ℕ)
    (path : Fin (n + 1) → α) : ℝ :=
  (Real.sqrt (n : ℝ))⁻¹ * (u (path 0) - u (path (Fin.last n)))

theorem poissonBoundary_secondMoment_le
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {u : α → ℝ} (hu : MemLp u 2 π) (n : ℕ) :
    (∫ path : Fin (n + 1) → α, (u (path 0) - u (path (Fin.last n))) ^ 2
      ∂finiteMarkovPathLaw π K (n + 1)) ≤ 4 * ∫ x, u x ^ 2 ∂π := by
  have h0 : MemLp (fun path : Fin (n + 1) → α => u (path 0)) 2
      (finiteMarkovPathLaw π K (n + 1)) := stationaryPathLaw_memLp_coordinate π K hπ hu _ _
  have hn : MemLp (fun path : Fin (n + 1) → α => u (path (Fin.last n))) 2
      (finiteMarkovPathLaw π K (n + 1)) := stationaryPathLaw_memLp_coordinate π K hπ hu _ _
  have hscalar (a b : ℝ) : (a - b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
    nlinarith [sq_nonneg (a + b)]
  have h0int : (∫ path : Fin (n + 1) → α, u (path 0) ^ 2
      ∂finiteMarkovPathLaw π K (n + 1)) = ∫ x, u x ^ 2 ∂π :=
    stationaryPathLaw_integral_coordinate π K hπ hu.integrable_sq.1 (n + 1) 0
  have hnint : (∫ path : Fin (n + 1) → α, u (path (Fin.last n)) ^ 2
      ∂finiteMarkovPathLaw π K (n + 1)) = ∫ x, u x ^ 2 ∂π :=
    stationaryPathLaw_integral_coordinate π K hπ hu.integrable_sq.1 (n + 1) (Fin.last n)
  have hI : Integrable (fun path : Fin (n + 1) → α =>
      (u (path 0) - u (path (Fin.last n))) ^ 2) (finiteMarkovPathLaw π K (n + 1)) :=
    (h0.sub hn).integrable_sq
  have hJ : Integrable (fun path : Fin (n + 1) → α =>
      2 * u (path 0) ^ 2 + 2 * u (path (Fin.last n)) ^ 2)
      (finiteMarkovPathLaw π K (n + 1)) :=
    (h0.integrable_sq.const_mul 2).add (hn.integrable_sq.const_mul 2)
  calc
    _ ≤ ∫ path : Fin (n + 1) → α, 2 * u (path 0) ^ 2 + 2 * u (path (Fin.last n)) ^ 2
        ∂finiteMarkovPathLaw π K (n + 1) :=
      integral_mono hI hJ
        (fun path => hscalar (u (path 0)) (u (path (Fin.last n))))
    _ = _ := by
      rw [integral_add (h0.integrable_sq.const_mul 2) (hn.integrable_sq.const_mul 2),
        integral_const_mul, integral_const_mul, h0int, hnint]
      ring

theorem normalizedPoissonBoundary_secondMoment_le
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {u : α → ℝ} (hu : MemLp u 2 π) (n : ℕ) :
    (∫ path, (normalizedPoissonBoundary u n path) ^ 2
      ∂finiteMarkovPathLaw π K (n + 1)) ≤ (4 * ∫ x, u x ^ 2 ∂π) / n := by
  simp only [normalizedPoissonBoundary, mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [integral_const_mul, div_eq_mul_inv]
  exact (mul_le_mul_of_nonneg_left (poissonBoundary_secondMoment_le π K hπ hu n)
    (inv_nonneg.mpr (Nat.cast_nonneg n))).trans_eq (mul_comm _ _)

/-- The endpoint error vanishes in actual mean square on the finite path
spaces, which is the required negligible-remainder step for a CLT. -/
theorem normalizedPoissonBoundary_secondMoment_tendsto_zero
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {u : α → ℝ} (hu : MemLp u 2 π) :
    Tendsto (fun n => ∫ path, (normalizedPoissonBoundary u n path) ^ 2
      ∂finiteMarkovPathLaw π K (n + 1)) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => integral_nonneg (fun _ => sq_nonneg _))
    (normalizedPoissonBoundary_secondMoment_le π K hπ hu)
  exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

end
end UniformRandomMALA.Concrete
