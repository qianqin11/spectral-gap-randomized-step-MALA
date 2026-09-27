import UniformRandomMALA.Concrete.MarkovInfiniteInitial
import UniformRandomMALA.Concrete.MarkovInfiniteRow
import UniformRandomMALA.Concrete.MartingaleCLTLimit

/-! # Genuine Poisson martingale rows from a bounded initial density -/

namespace UniformRandomMALA.Concrete
open MeasureTheory ProbabilityTheory Preorder Filter
open scoped ENNReal ProbabilityTheory Topology
noncomputable section
variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]

/-- The conditional transition identity requires integrability on the
actual path law, and does not require a stationary initial law. -/
theorem infiniteMarkovPath_condExp_edge_of_integrable
    (μ : Measure α) [IsProbabilityMeasure μ] (K : Kernel α α) [IsMarkovKernel K]
    {F : α × α → ℝ} (hF : Measurable F) (n : ℕ)
    (hi : Integrable (fun path : ℕ → α => F (path n, path (n + 1))) (infiniteMarkovPathLaw μ K)) :
    (infiniteMarkovPathLaw μ K)[fun path => F (path n, path (n + 1)) |
      markovPathFiltration n] =ᵐ[infiniteMarkovPathLaw μ K]
        fun path => ∫ y, F (path n, y) ∂K (path n) := by
  let H : ((i : Finset.Iic n) → α) × α → ℝ :=
    fun p => F (p.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩, p.2)
  have hH : StronglyMeasurable H :=
    (hF.comp (((measurable_pi_apply _).comp measurable_fst).prodMk measurable_snd)).stronglyMeasurable
  have he := condExp_prod_ae_eq_integral_condDistrib
    (μ := infiniteMarkovPathLaw μ K) (X := frestrictLe n)
    (Y := fun path : ℕ → α => path (n + 1)) (f := H)
    (measurable_frestrictLe n) (measurable_pi_apply (n + 1)).aemeasurable hH hi
  have hk := Kernel.condDistrib_trajMeasure (X := fun _ => α)
    (μ₀ := μ) (κ := markovHistoryKernel K) (a := n)
  have hk' := ae_of_ae_map (μ := infiniteMarkovPathLaw μ K)
    (f := frestrictLe n) (measurable_frestrictLe n).aemeasurable hk
  rw [markovPathFiltration, Filtration.piLE_eq_comap_frestrictLe]
  filter_upwards [he, hk'] with path he hk
  change condDistrib (fun path : ℕ → α => path (n + 1)) (frestrictLe n)
    (infiniteMarkovPathLaw μ K) (frestrictLe n path) =
      markovHistoryKernel K n (frestrictLe n path) at hk
  rw [hk] at he
  exact he

omit [StandardBorelSpace α] [Nonempty α] in
theorem boundedInitialPoisson_memLp
    (π μ : Measure α) [IsProbabilityMeasure π] [IsProbabilityMeasure μ]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hdom : μ ≤ B • π) (u : Lp ℝ 2 π) (k : ℕ) :
    MemLp (infinitePoissonIncrement K u k) 2 (infiniteMarkovPathLaw μ K) :=
  (infinitePoissonIncrement_memLp π K hπ (Lp.memLp u) k).of_measure_le_smul hB
    (infiniteMarkovPathLaw_le_smul B hdom K)

theorem boundedInitialPoisson_condExp_zero
    (π μ : Measure α) [IsProbabilityMeasure π] [IsProbabilityMeasure μ]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hdom : μ ≤ B • π) (u : Lp ℝ 2 π) (k : ℕ) :
    (infiniteMarkovPathLaw μ K)[infinitePoissonIncrement K u k | markovPathFiltration k]
      =ᵐ[infiniteMarkovPathLaw μ K] 0 := by
  have he := infiniteMarkovPath_condExp_edge_of_integrable μ K
    (measurable_poissonIncrement K (Lp.stronglyMeasurable u).measurable) k
    ((boundedInitialPoisson_memLp π μ K hπ hB hdom u k).integrable (by norm_num))
  have hz := (stationaryInfinitePathLaw_measurePreserving_coordinate π K hπ k).quasiMeasurePreserving
    |>.ae (poissonIncrement_conditional_mean_zero π K hπ (Lp.memLp u))
  have hac := Measure.absolutelyContinuous_of_le_smul (infiniteMarkovPathLaw_le_smul B hdom K)
  exact he.trans (hac.ae_le hz)

theorem boundedInitialPoisson_condExp_sq
    (π μ : Measure α) [IsProbabilityMeasure π] [IsProbabilityMeasure μ]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hdom : μ ≤ B • π) (u : Lp ℝ 2 π) (k : ℕ) :
    (infiniteMarkovPathLaw μ K)[fun path => infinitePoissonIncrement K u k path ^ 2 |
      markovPathFiltration k] =ᵐ[infiniteMarkovPathLaw μ K]
        fun path => poissonConditionalVariance K u (path k) :=
  infiniteMarkovPath_condExp_edge_of_integrable μ K
    ((measurable_poissonIncrement K (Lp.stronglyMeasurable u).measurable).pow_const 2) k
    (boundedInitialPoisson_memLp π μ K hπ hB hdom u k).integrable_sq

def boundedInitialPoissonRow
    (π μ : Measure α) [IsProbabilityMeasure π] [IsProbabilityMeasure μ]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hdom : μ ≤ B • π) (u : Lp ℝ 2 π) (n : ℕ) :
    MartingaleDifferenceRow (infiniteMarkovPathLaw μ K) where
  length := n
  filtration := markovPathFiltration
  increment := infinitePoissonIncrement K u
  memLp := boundedInitialPoisson_memLp π μ K hπ hB hdom u
  measurable := infinitePoissonIncrement_measurable K (Lp.stronglyMeasurable u).measurable
  mean_zero := boundedInitialPoisson_condExp_zero π μ K hπ hB hdom u

def boundedNormalizedPoissonRow
    (π μ : Measure α) [IsProbabilityMeasure π] [IsProbabilityMeasure μ]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hdom : μ ≤ B • π) (u : Lp ℝ 2 π) (n : ℕ) :
    MartingaleDifferenceRow (infiniteMarkovPathLaw μ K) :=
  scaledMartingaleRow (Real.sqrt (n : ℝ))⁻¹ (boundedInitialPoissonRow π μ K hπ hB hdom u n)

@[simp] theorem boundedNormalizedPoissonRow_increment
    (π μ : Measure α) [IsProbabilityMeasure π] [IsProbabilityMeasure μ]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hdom : μ ≤ B • π) (u : Lp ℝ 2 π) (n k : ℕ) (path : ℕ → α) :
    (boundedNormalizedPoissonRow π μ K hπ hB hdom u n).increment k path =
      (Real.sqrt (n : ℝ))⁻¹ * poissonIncrement K u (path k) (path (k + 1)) := rfl

@[simp] theorem boundedNormalizedPoissonRow_length
    (π μ : Measure α) [IsProbabilityMeasure π] [IsProbabilityMeasure μ]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hdom : μ ≤ B • π) (u : Lp ℝ 2 π) (n : ℕ) :
    (boundedNormalizedPoissonRow π μ K hπ hB hdom u n).length = n := rfl

theorem boundedNormalizedPoissonRow_conditionalVariance
    (π μ : Measure α) [IsProbabilityMeasure π] [IsProbabilityMeasure μ]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hdom : μ ≤ B • π) (u : Lp ℝ 2 π) (n k : ℕ) :
    (boundedNormalizedPoissonRow π μ K hπ hB hdom u n).conditionalVariance k
      =ᵐ[infiniteMarkovPathLaw μ K]
        fun path => (n : ℝ)⁻¹ * poissonConditionalVariance K u (path k) := by
  have hraw := ((boundedInitialPoissonRow π μ K hπ hB hdom u n).conditionalVariance_eq_condExp k).trans
    (boundedInitialPoisson_condExp_sq π μ K hπ hB hdom u k)
  have hs := scaledMartingaleRow_conditionalVariance (Real.sqrt (n : ℝ))⁻¹
    (boundedInitialPoissonRow π μ K hπ hB hdom u n) k
  filter_upwards [hs, hraw] with path hs hp
  simpa only [boundedNormalizedPoissonRow, hp, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)] using hs

end
end UniformRandomMALA.Concrete
