import UniformRandomMALA.Concrete.MarkovInfinitePath
import UniformRandomMALA.Concrete.MarkovCLTVariance
import UniformRandomMALA.Concrete.MartingaleCLTConditional

/-! # Genuine Poisson martingale differences on the infinite Markov law -/

namespace UniformRandomMALA.Concrete
open MeasureTheory ProbabilityTheory Preorder Filter
open scoped ENNReal ProbabilityTheory
noncomputable section
variable {α : Type*} [MeasurableSpace α]

theorem stationaryInfinitePathLaw_measurePreserving_coordinate
    (π : Measure α) [IsProbabilityMeasure π] (K : Kernel α α) [IsMarkovKernel K]
    (hπ : Kernel.Invariant K π) (n : ℕ) :
    MeasurePreserving (fun path : ℕ → α => path n) (infiniteMarkovPathLaw π K) π :=
  ⟨measurable_pi_apply n, stationaryInfinitePathLaw_map_coordinate π K hπ n⟩

theorem stationaryInfinitePathLaw_measurePreserving_successive
    (π : Measure α) [IsProbabilityMeasure π] (K : Kernel α α) [IsMarkovKernel K]
    (hπ : Kernel.Invariant K π) (n : ℕ) :
    MeasurePreserving (fun path : ℕ → α => (path n, path (n + 1)))
      (infiniteMarkovPathLaw π K) (π ⊗ₘ K) :=
  ⟨(measurable_pi_apply n).prodMk (measurable_pi_apply (n + 1)),
    stationaryInfinitePathLaw_map_successive π K hπ n⟩

variable [StandardBorelSpace α] [Nonempty α]

/-- The Markov conditional-expectation identity follows from the actual
trajectory law, rather than being assumed of an arbitrary process. -/
theorem infiniteMarkovPath_condExp_edge
    (π : Measure α) [IsProbabilityMeasure π] (K : Kernel α α) [IsMarkovKernel K]
    (hπ : Kernel.Invariant K π) {F : α × α → ℝ} (hF : Measurable F)
    (hFi : Integrable F (π ⊗ₘ K)) (n : ℕ) :
    (infiniteMarkovPathLaw π K)[fun path => F (path n, path (n + 1)) |
      markovPathFiltration n] =ᵐ[infiniteMarkovPathLaw π K]
        fun path => ∫ y, F (path n, y) ∂K (path n) := by
  let H : ((i : Finset.Iic n) → α) × α → ℝ :=
    fun p => F (p.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩, p.2)
  have hH : StronglyMeasurable H :=
    (hF.comp (((measurable_pi_apply _).comp measurable_fst).prodMk measurable_snd)).stronglyMeasurable
  have hi : Integrable (fun path : ℕ → α => F (path n, path (n + 1)))
      (infiniteMarkovPathLaw π K) := by
    have hi' : Integrable F ((infiniteMarkovPathLaw π K).map
        (fun path => (path n, path (n + 1)))) := by
      rw [stationaryInfinitePathLaw_map_successive π K hπ]
      exact hFi
    exact hi'.comp_measurable ((measurable_pi_apply n).prodMk (measurable_pi_apply (n + 1)))
  have he := condExp_prod_ae_eq_integral_condDistrib
    (μ := infiniteMarkovPathLaw π K) (X := frestrictLe n)
    (Y := fun path : ℕ → α => path (n + 1)) (f := H)
    (measurable_frestrictLe n) (measurable_pi_apply (n + 1)).aemeasurable hH hi
  have hk := Kernel.condDistrib_trajMeasure (X := fun _ => α)
    (μ₀ := π) (κ := markovHistoryKernel K) (a := n)
  have hk' := ae_of_ae_map (μ := infiniteMarkovPathLaw π K)
    (f := frestrictLe n) (measurable_frestrictLe n).aemeasurable hk
  rw [markovPathFiltration, Filtration.piLE_eq_comap_frestrictLe]
  filter_upwards [he, hk'] with path he hk
  change condDistrib (fun path : ℕ → α => path (n + 1)) (frestrictLe n)
    (infiniteMarkovPathLaw π K) (frestrictLe n path) =
      markovHistoryKernel K n (frestrictLe n path) at hk
  rw [hk] at he
  exact he

def infinitePoissonIncrement (K : Kernel α α) (u : α → ℝ) (k : ℕ) (path : ℕ → α) : ℝ :=
  poissonIncrement K u (path k) (path (k + 1))

omit [StandardBorelSpace α] [Nonempty α] in
theorem measurable_poissonIncrement (K : Kernel α α) [IsMarkovKernel K]
    {u : α → ℝ} (hu : Measurable u) :
    Measurable (fun z : α × α => poissonIncrement K u z.1 z.2) := by
  have ha : Measurable (KernelLp.average K u) := hu.stronglyMeasurable.integral_kernel.measurable
  exact (hu.comp measurable_snd).sub (ha.comp measurable_fst)

omit [StandardBorelSpace α] [Nonempty α] in
theorem infinitePoissonIncrement_memLp
    (π : Measure α) [IsProbabilityMeasure π] (K : Kernel α α) [IsMarkovKernel K]
    (hπ : Kernel.Invariant K π) {u : α → ℝ} (hu : MemLp u 2 π) (k : ℕ) :
    MemLp (infinitePoissonIncrement K u k) 2 (infiniteMarkovPathLaw π K) :=
  (poissonIncrement_memLp π K hπ hu).comp_measurePreserving
    (stationaryInfinitePathLaw_measurePreserving_successive π K hπ k)

omit [StandardBorelSpace α] [Nonempty α] in
theorem infinitePoissonIncrement_measurable (K : Kernel α α) [IsMarkovKernel K]
    {u : α → ℝ} (hu : Measurable u) (k : ℕ) :
    StronglyMeasurable[markovPathFiltration (k + 1)] (infinitePoissonIncrement K u k) := by
  exact ((measurable_poissonIncrement K hu).comp
    ((measurable_coordinate_markovPathFiltration (k + 1) k (by omega)).prodMk
      (measurable_coordinate_markovPathFiltration (k + 1) (k + 1) le_rfl))).stronglyMeasurable

theorem infinitePoissonIncrement_condExp_zero
    (π : Measure α) [IsProbabilityMeasure π] (K : Kernel α α) [IsMarkovKernel K]
    (hπ : Kernel.Invariant K π) {u : α → ℝ} (hm : Measurable u) (hu : MemLp u 2 π) (k : ℕ) :
    (infiniteMarkovPathLaw π K)[infinitePoissonIncrement K u k | markovPathFiltration k]
      =ᵐ[infiniteMarkovPathLaw π K] 0 := by
  have he := infiniteMarkovPath_condExp_edge π K hπ (measurable_poissonIncrement K hm)
    ((poissonIncrement_memLp π K hπ hu).integrable (by norm_num)) k
  have hz := (stationaryInfinitePathLaw_measurePreserving_coordinate π K hπ k).quasiMeasurePreserving
    |>.ae (poissonIncrement_conditional_mean_zero π K hπ hu)
  exact he.trans hz

theorem infinitePoissonIncrement_condExp_sq
    (π : Measure α) [IsProbabilityMeasure π] (K : Kernel α α) [IsMarkovKernel K]
    (hπ : Kernel.Invariant K π) {u : α → ℝ} (hm : Measurable u) (hu : MemLp u 2 π) (k : ℕ) :
    (infiniteMarkovPathLaw π K)[fun path => infinitePoissonIncrement K u k path ^ 2 |
      markovPathFiltration k] =ᵐ[infiniteMarkovPathLaw π K]
        fun path => poissonConditionalVariance K u (path k) :=
  infiniteMarkovPath_condExp_edge π K hπ ((measurable_poissonIncrement K hm).pow_const 2)
    (poissonIncrement_memLp π K hπ hu).integrable_sq k

/-- A row of the actual stationary Poisson martingale differences. -/
def poissonMartingaleRow
    (π : Measure α) [IsProbabilityMeasure π] (K : Kernel α α) [IsMarkovKernel K]
    (hπ : Kernel.Invariant K π) (u : Lp ℝ 2 π) (n : ℕ) :
    MartingaleDifferenceRow (infiniteMarkovPathLaw π K) where
  length := n
  filtration := markovPathFiltration
  increment := infinitePoissonIncrement K u
  memLp := infinitePoissonIncrement_memLp π K hπ (Lp.memLp u)
  measurable := infinitePoissonIncrement_measurable K (Lp.stronglyMeasurable u).measurable
  mean_zero := infinitePoissonIncrement_condExp_zero π K hπ (Lp.stronglyMeasurable u).measurable (Lp.memLp u)

theorem poissonMartingaleRow_conditionalVariance
    (π : Measure α) [IsProbabilityMeasure π] (K : Kernel α α) [IsMarkovKernel K]
    (hπ : Kernel.Invariant K π) (u : Lp ℝ 2 π) (n k : ℕ) :
    (poissonMartingaleRow π K hπ u n).conditionalVariance k =ᵐ[infiniteMarkovPathLaw π K]
      fun path => poissonConditionalVariance K u (path k) :=
  ((poissonMartingaleRow π K hπ u n).conditionalVariance_eq_condExp k).trans
    (infinitePoissonIncrement_condExp_sq π K hπ (Lp.stronglyMeasurable u).measurable (Lp.memLp u) k)

end
end UniformRandomMALA.Concrete
