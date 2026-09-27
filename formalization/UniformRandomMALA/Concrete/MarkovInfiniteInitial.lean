import UniformRandomMALA.Concrete.MarkovInfinitePrefix

/-! # Initial-law linearity and time shifts of the actual Markov law -/

namespace UniformRandomMALA.Concrete
open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal ProbabilityTheory
noncomputable section
variable {α : Type*} [MeasurableSpace α]

/-- The complete trajectory kernel, conditional on its starting point. -/
def infiniteMarkovPathKernel (K : Kernel α α) [IsMarkovKernel K] : Kernel α (ℕ → α) :=
  (Kernel.traj (markovHistoryKernel K) 0).comap
    (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => α)).symm (by fun_prop)

instance infiniteMarkovPathKernel_isMarkov (K : Kernel α α) [IsMarkovKernel K] :
    IsMarkovKernel (infiniteMarkovPathKernel K) := by
  unfold infiniteMarkovPathKernel
  infer_instance

theorem infiniteMarkovPathLaw_eq_comp (μ : Measure α) (K : Kernel α α) [IsMarkovKernel K] :
    infiniteMarkovPathLaw μ K = infiniteMarkovPathKernel K ∘ₘ μ := by
  unfold infiniteMarkovPathLaw Kernel.trajMeasure infiniteMarkovPathKernel
  rw [← Kernel.comp_deterministic_eq_comap, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map]

@[simp] theorem infiniteMarkovPathLaw_univ (μ : Measure α) (K : Kernel α α)
    [IsMarkovKernel K] : infiniteMarkovPathLaw μ K Set.univ = μ Set.univ := by
  rw [infiniteMarkovPathLaw_eq_comp, Measure.comp_apply_univ]

instance infiniteMarkovPathLaw_isFinite (μ : Measure α) [IsFiniteMeasure μ]
    (K : Kernel α α) [IsMarkovKernel K] : IsFiniteMeasure (infiniteMarkovPathLaw μ K) :=
  ⟨by rw [infiniteMarkovPathLaw_univ]; exact measure_lt_top _ _⟩

theorem infiniteMarkovPathLaw_add (μ ν : Measure α) (K : Kernel α α) [IsMarkovKernel K] :
    infiniteMarkovPathLaw (μ + ν) K = infiniteMarkovPathLaw μ K + infiniteMarkovPathLaw ν K := by
  unfold infiniteMarkovPathLaw Kernel.trajMeasure
  rw [Measure.map_add _ _ (by fun_prop), Measure.comp_add]

theorem infiniteMarkovPathLaw_smul (a : ℝ≥0∞) (μ : Measure α) (K : Kernel α α) [IsMarkovKernel K] :
    infiniteMarkovPathLaw (a • μ) K = a • infiniteMarkovPathLaw μ K := by
  unfold infiniteMarkovPathLaw Kernel.trajMeasure
  rw [Measure.map_smul, Measure.comp_smul]

theorem infiniteMarkovPathLaw_mono {μ ν : Measure α} (h : μ ≤ ν)
    (K : Kernel α α) [IsMarkovKernel K] : infiniteMarkovPathLaw μ K ≤ infiniteMarkovPathLaw ν K := by
  apply Measure.le_iff.mpr
  intro s hs
  unfold infiniteMarkovPathLaw Kernel.trajMeasure
  rw [Measure.bind_apply hs (Kernel.traj _ _).aemeasurable,
    Measure.bind_apply hs (Kernel.traj _ _).aemeasurable]
  exact lintegral_mono' (Measure.map_mono h (by fun_prop)) le_rfl

theorem infiniteMarkovPathLaw_le_smul {μ π : Measure α} (B : ℝ≥0∞)
    (h : μ ≤ B • π) (K : Kernel α α) [IsMarkovKernel K] :
    infiniteMarkovPathLaw μ K ≤ B • infiniteMarkovPathLaw π K :=
  (infiniteMarkovPathLaw_mono h K).trans_eq (infiniteMarkovPathLaw_smul B π K)

theorem infiniteMarkovPathLaw_decomposition {μ ν ρ : Measure α} (a : ℝ≥0∞)
    (h : μ = a • ν + ρ) (K : Kernel α α) [IsMarkovKernel K] :
    infiniteMarkovPathLaw μ K = a • infiniteMarkovPathLaw ν K + infiniteMarkovPathLaw ρ K := by
  rw [h, infiniteMarkovPathLaw_add, infiniteMarkovPathLaw_smul]

theorem pathMeasure_ext_prefix {μ ν : Measure (ℕ → α)} [IsFiniteMeasure μ]
    (h : ∀ n, μ.map (markovPathPrefix n) = ν.map (markovPathPrefix n)) : μ = ν := by
  let P := fun S : Finset ℕ => μ.map S.restrict
  have hμ : IsProjectiveLimit μ P := fun _ => rfl
  have hν : IsProjectiveLimit ν P := by
    intro S
    let n := S.sup id
    let f : (Fin (n + 1) → α) → (i : S) → α :=
      fun path i => path ⟨i.val, Nat.lt_succ_of_le (Finset.le_sup (f := id) i.property)⟩
    have hf : Measurable f := measurable_pi_iff.mpr fun _ => measurable_pi_apply _
    have hh := congrArg (fun η : Measure (Fin (n + 1) → α) => η.map f) (h (n + 1))
    rw [Measure.map_map hf (measurable_markovPathPrefix (n + 1)),
      Measure.map_map hf (measurable_markovPathPrefix (n + 1))] at hh
    exact hh.symm
  exact hμ.unique hν

def markovPathShift (k : ℕ) (path : ℕ → α) : ℕ → α := fun i => path (k + i)

theorem measurable_markovPathShift (k : ℕ) : Measurable (markovPathShift (α := α) k) :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply _

theorem infiniteMarkovPathLaw_shift_one
    (μ : Measure α) [IsProbabilityMeasure μ] (K : Kernel α α) [IsMarkovKernel K] :
    (infiniteMarkovPathLaw μ K).map (markovPathShift 1) = infiniteMarkovPathLaw (K ∘ₘ μ) K := by
  apply pathMeasure_ext_prefix
  intro n
  have heq : markovPathPrefix (α := α) n ∘ markovPathShift 1 =
      Fin.tail ∘ markovPathPrefix (n + 1) := by
    funext path i
    simp [markovPathPrefix, markovPathShift, Fin.tail, Nat.add_comm]
  rw [Measure.map_map (measurable_markovPathPrefix n) (measurable_markovPathShift 1), heq,
    ← Measure.map_map (measurable_markovPathTail n) (measurable_markovPathPrefix (n + 1)),
    infiniteMarkovPathLaw_map_prefix, finiteMarkovPathLaw_map_tail, infiniteMarkovPathLaw_map_prefix]

/-- Dropping `k` initial observations starts the same chain from its actual
`k`-step marginal. -/
theorem infiniteMarkovPathLaw_shift
    (μ : Measure α) [IsProbabilityMeasure μ] (K : Kernel α α) [IsMarkovKernel K] (k : ℕ) :
    (infiniteMarkovPathLaw μ K).map (markovPathShift k) =
      infiniteMarkovPathLaw (DiscreteTime.finiteKernelIterate K k ∘ₘ μ) K := by
  induction k with
  | zero =>
    have heq : markovPathShift (α := α) 0 = id := by funext path i; simp [markovPathShift]
    rw [heq, Measure.map_id]
    simp [DiscreteTime.finiteKernelIterate]
  | succ k ih =>
    have heq : markovPathShift (α := α) (k + 1) = markovPathShift 1 ∘ markovPathShift k := by
      funext path i
      simp [markovPathShift, Nat.add_assoc]
    rw [heq, ← Measure.map_map (measurable_markovPathShift 1) (measurable_markovPathShift k),
      ih, infiniteMarkovPathLaw_shift_one]
    rw [DiscreteTime.finiteKernelIterate, Measure.comp_assoc]

end
end UniformRandomMALA.Concrete
