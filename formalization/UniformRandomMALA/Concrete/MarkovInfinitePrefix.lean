import UniformRandomMALA.Concrete.MarkovFiniteExtension

/-! # Infinite trajectories restrict to the actual finite path laws -/

namespace UniformRandomMALA.Concrete
open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal ProbabilityTheory
noncomputable section
variable {α : Type*} [MeasurableSpace α]

def markovPathPrefix (n : ℕ) (path : ℕ → α) : Fin n → α := fun i => path i

theorem measurable_markovPathPrefix (n : ℕ) : Measurable (markovPathPrefix (α := α) n) :=
  measurable_pi_iff.mpr fun i => measurable_pi_apply i.val

def markovHistoryPrefix (n : ℕ) (path : (i : Finset.Iic n) → α) : Fin (n + 1) → α :=
  fun i => path ⟨i.val, Finset.mem_Iic.mpr (Nat.le_of_lt_succ i.isLt)⟩

theorem measurable_markovHistoryPrefix (n : ℕ) : Measurable (markovHistoryPrefix (α := α) n) :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply _

theorem infiniteMarkovPathLaw_prefix_next
    (μ : Measure α) [IsProbabilityMeasure μ] (K : Kernel α α) [IsMarkovKernel K] (n : ℕ) :
    (infiniteMarkovPathLaw μ K).map (fun path => (markovPathPrefix (n + 1) path, path (n + 1))) =
      (infiniteMarkovPathLaw μ K).map (markovPathPrefix (n + 1)) ⊗ₘ finitePathNextKernel K n := by
  let H := markovHistoryPrefix (α := α) n
  have hH : Measurable H := measurable_markovHistoryPrefix n
  let : IsProbabilityMeasure ((infiniteMarkovPathLaw μ K).map (frestrictLe n)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have h := congrArg (fun ν => ν.map (Prod.map H id)) (infiniteMarkovPathLaw_history_next μ K n)
  rw [Measure.map_map (hH.prodMap measurable_id) (by fun_prop)] at h
  change (infiniteMarkovPathLaw μ K).map (fun path => (markovPathPrefix (n + 1) path, path (n + 1))) =
    (((infiniteMarkovPathLaw μ K).map (frestrictLe n)) ⊗ₘ
      (finitePathNextKernel K n).comap H hH).map (Prod.map H id) at h
  rw [map_fst_compProd_comap _ (finitePathNextKernel K n) H hH,
    Measure.map_map hH (by fun_prop)] at h
  exact h

theorem infiniteMarkovPathLaw_prefix_append
    (μ : Measure α) [IsProbabilityMeasure μ] (K : Kernel α α) [IsMarkovKernel K] (n : ℕ) :
    (infiniteMarkovPathLaw μ K).map (markovPathPrefix (n + 2)) =
      ((infiniteMarkovPathLaw μ K).map (markovPathPrefix (n + 1)) ⊗ₘ finitePathNextKernel K n).map
        (fun z => Fin.snoc z.1 z.2) := by
  rw [← infiniteMarkovPathLaw_prefix_next μ K n,
    Measure.map_map (measurable_markovPathSnoc (n + 1))
      ((measurable_markovPathPrefix (n + 1)).prodMk (measurable_pi_apply (n + 1)))]
  congr 1
  funext path i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [markovPathPrefix]

theorem finiteMarkovPathLaw_one
    (μ : Measure α) [IsProbabilityMeasure μ] (K : Kernel α α) [IsMarkovKernel K] :
    finiteMarkovPathLaw μ K 1 = μ.map (fun x (_ : Fin 1) => x) := by
  apply Measure.ext_of_lintegral
  intro F hF
  have hc : Measurable (fun x : α => fun _ : Fin 1 => x) :=
    measurable_pi_iff.mpr fun _ => measurable_id
  rw [lintegral_map hF hc]
  change (∫⁻ path, F path ∂finiteMarkovPathKernel K 1 ∘ₘ μ) = _
  rw [Measure.lintegral_bind (finiteMarkovPathKernel K 1).aemeasurable hF.aemeasurable]
  exact lintegral_congr fun x => lintegral_finiteMarkovPathKernel_one K x hF

theorem infiniteMarkovPathLaw_map_prefix_succ
    (μ : Measure α) [IsProbabilityMeasure μ] (K : Kernel α α) [IsMarkovKernel K] (n : ℕ) :
    (infiniteMarkovPathLaw μ K).map (markovPathPrefix (n + 1)) = finiteMarkovPathLaw μ K (n + 1) := by
  induction n with
  | zero =>
    have heq : markovPathPrefix (α := α) 1 =
        (fun x (_ : Fin 1) => x) ∘ (fun path : ℕ → α => path 0) := by
      funext path i
      fin_cases i
      rfl
    have hc : Measurable (fun x : α => fun _ : Fin 1 => x) :=
      measurable_pi_iff.mpr fun _ => measurable_id
    have hz : Measurable (fun path : ℕ → α => path 0) := measurable_pi_apply 0
    rw [heq, ← Measure.map_map hc hz,
      infiniteMarkovPathLaw_map_zero, finiteMarkovPathLaw_one]
  | succ n ih => rw [infiniteMarkovPathLaw_prefix_append, ih, finiteMarkovPathLaw_append]

/-- Every finite collection `X₀,...,Xₙ₋₁` has exactly the previously defined
recursive finite Markov path law. -/
theorem infiniteMarkovPathLaw_map_prefix
    (μ : Measure α) [IsProbabilityMeasure μ] (K : Kernel α α) [IsMarkovKernel K] (n : ℕ) :
    (infiniteMarkovPathLaw μ K).map (markovPathPrefix n) = finiteMarkovPathLaw μ K n := by
  cases n with
  | zero =>
    have heq : markovPathPrefix (α := α) 0 = fun _ => Fin.elim0 := by
      funext path i
      exact Fin.elim0 i
    rw [heq, finiteMarkovPathLaw, finiteMarkovPathKernel, Measure.deterministic_comp_eq_map]
    simp
  | succ n => exact infiniteMarkovPathLaw_map_prefix_succ μ K n

end
end UniformRandomMALA.Concrete
