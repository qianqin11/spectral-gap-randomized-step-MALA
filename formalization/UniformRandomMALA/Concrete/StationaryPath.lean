import UniformRandomMALA.Concrete.NonstationaryMSEPath
import UniformRandomMALA.DiscreteTime.EulerRWMPairChain
import Mathlib.Probability.Kernel.Composition.CompMap

/-!
# Marginals of the actual finite Markov path law

These measure identities derive stationarity of coordinates from the
recursive trajectory construction. They apply to measurable observables
without a boundedness assumption.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory DiscreteTime
open scoped ENNReal ProbabilityTheory

noncomputable section

variable {α : Type*} [MeasurableSpace α]

theorem finiteKernelIterate_comp_right (K : Kernel α α) (n : ℕ) :
    finiteKernelIterate K n ∘ₖ K = finiteKernelIterate K (n + 1) := by
  induction n with
  | zero => simp [finiteKernelIterate]
  | succ n ih =>
    change (K ∘ₖ finiteKernelIterate K n) ∘ₖ K = _
    rw [Kernel.comp_assoc, ih]
    rfl

theorem finiteMarkovPathKernel_map_coordinate (K : Kernel α α) [IsMarkovKernel K]
    (n : ℕ) (i : Fin n) :
    (finiteMarkovPathKernel K n).map (fun path => path i) =
      finiteKernelIterate K i.val := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · ext x s hs
      have hcons : Measurable (fun path : Fin n → α => (Fin.cons x path : Fin (n + 1) → α)) :=
        (measurable_markovPathCons n).comp measurable_prodMk_left
      rw [Kernel.map_apply _ (measurable_pi_apply 0), finiteMarkovPathKernel_succ_apply,
        Measure.map_map (measurable_pi_apply 0) hcons]
      simp [Function.comp_def, finiteKernelIterate, Kernel.id_apply, hs]
    · have hm : (finiteMarkovPathKernel K (n + 1)).map (fun path => path j.succ) =
          (finiteMarkovPathKernel K n ∘ₖ K).map (fun path => path j) := by
        ext x s hs
        have hcons : Measurable (fun path : Fin n → α => (Fin.cons x path : Fin (n + 1) → α)) :=
          (measurable_markovPathCons n).comp measurable_prodMk_left
        rw [Kernel.map_apply _ (measurable_pi_apply j.succ),
          finiteMarkovPathKernel_succ_apply,
          Measure.map_map (measurable_pi_apply j.succ) hcons,
          Kernel.map_apply _ (measurable_pi_apply j)]
        rfl
      rw [hm, Kernel.map_comp, ih, finiteKernelIterate_comp_right]
      rfl

theorem finiteMarkovPathLaw_map_coordinate (μ : Measure α) (K : Kernel α α)
    [IsMarkovKernel K] (n : ℕ) (i : Fin n) :
    (finiteMarkovPathLaw μ K n).map (fun path => path i) =
      finiteKernelIterate K i.val ∘ₘ μ := by
  rw [finiteMarkovPathLaw, Measure.map_comp _ _ (measurable_pi_apply i),
    finiteMarkovPathKernel_map_coordinate]

theorem stationaryPathLaw_map_coordinate (π : Measure α) (K : Kernel α α)
    [IsMarkovKernel K] (hπ : Kernel.Invariant K π) (n : ℕ) (i : Fin n) :
    (finiteMarkovPathLaw π K n).map (fun path => path i) = π := by
  rw [finiteMarkovPathLaw_map_coordinate]
  exact finiteKernelIterate_invariant K π hπ i.val

theorem measurable_markovPathTail (n : ℕ) :
    Measurable (Fin.tail : (Fin (n + 1) → α) → (Fin n → α)) :=
  measurable_pi_iff.mpr fun i => measurable_pi_apply i.succ

theorem finiteMarkovPathKernel_map_tail (K : Kernel α α) [IsMarkovKernel K]
    (n : ℕ) :
    (finiteMarkovPathKernel K (n + 1)).map Fin.tail =
      finiteMarkovPathKernel K n ∘ₖ K := by
  rw [finiteMarkovPathKernel,
    ← Kernel.map_comp_right _ (measurable_markovPathCons n) (measurable_markovPathTail n)]
  have heq : (Fin.tail : (Fin (n + 1) → α) → (Fin n → α)) ∘
      (fun z : α × (Fin n → α) => Fin.cons z.1 z.2) = Prod.snd := by
    funext z i
    simp
  rw [heq, ← Kernel.snd_eq, Kernel.snd_prod]

theorem stationaryPathLaw_map_tail (π : Measure α) (K : Kernel α α)
    [IsMarkovKernel K] (hπ : Kernel.Invariant K π) (n : ℕ) :
    (finiteMarkovPathLaw π K (n + 1)).map Fin.tail = finiteMarkovPathLaw π K n := by
  rw [finiteMarkovPathLaw, Measure.map_comp _ _ (measurable_markovPathTail n),
    finiteMarkovPathKernel_map_tail, ← Measure.comp_assoc, hπ]
  rfl

theorem finiteMarkovPathLaw_map_tail (μ : Measure α) (K : Kernel α α)
    [IsMarkovKernel K] (n : ℕ) :
    (finiteMarkovPathLaw μ K (n + 1)).map Fin.tail =
      finiteMarkovPathLaw (K ∘ₘ μ) K n := by
  rw [finiteMarkovPathLaw, Measure.map_comp _ _ (measurable_markovPathTail n),
    finiteMarkovPathKernel_map_tail, ← Measure.comp_assoc]
  rfl

theorem finiteMarkovPathKernel_map_first_pair (K : Kernel α α) [IsMarkovKernel K]
    (n : ℕ) (j : Fin n) :
    (finiteMarkovPathKernel K (n + 1)).map (fun path => (path 0, path j.succ)) =
      Kernel.id ×ₖ finiteKernelIterate K (j.val + 1) := by
  rw [finiteMarkovPathKernel, ← Kernel.map_comp_right _ (measurable_markovPathCons n)
    ((measurable_pi_apply 0).prodMk (measurable_pi_apply j.succ))]
  have heq : (fun path : Fin (n + 1) → α => (path 0, path j.succ)) ∘
      (fun z : α × (Fin n → α) => Fin.cons z.1 z.2) =
      Prod.map id (fun path => path j) := by
    funext z
    rcases z with ⟨x, path⟩
    rfl
  rw [heq, ← Kernel.map_prod_map _ _ measurable_id (measurable_pi_apply j),
    Kernel.map_id, Kernel.map_comp, finiteMarkovPathKernel_map_coordinate,
    finiteKernelIterate_comp_right]

/-- The joint law of two stationary coordinates is the initial law paired
with the corresponding iterate of the transition kernel. -/
theorem stationaryPathLaw_map_pair (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    (n : ℕ) (i j : Fin n) (hij : i ≤ j) :
    (finiteMarkovPathLaw π K n).map (fun path => (path i, path j)) =
      π ⊗ₘ finiteKernelIterate K (j.val - i.val) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    revert hij
    refine Fin.cases ?_ (fun i' => ?_) i
    · refine Fin.cases ?_ (fun j' => ?_) j
      · intro _
        have hd : Measurable (Function.diag : α → α × α) :=
          measurable_id.prodMk measurable_id
        have heq : (fun path : Fin (n + 1) → α => (path 0, path 0)) =
            Function.diag ∘ (fun path => path 0) := rfl
        rw [heq, ← Measure.map_map hd
          (measurable_pi_apply 0), stationaryPathLaw_map_coordinate π K hπ,
          Fin.val_zero, Nat.sub_self, finiteKernelIterate, Measure.compProd_id]
      · intro _
        rw [finiteMarkovPathLaw, Measure.map_comp _ _
          ((measurable_pi_apply 0).prodMk (measurable_pi_apply j'.succ)),
          finiteMarkovPathKernel_map_first_pair, ← Measure.compProd_eq_comp_prod]
        simp
    · refine Fin.cases ?_ (fun j' => ?_) j
      · intro hij
        exact (Nat.not_succ_le_zero _ hij).elim
      · intro hij
        have heq : (fun path : Fin (n + 1) → α => (path i'.succ, path j'.succ)) =
            (fun path : Fin n → α => (path i', path j')) ∘ Fin.tail := rfl
        rw [heq, ← Measure.map_map
          ((measurable_pi_apply i').prodMk (measurable_pi_apply j'))
          (measurable_markovPathTail n), stationaryPathLaw_map_tail π K hπ]
        simpa using ih i' j' (Fin.succ_le_succ_iff.mp hij)

/-- Joint coordinates from any initial probability law; no stationarity
or absolute continuity is needed for this measure identity. -/
theorem finiteMarkovPathLaw_map_pair (μ : Measure α) [IsProbabilityMeasure μ]
    (K : Kernel α α) [IsMarkovKernel K]
    (n : ℕ) (i j : Fin n) (hij : i ≤ j) :
    (finiteMarkovPathLaw μ K n).map (fun path => (path i, path j)) =
      (finiteKernelIterate K i.val ∘ₘ μ) ⊗ₘ finiteKernelIterate K (j.val - i.val) := by
  induction n generalizing μ with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    revert hij
    refine Fin.cases ?_ (fun i' => ?_) i
    · refine Fin.cases ?_ (fun j' => ?_) j
      · intro _
        have hd : Measurable (Function.diag : α → α × α) :=
          measurable_id.prodMk measurable_id
        have heq : (fun path : Fin (n + 1) → α => (path 0, path 0)) =
            Function.diag ∘ (fun path => path 0) := rfl
        rw [heq, ← Measure.map_map hd (measurable_pi_apply 0),
          finiteMarkovPathLaw_map_coordinate, Fin.val_zero, Nat.sub_self,
          finiteKernelIterate, Measure.id_comp, Measure.compProd_id]
      · intro _
        rw [finiteMarkovPathLaw, Measure.map_comp _ _
          ((measurable_pi_apply 0).prodMk (measurable_pi_apply j'.succ)),
          finiteMarkovPathKernel_map_first_pair, ← Measure.compProd_eq_comp_prod]
        simp [finiteKernelIterate]
    · refine Fin.cases ?_ (fun j' => ?_) j
      · intro hij
        exact (Nat.not_succ_le_zero _ hij).elim
      · intro hij
        have heq : (fun path : Fin (n + 1) → α => (path i'.succ, path j'.succ)) =
            (fun path : Fin n → α => (path i', path j')) ∘ Fin.tail := rfl
        rw [heq, ← Measure.map_map
          ((measurable_pi_apply i').prodMk (measurable_pi_apply j'))
          (measurable_markovPathTail n), finiteMarkovPathLaw_map_tail,
          ih (K ∘ₘ μ) i' j' (Fin.succ_le_succ_iff.mp hij), Measure.comp_assoc,
          finiteKernelIterate_comp_right]
        simp

end
end UniformRandomMALA.Concrete
