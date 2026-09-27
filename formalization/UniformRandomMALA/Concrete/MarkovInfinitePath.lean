import UniformRandomMALA.Concrete.StationaryPathMoments
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-! # The actual infinite trajectory law of a Markov kernel

The Ionescu–Tulcea construction supplies one probability space carrying all
coordinates. Its transition kernel reads the final coordinate of the finite
history, so the construction describes the same homogeneous chain as the
finite path laws.
-/

namespace UniformRandomMALA.Concrete
open MeasureTheory ProbabilityTheory Preorder Set
open scoped ENNReal ProbabilityTheory
noncomputable section
variable {α : Type*} [MeasurableSpace α]

def markovHistoryKernel (K : Kernel α α) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → α) α :=
  K.comap (fun path => path ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)

instance markovHistoryKernel_isMarkovKernel (K : Kernel α α) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (markovHistoryKernel K n) := by
  unfold markovHistoryKernel
  infer_instance

def infiniteMarkovPathLaw (μ : Measure α) (K : Kernel α α) [IsMarkovKernel K] :
    Measure (ℕ → α) := Kernel.trajMeasure μ (markovHistoryKernel K)

instance infiniteMarkovPathLaw_isProbabilityMeasure (μ : Measure α) [IsProbabilityMeasure μ]
    (K : Kernel α α) [IsMarkovKernel K] : IsProbabilityMeasure (infiniteMarkovPathLaw μ K) := by
  unfold infiniteMarkovPathLaw
  infer_instance

def markovPathFiltration : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (ℕ → α)) :=
  Filtration.piLE

theorem measurable_coordinate_markovPathFiltration (n i : ℕ) (hi : i ≤ n) :
    Measurable[markovPathFiltration (α := α) n] (fun path : ℕ → α => path i) := by
  have hm : Measurable[markovPathFiltration (α := α) n] (frestrictLe (π := fun _ => α) n) := by
    rw [markovPathFiltration, Filtration.piLE_eq_comap_frestrictLe]
    exact measurable_iff_comap_le.mpr le_rfl
  exact (measurable_pi_apply ⟨i, Finset.mem_Iic.mpr hi⟩).comp hm

theorem infiniteMarkovPathLaw_map_history_zero
    (μ : Measure α) (K : Kernel α α) [IsMarkovKernel K] :
    (infiniteMarkovPathLaw μ K).map (frestrictLe (π := fun _ => α) 0) =
      μ.map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => α)).symm := by
  rw [infiniteMarkovPathLaw, Kernel.trajMeasure, Measure.map_comp _ _ (by fun_prop),
    Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]

theorem infiniteMarkovPathLaw_map_zero
    (μ : Measure α) (K : Kernel α α) [IsMarkovKernel K] :
    (infiniteMarkovPathLaw μ K).map (fun path => path 0) = μ := by
  have heq : (fun path : ℕ → α => path 0) =
      (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => α)) ∘ frestrictLe 0 := by
    funext path
    rfl
  rw [heq, ← Measure.map_map (by fun_prop) (by fun_prop),
    infiniteMarkovPathLaw_map_history_zero, Measure.map_map (by fun_prop) (by fun_prop)]
  change μ.map id = μ
  exact Measure.map_id

theorem infiniteMarkovPathLaw_history_next
    (μ : Measure α) [IsProbabilityMeasure μ] (K : Kernel α α) [IsMarkovKernel K] (n : ℕ) :
    (infiniteMarkovPathLaw μ K).map (fun path => (frestrictLe n path, path (n + 1))) =
      (infiniteMarkovPathLaw μ K).map (frestrictLe n) ⊗ₘ markovHistoryKernel K n := by
  exact Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure.symm

theorem map_fst_compProd_comap {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure β) [IsProbabilityMeasure μ] (K : Kernel α γ) [IsMarkovKernel K]
    (f : β → α) (hf : Measurable f) :
    (μ ⊗ₘ K.comap f hf).map (Prod.map f id) = μ.map f ⊗ₘ K := by
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.map_apply (hf.prodMap measurable_id) (hs.prod ht)]
  change (μ ⊗ₘ K.comap f hf) ((f ⁻¹' s) ×ˢ t) = _
  rw [Measure.compProd_apply_prod (hf hs) ht, Measure.compProd_apply_prod hs ht,
    setLIntegral_map hs (K.measurable_coe ht) hf]
  rfl

theorem infiniteMarkovPathLaw_map_successive
    (μ : Measure α) [IsProbabilityMeasure μ] (K : Kernel α α) [IsMarkovKernel K] (n : ℕ) :
    (infiniteMarkovPathLaw μ K).map (fun path => (path n, path (n + 1))) =
      (infiniteMarkovPathLaw μ K).map (fun path => path n) ⊗ₘ K := by
  let f : ((i : Finset.Iic n) → α) → α := fun path => path ⟨n, Finset.mem_Iic.mpr le_rfl⟩
  have hf : Measurable f := measurable_pi_apply _
  let : IsProbabilityMeasure ((infiniteMarkovPathLaw μ K).map (frestrictLe n)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have hmap := congrArg (fun ν => ν.map (Prod.map f id))
    (infiniteMarkovPathLaw_history_next μ K n)
  rw [Measure.map_map (hf.prodMap measurable_id) (by fun_prop)] at hmap
  change (infiniteMarkovPathLaw μ K).map (fun path => (path n, path (n + 1))) =
    (((infiniteMarkovPathLaw μ K).map (frestrictLe n)) ⊗ₘ K.comap f hf).map (Prod.map f id) at hmap
  rw [map_fst_compProd_comap _ K f hf, Measure.map_map hf (by fun_prop)] at hmap
  exact hmap

theorem infiniteMarkovPathLaw_map_coordinate
    (μ : Measure α) [IsProbabilityMeasure μ] (K : Kernel α α) [IsMarkovKernel K] (n : ℕ) :
    (infiniteMarkovPathLaw μ K).map (fun path => path n) =
      DiscreteTime.finiteKernelIterate K n ∘ₘ μ := by
  induction n with
  | zero => simpa [DiscreteTime.finiteKernelIterate] using infiniteMarkovPathLaw_map_zero μ K
  | succ n ih =>
    have h := congrArg (fun ν : Measure (α × α) => ν.snd)
      (infiniteMarkovPathLaw_map_successive μ K n)
    rw [Measure.snd, Measure.map_map measurable_snd (by fun_prop), Measure.snd_compProd, ih] at h
    simpa only [Function.comp_def, DiscreteTime.finiteKernelIterate, Measure.comp_assoc] using h

theorem stationaryInfinitePathLaw_map_coordinate
    (π : Measure α) [IsProbabilityMeasure π] (K : Kernel α α) [IsMarkovKernel K]
    (hπ : Kernel.Invariant K π) (n : ℕ) :
    (infiniteMarkovPathLaw π K).map (fun path => path n) = π := by
  rw [infiniteMarkovPathLaw_map_coordinate]
  exact DiscreteTime.finiteKernelIterate_invariant K π hπ n

theorem stationaryInfinitePathLaw_map_successive
    (π : Measure α) [IsProbabilityMeasure π] (K : Kernel α α) [IsMarkovKernel K]
    (hπ : Kernel.Invariant K π) (n : ℕ) :
    (infiniteMarkovPathLaw π K).map (fun path => (path n, path (n + 1))) = π ⊗ₘ K := by
  rw [infiniteMarkovPathLaw_map_successive, stationaryInfinitePathLaw_map_coordinate π K hπ]

end
end UniformRandomMALA.Concrete
