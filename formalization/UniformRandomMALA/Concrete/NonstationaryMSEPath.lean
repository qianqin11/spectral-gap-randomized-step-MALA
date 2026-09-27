import UniformRandomMALA.Concrete.L2MixingBase
import UniformRandomMALA.DiscreteTime.EulerRWMEdgeCoupling
import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Finite Markov paths and their empirical means

The path kernel records exactly `n` observations, starting at time zero.
It is constructed from the transition kernel by finite composition and
products, rather than specified through moment or covariance assumptions.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory DiscreteTime
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

variable {α : Type*} [MeasurableSpace α]

theorem measurable_markovPathCons (n : ℕ) :
    Measurable (fun z : α × (Fin n → α) => (Fin.cons z.1 z.2 : Fin (n + 1) → α)) := by
  apply measurable_pi_iff.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using (measurable_fst : Measurable (Prod.fst : α × (Fin n → α) → α))
  · simpa [Function.comp_def] using (measurable_pi_apply j).comp measurable_snd

/-- The joint law of `X₀,...,Xₙ₋₁` conditional on the given initial point.
At each recursive step the first point is retained and one transition is
taken before constructing the remaining coordinates. -/
def finiteMarkovPathKernel (K : Kernel α α) : (n : ℕ) → Kernel α (Fin n → α)
  | 0 => Kernel.deterministic (fun _ => Fin.elim0) measurable_const
  | n + 1 => (Kernel.id ×ₖ (finiteMarkovPathKernel K n ∘ₖ K)).map
      (fun z : α × (Fin n → α) => Fin.cons z.1 z.2)

instance finiteMarkovPathKernel_isMarkovKernel (K : Kernel α α)
    [IsMarkovKernel K] (n : ℕ) : IsMarkovKernel (finiteMarkovPathKernel K n) := by
  induction n with
  | zero => simp only [finiteMarkovPathKernel]; infer_instance
  | succ n ih =>
    simp only [finiteMarkovPathKernel]
    exact Kernel.IsMarkovKernel.map _ (measurable_markovPathCons n)

/-- The actual finite trajectory law from the initial probability measure. -/
def finiteMarkovPathLaw (μ : Measure α) (K : Kernel α α) (n : ℕ) :
    Measure (Fin n → α) := finiteMarkovPathKernel K n ∘ₘ μ

instance finiteMarkovPathLaw_isProbabilityMeasure (μ : Measure α)
    [IsProbabilityMeasure μ] (K : Kernel α α) [IsMarkovKernel K] (n : ℕ) :
    IsProbabilityMeasure (finiteMarkovPathLaw μ K n) := by
  unfold finiteMarkovPathLaw
  infer_instance

/-- The empirical mean includes `X₀` and has no burn-in. -/
def finiteMarkovSampleMean (f : α → ℝ) (n : ℕ) (path : Fin n → α) : ℝ :=
  (∑ i : Fin n, f (path i)) / n

/-- Mean-square error of the empirical mean under the actual finite path law. -/
def finiteMarkovMSE (μ π : Measure α) (K : Kernel α α) (f : α → ℝ) (n : ℕ) : ℝ :=
  ∫ path, (finiteMarkovSampleMean f n path - ∫ x, f x ∂π) ^ 2
    ∂finiteMarkovPathLaw μ K n

theorem finiteMarkovMSE_nonneg (μ π : Measure α) (K : Kernel α α)
    (f : α → ℝ) (n : ℕ) : 0 ≤ finiteMarkovMSE μ π K f n :=
  integral_nonneg fun _ => sq_nonneg _

theorem finiteMarkovPathKernel_succ_apply (K : Kernel α α) [IsMarkovKernel K]
    (n : ℕ) (x : α) :
    finiteMarkovPathKernel K (n + 1) x =
      ((finiteMarkovPathKernel K n ∘ₖ K) x).map (Fin.cons x) := by
  rw [finiteMarkovPathKernel, Kernel.map_apply _ (measurable_markovPathCons n),
    Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod,
    Measure.map_map (measurable_markovPathCons n) measurable_prodMk_left]
  rfl

namespace BoundedObservable

/-- Sum of the observable over every coordinate of a finite path. -/
def pathSum (f : BoundedObservable α) (n : ℕ) : BoundedObservable (Fin n → α) where
  toFun path := ∑ i : Fin n, f (path i)
  measurable_toFun := Finset.measurable_sum _ fun i _ =>
    f.measurable_toFun.comp (measurable_pi_apply i)
  bounded := by
    obtain ⟨C, hC, hf⟩ := f.bounded
    refine ⟨n * C, mul_nonneg (Nat.cast_nonneg _) hC, fun path => ?_⟩
    calc
      |∑ i : Fin n, f (path i)| ≤ ∑ i : Fin n, |f (path i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, C := Finset.sum_le_sum fun i _ => hf (path i)
      _ = n * C := by simp

@[simp] theorem pathSum_cons (f : BoundedObservable α) (n : ℕ)
    (x : α) (path : Fin n → α) :
    f.pathSum (n + 1) (Fin.cons x path) = f x + f.pathSum n path := by
  simp [pathSum, Fin.sum_univ_succ]

theorem average_finiteMarkovPathKernel_succ
    (K : Kernel α α) [IsMarkovKernel K] (n : ℕ)
    (F : BoundedObservable (Fin (n + 1) → α)) (x : α) :
    F.average (finiteMarkovPathKernel K (n + 1)) x =
      ∫ y, ∫ path, F (Fin.cons x path) ∂finiteMarkovPathKernel K n y ∂K x := by
  rw [average_apply, finiteMarkovPathKernel_succ_apply]
  have hc : Measurable (fun path : Fin n → α => (Fin.cons x path : Fin (n + 1) → α)) :=
    (measurable_markovPathCons n).comp measurable_prodMk_left
  rw [integral_map hc.aemeasurable F.measurable_toFun.aestronglyMeasurable]
  exact Kernel.integral_comp ((F.comp (Fin.cons x) hc).integrable _)

end BoundedObservable

end
end UniformRandomMALA.Concrete
