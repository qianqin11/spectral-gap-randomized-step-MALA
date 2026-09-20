import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Invariance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Moments.Variance

/-! # Bounded measurable observables and kernel averages -/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- A bounded measurable real function, with no topological assumptions on
the state space. -/
structure BoundedObservable (α : Type*) [MeasurableSpace α] where
  toFun : α → ℝ
  measurable_toFun : Measurable toFun
  bounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |toFun x| ≤ C

instance : CoeFun (BoundedObservable α) (fun _ => α → ℝ) :=
  ⟨BoundedObservable.toFun⟩

namespace BoundedObservable

@[ext] theorem ext {f g : BoundedObservable α} (h : ∀ x, f x = g x) : f = g := by
  cases f
  cases g
  congr
  exact funext h

theorem memLp (f : BoundedObservable α) (μ : Measure α) [IsFiniteMeasure μ]
    (p : ℝ≥0∞) : MemLp f p μ := by
  obtain ⟨C, _, hC⟩ := f.bounded
  exact MemLp.of_bound f.measurable_toFun.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x)

theorem integrable (f : BoundedObservable α) (μ : Measure α) [IsFiniteMeasure μ] :
    Integrable f μ := (memLp_one_iff_integrable).1 (f.memLp μ 1)

def const (c : ℝ) : BoundedObservable α :=
  ⟨fun _ => c, measurable_const, ⟨|c|, abs_nonneg c, fun _ => le_rfl⟩⟩

def add (f g : BoundedObservable α) : BoundedObservable α where
  toFun x := f x + g x
  measurable_toFun := f.measurable_toFun.add g.measurable_toFun
  bounded := by
    obtain ⟨C, hC, hf⟩ := f.bounded
    obtain ⟨D, hD, hg⟩ := g.bounded
    exact ⟨C + D, add_nonneg hC hD, fun x =>
      (abs_add_le _ _).trans (add_le_add (hf x) (hg x))⟩

def smul (c : ℝ) (f : BoundedObservable α) : BoundedObservable α where
  toFun x := c * f x
  measurable_toFun := measurable_const.mul f.measurable_toFun
  bounded := by
    obtain ⟨C, hC, hf⟩ := f.bounded
    refine ⟨|c| * C, mul_nonneg (abs_nonneg c) hC, fun x => ?_⟩
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hf x) (abs_nonneg c)

def mul (f g : BoundedObservable α) : BoundedObservable α where
  toFun x := f x * g x
  measurable_toFun := f.measurable_toFun.mul g.measurable_toFun
  bounded := by
    obtain ⟨C, hC, hf⟩ := f.bounded
    obtain ⟨D, hD, hg⟩ := g.bounded
    refine ⟨C * D, mul_nonneg hC hD, fun x => ?_⟩
    rw [abs_mul]
    exact mul_le_mul (hf x) (hg x) (abs_nonneg _) hC

def comp (f : BoundedObservable β) (g : α → β) (hg : Measurable g) :
    BoundedObservable α where
  toFun x := f (g x)
  measurable_toFun := f.measurable_toFun.comp hg
  bounded := by
    obtain ⟨C, hC, hf⟩ := f.bounded
    exact ⟨C, hC, fun x => hf (g x)⟩

def average (K : Kernel α β) [IsMarkovKernel K] (f : BoundedObservable β) :
    BoundedObservable α where
  toFun x := ∫ y, f y ∂K x
  measurable_toFun := f.measurable_toFun.stronglyMeasurable.integral_kernel.measurable
  bounded := by
    obtain ⟨C, hC, hf⟩ := f.bounded
    refine ⟨C, hC, fun x => ?_⟩
    simpa [Real.norm_eq_abs] using
      (norm_integral_le_of_norm_le_const (μ := K x) (f := fun y => f y) (C := C)
        (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hf y))

@[simp] theorem average_apply (K : Kernel α β) [IsMarkovKernel K]
    (f : BoundedObservable β) (x : α) : f.average K x = ∫ y, f y ∂K x := rfl

theorem integral_average (K : Kernel α β) [IsMarkovKernel K]
    (μ : Measure α) [IsFiniteMeasure μ] (f : BoundedObservable β) :
    ∫ x, f.average K x ∂μ = ∫ y, f y ∂(K ∘ₘ μ) := by
  rw [Measure.comp_eq_comp_const_apply]
  simpa using (Kernel.integral_comp (f.integrable ((K ∘ₖ Kernel.const Unit μ) ()))).symm

theorem integral_average_invariant (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsFiniteMeasure π] (hπ : Kernel.Invariant K π)
    (f : BoundedObservable α) : ∫ x, f.average K x ∂π = ∫ x, f x ∂π := by
  rw [f.integral_average K π, hπ]

theorem sq_average_le (K : Kernel α β) [IsMarkovKernel K]
    (f : BoundedObservable β) (x : α) :
    (f.average K x) ^ 2 ≤ ∫ y, (f y) ^ 2 ∂K x := by
  have hv := variance_nonneg (fun y => f y) (K x)
  rw [variance_eq_sub (f.memLp (K x) 2)] at hv
  exact sub_nonneg.mp hv

theorem integral_sq_average_le (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : Kernel.Invariant K π)
    (f : BoundedObservable α) :
    ∫ x, (f.average K x) ^ 2 ∂π ≤ ∫ x, (f x) ^ 2 ∂π := by
  calc
    (∫ x, (f.average K x) ^ 2 ∂π) ≤ ∫ x, (f.mul f).average K x ∂π :=
      integral_mono ((f.average K).memLp π 2).integrable_sq
        (((f.mul f).average K).integrable π)
        (fun x => by simpa only [average_apply, mul, pow_two] using f.sq_average_le K x)
    _ = ∫ x, (f x) ^ 2 ∂π := by
      rw [integral_average_invariant K π hπ]
      simp only [mul, pow_two]

/-- The real `L²` inner product of bounded observables. -/
def inner (π : Measure α) (f g : BoundedObservable α) : ℝ := ∫ x, f x * g x ∂π

/-- The squared `L²` norm. -/
def sqNorm (π : Measure α) (f : BoundedObservable α) : ℝ := ∫ x, (f x) ^ 2 ∂π

theorem sqNorm_nonneg (π : Measure α) (f : BoundedObservable α) : 0 ≤ f.sqNorm π :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem inner_self (π : Measure α) (f : BoundedObservable α) :
    inner π f f = f.sqNorm π := by simp [inner, sqNorm, pow_two]

theorem inner_comm (π : Measure α) (f g : BoundedObservable α) :
    inner π f g = inner π g f := by simp [inner, mul_comm]

theorem inner_add_right (π : Measure α) [IsFiniteMeasure π]
    (f g h : BoundedObservable α) :
    inner π f (g.add h) = inner π f g + inner π f h := by
  simp only [inner, add, mul_add]
  exact integral_add ((f.mul g).integrable π) ((f.mul h).integrable π)

theorem inner_smul_right (π : Measure α) (c : ℝ) (f g : BoundedObservable α) :
    inner π f (g.smul c) = c * inner π f g := by
  simp only [inner, smul]
  simp_rw [← mul_assoc, mul_comm (f _ ) c, mul_assoc, integral_const_mul]

theorem inner_add_left (π : Measure α) [IsFiniteMeasure π]
    (f g h : BoundedObservable α) :
    inner π (f.add g) h = inner π f h + inner π g h := by
  rw [inner_comm, inner_add_right, inner_comm π h f, inner_comm π h g]

theorem inner_smul_left (π : Measure α) (c : ℝ) (f g : BoundedObservable α) :
    inner π (f.smul c) g = c * inner π f g := by
  rw [inner_comm, inner_smul_right, inner_comm π g f]

theorem sqNorm_add (π : Measure α) [IsFiniteMeasure π]
    (f g : BoundedObservable α) :
    (f.add g).sqNorm π = f.sqNorm π + 2 * inner π f g + g.sqNorm π := by
  rw [← inner_self, inner_add_left, inner_add_right, inner_add_right,
    inner_self, inner_self, inner_comm π g f]
  ring

theorem average_add (K : Kernel α β) [IsMarkovKernel K]
    (f g : BoundedObservable β) (x : α) :
    (f.add g).average K x = f.average K x + g.average K x := by
  exact integral_add (f.integrable (K x)) (g.integrable (K x))

theorem average_smul (K : Kernel α β) [IsMarkovKernel K]
    (c : ℝ) (f : BoundedObservable β) (x : α) :
    (f.smul c).average K x = c * f.average K x := integral_const_mul _ _

theorem average_add_eq (K : Kernel α β) [IsMarkovKernel K]
    (f g : BoundedObservable β) :
    (f.add g).average K = (f.average K).add (g.average K) := by
  ext x
  exact average_add K f g x

theorem average_smul_eq (K : Kernel α β) [IsMarkovKernel K]
    (c : ℝ) (f : BoundedObservable β) :
    (f.smul c).average K = (f.average K).smul c := by
  ext x
  exact average_smul K c f x

theorem integral_edge_product (π : Measure α) [IsFiniteMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (f g : BoundedObservable α) :
    (∫ z, f z.1 * g z.2 ∂(π ⊗ₘ K)) = inner π f (g.average K) := by
  have hi := Measure.integral_compProd
    (((f.comp Prod.fst measurable_fst).mul (g.comp Prod.snd measurable_snd)).integrable
      (π ⊗ₘ K))
  simpa only [comp, mul, inner, average_apply, integral_const_mul] using hi


/-- Repeated backward application of a Markov kernel to an observable. -/
def iterateAverage (K : Kernel α α) [IsMarkovKernel K] (n : ℕ)
    (f : BoundedObservable α) : BoundedObservable α :=
  (fun g => g.average K)^[n] f

theorem integral_iterateAverage (K : Kernel α α) [IsMarkovKernel K]
    (π : Measure α) [IsFiniteMeasure π] (hπ : Kernel.Invariant K π)
    (f : BoundedObservable α) (n : ℕ) :
    ∫ x, f.iterateAverage K n x ∂π = ∫ x, f x ∂π := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ∫ x, ((fun g : BoundedObservable α => g.average K)^[n + 1] f) x ∂π = _
    rw [Function.iterate_succ_apply', integral_average_invariant K π hπ]
    exact ih

end BoundedObservable
end
end UniformRandomMALA.Concrete
