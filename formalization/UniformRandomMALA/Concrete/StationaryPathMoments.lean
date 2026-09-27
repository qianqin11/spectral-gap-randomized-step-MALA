import UniformRandomMALA.Concrete.StationaryPath
import UniformRandomMALA.Concrete.KernelLpBasic
import Mathlib.Probability.Moments.Covariance

/-!
# Stationary finite-path moments for arbitrary square-integrable observables

The identities use the actual joint coordinate laws, so their hypotheses
do not include a covariance or stationarity certificate for a process.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory DiscreteTime
open scoped ENNReal ProbabilityTheory

noncomputable section

variable {α : Type*} [MeasurableSpace α]

theorem stationaryPathLaw_measurePreserving_coordinate (π : Measure α) (K : Kernel α α)
    [IsMarkovKernel K] (hπ : Kernel.Invariant K π) (n : ℕ) (i : Fin n) :
    MeasurePreserving (fun path => path i) (finiteMarkovPathLaw π K n) π :=
  ⟨measurable_pi_apply i, stationaryPathLaw_map_coordinate π K hπ n i⟩

theorem stationaryPathLaw_memLp_coordinate (π : Measure α) (K : Kernel α α)
    [IsMarkovKernel K] (hπ : Kernel.Invariant K π) {p : ℝ≥0∞}
    {f : α → ℝ} (hf : MemLp f p π) (n : ℕ) (i : Fin n) :
    MemLp (fun path => f (path i)) p (finiteMarkovPathLaw π K n) :=
  hf.comp_measurePreserving (stationaryPathLaw_measurePreserving_coordinate π K hπ n i)

theorem stationaryPathLaw_integral_coordinate (π : Measure α) (K : Kernel α α)
    [IsMarkovKernel K] (hπ : Kernel.Invariant K π) {f : α → ℝ}
    (hf : AEStronglyMeasurable f π) (n : ℕ) (i : Fin n) :
    ∫ path, f (path i) ∂finiteMarkovPathLaw π K n = ∫ x, f x ∂π := by
  have hf' : AEStronglyMeasurable f
      ((finiteMarkovPathLaw π K n).map (fun path => path i)) := by
    rw [stationaryPathLaw_map_coordinate π K hπ n i]
    exact hf
  calc
    _ = ∫ x, f x ∂(finiteMarkovPathLaw π K n).map (fun path => path i) :=
      (integral_map (measurable_pi_apply i).aemeasurable hf').symm
    _ = ∫ x, f x ∂π := by rw [stationaryPathLaw_map_coordinate π K hπ n i]

theorem stationary_compProd_integrable_mul (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {f g : α → ℝ} (hf : MemLp f 2 π) (hg : MemLp g 2 π) :
    Integrable (fun z : α × α => f z.1 * g z.2) (π ⊗ₘ K) := by
  have hfst : MeasurePreserving (Prod.fst : α × α → α) (π ⊗ₘ K) π :=
    ⟨measurable_fst, Measure.fst_compProd π K⟩
  have hsnd : MeasurePreserving (Prod.snd : α × α → α) (π ⊗ₘ K) π :=
    ⟨measurable_snd, (Measure.snd_compProd π K).trans hπ⟩
  exact (hf.comp_measurePreserving hfst).integrable_mul (hg.comp_measurePreserving hsnd)

theorem stationaryPathLaw_integral_mul_coordinates
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {f g : α → ℝ} (hf : MemLp f 2 π) (hg : MemLp g 2 π)
    (n : ℕ) (i j : Fin n) (hij : i ≤ j) :
    ∫ path, f (path i) * g (path j) ∂finiteMarkovPathLaw π K n =
      ∫ x, f x * KernelLp.average (finiteKernelIterate K (j.val - i.val)) g x ∂π := by
  have hi := stationary_compProd_integrable_mul π
    (finiteKernelIterate K (j.val - i.val))
    (finiteKernelIterate_invariant K π hπ _) hf hg
  have hmeas : AEStronglyMeasurable (fun z : α × α => f z.1 * g z.2)
      ((finiteMarkovPathLaw π K n).map (fun path => (path i, path j))) := by
    rw [stationaryPathLaw_map_pair π K hπ n i j hij]
    exact hi.1
  calc
    _ = ∫ z, f z.1 * g z.2 ∂(finiteMarkovPathLaw π K n).map
        (fun path => (path i, path j)) :=
      (integral_map ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable
        hmeas).symm
    _ = _ := by
      rw [stationaryPathLaw_map_pair π K hπ n i j hij, Measure.integral_compProd hi]
      simp only [KernelLp.average, integral_const_mul]

theorem stationaryPathLaw_covariance (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {f : α → ℝ} (hf : MemLp f 2 π) (hf0 : ∫ x, f x ∂π = 0)
    (n : ℕ) (i j : Fin n) (hij : i ≤ j) :
    covariance (fun path => f (path i)) (fun path => f (path j))
        (finiteMarkovPathLaw π K n) =
      ∫ x, f x * KernelLp.average (finiteKernelIterate K (j.val - i.val)) f x ∂π := by
  rw [covariance_eq_sub (stationaryPathLaw_memLp_coordinate π K hπ hf n i)
    (stationaryPathLaw_memLp_coordinate π K hπ hf n j),
    stationaryPathLaw_integral_coordinate π K hπ hf.1 n i,
    stationaryPathLaw_integral_coordinate π K hπ hf.1 n j, hf0, mul_zero, sub_zero]
  exact stationaryPathLaw_integral_mul_coordinates π K hπ hf hf n i j hij

end
end UniformRandomMALA.Concrete
