import UniformRandomMALA.Concrete.L2DensityTV
import UniformRandomMALA.Concrete.L2Mixing
import UniformRandomMALA.DiscreteTime.EulerRWMPairChain

/-!
# Total-variation convergence from a variational spectral gap

The initial law is an arbitrary probability measure with square-integrable
Radon--Nikodym density.  Backward iteration of bounded centered indicators
and Cauchy--Schwarz transfer the kernel's squared-norm contraction to the
paper's total-variation bound, including iteration zero.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory DiscreteTime
open scoped ENNReal ProbabilityTheory

noncomputable section

variable {α : Type*} [MeasurableSpace α]

namespace BoundedObservable

/-- A bounded measurable centered indicator for testing event discrepancies. -/
def eventTest (π : Measure α) (s : Set α) (hs : MeasurableSet s) :
    BoundedObservable α where
  toFun := centeredIndicator π s
  measurable_toFun := (measurable_const.indicator hs).sub measurable_const
  bounded := by
    refine ⟨1 + |π.real s|, by positivity, fun x => ?_⟩
    have hi : |s.indicator (fun _ => (1 : ℝ)) x| ≤ 1 := by
      by_cases hx : x ∈ s <;> simp [hx]
    exact (abs_sub _ _).trans (add_le_add hi le_rfl)

/-- Backward observable iteration is dual to the existing finite kernel
iterate applied to the initial probability distribution. -/
theorem integral_iterateAverage_eq_finiteKernelIterate
    (K : Kernel α α) [IsMarkovKernel K]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (f : BoundedObservable α) (n : ℕ) :
    (∫ x, f.iterateAverage K n x ∂μ) =
      ∫ x, f x ∂(finiteKernelIterate K n ∘ₘ μ) := by
  induction n generalizing f with
  | zero => simp [iterateAverage, finiteKernelIterate]
  | succ n ih =>
    calc
      (∫ x, f.iterateAverage K (n + 1) x ∂μ) =
          ∫ x, (f.average K).iterateAverage K n x ∂μ := by
        simp only [iterateAverage, Function.iterate_succ_apply]
      _ = ∫ x, f.average K x ∂(finiteKernelIterate K n ∘ₘ μ) := ih (f.average K)
      _ = ∫ x, f x ∂(K ∘ₘ (finiteKernelIterate K n ∘ₘ μ)) :=
        f.integral_average K (finiteKernelIterate K n ∘ₘ μ)
      _ = ∫ x, f x ∂(finiteKernelIterate K (n + 1) ∘ₘ μ) := by
        rw [Measure.comp_assoc, finiteKernelIterate]

end BoundedObservable

/-- Transfer a proved squared-norm bound on bounded centered observables
to total variation for any initial square-integrable density. -/
theorem setwiseTV_iterate_le_of_sqNorm_bound
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : μ ≪ π)
    (hDensity : MemLp (fun x => (μ.rnDeriv π x).toReal) 2 π)
    (K : Kernel α α) [IsMarkovKernel K] (hπ : Kernel.Invariant K π)
    {a : ℝ} (ha : 0 ≤ a)
    (hcontract : ∀ (f : BoundedObservable α), (∫ x, f x ∂π) = 0 → ∀ n : ℕ,
      (f.iterateAverage K n).sqNorm π ≤ a ^ (2 * n) * f.sqNorm π) (n : ℕ) :
    setwiseTV (finiteKernelIterate K n ∘ₘ μ) π ≤
      centeredDensityL2Norm μ π / 2 * a ^ n := by
  apply setwiseTV_le_of_forall
  intro s hs
  let f := BoundedObservable.eventTest π s hs
  let u := f.iterateAverage K n
  have hf : ∫ x, f x ∂π = 0 := integral_centeredIndicator π hs
  have hu : ∫ x, u x ∂π = 0 := by
    rw [show u = f.iterateAverage K n from rfl,
      f.integral_iterateAverage _ π hπ, hf]
  have hvar : f.sqNorm π ≤ 1 / 4 := integral_centeredIndicator_sq_le_quarter π hs
  have hdecay := hcontract f hf n
  have hbound : u.sqNorm π ≤ a ^ (2 * n) / 4 := by
    exact hdecay.trans (by
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_left hvar (pow_nonneg ha _))
  have hroot : Real.sqrt (u.sqNorm π) ≤ a ^ n / 2 := by
    apply (Real.sqrt_le_left (div_nonneg (pow_nonneg ha _) (by norm_num))).2
    simpa only [div_pow, ← pow_mul, Nat.mul_comm n 2, (by norm_num : (2 : ℝ) ^ 2 = 4)]
      using hbound
  have hpair := abs_integral_sub_le_centeredDensityL2Norm μ π hμ hDensity (u.memLp π 2)
  rw [hu, sub_zero] at hpair
  have hdual : (∫ x, u x ∂μ) =
      (finiteKernelIterate K n ∘ₘ μ).real s - π.real s := by
    rw [show u = f.iterateAverage K n from rfl,
      BoundedObservable.integral_iterateAverage_eq_finiteKernelIterate K μ f n]
    exact integral_centeredIndicator_eq_sub _ π hs
  rw [hdual] at hpair
  calc
    |(finiteKernelIterate K n ∘ₘ μ).real s - π.real s| ≤
        centeredDensityL2Norm μ π * Real.sqrt (u.sqNorm π) := hpair
    _ ≤ centeredDensityL2Norm μ π * (a ^ n / 2) :=
      mul_le_mul_of_nonneg_left hroot (centeredDensityL2Norm_nonneg μ π)
    _ = centeredDensityL2Norm μ π / 2 * a ^ n := by ring

/-- The standard geometric `L²`-to-TV bound for a half-lazy reversible
kernel, derived from its Rayleigh spectral gap and the initial RN density. -/
theorem setwiseTV_iterate_halfLazy_le
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : μ ≪ π)
    (hDensity : MemLp (fun x => (μ.rnDeriv π x).toReal) 2 π)
    (K : Kernel α α) [IsMarkovKernel K] (hrev : Kernel.IsReversible K π)
    {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hgap : ENNReal.ofReal g ≤ rayleighSpectralGap π (halfLazyKernel K)) (n : ℕ) :
    setwiseTV (finiteKernelIterate (halfLazyKernel K) n ∘ₘ μ) π ≤
      centeredDensityL2Norm μ π / 2 * (1 - g) ^ n := by
  exact setwiseTV_iterate_le_of_sqNorm_bound μ π hμ hDensity (halfLazyKernel K)
    (halfLazyKernel_isReversible π K hrev).invariant (sub_nonneg.mpr hg1)
    (fun f hf n => BoundedObservable.sqNorm_iterate_halfLazy_le π K hrev hg0 hg1
      hgap f hf n) n

end

end UniformRandomMALA.Concrete
