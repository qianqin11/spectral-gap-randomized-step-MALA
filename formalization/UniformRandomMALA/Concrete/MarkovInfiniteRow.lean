import UniformRandomMALA.Concrete.MarkovInfiniteMartingale
import UniformRandomMALA.Concrete.MartingaleCLTEstimate
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Normalized Poisson rows and their genuine Lindeberg bound -/

namespace UniformRandomMALA.Concrete
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

def scaledMartingaleRow (a : ℝ) (D : MartingaleDifferenceRow μ) : MartingaleDifferenceRow μ where
  length := D.length
  filtration := D.filtration
  increment k x := a * D.increment k x
  memLp k := (D.memLp k).const_mul a
  measurable k := (D.measurable k).const_mul a
  mean_zero k := by
    have he := condExp_smul (μ := μ) a (D.increment k) (D.filtration k)
    refine he.trans ?_
    filter_upwards [D.mean_zero k] with x hx
    simp [hx]

theorem scaledMartingaleRow_conditionalVariance [IsProbabilityMeasure μ]
    (a : ℝ) (D : MartingaleDifferenceRow μ) (k : ℕ) :
    (scaledMartingaleRow a D).conditionalVariance k =ᵐ[μ]
      fun x => a ^ 2 * D.conditionalVariance k x := by
  have he := condExp_smul (μ := μ) (a ^ 2) (fun x => D.increment k x ^ 2) (D.filtration k)
  have hs := (scaledMartingaleRow a D).conditionalVariance_eq_condExp k
  have hd := D.conditionalVariance_eq_condExp k
  have hfun : (fun x => (scaledMartingaleRow a D).increment k x ^ 2) =
      a ^ 2 • (fun x => D.increment k x ^ 2) := by funext x; simp [scaledMartingaleRow, mul_pow]
  rw [hfun] at hs
  filter_upwards [hs, he, hd] with x hs he hd
  simpa [hd] using hs.trans he

variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]

def normalizedPoissonRow
    (π : Measure α) [IsProbabilityMeasure π] (K : Kernel α α) [IsMarkovKernel K]
    (hπ : Kernel.Invariant K π) (u : Lp ℝ 2 π) (n : ℕ) :
    MartingaleDifferenceRow (infiniteMarkovPathLaw π K) :=
  scaledMartingaleRow (Real.sqrt (n : ℝ))⁻¹ (poissonMartingaleRow π K hπ u n)

@[simp] theorem normalizedPoissonRow_length
    (π : Measure α) [IsProbabilityMeasure π] (K : Kernel α α) [IsMarkovKernel K]
    (hπ : Kernel.Invariant K π) (u : Lp ℝ 2 π) (n : ℕ) :
    (normalizedPoissonRow π K hπ u n).length = n := rfl

@[simp] theorem normalizedPoissonRow_increment
    (π : Measure α) [IsProbabilityMeasure π] (K : Kernel α α) [IsMarkovKernel K]
    (hπ : Kernel.Invariant K π) (u : Lp ℝ 2 π) (n k : ℕ) (path : ℕ → α) :
    (normalizedPoissonRow π K hπ u n).increment k path =
      (Real.sqrt (n : ℝ))⁻¹ * poissonIncrement K u (path k) (path (k + 1)) := rfl

theorem normalizedPoissonRow_conditionalVariance
    (π : Measure α) [IsProbabilityMeasure π] (K : Kernel α α) [IsMarkovKernel K]
    (hπ : Kernel.Invariant K π) (u : Lp ℝ 2 π) (n k : ℕ) :
    (normalizedPoissonRow π K hπ u n).conditionalVariance k =ᵐ[infiniteMarkovPathLaw π K]
      fun path => (n : ℝ)⁻¹ * poissonConditionalVariance K u (path k) := by
  have hs := scaledMartingaleRow_conditionalVariance
    (Real.sqrt (n : ℝ))⁻¹ (poissonMartingaleRow π K hπ u n) k
  filter_upwards [hs, poissonMartingaleRow_conditionalVariance π K hπ u n k] with path hs hp
  simpa only [normalizedPoissonRow, hp, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)] using hs

omit [StandardBorelSpace α] [Nonempty α] in
theorem square_tail_integral_tendsto_zero
    (μ : Measure α) {D : α → ℝ} (hm : Measurable D) (hi : Integrable (fun x => D x ^ 2) μ)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => ∫ x, (if δ * Real.sqrt (n : ℝ) < |D x| then D x ^ 2 else 0) ∂μ)
      atTop (𝓝 0) := by
  have hmF (n : ℕ) : Measurable (fun x =>
      if δ * Real.sqrt (n : ℝ) < |D x| then D x ^ 2 else 0) :=
    (hm.pow_const 2).ite (measurableSet_lt measurable_const hm.abs) measurable_const
  have hlim : Tendsto (fun n : ℕ => δ * Real.sqrt (n : ℝ)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hδ
  have ht := tendsto_integral_of_dominated_convergence
    (F := fun n x => if δ * Real.sqrt (n : ℝ) < |D x| then D x ^ 2 else 0)
    (f := fun _ => (0 : ℝ)) (fun x => D x ^ 2)
    (fun n => (hmF n).aestronglyMeasurable) hi
    (fun n => Eventually.of_forall fun x => by split_ifs <;> simp [Real.norm_eq_abs, sq_nonneg])
    (Eventually.of_forall fun x => ?_)
  · simpa only [integral_zero] using ht
  · apply tendsto_const_nhds.congr'
    filter_upwards [hlim.eventually (eventually_ge_atTop |D x|)] with n hn
    simp [not_lt.mpr hn]

private theorem normalized_square_tail (n : ℕ) (hn : n ≠ 0) (δ z : ℝ) :
    (if δ < |(Real.sqrt (n : ℝ))⁻¹ * z| then ((Real.sqrt (n : ℝ))⁻¹ * z) ^ 2 else 0) =
      (n : ℝ)⁻¹ * (if δ * Real.sqrt (n : ℝ) < |z| then z ^ 2 else 0) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn'
  have ha : |(Real.sqrt (n : ℝ))⁻¹ * z| = |z| / Real.sqrt (n : ℝ) := by
    rw [abs_mul, abs_inv, abs_of_pos hs]
    ring
  simp only [ha, lt_div_iff₀ hs]
  split_ifs <;> simp [mul_pow, inv_pow, Real.sq_sqrt hn'.le]

theorem normalizedPoissonRow_integral_tailTerm
    (π : Measure α) [IsProbabilityMeasure π] (K : Kernel α α) [IsMarkovKernel K]
    (hπ : Kernel.Invariant K π) (u : Lp ℝ 2 π) (n k : ℕ) (hn : n ≠ 0) (δ : ℝ) :
    (∫ path, (normalizedPoissonRow π K hπ u n).tailTerm δ k path ∂infiniteMarkovPathLaw π K) =
      (n : ℝ)⁻¹ * ∫ z : α × α,
        (if δ * Real.sqrt (n : ℝ) < |poissonIncrement K u z.1 z.2| then
          poissonIncrement K u z.1 z.2 ^ 2 else 0) ∂(π ⊗ₘ K) := by
  have heq : (normalizedPoissonRow π K hπ u n).tailTerm δ k =
      fun path => (n : ℝ)⁻¹ *
        (if δ * Real.sqrt (n : ℝ) < |poissonIncrement K u (path k) (path (k + 1))| then
          poissonIncrement K u (path k) (path (k + 1)) ^ 2 else 0) := by
    funext path
    exact normalized_square_tail n hn δ (poissonIncrement K u (path k) (path (k + 1)))
  rw [heq]
  rw [integral_const_mul]
  congr 1
  have hm := measurable_poissonIncrement K (Lp.stronglyMeasurable u).measurable
  have hF : Measurable (fun z : α × α =>
      if δ * Real.sqrt (n : ℝ) < |poissonIncrement K u z.1 z.2| then
        poissonIncrement K u z.1 z.2 ^ 2 else 0) :=
    (hm.pow_const 2).ite (measurableSet_lt measurable_const hm.abs) measurable_const
  have hmapp := integral_map (μ := infiniteMarkovPathLaw π K)
    (φ := fun path : ℕ → α => (path k, path (k + 1)))
    ((measurable_pi_apply k).prodMk (measurable_pi_apply (k + 1))).aemeasurable
    (f := fun z : α × α => if δ * Real.sqrt (n : ℝ) < |poissonIncrement K u z.1 z.2| then
      poissonIncrement K u z.1 z.2 ^ 2 else 0) hF.aestronglyMeasurable
  rw [stationaryInfinitePathLaw_map_successive π K hπ k] at hmapp
  exact hmapp.symm

/-- The expected Lindeberg tail vanishes by stationarity and dominated
convergence of the actual squared Poisson increment. -/
theorem normalizedPoissonRow_expectedTailSum_tendsto_zero
    (π : Measure α) [IsProbabilityMeasure π] (K : Kernel α α) [IsMarkovKernel K]
    (hπ : Kernel.Invariant K π) (u : Lp ℝ 2 π) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => (normalizedPoissonRow π K hπ u n).expectedTailSum δ n) atTop (𝓝 0) := by
  have ht := square_tail_integral_tendsto_zero (π ⊗ₘ K)
    (measurable_poissonIncrement K (Lp.stronglyMeasurable u).measurable)
    (poissonIncrement_memLp π K hπ (Lp.memLp u)).integrable_sq hδ
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : n ≠ 0 := by omega
  unfold MartingaleDifferenceRow.expectedTailSum
  simp_rw [normalizedPoissonRow_integral_tailTerm π K hπ u n _ hn0 δ]
  simp [Nat.cast_ne_zero.mpr hn0]

end
end UniformRandomMALA.Concrete
