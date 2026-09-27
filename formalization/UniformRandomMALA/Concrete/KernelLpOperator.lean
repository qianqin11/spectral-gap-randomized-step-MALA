import UniformRandomMALA.Concrete.KernelLpBasic

/-! # The invariant Markov operator as a continuous linear map on `Lᵖ` -/

namespace UniformRandomMALA.Concrete.KernelLp

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

variable {α : Type*} [MeasurableSpace α]

variable (K : Kernel α α) [IsMarkovKernel K]
  (π : Measure α) [IsProbabilityMeasure π] (hπ : Kernel.Invariant K π)
  (p : ℝ≥0∞) [Fact (1 ≤ p)] (hpt : p ≠ ∞)

/-- Markov integration on equivalence classes of almost-everywhere equal
functions. The range is in `Lᵖ` by the proved Jensen contraction. -/
def toLp (f : Lp ℝ p π) : Lp ℝ p π :=
  (average_memLp_of_ne_top K π hπ (Fact.out : 1 ≤ p) hpt (Lp.memLp f)).toLp
    (average K f)

theorem coeFn_toLp (f : Lp ℝ p π) :
    toLp K π hπ p hpt f =ᵐ[π] average K f := MemLp.coeFn_toLp _

theorem toLp_add (f g : Lp ℝ p π) :
    toLp K π hπ p hpt (f + g) = toLp K π hπ p hpt f + toLp K π hπ p hpt g := by
  apply Lp.ext
  filter_upwards [coeFn_toLp K π hπ p hpt (f + g), coeFn_toLp K π hπ p hpt f,
    coeFn_toLp K π hπ p hpt g,
    Lp.coeFn_add (toLp K π hπ p hpt f) (toLp K π hπ p hpt g),
    average_congr_ae K π hπ (Lp.coeFn_add f g),
    average_add_ae K π hπ ((Lp.memLp f).integrable (Fact.out : 1 ≤ p))
      ((Lp.memLp g).integrable (Fact.out : 1 ≤ p))] with x hsum hf hg hadd hcong havg
  simp only [Pi.add_apply] at hadd hcong havg
  rw [hsum, hcong, havg, hadd, hf, hg]

theorem toLp_smul (c : ℝ) (f : Lp ℝ p π) :
    toLp K π hπ p hpt (c • f) = c • toLp K π hπ p hpt f := by
  apply Lp.ext
  filter_upwards [coeFn_toLp K π hπ p hpt (c • f), coeFn_toLp K π hπ p hpt f,
    Lp.coeFn_smul c (toLp K π hπ p hpt f),
    average_congr_ae K π hπ (Lp.coeFn_smul c f)] with x hsmul hf hout hcong
  rw [hsmul, hcong, average_smul, hout]
  simp only [Pi.smul_apply, hf]

theorem norm_toLp_le (f : Lp ℝ p π) : ‖toLp K π hπ p hpt f‖ ≤ ‖f‖ := by
  rw [toLp, Lp.norm_toLp, Lp.norm_def,
    toReal_eLpNorm (average_memLp_of_ne_top K π hπ (Fact.out : 1 ≤ p) hpt
      (Lp.memLp f)).1, toReal_eLpNorm (Lp.memLp f).1]
  exact lpNorm_average_le_of_ne_top K π hπ (Fact.out : 1 ≤ p) hpt (Lp.memLp f)

/-- The Markov operator is a contraction on every finite `Lᵖ`, `p ≥ 1`. -/
def operator : Lp ℝ p π →L[ℝ] Lp ℝ p π :=
  LinearMap.mkContinuous
    { toFun := toLp K π hπ p hpt
      map_add' := toLp_add K π hπ p hpt
      map_smul' := toLp_smul K π hπ p hpt }
    1 (fun f => by
      change ‖toLp K π hπ p hpt f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using norm_toLp_le K π hπ p hpt f)

@[simp] theorem operator_apply (f : Lp ℝ p π) :
    operator K π hπ p hpt f = toLp K π hπ p hpt f := rfl

theorem operator_coeFn (f : Lp ℝ p π) :
    operator K π hπ p hpt f =ᵐ[π] average K f := coeFn_toLp K π hπ p hpt f

theorem norm_operator_le : ‖operator K π hπ p hpt‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [operator_apply, one_mul] using norm_toLp_le K π hπ p hpt f

theorem integral_operator (f : Lp ℝ p π) :
    ∫ x, operator K π hπ p hpt f x ∂π = ∫ x, f x ∂π := by
  rw [integral_congr_ae (operator_coeFn K π hπ p hpt f)]
  exact integral_average_invariant K π hπ ((Lp.memLp f).integrable (Fact.out : 1 ≤ p))

end
end UniformRandomMALA.Concrete.KernelLp
