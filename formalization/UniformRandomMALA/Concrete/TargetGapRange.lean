import UniformRandomMALA.Concrete.StickyRegionCut

/-!
# Finite spectral gaps on the concrete target

The target's positive Lebesgue density supplies a measurable set with mass
strictly between zero and one half. Its indicator is a nonconstant `L²` test,
so every reversible Markov kernel on this target has Rayleigh gap at most
two. In particular the gap in the mixing-time denominator is finite.
-/

namespace UniformRandomMALA.Concrete.FirstOrderPotential

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

variable {d : ℕ} (V : FirstOrderPotential d)

/-- Every reversible Markov kernel on the normalized target has Rayleigh
spectral gap at most two. The needed nonconstant test is constructed from
the target density, rather than assumed. -/
theorem rayleighSpectralGap_le_two
    (K : Kernel (State d) (State d)) [IsMarkovKernel K]
    (hrev : Kernel.IsReversible K (V.target : Measure (State d))) :
    rayleighSpectralGap (V.target : Measure (State d)) K ≤ 2 := by
  rcases V.exists_open_target_cut_inside isOpen_univ (Set.mem_univ 0) with
    ⟨A, hAopen, _, _, hApos, hAhalf⟩
  have hA := hAopen.measurableSet
  let q : ℝ := (V.target : Measure (State d)).real A
  have hAtop : (V.target : Measure (State d)) A ≠ ∞ := measure_ne_top _ _
  have hqpos : 0 < q := by
    dsimp [q]
    rw [measureReal_def]
    exact ENNReal.toReal_pos hApos.ne' hAtop
  have hqhalf : q < 1 / 2 := by
    have hhalfTop : (2 : ℝ≥0∞)⁻¹ ≠ ∞ := by simp
    have hto := (ENNReal.toReal_lt_toReal hAtop hhalfTop).2 hAhalf
    simpa [q, measureReal_def] using hto
  have hqone : 0 < 1 - q := by linarith
  have hvar : (V.target : Measure (State d)).real A *
      (1 - (V.target : Measure (State d)).real A) ≠ 0 :=
    mul_ne_zero hqpos.ne' hqone.ne'
  have hgap := rayleighSpectralGap_le_boundaryFlow_div_cutVariance K hrev hA hvar
  apply hgap.trans
  calc
    boundaryFlow (V.target : Measure (State d)) K A /
        ENNReal.ofReal (q * (1 - q)) ≤
        (V.target : Measure (State d)) A /
          ENNReal.ofReal (q * (1 - q)) :=
      ENNReal.div_le_div_right
        (boundaryFlow_le_measure (V.target : Measure (State d)) K hA) _
    _ = ENNReal.ofReal (q / (q * (1 - q))) := by
      rw [← ofReal_measureReal (μ := (V.target : Measure (State d)))
        (s := A) hAtop]
      exact (ENNReal.ofReal_div_of_pos (mul_pos hqpos hqone)).symm
    _ ≤ ENNReal.ofReal 2 := by
      apply ENNReal.ofReal_le_ofReal
      apply (div_le_iff₀ (mul_pos hqpos hqone)).2
      nlinarith [mul_nonneg hqpos.le (by linarith : 0 ≤ 1 - 2 * q)]
    _ = 2 := by norm_num

/-- The concrete target prevents the empty-test-space value `∞` of the
Rayleigh infimum, for every reversible Markov kernel. -/
theorem rayleighSpectralGap_ne_top
    (K : Kernel (State d) (State d)) [IsMarkovKernel K]
    (hrev : Kernel.IsReversible K (V.target : Measure (State d))) :
    rayleighSpectralGap (V.target : Measure (State d)) K ≠ ∞ :=
  ne_of_lt ((V.rayleighSpectralGap_le_two K hrev).trans_lt (by norm_num))

end

end UniformRandomMALA.Concrete.FirstOrderPotential
