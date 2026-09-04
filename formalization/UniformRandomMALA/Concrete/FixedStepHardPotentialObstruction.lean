import UniformRandomMALA.Concrete.HardPotentialLocalObstruction
import UniformRandomMALA.Concrete.HardPotentialStickyObstruction
import UniformRandomMALA.Concrete.FixedStepObstructionOptimization

/-!
# Generic fixed-step obstruction for the explicit smooth hard potential

This file packages the independent first-coordinate and sticky-region test
functions for the same concrete `C∞` potential.  Scalar compression of the
two exponential terms and the final minimax optimization are kept separate.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

/-- Kernel-checked generic obstruction with one universal Chernoff
contraction factor.  This is the exact two-branch result before rewriting
the sticky branch in `C exp(-c n min((L-m)h,1))` form. -/
theorem exists_universal_fixedStepHardPotential_raw_obstruction :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ (n : ℕ) (hn : 1 ≤ n) {m L h : ℝ}
        (hm : 0 < m) (hmL : m < L) (hh : 0 < h),
        rayleighSpectralGap
            ((fixedStepHardFirstOrderPotential (d := n + 1) (by omega)
              hm hmL hh).target : Measure (State (n + 1)))
            ((fixedStepHardFirstOrderPotential (d := n + 1) (by omega)
              hm hmL hh).malaKernel h hh) ≤
          min
            (ENNReal.ofReal (m * h + (m * h) ^ 2 / 2))
            (ENNReal.ofReal (4 *
              (ρ ^ n + Real.exp
                (-(((L - m) / 2) * h * hardAcceptanceDrift * n))))) := by
  obtain ⟨ρ, hρ0, hρ1, hsticky⟩ :=
    exists_universal_fixedStepHard_sticky_rayleighSpectralGap_upper
  refine ⟨ρ, hρ0, hρ1, ?_⟩
  intro n hn m L h hm hmL hh
  apply le_min
  · exact fixedStepHardMALA_rayleighSpectralGap_le_local_succ
      n hn hm hmL hh
  · exact hsticky n hn hm hmL hh

/-- Proposition-level generic obstruction in the manuscript's compressed
form.  The constants `8` and the existential universal rate `c` are
independent of the dimension, curvature constants, and step size. -/
theorem exists_universal_fixedStepHardPotential_obstruction :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ) (hn : 1 ≤ n) {m L h : ℝ}
        (hm : 0 < m) (hmL : m < L) (hh : 0 < h),
        rayleighSpectralGap
            ((fixedStepHardFirstOrderPotential (d := n + 1) (by omega)
              hm hmL hh).target : Measure (State (n + 1)))
            ((fixedStepHardFirstOrderPotential (d := n + 1) (by omega)
              hm hmL hh).malaKernel h hh) ≤
          ENNReal.ofReal (8 * min
            (m * h + (m * h) ^ 2 / 2)
            (Real.exp (-c * n * min ((L - m) * h) 1))) := by
  obtain ⟨ρ, hρ0, hρ1, hraw⟩ :=
    exists_universal_fixedStepHardPotential_raw_obstruction
  have ha : 0 < hardAcceptanceDrift / 2 := by
    exact div_pos hardAcceptanceDrift_pos (by norm_num)
  obtain ⟨c, hc, hcompress⟩ :=
    exists_ennreal_exponential_compression_rate hρ0 hρ1 ha
  refine ⟨c, hc, ?_⟩
  intro n hn m L h hm hmL hh
  have hgap := hraw n hn hm hmL hh
  have hlocal := hgap.trans (min_le_left _ _)
  have hsticky := hgap.trans (min_le_right _ _)
  have hmh0 : 0 ≤ m * h := by positivity
  have hlocal0 : 0 ≤ m * h + (m * h) ^ 2 / 2 := by
    nlinarith [sq_nonneg (m * h)]
  have hs : 0 ≤ (L - m) * h := by positivity
  have hcompressed := hcompress 4 n ((L - m) * h)
    (by norm_num) hn hs
  have hsticky' :
      rayleighSpectralGap
          ((fixedStepHardFirstOrderPotential (d := n + 1) (by omega)
            hm hmL hh).target : Measure (State (n + 1)))
          ((fixedStepHardFirstOrderPotential (d := n + 1) (by omega)
            hm hmL hh).malaKernel h hh) ≤
        ENNReal.ofReal
          (8 * Real.exp (-c * n * min ((L - m) * h) 1)) := by
    apply hsticky.trans
    have hexponent :
        -((L - m) / 2 * h * hardAcceptanceDrift * (n : ℝ)) =
          -(hardAcceptanceDrift / 2) * (n : ℝ) * ((L - m) * h) := by
      ring
    simpa only [hexponent, show (2 : ℝ) * 4 = 8 by norm_num] using
      hcompressed
  rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 8),
    ENNReal.ofReal_min]
  apply le_min
  · apply hlocal.trans
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  · exact hsticky'

/-- Dimension-indexed form of the generic obstruction, matching the paper's
statement for every `d ≥ 2`. -/
theorem exists_universal_fixedStepHardPotential_obstruction_allDimensions :
    ∃ c : ℝ, 0 < c ∧
      ∀ {d : ℕ} (hd : 2 ≤ d) {m L h : ℝ}
        (hm : 0 < m) (hmL : m < L) (hh : 0 < h),
        rayleighSpectralGap
            ((fixedStepHardFirstOrderPotential hd hm hmL hh).target :
              Measure (State d))
            ((fixedStepHardFirstOrderPotential hd hm hmL hh).malaKernel h hh) ≤
          ENNReal.ofReal (8 * min
            (m * h + (m * h) ^ 2 / 2)
            (Real.exp (-c * (d - 1) * min ((L - m) * h) 1))) := by
  obtain ⟨c, hc, hbound⟩ :=
    exists_universal_fixedStepHardPotential_obstruction
  refine ⟨c, hc, ?_⟩
  intro d hd m L h hm hmL hh
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  simpa using hbound n (by omega) hm hmL hh

end

end UniformRandomMALA.Concrete
