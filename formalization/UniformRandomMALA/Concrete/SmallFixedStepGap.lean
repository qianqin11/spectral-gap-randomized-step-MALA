import UniformRandomMALA.Concrete.SafeComponent
import UniformRandomMALA.Concrete.C1MainTheorem

/-!
# The small-step fixed MALA bound

Proposition G.1 (`prop:small-fixed-step-gap`) follows from global acceptance,
proposal overlap, separated sets, and one-component Cheeger aggregation.
The public endpoint uses the actual fixed-step Metropolis kernel and the
paper's Rayleigh spectral gap, under the standing first-order assumptions.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace UniformRandomMALA.Concrete

noncomputable section

namespace FirstOrderPotential

variable {d : ℕ} (V : FirstOrderPotential d)

theorem smallFixedStep_boundaryFlow_lower
    (hseparated : SeparatedSets (V.target : Measure (State d)) V.m)
    (h : ℝ) (hh : 0 < h) (hsmall : h ≤ 1 / (2 * V.L * (d : ℝ)))
    {S : Set (State d)} (hS : MeasurableSet S)
    (hSpos : 0 < (V.target : Measure (State d)).real S)
    (hShalf : (V.target : Measure (State d)).real S ≤ 1 / 2) :
    (V.target : Measure (State d)).real S *
        min 1 (Real.sqrt (V.m * h * Real.log
          (1 / (V.target : Measure (State d)).real S))) / (2 : ℝ) ^ 13 ≤
      (boundaryFlow (V.target : Measure (State d)) (V.malaKernel h hh) S).toReal := by
  let := V.malaKernel_isMarkovKernel h hh
  apply defectiveConductance_of_separatedSets
    (V.target : Measure (State d)) (V.malaKernel h hh)
    V.m h V.hm hh (V.malaKernel_isReversible h hh)
    hseparated MeasurableSet.univ hS
  · intro x _ y _ hxy
    apply setwiseTV_le_of_forall
    intro B hB
    have hbound := V.abs_malaKernel_apply_toReal_sub_le_seventeen_div_32
      hh hh (by linarith) hsmall x y (by simpa only [dist_eq_norm] using hxy) hB
    simpa only [Measure.real_def] using hbound.trans (by norm_num : (17 : ℝ) / 32 ≤ 3 / 4)
  · exact hSpos
  · exact hShalf
  · rw [Set.compl_univ, measureReal_empty]
    exact div_nonneg (mul_nonneg hSpos.le (le_min (by norm_num)
      (Real.sqrt_nonneg _))) (by positivity)

theorem smallFixedStep_conductance_lower
    (hseparated : SeparatedSets (V.target : Measure (State d)) V.m)
    (h : ℝ) (hh : 0 < h) (hsmall : h ≤ 1 / (2 * V.L * (d : ℝ)))
    {S : Set (State d)} (hS : MeasurableSet S)
    (hSpos : 0 < (V.target : Measure (State d)) S)
    (hShalf : (V.target : Measure (State d)) S ≤ (2 : ℝ≥0∞)⁻¹) :
    safeConductance V.m h * (V.target : Measure (State d)) S ≤
      boundaryFlow (V.target : Measure (State d)) (V.malaKernel h hh) S := by
  let := V.malaKernel_isMarkovKernel h hh
  have hStop : (V.target : Measure (State d)) S ≠ ∞ := measure_ne_top _ _
  have hqpos : 0 < (V.target : Measure (State d)).real S :=
    ENNReal.toReal_pos hSpos.ne' hStop
  have hqhalf : (V.target : Measure (State d)).real S ≤ 1 / 2 := by
    have := ENNReal.toReal_mono (by norm_num : (2 : ℝ≥0∞)⁻¹ ≠ ∞) hShalf
    simpa only [measureReal_def, ENNReal.toReal_inv, ENNReal.toReal_ofNat, one_div] using this
  have hraw := V.smallFixedStep_boundaryFlow_lower hseparated h hh hsmall hS hqpos hqhalf
  have ht : h ≤ (1 / 2) / (V.L * (d : ℝ)) := by
    convert hsmall using 1
    ring
  have hfactor := safe_defective_factor_lower V.m V.L (d : ℝ) (1 / 2) h
    ((V.target : Measure (State d)).real S)
    V.hm V.hmL V.hL V.dimension_real_one (by norm_num) le_rfl hh ht hqpos hqhalf
  have hphi0 : 0 ≤ Real.sqrt (V.m * h * Real.log 2) / (2 : ℝ) ^ 13 := by positivity
  have hreal : (Real.sqrt (V.m * h * Real.log 2) / (2 : ℝ) ^ 13) *
      (V.target : Measure (State d)).real S ≤
      (boundaryFlow (V.target : Measure (State d)) (V.malaKernel h hh) S).toReal := by
    have := mul_le_mul_of_nonneg_left hfactor hqpos.le
    nlinarith
  have hflowtop : boundaryFlow (V.target : Measure (State d)) (V.malaKernel h hh) S ≠ ∞ :=
    flow_ne_top (V.target : Measure (State d)) (V.malaKernel h hh) S Sᶜ hS
  unfold safeConductance
  rw [← ENNReal.ofReal_toReal hflowtop, ← ENNReal.ofReal_toReal hStop,
    ← measureReal_def, ← ENNReal.ofReal_mul hphi0]
  exact ENNReal.ofReal_le_ofReal hreal

lemma smallFixedStep_harmonic_value (m h : ℝ) (hm : 0 < m) (hh : 0 < h) :
    ((2 : ℝ≥0∞) * harmonicCost (fun _ : Fin 1 => 1)
      (fun _ : Fin 1 => safeConductance m h))⁻¹ =
      ENNReal.ofReal (m * h * Real.log 2 / (2 : ℝ) ^ 27) := by
  have hbase : 0 < m * h * Real.log 2 := mul_pos (mul_pos hm hh) log_two_pos
  have hphi : 0 < Real.sqrt (m * h * Real.log 2) / (2 : ℝ) ^ 13 := by positivity
  have htop : ((2 : ℝ≥0∞) * harmonicCost (fun _ : Fin 1 => 1)
      (fun _ : Fin 1 => safeConductance m h))⁻¹ ≠ ∞ := by
    apply ENNReal.inv_ne_top.mpr
    exact mul_ne_zero (by norm_num) (harmonicCost_ne_zero (by norm_num)
      _ _ (fun _ => by norm_num) (fun _ => ENNReal.ofReal_ne_top))
  apply (ENNReal.toReal_eq_toReal_iff' htop ENNReal.ofReal_ne_top).mp
  simp only [harmonicCost, Fin.sum_univ_one, safeConductance,
    ENNReal.toReal_inv, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, ENNReal.toReal_one,
    ENNReal.toReal_ofReal hphi.le,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ m * h * Real.log 2 / (2 : ℝ) ^ 27)]
  have hsqrt := Real.sq_sqrt hbase.le
  field_simp [ne_of_gt hphi]
  nlinarith

theorem smallFixedStep_spectralGap_lower
    (hseparated : SeparatedSets (V.target : Measure (State d)) V.m)
    (h : ℝ) (hh : 0 < h) (hsmall : h ≤ 1 / (2 * V.L * (d : ℝ))) :
    ENNReal.ofReal (V.m * h * Real.log 2 / (2 : ℝ) ^ 27) ≤
      spectralGap (V.target : Measure (State d)) (V.malaKernel h hh) := by
  let := V.malaKernel_isMarkovKernel h hh
  rw [← smallFixedStep_harmonic_value V.m h V.hm hh]
  have hphi : 0 < Real.sqrt (V.m * h * Real.log 2) / (2 : ℝ) ^ 13 := by
    apply div_pos (Real.sqrt_pos.mpr _) (by positivity)
    exact mul_pos (mul_pos V.hm hh) log_two_pos
  apply componentAggregation_le_spectralGap (N := 1) (by norm_num)
    (V.target : Measure (State d)) (V.malaKernel h hh)
    (fun _ => V.malaKernel h hh) (fun _ => V.malaKernel_isReversible h hh)
    (fun _ => 1) (fun _ => safeConductance V.m h)
    (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => (ENNReal.ofReal_pos.mpr hphi).ne') (fun _ => ENNReal.ofReal_ne_top)
  · intro f _
    simp
  · intro S hS hSpos hShalf
    exact ⟨0, V.smallFixedStep_conductance_lower hseparated h hh hsmall hS hSpos hShalf⟩

end FirstOrderPotential

namespace C1Potential

/-- Proposition G.1 (`prop:small-fixed-step-gap`), with a concrete universal
constant. The stronger intermediate estimate also supplies the stated endpoint. -/
theorem smallFixedStep_rayleighSpectralGap_lower {d : ℕ} (V : C1Potential d)
    (h : ℝ) (hh : 0 < h) (hsmall : h ≤ 1 / (2 * V.L * (d : ℝ))) :
    ENNReal.ofReal (V.m * h * Real.log 2 / (2 : ℝ) ^ 27) ≤
      rayleighSpectralGap (V.toFirstOrderPotential.target : Measure (State d))
        (V.toFirstOrderPotential.malaKernel h hh) := by
  exact (V.toFirstOrderPotential.smallFixedStep_spectralGap_lower
    V.separatedSets h hh hsmall).trans (spectralGap_le_rayleighSpectralGap _)

/-- The explicit `h = 1/(2 L d)` endpoint in Proposition G.1
(`prop:small-fixed-step-gap`) and Remark 2.4 (`rem:minimax-fixed-step-ceiling`). -/
theorem dimensionStep_rayleighSpectralGap_lower {d : ℕ} (V : C1Potential d) :
    let W := V.toFirstOrderPotential
    let h := 1 / (2 * V.L * (d : ℝ))
    let hh : 0 < h := one_div_pos.mpr
      (mul_pos (mul_pos (by norm_num) W.hL) W.dimension_real_pos)
    ENNReal.ofReal ((Real.log 2 / (2 : ℝ) ^ 28) / ((V.L / V.m) * (d : ℝ))) ≤
      rayleighSpectralGap (W.target : Measure (State d)) (W.malaKernel h hh) := by
  dsimp only
  convert V.smallFixedStep_rayleighSpectralGap_lower
    (1 / (2 * V.L * (d : ℝ)))
    (one_div_pos.mpr (mul_pos (mul_pos (by norm_num)
      V.toFirstOrderPotential.hL) V.toFirstOrderPotential.dimension_real_pos)) le_rfl using 1
  congr 1
  field_simp

/-- A single strictly positive universal constant gives both statements of
Proposition G.1 (`prop:small-fixed-step-gap`) in every dimension. -/
theorem exists_universal_smallFixedStep_gap_constant :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ) (V : C1Potential d),
      (∀ (h : ℝ) (hh : 0 < h), h ≤ 1 / (2 * V.L * (d : ℝ)) →
        ENNReal.ofReal (c * V.m * h) ≤
          rayleighSpectralGap (V.toFirstOrderPotential.target : Measure (State d))
            (V.toFirstOrderPotential.malaKernel h hh)) ∧
      (let W := V.toFirstOrderPotential
       let h := 1 / (2 * V.L * (d : ℝ))
       let hh : 0 < h := one_div_pos.mpr
         (mul_pos (mul_pos (by norm_num) W.hL) W.dimension_real_pos)
       ENNReal.ofReal (c / ((V.L / V.m) * (d : ℝ))) ≤
         rayleighSpectralGap (W.target : Measure (State d)) (W.malaKernel h hh)) := by
  refine ⟨Real.log 2 / (2 : ℝ) ^ 28, div_pos log_two_pos (by positivity), ?_⟩
  intro d V
  refine ⟨?_, V.dimensionStep_rayleighSpectralGap_lower⟩
  intro h hh hsmall
  apply le_trans (ENNReal.ofReal_le_ofReal _) (V.smallFixedStep_rayleighSpectralGap_lower h hh hsmall)
  have hpos := mul_pos (mul_pos V.hm hh) log_two_pos
  nlinarith

end C1Potential
end
end UniformRandomMALA.Concrete
