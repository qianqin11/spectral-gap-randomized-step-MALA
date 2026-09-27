import UniformRandomMALA.Concrete.TargetGapRange

/-!
# The nonatomic target bounds the right gap by one

The variance comparison in Corollary 2.7 (`cor:variance-separation`) uses
arbitrarily small positive-mass indicator tests. The Boltzmann target has
positive density and no atoms, so those tests are constructed internally.
-/

namespace UniformRandomMALA.Concrete.FirstOrderPotential

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

variable {d : ℕ} (V : FirstOrderPotential d)

theorem exists_open_target_cut_mass_lt (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ A : Set (State d), IsOpen A ∧
      0 < (V.target : Measure (State d)) A ∧ (V.target : Measure (State d)) A < ε := by
  have hsmall : (V.target : Measure (State d)) ({0} : Set (State d)) < ε := by
    rw [V.target_singleton_zero]
    exact hε
  obtain ⟨A, hsub, hA, hAε⟩ := ({0} : Set (State d)).exists_isOpen_lt_of_lt ε hsmall
  exact ⟨A, hA, V.target_isOpen_measure_pos hA ⟨0, hsub (Set.mem_singleton 0)⟩, hAε⟩

/-- Every reversible Markov kernel on this nonatomic target has right
Rayleigh gap at most one, including the fixed-step and randomized kernels. -/
theorem rayleighSpectralGap_le_one
    (K : Kernel (State d) (State d)) [IsMarkovKernel K]
    (hrev : Kernel.IsReversible K (V.target : Measure (State d))) :
    rayleighSpectralGap (V.target : Measure (State d)) K ≤ 1 := by
  have htop := V.rayleighSpectralGap_ne_top K hrev
  apply (ENNReal.toReal_le_toReal htop (by norm_num)).mp
  simp only [ENNReal.toReal_one]
  let G := (rayleighSpectralGap (V.target : Measure (State d)) K).toReal
  change G ≤ 1
  by_contra hnot
  have hG : 1 < G := lt_of_not_ge hnot
  have hGpos : 0 < G := lt_trans zero_lt_one hG
  let ε : ℝ := 1 - 1 / G
  have hεpos : 0 < ε := sub_pos.mpr ((div_lt_one hGpos).mpr hG)
  obtain ⟨A, hAopen, hApos, hAε⟩ :=
    V.exists_open_target_cut_mass_lt (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hεpos)
  have hA := hAopen.measurableSet
  have hAtop : (V.target : Measure (State d)) A ≠ ∞ := measure_ne_top _ _
  let q := (V.target : Measure (State d)).real A
  have hqpos : 0 < q := ENNReal.toReal_pos hApos.ne' hAtop
  have hqε : q < ε := by
    have h := (ENNReal.toReal_lt_toReal hAtop ENNReal.ofReal_ne_top).mpr hAε
    simpa only [q, measureReal_def, ENNReal.toReal_ofReal hεpos.le] using h
  have hqone : 0 < 1 - q := by
    have h := one_div_pos.mpr hGpos
    dsimp [ε] at hqε
    linarith
  have hgap := rayleighSpectralGap_le_boundaryFlow_div_cutVariance K hrev hA
    (mul_ne_zero hqpos.ne' hqone.ne')
  have hbound : rayleighSpectralGap (V.target : Measure (State d)) K ≤
      ENNReal.ofReal (q / (q * (1 - q))) := by
    apply hgap.trans
    calc
      _ ≤ (V.target : Measure (State d)) A / ENNReal.ofReal (q * (1 - q)) :=
        ENNReal.div_le_div_right
          (boundaryFlow_le_measure (V.target : Measure (State d)) K hA) _
      _ = _ := by
        rw [← ofReal_measureReal (μ := (V.target : Measure (State d))) (s := A) hAtop]
        exact (ENNReal.ofReal_div_of_pos (mul_pos hqpos hqone)).symm
  have hboundReal : G ≤ q / (q * (1 - q)) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    simpa only [ENNReal.toReal_ofReal (div_nonneg hqpos.le (mul_pos hqpos hqone).le)] using h
  have hcancel : q / (q * (1 - q)) = 1 / (1 - q) := by field_simp
  rw [hcancel] at hboundReal
  have hle : G * (1 - q) ≤ 1 := (le_div_iff₀ hqone).mp hboundReal
  have hgt : 1 / G < 1 - q := by dsimp [ε] at hqε; linarith
  have hgt' := (div_lt_iff₀ hGpos).mp hgt
  nlinarith

end
end UniformRandomMALA.Concrete.FirstOrderPotential
