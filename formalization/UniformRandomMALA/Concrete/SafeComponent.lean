import UniformRandomMALA.Concrete.MALADefectiveConductance
import UniformRandomMALA.Concrete.ComponentAggregationFinal
import UniformRandomMALA.Concrete.Ladder

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace UniformRandomMALA.Concrete

noncomputable section

/-!
# The globally safe component

This file constructs the one-component spectral-gap estimate directly for
the concrete uniform-random MALA kernel.  Apart from Bakry--Ledoux, every
ingredient is an elementary real inequality or a previously checked kernel,
conductance, and aggregation theorem.
-/

/-- On a globally safe step, the uniform `log 2` conductance coefficient is
below the defective-conductance factor for every cut of mass at most one
half. -/
lemma safe_defective_factor_lower
    (m L d b t q : ℝ)
    (hm : 0 < m) (hmL : m ≤ L) (hL : 0 < L)
    (hd : 1 ≤ d) (hb0 : 0 < b) (hbhalf : b ≤ 1 / 2)
    (ht0 : 0 < t) (ht : t ≤ b / (L * d))
    (hq0 : 0 < q) (hqhalf : q ≤ 1 / 2) :
    Real.sqrt (m * t * Real.log 2) ≤
      min 1 (Real.sqrt (m * t * Real.log (1 / q))) := by
  have hLd : 0 < L * d := mul_pos hL (lt_of_lt_of_le zero_lt_one hd)
  have htLd : t * (L * d) ≤ b := (le_div_iff₀ hLd).mp ht
  have hmt0 : 0 ≤ m * t := (mul_pos hm ht0).le
  have hmtd : m * t * d ≤ b := by
    have hmLt : m * t ≤ L * t := mul_le_mul_of_nonneg_right hmL ht0.le
    have := mul_le_mul_of_nonneg_right hmLt (le_of_lt (lt_of_lt_of_le zero_lt_one hd))
    nlinarith
  have hmt : m * t ≤ b := by
    have := mul_le_mul_of_nonneg_left hd hmt0
    nlinarith
  have hlog2le : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num) using 1 <;>
      norm_num
  have hbasele : m * t * Real.log 2 ≤ 1 := by
    have hlog20 : 0 ≤ Real.log 2 := log_two_pos.le
    have h₁ := mul_le_mul_of_nonneg_right hmt hlog20
    have h₂ := mul_le_mul_of_nonneg_left hlog2le hb0.le
    nlinarith
  have hsqrtOne : Real.sqrt (m * t * Real.log 2) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hbasele
  have htwoq : 2 ≤ 1 / q := by
    apply (le_div_iff₀ hq0).2
    linarith
  have hlog : Real.log 2 ≤ Real.log (1 / q) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by norm_num) (one_div_pos.mpr hq0) htwoq
  have hinside : m * t * Real.log 2 ≤ m * t * Real.log (1 / q) :=
    mul_le_mul_of_nonneg_left hlog hmt0
  exact le_min hsqrtOne (Real.sqrt_le_sqrt hinside)

namespace FirstOrderPotential

variable {d : ℕ} (V : FirstOrderPotential d)

def safeStep (H b : ℝ) : ℝ := min H (b / (V.L * (d : ℝ)))

lemma safeStep_pos (H b : ℝ) (hH : 0 < H) (hb : 0 < b) :
    0 < V.safeStep H b := by
  exact lt_min hH (div_pos hb (mul_pos V.hL V.dimension_real_pos))

lemma safeStep_le_H (H b : ℝ) : V.safeStep H b ≤ H := min_le_left _ _

lemma safeStep_le_scale (H b : ℝ) :
    V.safeStep H b ≤ b / (V.L * (d : ℝ)) := min_le_right _ _

theorem safe_boundaryFlow_lower_of_bakryLedoux
    (H b : ℝ) (hH : 0 < H) (hb : 0 < b) (hbhalf : b ≤ 1 / 2)
    (hBL : BakryLedouxEnlargement
      (V.target : Measure (State d)) V.m
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure))
    {S : Set (State d)} (hS : MeasurableSet S)
    (hSpos : 0 < (V.target : Measure (State d)) S)
    (hShalf : (V.target : Measure (State d)) S ≤ (2 : ℝ≥0∞)⁻¹) :
    ENNReal.ofReal
          (Real.sqrt (V.m * V.safeStep H b * Real.log 2) / (2 : ℝ) ^ 13) *
        (V.target : Measure (State d)) S ≤
      boundaryFlow (V.target : Measure (State d))
        (V.dyadicMALA (V.safeStep H b) (V.safeStep_pos H b hH hb)) S := by
  let t : ℝ := V.safeStep H b
  let K : Kernel (State d) (State d) := V.dyadicMALA t (V.safeStep_pos H b hH hb)
  letI : IsMarkovKernel K := V.dyadicMALA_isMarkovKernel t (V.safeStep_pos H b hH hb)
  have ht : 0 < t := V.safeStep_pos H b hH hb
  have htSafe : t ≤ 1 / (2 * V.L * (d : ℝ)) := by
    have hden : 0 < V.L * (d : ℝ) := mul_pos V.hL V.dimension_real_pos
    have hbdiv : b / (V.L * (d : ℝ)) ≤ (1 / 2) / (V.L * (d : ℝ)) :=
      (div_le_div_iff_of_pos_right hden).2 hbhalf
    refine (V.safeStep_le_scale H b).trans ?_
    calc
      b / (V.L * (d : ℝ)) ≤ (1 / 2) / (V.L * (d : ℝ)) := hbdiv
      _ = 1 / (2 * V.L * (d : ℝ)) := by
        field_simp [ne_of_gt V.hL, ne_of_gt V.dimension_real_pos]

  have hStop : (V.target : Measure (State d)) S ≠ ∞ := measure_ne_top _ _
  have hqpos : 0 < (V.target : Measure (State d)).real S := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hSpos.ne' hStop
  have hqhalf : (V.target : Measure (State d)).real S ≤ 1 / 2 := by
    rw [measureReal_def]
    have := ENNReal.toReal_mono (by norm_num : (2 : ℝ≥0∞)⁻¹ ≠ ∞) hShalf
    norm_num at this ⊢
    exact this
  have hraw := V.safe_dyadicMALA_boundaryFlow_lower_of_bakryLedoux
    hBL t ht htSafe hS hqpos hqhalf
  have hfactor := safe_defective_factor_lower V.m V.L (d : ℝ) b t
    ((V.target : Measure (State d)).real S)
    (V.hm) V.hmL V.hL V.dimension_real_one hb hbhalf ht
    (V.safeStep_le_scale H b) hqpos hqhalf
  have hphi0 : 0 ≤ Real.sqrt (V.m * t * Real.log 2) / (2 : ℝ) ^ 13 := by positivity
  have hq0 : 0 ≤ (V.target : Measure (State d)).real S := hqpos.le
  have hreal :
      (Real.sqrt (V.m * t * Real.log 2) / (2 : ℝ) ^ 13) *
          (V.target : Measure (State d)).real S ≤
        (boundaryFlow (V.target : Measure (State d)) K S).toReal := by
    calc
      _ ≤ (V.target : Measure (State d)).real S *
          min 1 (Real.sqrt
            (V.m * t * Real.log
              (1 / (V.target : Measure (State d)).real S))) /
          (2 : ℝ) ^ 13 := by
        have := mul_le_mul_of_nonneg_left hfactor hq0
        nlinarith
      _ ≤ _ := by simpa only [K] using hraw
  have hflowtop : boundaryFlow (V.target : Measure (State d)) K S ≠ ∞ :=
    flow_ne_top (V.target : Measure (State d)) K S Sᶜ hS
  change ENNReal.ofReal
          (Real.sqrt (V.m * t * Real.log 2) / (2 : ℝ) ^ 13) *
        (V.target : Measure (State d)) S ≤
      boundaryFlow (V.target : Measure (State d)) K S
  rw [← ENNReal.ofReal_toReal hflowtop]
  rw [← ENNReal.ofReal_toReal hStop]
  rw [← measureReal_def]
  rw [← ENNReal.ofReal_mul hphi0]
  exact ENNReal.ofReal_le_ofReal hreal

def selectionWeight (H t : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal H)⁻¹ * ENNReal.ofReal (t / 2)

def safeConductance (m t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt (m * t * Real.log 2) / (2 : ℝ) ^ 13)

/-- The ENNReal harmonic constant of the safe component is exactly the
paper's `2⁻²⁸ (log 2) m t²/H` coefficient. -/
lemma safe_component_harmonic_value
    (H m t : ℝ) (hH : 0 < H) (hm : 0 < m) (ht : 0 < t) :
    ((2 : ℝ≥0∞) * harmonicCost
      (fun _ : Fin 1 => selectionWeight H t)
      (fun _ : Fin 1 => safeConductance m t))⁻¹ =
      ENNReal.ofReal
        (m * t ^ 2 * Real.log 2 / ((2 : ℝ) ^ 28 * H)) := by
  let γ : Fin 1 → ℝ≥0∞ := fun _ => selectionWeight H t
  let φ : Fin 1 → ℝ≥0∞ := fun _ => safeConductance m t
  have hbase : 0 < m * t * Real.log 2 :=
    mul_pos (mul_pos hm ht) log_two_pos
  have hphi : 0 < Real.sqrt (m * t * Real.log 2) / (2 : ℝ) ^ 13 :=
    div_pos (Real.sqrt_pos.2 hbase) (by positivity)
  have hγtop : ∀ j, γ j ≠ ∞ := by
    intro j
    exact ENNReal.mul_ne_top
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hH).ne')
      ENNReal.ofReal_ne_top
  have hφtop : ∀ j, φ j ≠ ∞ := fun _ => ENNReal.ofReal_ne_top
  have hharm0 : harmonicCost γ φ ≠ 0 :=
    harmonicCost_ne_zero (by norm_num) γ φ hγtop hφtop
  have hleftTop : ((2 : ℝ≥0∞) * harmonicCost γ φ)⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr (mul_ne_zero (by norm_num) hharm0)
  apply (ENNReal.toReal_eq_toReal_iff' hleftTop ENNReal.ofReal_ne_top).mp
  simp only [ENNReal.toReal_inv, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (by positivity :
      0 ≤ m * t ^ 2 * Real.log 2 / ((2 : ℝ) ^ 28 * H))]
  simp only [harmonicCost, Fin.sum_univ_one, γ, φ, selectionWeight,
    safeConductance, ENNReal.toReal_inv, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hH.le,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ t / 2),
    ENNReal.toReal_ofReal hphi.le]
  have hsqrt : (Real.sqrt (m * t * Real.log 2)) ^ 2 =
      m * t * Real.log 2 := Real.sq_sqrt hbase.le
  have hsqrt' : (Real.sqrt (t * m * Real.log 2)) ^ 2 =
      t * m * Real.log 2 := Real.sq_sqrt (by positivity)
  field_simp [ne_of_gt hH, ne_of_gt hm, ne_of_gt ht,
    log_two_ne_zero, ne_of_gt hphi]
  nlinarith

theorem safe_component_spectralGap_of_bakryLedoux
    (H b : ℝ) (hH : 0 < H) (hb : 0 < b) (hbhalf : b ≤ 1 / 2)
    (hBL : BakryLedouxEnlargement
      (V.target : Measure (State d)) V.m
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure)) :
    ((2 : ℝ≥0∞) * harmonicCost
      (fun _ : Fin 1 => selectionWeight H (V.safeStep H b))
      (fun _ : Fin 1 => safeConductance V.m (V.safeStep H b)))⁻¹ ≤
      spectralGap (V.target : Measure (State d)) (V.uniformMALA H hH) := by
  let t : ℝ := V.safeStep H b
  have ht : 0 < t := V.safeStep_pos H b hH hb
  let K : Fin 1 → Kernel (State d) (State d) := fun _ => V.dyadicMALA t ht
  let γ : Fin 1 → ℝ≥0∞ := fun _ => selectionWeight H t
  let φ : Fin 1 → ℝ≥0∞ := fun _ => safeConductance V.m t
  letI : IsMarkovKernel (V.uniformMALA H hH) := V.uniformMALA_isMarkovKernel H hH
  have hγ0 : ∀ j, γ j ≠ 0 := by
    intro j
    exact mul_ne_zero
      (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
      (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hγtop : ∀ j, γ j ≠ ∞ := by
    intro j
    exact ENNReal.mul_ne_top
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hH).ne')
      ENNReal.ofReal_ne_top
  have hbase : 0 < V.m * t * Real.log 2 :=
    mul_pos (mul_pos V.hm ht) log_two_pos
  have hφ0 : ∀ j, φ j ≠ 0 := by
    intro j
    exact (ENNReal.ofReal_pos.mpr
      (div_pos (Real.sqrt_pos.2 hbase) (by positivity))).ne'
  have hφtop : ∀ j, φ j ≠ ∞ := fun _ => ENNReal.ofReal_ne_top
  apply componentAggregation_le_spectralGap (N := 1) (by norm_num)
    (V.target : Measure (State d)) (V.uniformMALA H hH) K
    (hK := fun _ => V.dyadicMALA_isMarkovKernel t ht)
    (fun j => V.dyadicMALA_isReversible t ht)
    (fun j => γ j) (fun j => φ j) hγ0 hγtop hφ0 hφtop
  · intro f hf
    calc
      (∑ j, γ j * Dirichlet.energy (V.target : Measure (State d)) (K j) f) =
          selectionWeight H t *
            Dirichlet.energy (V.target : Measure (State d))
              (V.dyadicMALA t ht) f := by simp [γ, K]
      _ = Dirichlet.energy (V.target : Measure (State d))
          (Kernel.parameterMixture
            ((uniformStepMeasure H).restrict (Set.Ioc (t / 2) t))
            V.malaKernelFamily) f := by
        symm
        exact energy_restricted_uniformStep_eq_weight_dyadic V H t hH ht
          (V.safeStep_le_H H b) f hf
      _ ≤ Dirichlet.energy (V.target : Measure (State d))
          (V.uniformMALA H hH) f :=
        V.energy_uniformMALA_restrict_dyadic_le H t hH f hf
  · intro S hS hSpos hShalf
    refine ⟨0, ?_⟩
    simpa only [φ, K, safeConductance, t] using
      V.safe_boundaryFlow_lower_of_bakryLedoux H b hH hb hbhalf hBL
        hS hSpos hShalf

/-- Exact safe spectral-gap estimate, with Bakry--Ledoux as its sole
analytic premise. -/
theorem safe_spectralGap_lower_of_bakryLedoux
    (H b : ℝ) (hH : 0 < H) (hb : 0 < b) (hbhalf : b ≤ 1 / 2)
    (hBL : BakryLedouxEnlargement
      (V.target : Measure (State d)) V.m
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure)) :
    ENNReal.ofReal
        (V.m * (V.safeStep H b) ^ 2 * Real.log 2 /
          ((2 : ℝ) ^ 28 * H)) ≤
      spectralGap (V.target : Measure (State d)) (V.uniformMALA H hH) := by
  rw [← safe_component_harmonic_value H V.m (V.safeStep H b)
    hH V.hm (V.safeStep_pos H b hH hb)]
  exact V.safe_component_spectralGap_of_bakryLedoux H b hH hb hbhalf hBL

end FirstOrderPotential

end
end UniformRandomMALA.Concrete
