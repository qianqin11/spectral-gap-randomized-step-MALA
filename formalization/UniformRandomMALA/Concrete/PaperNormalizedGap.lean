import UniformRandomMALA.Concrete.TunedSpectralGap

/-!
# The normalized logarithmic threshold in the manuscript

Theorem 2.1 (`thm:main`) now uses `pStar = 1 + log d + log kappa`.
This module absorbs the earlier universal threshold and step constants into
one universal gap coefficient. All analytic inputs are supplied by the
existing end-to-end theorem.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

/-- Universal comparison between the internal and manuscript thresholds. -/
def normalizedThresholdFactor : ℝ := 2 * FirstOrderPotential.concreteA0

lemma normalizedThresholdFactor_ge_one : 1 ≤ normalizedThresholdFactor := by
  unfold normalizedThresholdFactor
  linarith [FirstOrderPotential.concreteA0_ge_two]

lemma normalizedThresholdFactor_pos : 0 < normalizedThresholdFactor :=
  zero_lt_one.trans_le normalizedThresholdFactor_ge_one

/-- The universal reduction of the certified scale under normalization. -/
def normalizedScaleFactor : ℝ :=
  FirstOrderPotential.concreteB0 / normalizedThresholdFactor

lemma normalizedScaleFactor_pos : 0 < normalizedScaleFactor :=
  div_pos FirstOrderPotential.concreteB0_pos normalizedThresholdFactor_pos

lemma normalizedScaleFactor_le_one : normalizedScaleFactor ≤ 1 := by
  unfold normalizedScaleFactor
  apply (div_le_one normalizedThresholdFactor_pos).2
  linarith [FirstOrderPotential.concreteB0_le_half, normalizedThresholdFactor_ge_one]

/-- Universal constant in the normalized master bound. -/
def normalizedGapConstant : ℝ := concreteGapConstant * normalizedScaleFactor ^ 2

lemma normalizedGapConstant_pos : 0 < normalizedGapConstant :=
  mul_pos concreteGapConstant_pos (sq_pos_of_pos normalizedScaleFactor_pos)

/-- The manuscript's dimension/moment maximum, without universal factors. -/
def normalizedGapShape (D p : ℝ) : ℝ :=
  max (1 / Real.sqrt (p * (D + p))) (1 / D)

lemma normalizedGapShape_nonneg {D p : ℝ} (hD : 0 ≤ D) :
    0 ≤ normalizedGapShape D p :=
  (one_div_nonneg.mpr hD).trans (le_max_right _ _)

lemma normalizedGapShape_compare {D p P A : ℝ}
    (hD : 0 < D) (hp : 0 < p) (hP : 0 < P)
    (hA : 1 ≤ A) (hPA : P ≤ A * p) :
    normalizedGapShape D p / A ≤ normalizedGapShape D P := by
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hsum : D + P ≤ A * (D + p) := by
    nlinarith [mul_nonneg hD.le (sub_nonneg.mpr hA)]
  have hprod : P * (D + P) ≤ A ^ 2 * (p * (D + p)) := by
    calc
      P * (D + P) ≤ (A * p) * (A * (D + p)) :=
        mul_le_mul hPA hsum (add_pos hD hP).le (mul_pos hApos hp).le
      _ = A ^ 2 * (p * (D + p)) := by ring
  have hroot : Real.sqrt (P * (D + P)) ≤ A * Real.sqrt (p * (D + p)) := by
    calc
      _ ≤ Real.sqrt (A ^ 2 * (p * (D + p))) := Real.sqrt_le_sqrt hprod
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg A), Real.sqrt_sq hApos.le]
  unfold normalizedGapShape
  rw [← max_div_div_right hApos.le]
  apply max_le
  · apply le_trans _ (le_max_left _ _)
    have h := one_div_le_one_div_of_le
      (Real.sqrt_pos.2 (mul_pos hP (add_pos hD hP))) hroot
    simpa only [div_eq_mul_inv, one_mul, mul_inv_rev, mul_comm] using h
  · exact (div_le_self (one_div_nonneg.mpr hD.le) hA).trans (le_max_right _ _)

namespace C1Potential

variable {d : ℕ}

/-- The threshold in Theorem 2.1 (`thm:main`), with no hidden multiplier. -/
def normalizedMomentThreshold (V : C1Potential d) : ℝ :=
  1 + Real.log (d : ℝ) + Real.log (V.L / V.m)

lemma normalizedMomentThreshold_ge_one (V : C1Potential d) :
    1 ≤ V.normalizedMomentThreshold := by
  have hd := Real.log_nonneg V.toFirstOrderPotential.dimension_real_one
  have hk := Real.log_nonneg V.toFirstOrderPotential.conditionNumber_one
  change 0 ≤ Real.log (V.L / V.m) at hk
  unfold normalizedMomentThreshold
  linarith

lemma normalizedMomentThreshold_pos (V : C1Potential d) :
    0 < V.normalizedMomentThreshold := zero_lt_one.trans_le V.normalizedMomentThreshold_ge_one

lemma paperMomentThreshold_le_normalized (V : C1Potential d) :
    V.paperMomentThreshold FirstOrderPotential.concreteA0 ≤
      normalizedThresholdFactor * V.normalizedMomentThreshold := by
  have hd := V.toFirstOrderPotential.dimension_real_one
  have hdpos := V.toFirstOrderPotential.dimension_real_pos
  have hlog : Real.log ((d : ℝ) + 1) ≤ Real.log (d : ℝ) + 1 := by
    calc
      _ ≤ Real.log ((d : ℝ) * 2) := Real.log_le_log (by linarith) (by linarith)
      _ = Real.log (d : ℝ) + Real.log 2 := Real.log_mul hdpos.ne' (by norm_num)
      _ ≤ Real.log (d : ℝ) + 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
  have hbase : 1 + Real.log ((d : ℝ) + 1) + Real.log (V.L / V.m) ≤
      2 * V.normalizedMomentThreshold := by
    have := V.normalizedMomentThreshold_ge_one
    unfold normalizedMomentThreshold at *
    linarith
  unfold paperMomentThreshold normalizedThresholdFactor
  nlinarith [mul_le_mul_of_nonneg_left hbase
    (le_trans (by norm_num : (0 : ℝ) ≤ 2) FirstOrderPotential.concreteA0_ge_two)]

/-- The literal right-hand side of Theorem 2.1 (`thm:main`). -/
def normalizedMasterRHS (V : C1Potential d) (C H : ℝ) : ℝ :=
  C * (V.m / H) *
    (min H (1 / V.L * normalizedGapShape d V.normalizedMomentThreshold)) ^ 2

lemma normalizedMasterRHS_le_internal (V : C1Potential d) (H : ℝ) (hH : 0 < H) :
    V.normalizedMasterRHS normalizedGapConstant H ≤
      V.paperMasterRHS FirstOrderPotential.concreteA0
        FirstOrderPotential.concreteB0 concreteGapConstant H := by
  let S := 1 / V.L * normalizedGapShape d V.normalizedMomentThreshold
  let T := FirstOrderPotential.concreteB0 / V.L *
    normalizedGapShape d (V.paperMomentThreshold FirstOrderPotential.concreteA0)
  have hS : 0 ≤ S := mul_nonneg (one_div_nonneg.mpr V.hL.le)
    (normalizedGapShape_nonneg V.toFirstOrderPotential.dimension_real_pos.le)
  have hT : 0 ≤ T := mul_nonneg
    (div_nonneg FirstOrderPotential.concreteB0_pos.le V.hL.le)
    (normalizedGapShape_nonneg V.toFirstOrderPotential.dimension_real_pos.le)
  have hshape := normalizedGapShape_compare V.toFirstOrderPotential.dimension_real_pos
    V.normalizedMomentThreshold_pos V.paperMomentThreshold_concrete_pos
    normalizedThresholdFactor_ge_one V.paperMomentThreshold_le_normalized
  have hscale : normalizedScaleFactor * S ≤ T := by
    calc
      normalizedScaleFactor * S = FirstOrderPotential.concreteB0 / V.L *
          (normalizedGapShape d V.normalizedMomentThreshold / normalizedThresholdFactor) := by
        dsimp [S, normalizedScaleFactor]
        ring
      _ ≤ T := mul_le_mul_of_nonneg_left hshape
        (div_nonneg FirstOrderPotential.concreteB0_pos.le V.hL.le)
  have hmin : normalizedScaleFactor * min H S ≤ min H T := by
    apply le_min
    · calc
        normalizedScaleFactor * min H S ≤ 1 * H :=
          mul_le_mul normalizedScaleFactor_le_one (min_le_left _ _)
            (le_min hH.le hS) zero_le_one
        _ = H := one_mul _
    · exact (mul_le_mul_of_nonneg_left (min_le_right _ _)
        normalizedScaleFactor_pos.le).trans hscale
  have hsquares := sq_le_sq_of_nonneg
    (mul_nonneg normalizedScaleFactor_pos.le (le_min hH.le hS)) hmin
  have h := mul_le_mul_of_nonneg_left hsquares
    (mul_nonneg concreteGapConstant_pos.le (div_nonneg V.hm.le hH.le))
  change normalizedGapConstant * (V.m / H) * (min H S) ^ 2 ≤
    concreteGapConstant * (V.m / H) * (min H T) ^ 2
  unfold normalizedGapConstant
  nlinarith only [h]

/-- The normalized Theorem 2.1 (`thm:main`) for the actual MALA mixture,
with its universal constant supplied internally. -/
theorem normalized_masterRHS_rayleighSpectralGap_lower
    (V : C1Potential d) (H : ℝ) (hH : 0 < H) :
    ENNReal.ofReal (V.normalizedMasterRHS normalizedGapConstant H) ≤
      rayleighSpectralGap (V.toFirstOrderPotential.target : Measure (State d))
        (V.toFirstOrderPotential.uniformMALA H hH) := by
  apply (ENNReal.ofReal_le_ofReal (V.normalizedMasterRHS_le_internal H hH)).trans
  exact V.universal_masterRHS_rayleighSpectralGap_lower H hH

/-- Theorem 2.1 (`thm:main`) with one universal constant chosen before all
target parameters, together with the paper's exact lazy-gap identity. -/
theorem exists_universal_normalizedMasterRHS_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ {d : ℕ} (V : C1Potential d) (H : ℝ) (hH : 0 < H),
      (ENNReal.ofReal (V.normalizedMasterRHS C H) ≤
        rayleighSpectralGap (V.toFirstOrderPotential.target : Measure (State d))
          (V.toFirstOrderPotential.uniformMALA H hH)) ∧
      (rayleighSpectralGap (V.toFirstOrderPotential.target : Measure (State d))
          (V.toFirstOrderPotential.lazyUniformMALA H hH) =
        (2 : ℝ≥0∞)⁻¹ *
          rayleighSpectralGap (V.toFirstOrderPotential.target : Measure (State d))
            (V.toFirstOrderPotential.uniformMALA H hH)) := by
  refine ⟨normalizedGapConstant, normalizedGapConstant_pos, ?_⟩
  intro d V H hH
  exact ⟨V.normalized_masterRHS_rayleighSpectralGap_lower H hH,
    V.toFirstOrderPotential.rayleighSpectralGap_lazyUniformMALA H hH⟩

end C1Potential

lemma normalizedGapShape_square_bound {D p : ℝ} (hD : 0 < D) (hp : 0 < p) :
    max (D / (p * (D + p))) (1 / D) ≤ D * normalizedGapShape D p ^ 2 := by
  have hrej := sq_le_sq_of_nonneg
    (one_div_nonneg.mpr (Real.sqrt_nonneg (p * (D + p))))
    (le_max_left (1 / Real.sqrt (p * (D + p))) (1 / D))
  have hsafe := sq_le_sq_of_nonneg (one_div_nonneg.mpr hD.le)
    (le_max_right (1 / Real.sqrt (p * (D + p))) (1 / D))
  apply max_le
  · calc
      D / (p * (D + p)) = D * (1 / Real.sqrt (p * (D + p))) ^ 2 := by
        rw [div_pow, one_pow, Real.sq_sqrt (mul_pos hp (add_pos hD hp)).le]
        ring
      _ ≤ D * normalizedGapShape D p ^ 2 := mul_le_mul_of_nonneg_left hrej hD.le
  · calc
      1 / D = D * (1 / D) ^ 2 := by field_simp
      _ ≤ D * normalizedGapShape D p ^ 2 := mul_le_mul_of_nonneg_left hsafe hD.le

lemma normalizedReciprocalShape_lower {D p : ℝ} (hD : 0 < D) (hp : 0 < p) :
    1 / (2 * p) ≤ max (D / (p * (D + p))) (1 / D) := by
  rcases le_total p D with hpd | hdp
  · apply le_trans _ (le_max_left _ _)
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * p) (mul_pos hp (add_pos hD hp))).2
    nlinarith [mul_le_mul_of_nonneg_left hpd hp.le]
  · apply le_trans _ (le_max_right _ _)
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * p) hD).2
    linarith

namespace C1Potential

variable {d : ℕ}

/-- The larger endpoint of Corollary 2.2 (`cor:sqrt-d-endpoint`). -/
def normalizedSquareRootStep (V : C1Potential d) (c : ℝ) : ℝ :=
  c / (V.L * Real.sqrt (d : ℝ))

lemma normalizedSquareRootStep_pos (V : C1Potential d) (c : ℝ) (hc : 0 < c) :
    0 < V.normalizedSquareRootStep c :=
  div_pos hc (mul_pos V.hL (Real.sqrt_pos.2 V.toFirstOrderPotential.dimension_real_pos))

/-- First display in Corollary 2.2 (`cor:sqrt-d-endpoint`). -/
def normalizedSquareRootGapRHS (V : C1Potential d) (c : ℝ) : ℝ :=
  normalizedGapConstant / ((V.L / V.m) * Real.sqrt (d : ℝ)) *
    min c (1 / c * max
      ((d : ℝ) / (V.normalizedMomentThreshold * ((d : ℝ) + V.normalizedMomentThreshold)))
      (1 / (d : ℝ)))

lemma normalizedSquareRootGapRHS_le_master (V : C1Potential d) (c : ℝ) (hc : 0 < c) :
    V.normalizedSquareRootGapRHS c ≤
      V.normalizedMasterRHS normalizedGapConstant (V.normalizedSquareRootStep c) := by
  let M := normalizedGapShape d V.normalizedMomentThreshold
  let S := 1 / V.L * M
  let H := V.normalizedSquareRootStep c
  have hD := V.toFirstOrderPotential.dimension_real_pos
  have hr : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hD
  have hrsq := Real.sq_sqrt hD.le
  have hpref : 0 ≤ normalizedGapConstant / ((V.L / V.m) * Real.sqrt (d : ℝ)) :=
    (div_pos normalizedGapConstant_pos (mul_pos (div_pos V.hL V.hm) hr)).le
  have hshape := normalizedGapShape_square_bound hD V.normalizedMomentThreshold_pos
  change V.normalizedSquareRootGapRHS c ≤
    normalizedGapConstant * (V.m / H) * (min H S) ^ 2
  by_cases hbranch : H ≤ S
  · rw [min_eq_left hbranch]
    calc
      V.normalizedSquareRootGapRHS c ≤
          normalizedGapConstant / ((V.L / V.m) * Real.sqrt (d : ℝ)) * c :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) hpref
      _ = normalizedGapConstant * (V.m / H) * H ^ 2 := by
        dsimp [H, normalizedSquareRootStep]
        field_simp [V.hL.ne', V.hm.ne', hr.ne', hc.ne']
  · rw [min_eq_right (le_of_not_ge hbranch)]
    calc
      V.normalizedSquareRootGapRHS c ≤
          normalizedGapConstant / ((V.L / V.m) * Real.sqrt (d : ℝ)) *
            (1 / c * max ((d : ℝ) / (V.normalizedMomentThreshold *
              ((d : ℝ) + V.normalizedMomentThreshold))) (1 / (d : ℝ))) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hpref
      _ ≤ normalizedGapConstant / ((V.L / V.m) * Real.sqrt (d : ℝ)) *
          (1 / c * ((d : ℝ) * M ^ 2)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hshape (one_div_nonneg.mpr hc.le)) hpref
      _ = normalizedGapConstant * (V.m / H) * S ^ 2 := by
        dsimp [H, S, normalizedSquareRootStep]
        field_simp [V.hL.ne', V.hm.ne', hr.ne', hc.ne']
        rw [hrsq]

/-- Corollary 2.2 (`cor:sqrt-d-endpoint`), first display with the normalized threshold. -/
theorem normalizedSquareRootCorollary_rayleighSpectralGap_lower
    (V : C1Potential d) (c : ℝ) (hc : 0 < c) :
    ENNReal.ofReal (V.normalizedSquareRootGapRHS c) ≤
      rayleighSpectralGap (V.toFirstOrderPotential.target : Measure (State d))
        (V.toFirstOrderPotential.uniformMALA (V.normalizedSquareRootStep c)
          (V.normalizedSquareRootStep_pos c hc)) :=
  (ENNReal.ofReal_le_ofReal (V.normalizedSquareRootGapRHS_le_master c hc)).trans
    (V.normalized_masterRHS_rayleighSpectralGap_lower _ (V.normalizedSquareRootStep_pos c hc))

/-- The universal coefficient after the adjustment in the second display. -/
def normalizedCorollaryConstant : ℝ := normalizedGapConstant / 2

lemma normalizedCorollaryConstant_pos : 0 < normalizedCorollaryConstant :=
  div_pos normalizedGapConstant_pos (by norm_num)

/-- Second display in Corollary 2.2 (`cor:sqrt-d-endpoint`). -/
def normalizedSimplifiedGapRHS (V : C1Potential d) (c : ℝ) : ℝ :=
  normalizedCorollaryConstant / ((V.L / V.m) * Real.sqrt (d : ℝ)) *
    min c (1 / (c * V.normalizedMomentThreshold))

lemma normalizedSimplifiedGapRHS_le (V : C1Potential d) (c : ℝ) (hc : 0 < c) :
    V.normalizedSimplifiedGapRHS c ≤ V.normalizedSquareRootGapRHS c := by
  have hpref : 0 ≤ normalizedGapConstant / ((V.L / V.m) * Real.sqrt (d : ℝ)) := by
    have := V.toFirstOrderPotential.dimension_real_pos
    have := V.hL
    have := V.hm
    have := normalizedGapConstant_pos
    positivity
  have hshape := normalizedReciprocalShape_lower V.toFirstOrderPotential.dimension_real_pos
    V.normalizedMomentThreshold_pos
  have hmin : (1 / 2 : ℝ) * min c (1 / (c * V.normalizedMomentThreshold)) ≤
      min c (1 / c * max ((d : ℝ) / (V.normalizedMomentThreshold *
        ((d : ℝ) + V.normalizedMomentThreshold))) (1 / (d : ℝ))) := by
    apply le_min
    · have := min_le_left c (1 / (c * V.normalizedMomentThreshold))
      linarith
    · calc
        (1 / 2 : ℝ) * min c (1 / (c * V.normalizedMomentThreshold)) ≤
            (1 / 2 : ℝ) * (1 / (c * V.normalizedMomentThreshold)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
        _ = 1 / c * (1 / (2 * V.normalizedMomentThreshold)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hshape (one_div_nonneg.mpr hc.le)
  have h := mul_le_mul_of_nonneg_left hmin hpref
  unfold normalizedSimplifiedGapRHS normalizedSquareRootGapRHS normalizedCorollaryConstant
  calc
    _ = normalizedGapConstant / ((V.L / V.m) * Real.sqrt (d : ℝ)) *
        ((1 / 2 : ℝ) * min c (1 / (c * V.normalizedMomentThreshold))) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ _ := h

/-- Corollary 2.2 (`cor:sqrt-d-endpoint`), second display after the permitted
universal-constant adjustment, with no comparison hypothesis between `pStar` and `d`. -/
theorem normalizedSimplifiedCorollary_rayleighSpectralGap_lower
    (V : C1Potential d) (c : ℝ) (hc : 0 < c) :
    ENNReal.ofReal (V.normalizedSimplifiedGapRHS c) ≤
      rayleighSpectralGap (V.toFirstOrderPotential.target : Measure (State d))
        (V.toFirstOrderPotential.uniformMALA (V.normalizedSquareRootStep c)
          (V.normalizedSquareRootStep_pos c hc)) :=
  (ENNReal.ofReal_le_ofReal (V.normalizedSimplifiedGapRHS_le c hc)).trans
    (V.normalizedSquareRootCorollary_rayleighSpectralGap_lower c hc)

/-- The tuned endpoint in Corollary 2.2 (`cor:sqrt-d-endpoint`). -/
def normalizedTunedStep (V : C1Potential d) (c : ℝ) : ℝ :=
  c / (V.L * Real.sqrt ((d : ℝ) * V.normalizedMomentThreshold))

lemma normalizedTunedStep_pos (V : C1Potential d) (c : ℝ) (hc : 0 < c) :
    0 < V.normalizedTunedStep c :=
  div_pos hc (mul_pos V.hL (Real.sqrt_pos.2
    (mul_pos V.toFirstOrderPotential.dimension_real_pos V.normalizedMomentThreshold_pos)))

/-- Third display in Corollary 2.2 (`cor:sqrt-d-endpoint`). -/
def normalizedTunedGapRHS (V : C1Potential d) (c : ℝ) : ℝ :=
  normalizedCorollaryConstant / ((V.L / V.m) *
    Real.sqrt ((d : ℝ) * V.normalizedMomentThreshold)) * min c (1 / c)

lemma normalizedTunedGapRHS_pos (V : C1Potential d) (c : ℝ) (hc : 0 < c) :
    0 < V.normalizedTunedGapRHS c := by
  unfold normalizedTunedGapRHS
  exact mul_pos (div_pos normalizedCorollaryConstant_pos
    (mul_pos (div_pos V.hL V.hm) (Real.sqrt_pos.2
      (mul_pos V.toFirstOrderPotential.dimension_real_pos V.normalizedMomentThreshold_pos))))
    (lt_min hc (one_div_pos.mpr hc))

lemma normalizedTunedStep_eq (V : C1Potential d) (c : ℝ) :
    V.normalizedTunedStep c =
      V.normalizedSquareRootStep (c / Real.sqrt V.normalizedMomentThreshold) := by
  unfold normalizedTunedStep normalizedSquareRootStep
  rw [Real.sqrt_mul V.toFirstOrderPotential.dimension_real_pos.le]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

lemma normalizedTunedGapRHS_eq (V : C1Potential d) (c : ℝ) :
    V.normalizedTunedGapRHS c =
      V.normalizedSimplifiedGapRHS (c / Real.sqrt V.normalizedMomentThreshold) := by
  have hs := Real.sqrt_pos.2 V.normalizedMomentThreshold_pos
  have hs_sq := Real.sq_sqrt V.normalizedMomentThreshold_pos.le
  have hden : (c / Real.sqrt V.normalizedMomentThreshold) * V.normalizedMomentThreshold =
      c * Real.sqrt V.normalizedMomentThreshold := by
    calc
      _ = (c / Real.sqrt V.normalizedMomentThreshold) *
          (Real.sqrt V.normalizedMomentThreshold) ^ 2 := by rw [hs_sq]
      _ = _ := by field_simp [hs.ne']
  have hrec : 1 / (c * Real.sqrt V.normalizedMomentThreshold) =
      (1 / c) / Real.sqrt V.normalizedMomentThreshold := (div_div _ _ _).symm
  unfold normalizedTunedGapRHS normalizedSimplifiedGapRHS
  rw [hden, hrec, min_div_div_right hs.le,
    Real.sqrt_mul V.toFirstOrderPotential.dimension_real_pos.le]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Corollary 2.2 (`cor:sqrt-d-endpoint`), third display for the actual
kernel at the normalized tuned step. -/
theorem normalizedTunedCorollary_rayleighSpectralGap_lower
    (V : C1Potential d) (c : ℝ) (hc : 0 < c) :
    ENNReal.ofReal (V.normalizedTunedGapRHS c) ≤
      rayleighSpectralGap (V.toFirstOrderPotential.target : Measure (State d))
        (V.toFirstOrderPotential.uniformMALA (V.normalizedTunedStep c)
          (V.normalizedTunedStep_pos c hc)) := by
  have h := V.normalizedSimplifiedCorollary_rayleighSpectralGap_lower
    (c / Real.sqrt V.normalizedMomentThreshold)
    (div_pos hc (Real.sqrt_pos.2 V.normalizedMomentThreshold_pos))
  rw [← V.normalizedTunedGapRHS_eq c] at h
  simpa only [V.normalizedTunedStep_eq c] using h

end C1Potential
end
end UniformRandomMALA.Concrete
