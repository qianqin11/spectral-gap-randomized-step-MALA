import UniformRandomMALA.Concrete.FixedStepHardPotentialObstruction

/-!
# Fixed-step minimax spectral gap

This module gives literal complete-lattice definitions of the infimum over
infinitely differentiable Hessian-bounded potentials and the supremum over
positive fixed step sizes.  The explicit cosine-perturbed Gaussian is then
inserted into that class without weakening its smoothness assumption.
-/

namespace UniformRandomMALA.Concrete

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

/-- Rayleigh spectral-gap values attained by `C∞` potentials with the
paper's actual second-Fréchet-derivative bounds and fixed constants `m,L`.
The associated MALA kernel is built through the proved Hessian-to-gradient
bridge. -/
def smoothHessianPotentialGapValues
    (d : ℕ) (m L h : ℝ) : Set ℝ≥0∞ :=
  {g | ∃ hh : 0 < h, ∃ V : HessianBoundedPotential d,
    V.m = m ∧ V.L = L ∧ ContDiff ℝ ⊤ V.U ∧
    g = rayleighSpectralGap
      (V.toFirstOrderPotential.target : Measure (State d))
      (V.toFirstOrderPotential.malaKernel h hh)}

/-- Infimum over the paper's `C∞`, `[mI,LI]` potential class at one fixed
step size. -/
def fixedStepWorstPotentialGap (d : ℕ) (m L h : ℝ) : ℝ≥0∞ :=
  sInf (smoothHessianPotentialGapValues d m L h)

/-- Supremum over all positive fixed step sizes of the worst-potential gap. -/
def fixedStepMinimaxGap (d : ℕ) (m L : ℝ) : ℝ≥0∞ :=
  ⨆ h : {h : ℝ // 0 < h}, fixedStepWorstPotentialGap d m L h

/-- The explicit hard potential belongs to the exact `C∞` Hessian class. -/
theorem fixedStepHardPotential_mem_smoothHessianPotentialGapValues
    {d : ℕ} (hd : 2 ≤ d) {m L h : ℝ}
    (hm : 0 < m) (hmL : m < L) (hh : 0 < h) :
    rayleighSpectralGap
        ((fixedStepHardFirstOrderPotential hd hm hmL hh).target :
          Measure (State d))
        ((fixedStepHardFirstOrderPotential hd hm hmL hh).malaKernel h hh) ∈
      smoothHessianPotentialGapValues d m L h := by
  refine ⟨hh, fixedStepHardHessianPotential hd hm hmL hh,
    rfl, rfl, ?_, ?_⟩
  · change ContDiff ℝ ⊤ (fixedStepHardPotential d m L h)
    exact contDiff_infty_fixedStepHardPotential d m L h
  exact rfl

/-- The minimization over all smooth admissible potentials is bounded above
by the explicit hard witness. -/
theorem fixedStepWorstPotentialGap_le_hardWitness
    {d : ℕ} (hd : 2 ≤ d) {m L h : ℝ}
    (hm : 0 < m) (hmL : m < L) (hh : 0 < h) :
    fixedStepWorstPotentialGap d m L h ≤
      rayleighSpectralGap
        ((fixedStepHardFirstOrderPotential hd hm hmL hh).target :
          Measure (State d))
        ((fixedStepHardFirstOrderPotential hd hm hmL hh).malaKernel h hh) := by
  exact sInf_le
    (fixedStepHardPotential_mem_smoothHessianPotentialGapValues
      hd hm hmL hh)

/-- Pointwise minimax consequence of the raw two-branch obstruction.  One
universal `ρ<1` works for every dimension and every positive step. -/
theorem exists_universal_fixedStepWorstPotentialGap_raw_upper :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ (n : ℕ) (_hn : 1 ≤ n) {m L h : ℝ}
        (_hm : 0 < m) (_hmL : m < L) (_hh : 0 < h),
        fixedStepWorstPotentialGap (n + 1) m L h ≤
          min
            (ENNReal.ofReal (m * h + (m * h) ^ 2 / 2))
            (ENNReal.ofReal (4 *
              (ρ ^ n + Real.exp
                (-(((L - m) / 2) * h * hardAcceptanceDrift * n))))) := by
  obtain ⟨ρ, hρ0, hρ1, hhard⟩ :=
    exists_universal_fixedStepHardPotential_raw_obstruction
  refine ⟨ρ, hρ0, hρ1, ?_⟩
  intro n hn m L h hm hmL hh
  exact (fixedStepWorstPotentialGap_le_hardWitness
    (d := n + 1) (by omega) hm hmL hh).trans
      (hhard n hn hm hmL hh)

/-- The explicit hard witness turns the generic compressed obstruction into
an upper bound for the infimum over the paper's full smooth potential class. -/
theorem exists_universal_fixedStepWorstPotentialGap_obstruction_allDimensions :
    ∃ c : ℝ, 0 < c ∧
      ∀ {d : ℕ} (hd : 2 ≤ d) {m L h : ℝ}
        (hm : 0 < m) (hmL : m < L) (hh : 0 < h),
        fixedStepWorstPotentialGap d m L h ≤
          ENNReal.ofReal (8 * min
            (m * h + (m * h) ^ 2 / 2)
            (Real.exp (-c * (d - 1) * min ((L - m) * h) 1))) := by
  obtain ⟨c, hc, hhard⟩ :=
    exists_universal_fixedStepHardPotential_obstruction_allDimensions
  refine ⟨c, hc, ?_⟩
  intro d hd m L h hm hmL hh
  exact (fixedStepWorstPotentialGap_le_hardWitness hd hm hmL hh).trans
    (hhard hd hm hmL hh)

/-- Elementary absorption of the quadratic correction in the local branch.
The only property of the competing sticky bound used here is `e ≤ 1`. -/
theorem min_quadraticCorrection_le_threeHalves
    {u e : ℝ} (hu : 0 ≤ u) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    min (u + u ^ 2 / 2) e ≤ (3 / 2 : ℝ) * min u e := by
  by_cases hu1 : u ≤ 1
  · by_cases hue : u ≤ e
    · rw [min_eq_left hue]
      apply (min_le_left _ _).trans
      nlinarith [sq_nonneg u]
    · have heu : e ≤ u := le_of_not_ge hue
      rw [min_eq_right heu]
      exact (min_le_right _ _).trans (by nlinarith)
  · have h1u : 1 ≤ u := le_of_not_ge hu1
    have heu : e ≤ u := he1.trans h1u
    rw [min_eq_right heu]
    exact (min_le_right _ _).trans (by nlinarith)

/-- Reparametrize the hard-potential obstruction by the dimensionless step
`t = Lh` and condition number `κ = L/m`.  Losing a factor two in the
universal exponential rate replaces `d-1` by `d`; the factor `3/2` absorbs
the exact quadratic local correction. -/
theorem hardObstructionScalar_le_twoBranchEnvelope
    {d : ℕ} (hd : 2 ≤ d) {m L h c c₀ : ℝ}
    (hm : 0 < m) (hmL : m < L) (hh : 0 < h)
    (hc : 0 < c) (hc₀ : 0 < c₀) (hc₀c : c₀ ≤ c / 2) :
    8 * min
        (m * h + (m * h) ^ 2 / 2)
        (Real.exp (-c * (d - 1) * min ((L - m) * h) 1)) ≤
      12 * fixedStepTwoBranchEnvelope (L / m) d c₀ (L * h) := by
  have hL : 0 < L := hm.trans hmL
  have hu : 0 ≤ m * h := by positivity
  have hs : 0 ≤ (L - m) * h := by positivity
  have hmin0 : 0 ≤ min ((L - m) * h) 1 := le_min hs zero_le_one
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hrate : c₀ * (d : ℝ) ≤ c * ((d : ℝ) - 1) := by
    have hc₀' : 2 * c₀ ≤ c := by linarith
    nlinarith [mul_nonneg hc₀.le (sub_nonneg.mpr hdR)]
  have hexp :
      Real.exp (-c * (d - 1) * min ((L - m) * h) 1) ≤
        Real.exp (-c₀ * d * min ((L - m) * h) 1) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right hrate hmin0
    calc
      -c * (d - 1) * min ((L - m) * h) 1 =
          -(c * (d - 1) * min ((L - m) * h) 1) := by ring
      _ ≤ -(c₀ * d * min ((L - m) * h) 1) := neg_le_neg this
      _ = -c₀ * d * min ((L - m) * h) 1 := by ring
  have he0 : 0 ≤ Real.exp (-c₀ * d * min ((L - m) * h) 1) :=
    (Real.exp_pos _).le
  have he1 : Real.exp (-c₀ * d * min ((L - m) * h) 1) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc₀.le) hd0) hmin0
  have hminmono :
      min (m * h + (m * h) ^ 2 / 2)
          (Real.exp (-c * (d - 1) * min ((L - m) * h) 1)) ≤
        min (m * h + (m * h) ^ 2 / 2)
          (Real.exp (-c₀ * d * min ((L - m) * h) 1)) :=
    min_le_min_left _ hexp
  have habsorb := min_quadraticCorrection_le_threeHalves hu he0 he1
  have hkinv : (L / m)⁻¹ * (L * h) = m * h := by
    field_simp [hm.ne', hL.ne']
    <;> ring
  have hshape : (1 - (L / m)⁻¹) * (L * h) = (L - m) * h := by
    field_simp [hm.ne', hL.ne']
    <;> ring
  rw [fixedStepTwoBranchEnvelope, hkinv, hshape]
  nlinarith

/-- Pointwise minimax obstruction in the dimensionless variables used by the
paper's final scalar optimization. -/
theorem exists_universal_fixedStepWorstPotentialGap_le_twoBranchEnvelope :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ {d : ℕ} (hd : 2 ≤ d) {m L h : ℝ}
        (hm : 0 < m) (hmL : m < L) (hh : 0 < h),
        fixedStepWorstPotentialGap d m L h ≤
          ENNReal.ofReal
            (12 * fixedStepTwoBranchEnvelope (L / m) d c (L * h)) := by
  obtain ⟨a, ha, hraw⟩ :=
    exists_universal_fixedStepWorstPotentialGap_obstruction_allDimensions
  let c : ℝ := min (a / 2) 1
  have hc : 0 < c := lt_min (by positivity) zero_lt_one
  have hc1 : c ≤ 1 := min_le_right _ _
  have hca : c ≤ a / 2 := min_le_left _ _
  refine ⟨c, hc, hc1, ?_⟩
  intro d hd m L h hm hmL hh
  apply (hraw hd hm hmL hh).trans
  exact ENNReal.ofReal_le_ofReal
    (hardObstructionScalar_le_twoBranchEnvelope
      hd hm hmL hh ha hc hca)

/-- Explicit optimized fixed-step minimax bound.  This is the sharp
pre-absorption form of Proposition 2.3: the first coefficient displays its
dependence on the lower condition-number cutoff `κ₀`, while the exponential
rate is universal. -/
theorem exists_universal_fixedStepMinimaxGap_explicit_upper :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ {κ₀ : ℝ}, 1 < κ₀ →
      ∀ {d : ℕ}, 2 ≤ d →
      ∀ {m L : ℝ}, 0 < m → m < L → κ₀ ≤ L / m →
        fixedStepMinimaxGap d m L ≤
          ENNReal.ofReal
            (12 * max
              (2 * Real.log ((L / m) * d) /
                (c * (1 - κ₀⁻¹) * (L / m) * d))
              (Real.exp (-c * d))) := by
  obtain ⟨c, hc, hc1, hpoint⟩ :=
    exists_universal_fixedStepWorstPotentialGap_le_twoBranchEnvelope
  refine ⟨c, hc, hc1, ?_⟩
  intro κ₀ hκ₀ d hd m L hm hmL hκ
  rw [fixedStepMinimaxGap]
  apply iSup_le
  intro h
  apply (hpoint hd hm hmL h.property).trans
  apply ENNReal.ofReal_le_ofReal
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hL : 0 < L := hm.trans hmL
  have hopen := fixedStepTwoBranchEnvelope_le_log_max_exp
    hκ₀ hκ hdR hc hc1 (mul_nonneg hL.le h.property.le)
  exact mul_le_mul_of_nonneg_left hopen (by norm_num)

/-- Absorb the explicit balance coefficient into one multiplicative
constant.  The resulting constant depends only on `κ₀`; the exponential
rate `c` remains universal. -/
theorem explicitMinimaxMax_le_paperMax
    {κ₀ κ d c : ℝ} (hκ₀ : 1 < κ₀) (hκ : κ₀ ≤ κ)
    (hd : 2 ≤ d) (hc : 0 < c) :
    12 * max
        (2 * Real.log (κ * d) /
          (c * (1 - κ₀⁻¹) * κ * d))
        (Real.exp (-c * d)) ≤
      max (24 / (c * (1 - κ₀⁻¹))) 12 *
        max
          (Real.log (κ * d) / (κ * d))
          (Real.exp (-c * d)) := by
  have hκ₀0 : 0 < κ₀ := zero_lt_one.trans hκ₀
  have hκ1 : 1 < κ := hκ₀.trans_le hκ
  have hκ0 : 0 < κ := zero_lt_one.trans hκ1
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hq : 0 < 1 - κ₀⁻¹ :=
    sub_pos.mpr ((inv_lt_one₀ hκ₀0).mpr hκ₀)
  have hz : 1 < κ * d := by nlinarith
  have hlog0 : 0 ≤ Real.log (κ * d) := (Real.log_pos hz).le
  have hratio0 : 0 ≤ Real.log (κ * d) / (κ * d) := by positivity
  have hexp0 : 0 ≤ Real.exp (-c * d) := (Real.exp_pos _).le
  have hC0 : 0 ≤ max (24 / (c * (1 - κ₀⁻¹))) 12 := by
    exact (le_max_right _ _).trans' (by norm_num)
  rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 12)]
  apply max_le
  · calc
      12 * (2 * Real.log (κ * d) /
          (c * (1 - κ₀⁻¹) * κ * d)) =
          (24 / (c * (1 - κ₀⁻¹))) *
            (Real.log (κ * d) / (κ * d)) := by
              field_simp [hc.ne', hq.ne', hκ0.ne', hd0.ne']
              <;> ring
      _ ≤ max (24 / (c * (1 - κ₀⁻¹))) 12 *
          (Real.log (κ * d) / (κ * d)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hratio0
      _ ≤ max (24 / (c * (1 - κ₀⁻¹))) 12 *
          max (Real.log (κ * d) / (κ * d)) (Real.exp (-c * d)) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) hC0
  · calc
      12 * Real.exp (-c * d) ≤
          max (24 / (c * (1 - κ₀⁻¹))) 12 * Real.exp (-c * d) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hexp0
      _ ≤ max (24 / (c * (1 - κ₀⁻¹))) 12 *
          max (Real.log (κ * d) / (κ * d)) (Real.exp (-c * d)) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) hC0

/-- Paper-form Proposition 2.3.  The infimum is over the exact class of
infinitely differentiable potentials satisfying the actual Hessian bounds,
and the supremum ranges over every positive fixed step size. -/
theorem exists_universal_fixedStepMinimaxGap_paper_upper :
    ∃ c : ℝ, 0 < c ∧
      ∀ {κ₀ : ℝ}, 1 < κ₀ →
        ∃ C : ℝ, 0 < C ∧
          ∀ {d : ℕ}, 2 ≤ d →
          ∀ {m L : ℝ}, 0 < m → m < L → κ₀ ≤ L / m →
            fixedStepMinimaxGap d m L ≤
              ENNReal.ofReal
                (C * max
                  (Real.log ((L / m) * d) / ((L / m) * d))
                  (Real.exp (-c * d))) := by
  obtain ⟨c, hc, _hc1, hexplicit⟩ :=
    exists_universal_fixedStepMinimaxGap_explicit_upper
  refine ⟨c, hc, ?_⟩
  intro κ₀ hκ₀
  let C : ℝ := max (24 / (c * (1 - κ₀⁻¹))) 12
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  refine ⟨C, hC, ?_⟩
  intro d hd m L hm hmL hκ
  apply (hexplicit hκ₀ hd hm hmL hκ).trans
  exact ENNReal.ofReal_le_ofReal
    (explicitMinimaxMax_le_paperMax hκ₀ hκ
      (by exact_mod_cast hd) hc)

end

end UniformRandomMALA.Concrete
