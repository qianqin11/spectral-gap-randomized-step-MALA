import UniformRandomMALA.Concrete.MALAFamily
import UniformRandomMALA.Arithmetic
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Concrete geometric moment ladder

This file constructs the finite index used in the paper rather than
postulating a finite family.  In the regime `p⋆ < d`, the moments are
`p_j = 4^j p⋆`; `ladderTopIndex` is the least index whose moment reaches
the dimension.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace Concrete

/-- The geometric sequence `p_j = 4^j p⋆`. -/
def ladderMoment (p : Parameters) (j : ℕ) : ℝ :=
  (4 : ℝ) ^ j * p.pStar

lemma ladderMoment_pos (p : Parameters) (j : ℕ) :
    0 < ladderMoment p j := by
  unfold ladderMoment
  exact mul_pos (pow_pos (by norm_num) j) p.hpStar_pos

lemma ladderMoment_zero (p : Parameters) :
    ladderMoment p 0 = p.pStar := by
  simp [ladderMoment]

lemma ladderMoment_succ (p : Parameters) (j : ℕ) :
    ladderMoment p (j + 1) = 4 * ladderMoment p j := by
  unfold ladderMoment
  rw [pow_succ]
  ring

lemma exists_ladderMoment_ge_dimension (p : Parameters) :
    ∃ J : ℕ, p.d ≤ ladderMoment p J := by
  obtain ⟨j, hjle, hjlt⟩ :=
    exists_nat_pow_near
      (show (1 : ℝ) ≤ max 1 (p.d / p.pStar) from le_max_left _ _)
      (show (1 : ℝ) < 4 by norm_num)
  refine ⟨j + 1, ?_⟩
  have hratio : p.d / p.pStar < (4 : ℝ) ^ (j + 1) :=
    lt_of_le_of_lt (le_max_right _ _) hjlt
  have hmul : p.d < (4 : ℝ) ^ (j + 1) * p.pStar := by
    exact (div_lt_iff₀ p.hpStar_pos).mp hratio
  exact hmul.le

/-- The least ladder index whose moment reaches the dimension. -/
def ladderTopIndex (p : Parameters) : ℕ :=
  Nat.find (exists_ladderMoment_ge_dimension p)

lemma ladderMoment_top_ge (p : Parameters) :
    p.d ≤ ladderMoment p (ladderTopIndex p) := by
  exact Nat.find_spec (exists_ladderMoment_ge_dimension p)

lemma ladderMoment_before_top_lt
    (p : Parameters) {j : ℕ} (hj : j < ladderTopIndex p) :
    ladderMoment p j < p.d := by
  exact lt_of_not_ge
    (Nat.find_min (exists_ladderMoment_ge_dimension p) hj)

/-- In the ladder regime, the terminal moment lies in `[d,4d)`, exactly
as in equation `(pJ-range)` of the paper. -/
theorem ladderMoment_top_range
    (p : Parameters) (hsmall : p.pStar < p.d) :
    p.d ≤ ladderMoment p (ladderTopIndex p) ∧
      ladderMoment p (ladderTopIndex p) < 4 * p.d := by
  refine ⟨ladderMoment_top_ge p, ?_⟩
  by_cases hJ : ladderTopIndex p = 0
  · rw [hJ, ladderMoment_zero]
    nlinarith [p.hd]
  · have hpred : ladderTopIndex p - 1 < ladderTopIndex p := by
      omega
    have hbelow := ladderMoment_before_top_lt p hpred
    have hsucc : ladderTopIndex p - 1 + 1 = ladderTopIndex p :=
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hJ)
    rw [← hsucc, ladderMoment_succ]
    nlinarith

/-- Nominal endpoint `τ_j` from the paper. -/
def ladderNominalEndpoint (p : Parameters) (j : ℕ) : ℝ :=
  p.b0 /
    (p.L * Real.sqrt (ladderMoment p j * (p.d + ladderMoment p j)))

lemma ladderNominalEndpoint_pos (p : Parameters) (j : ℕ) :
    0 < ladderNominalEndpoint p j := by
  unfold ladderNominalEndpoint
  have hpj := ladderMoment_pos p j
  have harg :
      0 < ladderMoment p j * (p.d + ladderMoment p j) :=
    mul_pos hpj (add_pos p.hd hpj)
  exact div_pos p.hb0 (mul_pos p.hL (Real.sqrt_pos.2 harg))

private lemma nominalEndpoint_shrinks_aux
    (d L b q : ℝ) (hd : 0 < d) (hL : 0 < L)
    (hb : 0 < b) (hq : 0 < q) :
    b / (L * Real.sqrt ((4 * q) * (d + 4 * q))) <
      (b / (L * Real.sqrt (q * (d + q)))) / 2 := by
  have harg0 : 0 < q * (d + q) := mul_pos hq (add_pos hd hq)
  have harg1 : 0 < (4 * q) * (d + 4 * q) := by positivity
  have hs0 : 0 < Real.sqrt (q * (d + q)) := Real.sqrt_pos.2 harg0
  have hs1 : 0 < Real.sqrt ((4 * q) * (d + 4 * q)) :=
    Real.sqrt_pos.2 harg1
  have hs0sq : (Real.sqrt (q * (d + q))) ^ 2 = q * (d + q) :=
    Real.sq_sqrt harg0.le
  have hs1sq :
      (Real.sqrt ((4 * q) * (d + 4 * q))) ^ 2 =
        (4 * q) * (d + 4 * q) := Real.sq_sqrt harg1.le
  have hsqrt :
      2 * Real.sqrt (q * (d + q)) <
        Real.sqrt ((4 * q) * (d + 4 * q)) := by
    have hs0nonneg : 0 ≤ Real.sqrt (q * (d + q)) := hs0.le
    have hs1nonneg : 0 ≤ Real.sqrt ((4 * q) * (d + 4 * q)) := hs1.le
    nlinarith [sq_nonneg q]
  have hden0 : 0 < L * Real.sqrt (q * (d + q)) := mul_pos hL hs0
  have hden1 : 0 < L * Real.sqrt ((4 * q) * (d + 4 * q)) := mul_pos hL hs1
  have hden :
      2 * (L * Real.sqrt (q * (d + q))) <
        L * Real.sqrt ((4 * q) * (d + 4 * q)) := by
    nlinarith [mul_lt_mul_of_pos_left hsqrt hL]
  have hdiv :
      b / (L * Real.sqrt ((4 * q) * (d + 4 * q))) <
        b / (2 * (L * Real.sqrt (q * (d + q)))) := by
    apply (div_lt_div_iff₀ hden1 (mul_pos (by norm_num) hden0)).2
    nlinarith
  convert hdiv using 1
  field_simp

/-- Successive nominal endpoints decrease by a factor strictly larger than
two, which is the separation needed for disjoint dyadic intervals. -/
theorem ladderNominalEndpoint_succ_lt_half
    (p : Parameters) (j : ℕ) :
    ladderNominalEndpoint p (j + 1) < ladderNominalEndpoint p j / 2 := by
  unfold ladderNominalEndpoint
  rw [ladderMoment_succ]
  exact nominalEndpoint_shrinks_aux p.d p.L p.b0 (ladderMoment p j)
    p.hd p.hL p.hb0 (ladderMoment_pos p j)

/-- Endpoint after truncation to the user-supplied range. -/
def ladderEndpoint (p : Parameters) (j : ℕ) : ℝ :=
  p.ladderTheta * ladderNominalEndpoint p j

lemma ladderEndpoint_pos (p : Parameters) (j : ℕ) :
    0 < ladderEndpoint p j := by
  exact mul_pos p.ladderTheta_pos (ladderNominalEndpoint_pos p j)

theorem ladderEndpoint_succ_lt_half (p : Parameters) (j : ℕ) :
    ladderEndpoint p (j + 1) < ladderEndpoint p j / 2 := by
  unfold ladderEndpoint
  have h := mul_lt_mul_of_pos_left
    (ladderNominalEndpoint_succ_lt_half p j) p.ladderTheta_pos
  nlinarith

theorem ladderEndpoint_strictAnti (p : Parameters) :
    StrictAnti (ladderEndpoint p) := by
  apply strictAnti_nat_of_succ_lt
  intro j
  exact (ladderEndpoint_succ_lt_half p j).trans
    (div_lt_self (ladderEndpoint_pos p j) (by norm_num))

theorem ladderEndpoint_later_lt_half
    (p : Parameters) {i j : ℕ} (hij : i < j) :
    ladderEndpoint p j < ladderEndpoint p i / 2 := by
  have hsucc : i + 1 ≤ j := Nat.succ_le_iff.mpr hij
  exact lt_of_le_of_lt
    ((ladderEndpoint_strictAnti p).antitone hsucc)
    (ladderEndpoint_succ_lt_half p i)

lemma ladderNominalEndpoint_zero_eq_rejectionScale (p : Parameters) :
    ladderNominalEndpoint p 0 = p.rejectionScale := by
  unfold ladderNominalEndpoint Parameters.rejectionScale Parameters.baseFactor
    Parameters.rejectionShape
  rw [ladderMoment_zero]
  field_simp [ne_of_gt p.hL, ne_of_gt p.rejectionSqrt_pos]

lemma ladderEndpoint_zero_eq_min (p : Parameters) :
    ladderEndpoint p 0 = min p.H p.rejectionScale := by
  rw [ladderEndpoint, ladderNominalEndpoint_zero_eq_rejectionScale]
  exact endpointTheta_mul p.H p.rejectionScale p.hH p.rejectionScale_pos

lemma ladderEndpoint_le_H (p : Parameters) (j : ℕ) :
    ladderEndpoint p j ≤ p.H := by
  have hj0 : ladderEndpoint p j ≤ ladderEndpoint p 0 :=
    (ladderEndpoint_strictAnti p).antitone (Nat.zero_le j)
  rw [ladderEndpoint_zero_eq_min] at hj0
  exact hj0.trans (min_le_left _ _)

/-- The actual upper-half interval used to select the `j`th component. -/
def ladderInterval (p : Parameters) (j : ℕ) : Set ℝ :=
  Set.Ioc (ladderEndpoint p j / 2) (ladderEndpoint p j)

lemma measurableSet_ladderInterval (p : Parameters) (j : ℕ) :
    MeasurableSet (ladderInterval p j) := measurableSet_Ioc

lemma volume_ladderInterval (p : Parameters) (j : ℕ) :
    volume (ladderInterval p j) = ENNReal.ofReal (ladderEndpoint p j / 2) := by
  rw [ladderInterval, Real.volume_Ioc]
  congr 1
  ring

/-- Distinct ladder indices select disjoint step-size intervals. -/
theorem ladderInterval_disjoint
    (p : Parameters) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (ladderInterval p i) (ladderInterval p j) := by
  apply Set.disjoint_left.2
  intro h hhi hhj
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hjhalf := ladderEndpoint_later_lt_half p hijlt
    exact (not_lt_of_ge hhj.2) (lt_trans hjhalf hhi.1)
  · have hihalf := ladderEndpoint_later_lt_half p hjilt
    exact (not_lt_of_ge hhi.2) (lt_trans hihalf hhj.1)

theorem ladderIntervals_pairwiseDisjoint (p : Parameters) (N : ℕ) :
    Set.Pairwise (Finset.range N : Set ℕ)
      (fun i j => Disjoint (ladderInterval p i) (ladderInterval p j)) := by
  intro i hi j hj hij
  exact ladderInterval_disjoint p hij

namespace FirstOrderPotential

/-- Exact subprobability law contributed by a dyadic component of the
uniform step distribution. -/
theorem uniformStepMeasure_restrict_dyadic
    (H t : ℝ) (_hH : 0 < H) (ht : 0 < t) (htH : t ≤ H) :
    (uniformStepMeasure H).restrict (Set.Ioc (t / 2) t) =
      ((ENNReal.ofReal H)⁻¹ * ENNReal.ofReal (t / 2)) •
        dyadicStepMeasure t := by
  ext s hs
  rw [Measure.restrict_apply hs, Measure.smul_apply]
  change uniformStepMeasure H (s ∩ Set.Ioc (t / 2) t) =
    ((ENNReal.ofReal H)⁻¹ * ENNReal.ofReal (t / 2)) *
      intervalStepMeasure (t / 2) t s
  rw [uniformStepMeasure, intervalStepMeasure,
    ProbabilityTheory.cond_apply measurableSet_Ioc,
    ProbabilityTheory.cond_apply measurableSet_Ioc,
    Real.volume_Ioc, Real.volume_Ioc]
  simp only [sub_zero]
  have hsub : Set.Ioc (t / 2) t ⊆ Set.Ioc 0 H := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2.trans htH⟩
  have hinter :
      Set.Ioc 0 H ∩ (s ∩ Set.Ioc (t / 2) t) =
        Set.Ioc (t / 2) t ∩ s := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc]
    constructor
    · rintro ⟨hxH, hxs, hxt⟩
      exact ⟨hxt, hxs⟩
    · rintro ⟨hxt, hxs⟩
      exact ⟨hsub hxt, hxs, hxt⟩
  rw [hinter]
  rw [show t - t / 2 = t / 2 by ring]
  have ha0 : ENNReal.ofReal (t / 2) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hatop : ENNReal.ofReal (t / 2) ≠ ∞ := ENNReal.ofReal_ne_top
  rw [mul_assoc, ← mul_assoc (ENNReal.ofReal (t / 2)),
    ENNReal.mul_inv_cancel ha0 hatop, one_mul]

/-- Exact weighted component energy identity. -/
theorem energy_restricted_uniformStep_eq_weight_dyadic
    {d : ℕ} (V : FirstOrderPotential d)
    (H t : ℝ) (hH : 0 < H) (ht : 0 < t) (htH : t ≤ H)
    (f : State d → ℝ) (hf : Measurable f) :
    Dirichlet.energy (V.target : Measure (State d))
        (Kernel.parameterMixture
          ((uniformStepMeasure H).restrict (Set.Ioc (t / 2) t))
          V.malaKernelFamily) f =
      ((ENNReal.ofReal H)⁻¹ * ENNReal.ofReal (t / 2)) *
        Dirichlet.energy (V.target : Measure (State d))
          (V.dyadicMALA t ht) f := by
  let w : ℝ≥0∞ := (ENNReal.ofReal H)⁻¹ * ENNReal.ofReal (t / 2)
  letI : IsProbabilityMeasure (uniformStepMeasure H) :=
    uniformStepMeasure_isProbabilityMeasure H hH
  letI : IsProbabilityMeasure (dyadicStepMeasure t) :=
    dyadicStepMeasure_isProbabilityMeasure ht
  unfold dyadicMALA
  rw [Dirichlet.energy_parameterMixture
      (V.target : Measure (State d))
      ((uniformStepMeasure H).restrict (Set.Ioc (t / 2) t))
      V.malaKernelFamily f hf,
    uniformStepMeasure_restrict_dyadic H t hH ht htH,
    lintegral_smul_measure,
    Dirichlet.energy_parameterMixture
      (V.target : Measure (State d)) (dyadicStepMeasure t)
      V.malaKernelFamily f hf]
  rfl

/-- Selection probability of the `j`th ladder interval inside `(0,H]`. -/
def ladderSelectionWeight (p : Parameters) (j : ℕ) : ℝ≥0∞ :=
  (ENNReal.ofReal p.H)⁻¹ * ENNReal.ofReal (ladderEndpoint p j / 2)

/-- Concrete form of equation `(ladder-dirichlet)`: the energy of the
uniform-random MALA kernel dominates the sum of all finite ladder
components with their exact selection probabilities. -/
theorem ladder_energy_domination
    {d : ℕ} (V : FirstOrderPotential d) (p : Parameters)
    (f : State d → ℝ) (hf : Measurable f) :
    (∑ j ∈ Finset.range (ladderTopIndex p + 1),
        ladderSelectionWeight p j *
          Dirichlet.energy (V.target : Measure (State d))
            (V.dyadicMALA (ladderEndpoint p j) (ladderEndpoint_pos p j)) f) ≤
      Dirichlet.energy (V.target : Measure (State d))
        (V.uniformMALA p.H p.hH) f := by
  letI : IsProbabilityMeasure (uniformStepMeasure p.H) :=
    uniformStepMeasure_isProbabilityMeasure p.H p.hH
  have hraw := Dirichlet.sum_energy_parameterMixture_restrict_le
    (Finset.range (ladderTopIndex p + 1))
    (V.target : Measure (State d)) (uniformStepMeasure p.H)
    (ladderInterval p) V.malaKernelFamily
    (ladderIntervals_pairwiseDisjoint p (ladderTopIndex p + 1))
    (fun j hj => measurableSet_ladderInterval p j) f hf
  calc
    (∑ j ∈ Finset.range (ladderTopIndex p + 1),
        ladderSelectionWeight p j *
          Dirichlet.energy (V.target : Measure (State d))
            (V.dyadicMALA (ladderEndpoint p j) (ladderEndpoint_pos p j)) f) =
        ∑ j ∈ Finset.range (ladderTopIndex p + 1),
          Dirichlet.energy (V.target : Measure (State d))
            (Kernel.parameterMixture
              ((uniformStepMeasure p.H).restrict (ladderInterval p j))
              V.malaKernelFamily) f := by
      apply Finset.sum_congr rfl
      intro j hj
      unfold ladderSelectionWeight ladderInterval
      exact (energy_restricted_uniformStep_eq_weight_dyadic V
        p.H (ladderEndpoint p j) p.hH (ladderEndpoint_pos p j)
        (ladderEndpoint_le_H p j) f hf).symm
    _ ≤ Dirichlet.energy (V.target : Measure (State d))
        (Kernel.parameterMixture (uniformStepMeasure p.H) V.malaKernelFamily) f := hraw
    _ = Dirichlet.energy (V.target : Measure (State d))
        (V.uniformMALA p.H p.hH) f := rfl

end FirstOrderPotential

end Concrete

end

end UniformRandomMALA
