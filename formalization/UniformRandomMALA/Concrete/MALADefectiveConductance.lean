import UniformRandomMALA.Concrete.MALAOverlapBounds
import UniformRandomMALA.Concrete.StandardGaussianShift

/-!
# Concrete defective conductance for the dyadic MALA components

This is the direct adapter from the unconditional Proposition 3.2 theorem to
the generic Appendix D.1 argument.  Its globally safe clause now depends
only on the separated-set theorem (and hence, once the Gaussian shift is
closed, on Bakry--Ledoux).
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace Concrete
namespace FirstOrderPotential

variable {d : ℕ} (V : FirstOrderPotential d)

/-- The second assertion of Proposition 3.4, for the concrete dyadic MALA
kernel. -/
theorem safe_dyadicMALA_boundaryFlow_lower
    (hseparated :
      SeparatedSets (V.target : Measure (State d)) V.m)
    (t : ℝ) (ht : 0 < t)
    (hsmall : t ≤ 1 / (2 * V.L * (d : ℝ)))
    {S : Set (State d)} (hS : MeasurableSet S)
    (hSpos : 0 < (V.target : Measure (State d)).real S)
    (hShalf : (V.target : Measure (State d)).real S ≤ 1 / 2) :
    (V.target : Measure (State d)).real S *
          min 1 (Real.sqrt
            (V.m * t * Real.log
              (1 / (V.target : Measure (State d)).real S))) /
          (2 : ℝ) ^ 13 ≤
      (boundaryFlow (V.target : Measure (State d))
        (V.dyadicMALA t ht) S).toReal := by
  letI : IsMarkovKernel (V.dyadicMALA t ht) :=
    V.dyadicMALA_isMarkovKernel t ht
  apply defectiveConductance_of_separatedSets
    (V.target : Measure (State d)) (V.dyadicMALA t ht)
    V.m t V.hm ht (V.dyadicMALA_isReversible t ht)
    hseparated MeasurableSet.univ hS
  · intro x hx y hy hxy
    exact V.proposition32_discreteTime.2 t ht hsmall x y hxy
  · exact hSpos
  · exact hShalf
  · rw [Set.compl_univ, measureReal_empty]
    have hmass0 : 0 ≤ (V.target : Measure (State d)).real S := hSpos.le
    have hmin0 : 0 ≤ min 1 (Real.sqrt
        (V.m * t * Real.log
          (1 / (V.target : Measure (State d)).real S))) :=
      le_min (by norm_num) (Real.sqrt_nonneg _)
    have hden0 : 0 ≤ (2 : ℝ) ^ 13 := by norm_num
    exact div_nonneg (mul_nonneg hmass0 hmin0) hden0

/-- Local Proposition 3.2 plus an explicit scalar exceptional-budget
comparison imply the first defective-conductance bound.  This formulation
keeps the remaining multiscale arithmetic independent of measure theory. -/
theorem local_dyadicMALA_boundaryFlow_lower
    (hseparated :
      SeparatedSets (V.target : Measure (State d)) V.m)
    (p t : ℝ) (hp : 2 ≤ p) (ht : 0 < t)
    (hstep : t ≤ proposition32CrSmall /
      (V.L * Real.sqrt (p * ((d : ℝ) + p))))
    {S : Set (State d)} (hS : MeasurableSet S)
    (hSpos : 0 < (V.target : Measure (State d)).real S)
    (hShalf : (V.target : Measure (State d)).real S ≤ 1 / 2)
    (hbudget :
      (proposition32CrLarge * V.L * t *
          Real.sqrt (p * ((d : ℝ) + p))) ^ p ≤
        (V.target : Measure (State d)).real S *
          min 1 (Real.sqrt
            (V.m * t * Real.log
              (1 / (V.target : Measure (State d)).real S))) /
          (2 : ℝ) ^ 13) :
    (V.target : Measure (State d)).real S *
          min 1 (Real.sqrt
            (V.m * t * Real.log
              (1 / (V.target : Measure (State d)).real S))) /
          (2 : ℝ) ^ 13 ≤
      (boundaryFlow (V.target : Measure (State d))
        (V.dyadicMALA t ht) S).toReal := by
  obtain ⟨G, hGm, hGmass, hoverlap⟩ :=
    V.proposition32_discreteTime.1 p t hp ht hstep
  letI : IsMarkovKernel (V.dyadicMALA t ht) :=
    V.dyadicMALA_isMarkovKernel t ht
  apply defectiveConductance_of_separatedSets
    (V.target : Measure (State d)) (V.dyadicMALA t ht)
    V.m t V.hm ht (V.dyadicMALA_isReversible t ht)
    hseparated hGm hS hoverlap hSpos hShalf
  have htop :
      ENNReal.ofReal
        ((proposition32CrLarge * V.L * t *
          Real.sqrt (p * ((d : ℝ) + p))) ^ p) ≠ ∞ :=
    ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono htop hGmass
  have hbase0 : 0 ≤ proposition32CrLarge * V.L * t *
      Real.sqrt (p * ((d : ℝ) + p)) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg proposition32CrLarge_pos.le V.hL.le) ht.le)
      (Real.sqrt_nonneg _)
  have hpow0 : 0 ≤
      (proposition32CrLarge * V.L * t *
        Real.sqrt (p * ((d : ℝ) + p))) ^ p :=
    Real.rpow_nonneg hbase0 _
  rw [ENNReal.toReal_ofReal hpow0] at hreal
  exact hreal.trans hbudget

/-- Globally safe dyadic MALA conductance, with Bakry--Ledoux as the only
remaining analytic hypothesis. -/
theorem safe_dyadicMALA_boundaryFlow_lower_of_bakryLedoux
    (hBL : BakryLedouxEnlargement
      (V.target : Measure (State d)) V.m
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure))
    (t : ℝ) (ht : 0 < t)
    (hsmall : t ≤ 1 / (2 * V.L * (d : ℝ)))
    {S : Set (State d)} (hS : MeasurableSet S)
    (hSpos : 0 < (V.target : Measure (State d)).real S)
    (hShalf : (V.target : Measure (State d)).real S ≤ 1 / 2) :
    (V.target : Measure (State d)).real S *
          min 1 (Real.sqrt
            (V.m * t * Real.log
              (1 / (V.target : Measure (State d)).real S))) /
          (2 : ℝ) ^ 13 ≤
      (boundaryFlow (V.target : Measure (State d))
        (V.dyadicMALA t ht) S).toReal := by
  apply V.safe_dyadicMALA_boundaryFlow_lower
    (separatedSets_of_bakryLedoux
      (V.target : Measure (State d)) V.m V.hm.le hBL)
    t ht hsmall hS hSpos hShalf

/-- Local dyadic MALA conductance, with Bakry--Ledoux and the explicit scalar
exceptional-budget inequality as the only inputs beyond Proposition 3.2. -/
theorem local_dyadicMALA_boundaryFlow_lower_of_bakryLedoux
    (hBL : BakryLedouxEnlargement
      (V.target : Measure (State d)) V.m
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure))
    (p t : ℝ) (hp : 2 ≤ p) (ht : 0 < t)
    (hstep : t ≤ proposition32CrSmall /
      (V.L * Real.sqrt (p * ((d : ℝ) + p))))
    {S : Set (State d)} (hS : MeasurableSet S)
    (hSpos : 0 < (V.target : Measure (State d)).real S)
    (hShalf : (V.target : Measure (State d)).real S ≤ 1 / 2)
    (hbudget :
      (proposition32CrLarge * V.L * t *
          Real.sqrt (p * ((d : ℝ) + p))) ^ p ≤
        (V.target : Measure (State d)).real S *
          min 1 (Real.sqrt
            (V.m * t * Real.log
              (1 / (V.target : Measure (State d)).real S))) /
          (2 : ℝ) ^ 13) :
    (V.target : Measure (State d)).real S *
          min 1 (Real.sqrt
            (V.m * t * Real.log
              (1 / (V.target : Measure (State d)).real S))) /
          (2 : ℝ) ^ 13 ≤
      (boundaryFlow (V.target : Measure (State d))
        (V.dyadicMALA t ht) S).toReal := by
  apply V.local_dyadicMALA_boundaryFlow_lower
    (separatedSets_of_bakryLedoux
      (V.target : Measure (State d)) V.m V.hm.le hBL)
    p t hp ht hstep hS hSpos hShalf hbudget

end FirstOrderPotential
end Concrete

end

end UniformRandomMALA
