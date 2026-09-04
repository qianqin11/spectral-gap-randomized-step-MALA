import UniformRandomMALA.Concrete.MALALocalOverlap

/-!
# MALA overlap from a stationary rejection-moment bound

This module makes the last analytic hypothesis for Proposition 3.2 visible in
one theorem.  It assumes a stationary `L^p` rejection estimate at every fixed
step.  Everything after that estimate -- the dyadic good set, Gaussian
proposal comparison, accept/reject triangle, and globally safe clause -- is
proved by the imported elementary modules.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace Concrete
namespace FirstOrderPotential

variable {d : ℕ} (V : FirstOrderPotential d)

/-- The concrete fixed-step stationary rejection estimate that remains to be
supplied by the discrete-time analysis.  The factor `Cr / 3` is chosen so that
Markov's inequality produces the paper's exceptional-set constant `Cr`.

The estimate is required only in the same small-step regime used by the local
clause of Proposition 3.2. -/
def StationaryMALARejectionMomentBound (cr Cr : ℝ) : Prop :=
  ∀ p h : ℝ, 2 ≤ p → 0 < h →
    h ≤ cr / (V.L * Real.sqrt (p * ((d : ℝ) + p))) →
    (∫ x : State d,
      ((1 - MetropolisHastings.acceptanceMass
        (V.gaussianDensityProposal h) (V.malaAcceptance h) x).toReal) ^ p
        ∂(V.target : Measure (State d))) ≤
      ((Cr / 3) * V.L * h * Real.sqrt (p * ((d : ℝ) + p))) ^ p

/-- Both clauses of Proposition 3.2, conditional only on the displayed
fixed-step stationary rejection moment estimate.

The harmless normalization `cr ≤ 1` guarantees that the local step range is
inside `h ≤ 2/L`, where the elementary Gaussian proposal comparison applies.
The local exceptional mass has exactly the paper form
`(Cr L t sqrt(p(d+p)))^p`. -/
theorem proposition32_of_stationaryMALARejectionMomentBound
    {cr Cr : ℝ} (hcr : 0 < cr) (hcr1 : cr ≤ 1) (hCr : 0 < Cr)
    (hrej : V.StationaryMALARejectionMomentBound cr Cr) :
    (∀ p t : ℝ, 2 ≤ p → ∀ ht : 0 < t,
      t ≤ cr / (V.L * Real.sqrt (p * ((d : ℝ) + p))) →
      ∃ G : Set (State d),
        MeasurableSet G ∧
        (V.target : Measure (State d)) Gᶜ ≤
          ENNReal.ofReal
            ((Cr * V.L * t * Real.sqrt (p * ((d : ℝ) + p))) ^ p) ∧
        ∀ x ∈ G, ∀ y ∈ G,
          ‖x - y‖ ≤ Real.sqrt t / 16 →
          setwiseTV (V.dyadicMALA t ht x)
            (V.dyadicMALA t ht y) ≤ 3 / 4) ∧
    (∀ t : ℝ, ∀ ht : 0 < t,
      t ≤ 1 / (2 * V.L * (d : ℝ)) →
      ∀ x y : State d,
        ‖x - y‖ ≤ Real.sqrt t / 16 →
        setwiseTV (V.dyadicMALA t ht x)
          (V.dyadicMALA t ht y) ≤ 3 / 4) := by
  constructor
  · intro p t hp ht hstep
    let s : ℝ := Real.sqrt (p * ((d : ℝ) + p))
    let C : ℝ := (Cr / 3) * V.L * t * s
    have hp0 : 0 ≤ p := by linarith
    have hd1 : 1 ≤ (d : ℝ) := V.dimension_real_one
    have hins : 1 ≤ p * ((d : ℝ) + p) := by nlinarith
    have hs1 : 1 ≤ s := by
      dsimp [s]
      exact Real.one_le_sqrt.mpr hins
    have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs1
    have hden : 0 < V.L * s := mul_pos V.hL hspos
    have hthreshold_le : cr / (V.L * s) ≤ 1 / V.L := by
      calc
        cr / (V.L * s) ≤ 1 / (V.L * s) :=
          div_le_div_of_nonneg_right hcr1 hden.le
        _ ≤ 1 / V.L := by
          apply div_le_div_of_nonneg_left zero_le_one V.hL
          simpa using mul_le_mul_of_nonneg_left hs1 V.hL.le
    have htL : t ≤ 2 / V.L := by
      have ht_one : t ≤ 1 / V.L := by
        exact hstep.trans (by simpa only [s] using hthreshold_le)
      exact ht_one.trans (div_le_div_of_nonneg_right (by norm_num) V.hL.le)
    have hC0 : 0 ≤ C := by
      dsimp [C]
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (div_nonneg hCr.le (by norm_num)) V.hL.le) ht.le)
        (Real.sqrt_nonneg _)
    have hmoment : ∀ h ∈ Set.Ioc (t / 2) t,
        (∫ x : State d,
          ((1 - MetropolisHastings.acceptanceMass
            (V.gaussianDensityProposal h) (V.malaAcceptance h) x).toReal) ^ p
            ∂(V.target : Measure (State d))) ≤ C ^ p := by
      intro h hhmem
      have hh : 0 < h := lt_of_lt_of_le (by linarith [ht]) hhmem.1.le
      have hhstep : h ≤ cr / (V.L * Real.sqrt (p * ((d : ℝ) + p))) :=
        hhmem.2.trans hstep
      have hfixed := hrej p h hp hh hhstep
      have hbase0 :
          0 ≤ (Cr / 3) * V.L * h * Real.sqrt (p * ((d : ℝ) + p)) := by
        exact mul_nonneg
          (mul_nonneg (mul_nonneg (div_nonneg hCr.le (by norm_num)) V.hL.le) hh.le)
          (Real.sqrt_nonneg _)
      have hbase_le :
          (Cr / 3) * V.L * h * Real.sqrt (p * ((d : ℝ) + p)) ≤ C := by
        have hfac0 : 0 ≤ (Cr / 3) * V.L *
            Real.sqrt (p * ((d : ℝ) + p)) := by
          exact mul_nonneg
            (mul_nonneg (div_nonneg hCr.le (by norm_num)) V.hL.le)
            (Real.sqrt_nonneg _)
        dsimp [C, s]
        calc
          (Cr / 3) * V.L * h * Real.sqrt (p * ((d : ℝ) + p)) =
              ((Cr / 3) * V.L * Real.sqrt (p * ((d : ℝ) + p))) * h := by ring
          _ ≤ ((Cr / 3) * V.L * Real.sqrt (p * ((d : ℝ) + p))) * t :=
            mul_le_mul_of_nonneg_left hhmem.2 hfac0
          _ = (Cr / 3) * V.L * t * Real.sqrt (p * ((d : ℝ) + p)) := by ring
      exact hfixed.trans (Real.rpow_le_rpow hbase0 hbase_le hp0)
    obtain ⟨G, hG, hGmass, hlocal⟩ :=
      V.exists_dyadicMALALocalOverlap_goodSet
        ht htL (show 1 ≤ p by linarith) hC0 hmoment
    refine ⟨G, hG, ?_, hlocal⟩
    have hcoef : 3 * C = Cr * V.L * t *
        Real.sqrt (p * ((d : ℝ) + p)) := by
      dsimp [C, s]
      ring
    rwa [hcoef] at hGmass
  · intro t ht hsmall x y hxy
    exact V.setwiseTV_dyadicMALA_le_three_quarters ht hsmall x y hxy

end FirstOrderPotential
end Concrete

end
end UniformRandomMALA
