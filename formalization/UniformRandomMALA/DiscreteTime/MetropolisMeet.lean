import UniformRandomMALA.DiscreteTime.Acceptance
import UniformRandomMALA.DiscreteTime.KernelAveraging
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# The Metropolis meet under a symmetric reference law

The accepted part of a Metropolis--Hastings endpoint flow has density
`min (F x) (F x.swap)` with respect to a swap-invariant reference law.
Consequently the rejected density is `F x - min (F x) (F x.swap)`.

This file proves the required centered-moment estimate directly from the
pointwise meet inequality.  Instead of importing the triangle inequality in
an abstract `L^p` space, we use the elementary two-term inequality

`(a + b)^p <= 2^(p-1) (a^p + b^p)`.

Swap invariance makes the two moments on the right equal.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

noncomputable section

namespace DiscreteTime

/-- Real version of the two-term power inequality used in the meet proof. -/
theorem real_rpow_add_le_mul_rpow_add_rpow
    {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 1 ≤ p) :
    (a + b) ^ p ≤ 2 ^ (p - 1) * (a ^ p + b ^ p) := by
  lift a to NNReal using ha
  lift b to NNReal using hb
  exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow a b hp

/-- The density of the rejected part of a proposal flow relative to a
reference endpoint law. -/
def rejectedMeetDensity {X : Type*} (F : X × X → ℝ) (z : X × X) : ℝ :=
  F z - min (F z) (F (Prod.swap z))

theorem rejectedMeetDensity_nonneg {X : Type*} (F : X × X → ℝ)
    (z : X × X) :
    0 ≤ rejectedMeetDensity F z :=
  (meet_rejection_le_deviations (F z) (F (Prod.swap z))).1

theorem rejectedMeetDensity_le {X : Type*} (F : X × X → ℝ)
    (z : X × X) :
    rejectedMeetDensity F z ≤ |F z - 1| + |F (Prod.swap z) - 1| :=
  (meet_rejection_le_deviations (F z) (F (Prod.swap z))).2

section SymmetricMoment

variable {X : Type*} [MeasurableSpace X]

/-- A swap-invariant reference endpoint law turns a centered `p`-moment
bound for `F` into a moment bound for the rejected meet density.

The conclusion retains the factor `2^(p-1) * (I + I)`.  This is exactly
`2^p I`, but the displayed form avoids any normalization convention for an
eventual `L^p` root and is often easier to rewrite in applications. -/
theorem integral_rejectedMeetDensity_rpow_le
    {sigma : Measure (X × X)} {F : X × X → ℝ} {p : ℝ}
    (hp : 1 ≤ p) (hF : Measurable F)
    (hSymm : Measure.map Prod.swap sigma = sigma)
    (hInt : Integrable (fun z => |F z - 1| ^ p) sigma) :
    Integrable (fun z => (rejectedMeetDensity F z) ^ p) sigma ∧
      (∫ z, (rejectedMeetDensity F z) ^ p ∂sigma) ≤
        2 ^ (p - 1) *
          ((∫ z, |F z - 1| ^ p ∂sigma) +
            ∫ z, |F z - 1| ^ p ∂sigma) := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  let g : X × X → ℝ := fun z => |F z - 1| ^ p
  have hgMeas : Measurable g := by
    unfold g
    fun_prop
  have hswapPreserving : MeasurePreserving Prod.swap sigma sigma :=
    ⟨measurable_swap, hSymm⟩
  have hSwapInt : Integrable (fun z => |F (Prod.swap z) - 1| ^ p) sigma := by
    have h := hswapPreserving.integrable_comp_of_integrable hInt
    change Integrable
      ((fun z : X × X => |F z - 1| ^ p) ∘
        (Prod.swap : X × X → X × X)) sigma
    exact h
  have hSwapIntegral :
      (∫ z, |F (Prod.swap z) - 1| ^ p ∂sigma) =
        ∫ z, |F z - 1| ^ p ∂sigma := by
    simpa only [Function.comp_apply] using
      hswapPreserving.integral_comp
        MeasurableEquiv.prodComm.measurableEmbedding g
  have hUpperInt : Integrable
      (fun z => 2 ^ (p - 1) *
        (|F z - 1| ^ p + |F (Prod.swap z) - 1| ^ p)) sigma := by
    exact (hInt.add hSwapInt).const_mul _
  have hRejectedMeas : Measurable (fun z => (rejectedMeetDensity F z) ^ p) := by
    apply (Real.continuous_rpow_const hp0).measurable.comp
    unfold rejectedMeetDensity
    exact hF.sub (hF.min (hF.comp measurable_swap))
  have hPointwise : ∀ z,
      (rejectedMeetDensity F z) ^ p ≤
        2 ^ (p - 1) *
          (|F z - 1| ^ p + |F (Prod.swap z) - 1| ^ p) := by
    intro z
    have hmeetNonneg := rejectedMeetDensity_nonneg F z
    have hmeetLe := rejectedMeetDensity_le F z
    calc
      (rejectedMeetDensity F z) ^ p ≤
          (|F z - 1| + |F (Prod.swap z) - 1|) ^ p :=
        Real.rpow_le_rpow hmeetNonneg hmeetLe hp0
      _ ≤ 2 ^ (p - 1) *
          (|F z - 1| ^ p + |F (Prod.swap z) - 1| ^ p) :=
        real_rpow_add_le_mul_rpow_add_rpow
          (abs_nonneg _) (abs_nonneg _) hp
  have hRejectedInt : Integrable
      (fun z => (rejectedMeetDensity F z) ^ p) sigma := by
    apply integrable_of_le_of_le hRejectedMeas.aestronglyMeasurable
      (ae_of_all _ fun z => Real.rpow_nonneg
        (rejectedMeetDensity_nonneg F z) p)
      (ae_of_all _ hPointwise)
      (integrable_zero (X × X) ℝ sigma) hUpperInt
  refine ⟨hRejectedInt, ?_⟩
  calc
    (∫ z, (rejectedMeetDensity F z) ^ p ∂sigma) ≤
        ∫ z, 2 ^ (p - 1) *
          (|F z - 1| ^ p + |F (Prod.swap z) - 1| ^ p) ∂sigma :=
      integral_mono_ae hRejectedInt hUpperInt (ae_of_all _ hPointwise)
    _ = 2 ^ (p - 1) *
          ((∫ z, |F z - 1| ^ p ∂sigma) +
            ∫ z, |F (Prod.swap z) - 1| ^ p ∂sigma) := by
      rw [integral_const_mul, integral_add hInt hSwapInt]
    _ = 2 ^ (p - 1) *
          ((∫ z, |F z - 1| ^ p ∂sigma) +
            ∫ z, |F z - 1| ^ p ∂sigma) := by
      rw [hSwapIntegral]

end SymmetricMoment

section RejectionMarginal

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
  [OpensMeasurableSpace X] [StandardBorelSpace X] [Nonempty X]

/-- The rejection probability obtained by disintegrating the rejected
endpoint flow over its first coordinate. -/
def rejectionMarginal (sigma : Measure (X × X)) [IsFiniteMeasure sigma]
    (F : X × X → ℝ) (x : X) : ℝ :=
  kernelAverage sigma.condKernel (rejectedMeetDensity F) x

/-- Complete density-level MH step: under a symmetric probability reference
law, the `p`-moment of the rejection marginal is bounded by twice the two
centered endpoint-likelihood moments (before taking the `p`-th root).

This theorem combines only finite-measure disintegration, the pointwise meet
identity, and scalar Jensen. -/
theorem integral_rejectionMarginal_rpow_le
    {sigma : Measure (X × X)} [IsProbabilityMeasure sigma]
    {F : X × X → ℝ} {p : ℝ}
    (hp : 1 ≤ p) (hF : Measurable F)
    (hSymm : Measure.map Prod.swap sigma = sigma)
    (hInt : Integrable (fun z => |F z - 1| ^ p) sigma) :
    Integrable (fun x => (rejectionMarginal sigma F x) ^ p) sigma.fst ∧
      (∫ x, (rejectionMarginal sigma F x) ^ p ∂sigma.fst) ≤
        2 ^ (p - 1) *
          ((∫ z, |F z - 1| ^ p ∂sigma) +
            ∫ z, |F z - 1| ^ p ∂sigma) := by
  have hMeet := integral_rejectedMeetDensity_rpow_le hp hF hSymm hInt
  have hRejectedMeas : Measurable (rejectedMeetDensity F) := by
    unfold rejectedMeetDensity
    exact hF.sub (hF.min (hF.comp measurable_swap))
  have hRejectedInt : Integrable (rejectedMeetDensity F) sigma :=
    integrable_of_nonneg_rpow_integrable hp hRejectedMeas
      (rejectedMeetDensity_nonneg F) hMeet.1
  have hRejectedIntComp : Integrable (rejectedMeetDensity F)
      (sigma.fst ⊗ₘ sigma.condKernel) := by
    simpa only [sigma.disintegrate sigma.condKernel] using hRejectedInt
  have hRejectedPowIntComp : Integrable
      (fun z => (rejectedMeetDensity F z) ^ p)
      (sigma.fst ⊗ₘ sigma.condKernel) := by
    simpa only [sigma.disintegrate sigma.condKernel] using hMeet.1
  have hAverage := integral_kernelAverage_rpow_le hp hRejectedMeas
    (rejectedMeetDensity_nonneg F) hRejectedIntComp hRejectedPowIntComp
  refine ⟨by simpa [rejectionMarginal] using hAverage.1, ?_⟩
  calc
    (∫ x, (rejectionMarginal sigma F x) ^ p ∂sigma.fst) =
        ∫ x, (kernelAverage sigma.condKernel
          (rejectedMeetDensity F) x) ^ p ∂sigma.fst := by rfl
    _ ≤ ∫ z, (rejectedMeetDensity F z) ^ p
          ∂(sigma.fst ⊗ₘ sigma.condKernel) := hAverage.2
    _ = ∫ z, (rejectedMeetDensity F z) ^ p ∂sigma := by
      rw [sigma.disintegrate sigma.condKernel]
    _ ≤ 2 ^ (p - 1) *
          ((∫ z, |F z - 1| ^ p ∂sigma) +
            ∫ z, |F z - 1| ^ p ∂sigma) := hMeet.2

end RejectionMarginal

end DiscreteTime

end

end UniformRandomMALA
