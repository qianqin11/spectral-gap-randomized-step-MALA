import UniformRandomMALA.Concrete.C1ToFirstOrder
import UniformRandomMALA.Concrete.LazyKernel
import UniformRandomMALA.Concrete.SqrtDimensionCorollary
import UniformRandomMALA.Concrete.RejectionMomentsOne
import UniformRandomMALA.Concrete.AllParameterMALAFlow

/-!
# Paper-facing endpoints under the revised first-order assumptions

The target and MALA kernels are the concrete objects built from `U` and its
actual gradient by `C1Potential.toFirstOrderPotential`. The descent lemma
supplies the upper Taylor inequality; it is not an input certificate.

The core Gaussian isoperimetric and discrete-time rejection proofs are reused.
The manuscript uses a literature contraction theorem for isoperimetry, whereas
Lean still derives it from Gaussian OU/Bobkov and finite-Euler weak limits.
Neither route assumes second derivatives of the target potential.

The additional nonconvex assertion in Appendix B is outside these endpoints:
strong convexity is retained here, exactly as in the revised standing setup.
-/

namespace UniformRandomMALA.Concrete.C1Potential

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory Gradient

noncomputable section

variable {d : ℕ}

/-- The non-lazy master lower bound under the manuscript's first-order
assumptions, stated with the package's original all-measurable Poincaré gap. -/
theorem universal_masterRHS_spectralGap_lower
    (V : C1Potential d) (H : ℝ) (hH : 0 < H) :
    let W := V.toFirstOrderPotential
    let p := W.universalParameters H hH
    ENNReal.ofReal p.masterRHS ≤
      spectralGap (W.target : Measure (State d))
        (W.uniformMALA p.H p.hH) := by
  exact V.toFirstOrderPotential.universal_masterRHS_spectralGap_lower H hH

/-- Exact first-order non-lazy endpoint: the hypotheses use only `C¹`,
strong convexity, and a Lipschitz actual gradient. All universal constants
are supplied internally, and the conclusion uses the manuscript's `L²`
Rayleigh spectral gap. No external analytic certificate is a parameter. -/
theorem universal_masterRHS_rayleighSpectralGap_lower
    (V : C1Potential d) (H : ℝ) (hH : 0 < H) :
    let W := V.toFirstOrderPotential
    let p := W.universalParameters H hH
    ENNReal.ofReal p.masterRHS ≤
      rayleighSpectralGap (W.target : Measure (State d))
        (W.uniformMALA p.H p.hH) := by
  let W := V.toFirstOrderPotential
  let p := W.universalParameters H hH
  exact (W.universal_masterRHS_spectralGap_lower H hH).trans
    (spectralGap_le_rayleighSpectralGap (W.uniformMALA p.H p.hH))

end

end UniformRandomMALA.Concrete.C1Potential

namespace UniformRandomMALA.Concrete.C1Potential

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

variable {d : ℕ}

/-- The lazy clause of Theorem 2.1 under the manuscript's first-order
assumptions: the non-lazy master right-hand side is divided exactly by two. -/
theorem universal_half_masterRHS_lazy_rayleighSpectralGap_lower
    (V : C1Potential d) (H : ℝ) (hH : 0 < H) :
    let W := V.toFirstOrderPotential
    let p := W.universalParameters H hH
    (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal p.masterRHS ≤
      rayleighSpectralGap (W.target : Measure (State d))
        (W.lazyUniformMALA p.H p.hH) := by
  simp only
  let W := V.toFirstOrderPotential
  let p := W.universalParameters H hH
  letI : IsMarkovKernel (W.uniformMALA p.H p.hH) :=
    W.uniformMALA_isMarkovKernel p.H p.hH
  rw [W.rayleighSpectralGap_lazyUniformMALA p.H p.hH]
  exact mul_le_mul_of_nonneg_left
    (V.universal_masterRHS_rayleighSpectralGap_lower H hH) bot_le

end

end UniformRandomMALA.Concrete.C1Potential

namespace UniformRandomMALA.Concrete.C1Potential

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

variable {d : ℕ}

/-- Corollary 2.2, first display, for randomized MALA under the manuscript's
first-order assumptions. -/
theorem sqrtDimensionCorollary_rayleighSpectralGap_lower
    (V : C1Potential d) (c : ℝ) (hc : 0 < c) :
    let W := V.toFirstOrderPotential
    let H := c / (W.L * Real.sqrt (d : ℝ))
    let hH : 0 < H := div_pos hc (mul_pos W.hL (Real.sqrt_pos.2 W.dimension_real_pos))
    let p := W.universalParameters H hH
    ENNReal.ofReal (p.sqrtDimensionCorollaryRHS c) ≤
      rayleighSpectralGap (W.target : Measure (State d))
        (W.uniformMALA p.H p.hH) := by
  let W := V.toFirstOrderPotential
  let H := c / (W.L * Real.sqrt (d : ℝ))
  have hH : 0 < H :=
    div_pos hc (mul_pos W.hL (Real.sqrt_pos.2 W.dimension_real_pos))
  let p := W.universalParameters H hH
  have hmaster := V.universal_masterRHS_rayleighSpectralGap_lower H hH
  exact p.sqrtDimensionCorollaryRHS_le_gap c hc rfl hmaster

/-- Corollary 2.2, simplified second display, for randomized MALA under the
manuscript's first-order assumptions and without assuming `pStar ≤ d`. -/
theorem sqrtDimensionCorollarySimplified_rayleighSpectralGap_lower
    (V : C1Potential d) (c : ℝ) (hc : 0 < c) :
    let W := V.toFirstOrderPotential
    let H := c / (W.L * Real.sqrt (d : ℝ))
    let hH : 0 < H := div_pos hc (mul_pos W.hL (Real.sqrt_pos.2 W.dimension_real_pos))
    let p := W.universalParameters H hH
    ENNReal.ofReal (p.sqrtDimensionCorollarySimplifiedRHS c) ≤
      rayleighSpectralGap (W.target : Measure (State d))
        (W.uniformMALA p.H p.hH) := by
  let W := V.toFirstOrderPotential
  let H := c / (W.L * Real.sqrt (d : ℝ))
  have hH : 0 < H :=
    div_pos hc (mul_pos W.hL (Real.sqrt_pos.2 W.dimension_real_pos))
  let p := W.universalParameters H hH
  have hmaster := V.universal_masterRHS_rayleighSpectralGap_lower H hH
  exact p.sqrtDimensionCorollarySimplifiedRHS_le_gap c hc rfl hmaster

end

end UniformRandomMALA.Concrete.C1Potential

namespace UniformRandomMALA.Concrete.C1Potential

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

variable {d : ℕ}

/-- The displayed threshold `p⋆` from the manuscript. -/
def paperMomentThreshold (V : C1Potential d) (A₀ : ℝ) : ℝ :=
  A₀ * (1 + Real.log ((d : ℝ) + 1) + Real.log (V.L / V.m))

/-- The displayed non-lazy right-hand side from the manuscript. -/
def paperMasterRHS (V : C1Potential d) (A₀ b₀ c₀ H : ℝ) : ℝ :=
  let pStar := V.paperMomentThreshold A₀
  c₀ * (V.m / H) *
    (min H (b₀ / V.L *
      max (1 / Real.sqrt (pStar * ((d : ℝ) + pStar)))
        (1 / (d : ℝ)))) ^ 2

/-- Both clauses of Theorem 2.1 with the same universal constants chosen
before the dimension, potential, and endpoint. The public range is `A₀ ≥ 1`;
the internal witness satisfies the stronger bound `A₀ ≥ 2`. -/
theorem exists_universal_paperMasterRHS_bounds :
    ∃ A₀ b₀ c₀ : ℝ,
      1 ≤ A₀ ∧ 0 < b₀ ∧ b₀ ≤ 1 / 2 ∧ 0 < c₀ ∧
      ∀ {d : ℕ} (V : C1Potential d) (H : ℝ) (hH : 0 < H),
        (ENNReal.ofReal (V.paperMasterRHS A₀ b₀ c₀ H) ≤
          rayleighSpectralGap
            (V.toFirstOrderPotential.target : Measure (State d))
            (V.toFirstOrderPotential.uniformMALA H hH)) ∧
        ((2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal (V.paperMasterRHS A₀ b₀ c₀ H) ≤
          rayleighSpectralGap
            (V.toFirstOrderPotential.target : Measure (State d))
            (V.toFirstOrderPotential.lazyUniformMALA H hH)) := by
  refine ⟨FirstOrderPotential.concreteA0,
    FirstOrderPotential.concreteB0, concreteGapConstant,
    le_trans (by norm_num : (1 : ℝ) ≤ 2) FirstOrderPotential.concreteA0_ge_two,
    FirstOrderPotential.concreteB0_pos,
    FirstOrderPotential.concreteB0_le_half,
    concreteGapConstant_pos, ?_⟩
  intro d V H hH
  constructor
  · have hmain := V.universal_masterRHS_rayleighSpectralGap_lower H hH
    simpa [paperMasterRHS, paperMomentThreshold, toFirstOrderPotential,
      FirstOrderPotential.universalParameters,
      FirstOrderPotential.toParameters,
      Parameters.masterRHS, Parameters.certifiedScale,
      Parameters.baseFactor, Parameters.certifiedShape,
      Parameters.rejectionShape, Parameters.safeShape] using hmain
  · have hmain := V.universal_half_masterRHS_lazy_rayleighSpectralGap_lower H hH
    simpa [paperMasterRHS, paperMomentThreshold, toFirstOrderPotential,
      FirstOrderPotential.universalParameters,
      FirstOrderPotential.toParameters,
      Parameters.masterRHS, Parameters.certifiedScale,
      Parameters.baseFactor, Parameters.certifiedShape,
      Parameters.rejectionShape, Parameters.safeShape] using hmain

/-- Gaussian enlargement under the first-order input, derived internally
rather than taking the contraction theorem as an axiom. -/
theorem target_bakryLedoux (V : C1Potential d) :
    BakryLedouxEnlargement
      (V.toFirstOrderPotential.target : Measure (State d)) V.m
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure) :=
  DiscreteTime.target_bakryLedoux V.toFirstOrderPotential 0

/-- Proposition 3.3 for the normalized first-order target. -/
theorem separatedSets (V : C1Potential d) :
    SeparatedSets (V.toFirstOrderPotential.target : Measure (State d)) V.m :=
  separatedSets_of_bakryLedoux _ V.m V.hm.le V.target_bakryLedoux

/-- Proposition B.1 in real-moment form, for every `p ≥ 1`. This endpoint
retains strong convexity; it does not assert the extra nonconvex scope. -/
theorem stationary_rejection_moments (V : C1Potential d) :
    V.toFirstOrderPotential.StationaryMALARejectionMomentBoundOne
      FirstOrderPotential.proposition32CrSmallOne
      FirstOrderPotential.proposition32CrLargeOne :=
  V.toFirstOrderPotential.stationaryMALARejectionMomentBoundOne_proposition32

/-- Proposition 3.2 under the actual-gradient first-order assumptions. -/
theorem mala_overlap_bounds (V : C1Potential d) :
    (∀ p t : ℝ, 1 ≤ p → ∀ ht : 0 < t,
      t ≤ FirstOrderPotential.proposition32CrSmallOne /
        (V.L * Real.sqrt (p * ((d : ℝ) + p))) →
      ∃ G : Set (State d),
        MeasurableSet G ∧
        (V.toFirstOrderPotential.target : Measure (State d)) Gᶜ ≤
          ENNReal.ofReal
            ((FirstOrderPotential.proposition32CrLargeOne * V.L * t *
              Real.sqrt (p * ((d : ℝ) + p))) ^ p) ∧
        ∀ x ∈ G, ∀ y ∈ G,
          ‖x - y‖ ≤ Real.sqrt t / 16 →
          setwiseTV (V.toFirstOrderPotential.dyadicMALA t ht x)
            (V.toFirstOrderPotential.dyadicMALA t ht y) ≤ 3 / 4) ∧
    (∀ t : ℝ, ∀ ht : 0 < t,
      t ≤ 1 / (2 * V.L * (d : ℝ)) →
      ∀ x y : State d,
        ‖x - y‖ ≤ Real.sqrt t / 16 →
        setwiseTV (V.toFirstOrderPotential.dyadicMALA t ht x)
          (V.toFirstOrderPotential.dyadicMALA t ht y) ≤ 3 / 4) :=
  V.toFirstOrderPotential.mala_overlap_bounds_p1

/-- Proposition 3.4 in its full parameter range under the manuscript's
first-order assumptions. The target, dyadic MALA kernel, and constants in the
bundled conclusion are those constructed from the actual gradient of `V.U`. -/
theorem allParameterMALAFlowBounds (V : C1Potential d) :
    FirstOrderPotential.AllParameterMALAFlowBounds V.toFirstOrderPotential :=
  V.toFirstOrderPotential.allParameterMALAFlowBounds

end

end UniformRandomMALA.Concrete.C1Potential
