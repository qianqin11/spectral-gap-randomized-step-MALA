import UniformRandomMALA.Prelude
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!
# Parameter mixtures of Markov kernels

This file begins the unconditional kernel layer of the paper.  A measurable
family of kernels is represented by one kernel whose input is a pair
`(parameter, state)`.  Integrating out the parameter is implemented using
ordinary kernel composition, rather than an abstract operation postulated by
an interface.

The two main results are the exact Tonelli identity for the extended-valued
Dirichlet energy and preservation of reversibility.  They are the
measure-theoretic core of Lemma 3.1 (`lem:Kt`) in the current paper.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace Kernel

variable {ι α β : Type*}
  [MeasurableSpace ι] [MeasurableSpace α] [MeasurableSpace β]

/-- Integrate the parameter of a jointly measurable kernel family.

For a parameter measure `ν` and `κ : Kernel (ι × α) β`, the resulting
kernel sends `x` to `∫ κ (h,x) ∂ν(h)`. -/
def parameterMixture (ν : Measure ι) (κ : Kernel (ι × α) β) : Kernel α β :=
  κ ∘ₖ (Kernel.const α ν ×ₖ Kernel.id)

theorem parameterMixture_apply
    (ν : Measure ι) [SFinite ν] (κ : Kernel (ι × α) β)
    [IsSFiniteKernel κ] (x : α) (s : Set β) (hs : MeasurableSet s) :
    parameterMixture ν κ x s = ∫⁻ h, κ (h, x) s ∂ν := by
  rw [parameterMixture, Kernel.comp_apply' _ _ _ hs]
  rw [Kernel.lintegral_prod_id (κ.measurable_coe hs) (Kernel.const α ν) x]
  rfl

theorem lintegral_parameterMixture
    (ν : Measure ι) [SFinite ν] (κ : Kernel (ι × α) β)
    [IsSFiniteKernel κ] (x : α) {g : β → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y, g y ∂parameterMixture ν κ x =
      ∫⁻ h, ∫⁻ y, g y ∂κ (h, x) ∂ν := by
  rw [parameterMixture, Kernel.lintegral_comp _ _ _ hg]
  rw [Kernel.lintegral_prod_id hg.lintegral_kernel (Kernel.const α ν) x]
  rfl

instance parameterMixture_isMarkovKernel
    (ν : Measure ι) [IsProbabilityMeasure ν]
    (κ : Kernel (ι × α) β) [IsMarkovKernel κ] :
    IsMarkovKernel (parameterMixture ν κ) := by
  unfold parameterMixture
  infer_instance

/-- Reversibility is preserved when a common parameter distribution is
integrated out. -/
theorem isReversible_parameterMixture
    (π : Measure α) [SFinite π]
    (ν : Measure ι) [SFinite ν]
    (κ : Kernel (ι × α) α) [IsSFiniteKernel κ]
    (hrev : ∀ h, Kernel.IsReversible (Kernel.sectR κ h) π) :
    Kernel.IsReversible (parameterMixture ν κ) π := by
  intro A B hA hB
  simp_rw [parameterMixture_apply ν κ _ _ hB,
    parameterMixture_apply ν κ _ _ hA]
  have hmB : Measurable (fun z : α × ι => κ (z.2, z.1) B) :=
    (κ.measurable_coe hB).comp measurable_swap
  have hmA : Measurable (fun z : α × ι => κ (z.2, z.1) A) :=
    (κ.measurable_coe hA).comp measurable_swap
  calc
    (∫⁻ x in A, ∫⁻ h, κ (h, x) B ∂ν ∂π) =
        ∫⁻ h, ∫⁻ x in A, κ (h, x) B ∂π ∂ν :=
      lintegral_lintegral_swap hmB.aemeasurable
    _ = ∫⁻ h, ∫⁻ x in B, κ (h, x) A ∂π ∂ν := by
      apply lintegral_congr
      intro h
      simpa using hrev h hA hB
    _ = ∫⁻ x in B, ∫⁻ h, κ (h, x) A ∂ν ∂π :=
      (lintegral_lintegral_swap hmA.aemeasurable).symm

end Kernel

namespace Measure

variable {ι τ : Type*} [MeasurableSpace ι]

/-- Restrictions of a measure to a finite pairwise-disjoint measurable family
sum to a submeasure of the original measure. -/
theorem finsetSum_restrict_le_of_pairwiseDisjoint
    (ν : Measure ι) (J : Finset τ) (s : τ → Set ι)
    (hdisj : Set.Pairwise (J : Set τ) (fun i j => Disjoint (s i) (s j)))
    (hmeas : ∀ j ∈ J, MeasurableSet (s j)) :
    (∑ j ∈ J, ν.restrict (s j)) ≤ ν := by
  refine Measure.le_iff.2 ?_
  intro A hA
  rw [Measure.finsetSum_apply]
  simp_rw [Measure.restrict_apply hA]
  rw [← measure_biUnion_finset]
  · apply measure_mono
    apply Set.iUnion₂_subset
    intro j hj
    exact Set.inter_subset_left
  · intro i hi j hj hij
    exact (hdisj hi hj hij).mono Set.inter_subset_right Set.inter_subset_right
  · intro j hj
    exact hA.inter (hmeas j hj)

end Measure

namespace Dirichlet

variable {ι α : Type*} [MeasurableSpace ι] [MeasurableSpace α]

/-- Extended-valued Dirichlet energy.  The `ℝ≥0∞` codomain makes Tonelli's
theorem applicable without a finite-energy hypothesis. -/
def energy (π : Measure α) (K : Kernel α α) (f : α → ℝ) : ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ *
    ∫⁻ x, ∫⁻ y, ENNReal.ofReal ((f x - f y) ^ 2) ∂K x ∂π

lemma measurable_sqDiff {f : α → ℝ} (hf : Measurable f) :
    Measurable (fun z : α × α =>
      ENNReal.ofReal ((f z.1 - f z.2) ^ 2)) := by
  exact ENNReal.measurable_ofReal.comp
    (((hf.comp measurable_fst).sub (hf.comp measurable_snd)).pow_const 2)

/-- Exact mixture--Dirichlet identity in `[0,∞]`. -/
theorem energy_parameterMixture
    (π : Measure α) [SFinite π]
    (ν : Measure ι) [SFinite ν]
    (κ : Kernel (ι × α) α) [IsSFiniteKernel κ]
    (f : α → ℝ) (hf : Measurable f) :
    energy π (Kernel.parameterMixture ν κ) f =
      ∫⁻ h, energy π (Kernel.sectR κ h) f ∂ν := by
  let e : α × α → ℝ≥0∞ := fun z =>
    ENNReal.ofReal ((f z.1 - f z.2) ^ 2)
  have he : Measurable e := measurable_sqDiff hf
  have hInner : Measurable (fun z : ι × α =>
      ∫⁻ y, e (z.2, y) ∂κ z) := by
    exact Measurable.lintegral_kernel_prod_right'
      (κ := κ) (he.comp
        (Measurable.prodMk (measurable_snd.comp measurable_fst) measurable_snd))
  have hOuter : Measurable (fun h : ι =>
      ∫⁻ x, ∫⁻ y, e (x, y) ∂κ (h, x) ∂π) := by
    exact hInner.lintegral_prod_right'
  have hTonelli :
      (∫⁻ x, ∫⁻ y, e (x, y) ∂Kernel.parameterMixture ν κ x ∂π) =
        ∫⁻ h, ∫⁻ x, ∫⁻ y, e (x, y) ∂κ (h, x) ∂π ∂ν := by
    calc
      (∫⁻ x, ∫⁻ y, e (x, y) ∂Kernel.parameterMixture ν κ x ∂π) =
          ∫⁻ x, ∫⁻ h, ∫⁻ y, e (x, y) ∂κ (h, x) ∂ν ∂π := by
        apply lintegral_congr
        intro x
        exact Kernel.lintegral_parameterMixture ν κ x
          (he.comp measurable_prodMk_left)
      _ = ∫⁻ h, ∫⁻ x, ∫⁻ y, e (x, y) ∂κ (h, x) ∂π ∂ν := by
        exact lintegral_lintegral_swap
          ((hInner.comp measurable_swap).aemeasurable)
  change (2 : ℝ≥0∞)⁻¹ *
      (∫⁻ x, ∫⁻ y, e (x, y) ∂Kernel.parameterMixture ν κ x ∂π) =
    ∫⁻ h, (2 : ℝ≥0∞)⁻¹ *
      (∫⁻ x, ∫⁻ y, e (x, y) ∂κ (h, x) ∂π) ∂ν
  rw [lintegral_const_mul (2 : ℝ≥0∞)⁻¹ hOuter]
  exact congrArg (fun z : ℝ≥0∞ => (2 : ℝ≥0∞)⁻¹ * z) hTonelli

/-- Dirichlet energy is monotone in the mixing measure.  In particular,
restricting the step-size distribution to one component cannot increase its
contribution beyond the energy of the full mixture. -/
theorem energy_parameterMixture_mono
    (π : Measure α) [SFinite π]
    (ν₁ ν₂ : Measure ι) [SFinite ν₁] [SFinite ν₂]
    (κ : Kernel (ι × α) α) [IsSFiniteKernel κ]
    (hν : ν₁ ≤ ν₂) (f : α → ℝ) (hf : Measurable f) :
    energy π (Kernel.parameterMixture ν₁ κ) f ≤
      energy π (Kernel.parameterMixture ν₂ κ) f := by
  rw [energy_parameterMixture π ν₁ κ f hf,
    energy_parameterMixture π ν₂ κ f hf]
  exact lintegral_mono' hν le_rfl

/-- A component obtained by restricting the parameter law to a measurable or
nonmeasurable set is automatically dominated by the full mixture energy. -/
theorem energy_parameterMixture_restrict_le
    (π : Measure α) [SFinite π]
    (ν : Measure ι) [SFinite ν]
    (s : Set ι)
    (κ : Kernel (ι × α) α) [IsSFiniteKernel κ]
    (f : α → ℝ) (hf : Measurable f) :
    energy π (Kernel.parameterMixture (ν.restrict s) κ) f ≤
      energy π (Kernel.parameterMixture ν κ) f := by
  exact energy_parameterMixture_mono π (ν.restrict s) ν κ
    Measure.restrict_le_self f hf

/-- Finite component form of the mixture inequality.  It is stated for an
arbitrary family of submeasures; the paper applies it to restrictions of the
uniform step-size law to disjoint intervals. -/
theorem sum_energy_parameterMixture_le
    {τ : Type*} (J : Finset τ)
    (π : Measure α) [SFinite π]
    (ν : Measure ι) [SFinite ν]
    (νj : τ → Measure ι) [∀ j, SFinite (νj j)]
    (κ : Kernel (ι × α) α) [IsSFiniteKernel κ]
    (hν : (∑ j ∈ J, νj j) ≤ ν)
    (f : α → ℝ) (hf : Measurable f) :
    (∑ j ∈ J, energy π (Kernel.parameterMixture (νj j) κ) f) ≤
      energy π (Kernel.parameterMixture ν κ) f := by
  rw [energy_parameterMixture π ν κ f hf]
  simp_rw [energy_parameterMixture π (νj _) κ f hf]
  rw [← lintegral_finsetSum_measure]
  exact lintegral_mono' hν le_rfl

/-- The finite disjoint-set component inequality used in the paper, in its
unnormalized measure form.  Taking `ν` to be the uniform law on `(0,H)` and
`s j = I_j` gives exactly the weighted component inequality after normalizing
each nonzero restriction. -/
theorem sum_energy_parameterMixture_restrict_le
    {τ : Type*} (J : Finset τ)
    (π : Measure α) [SFinite π]
    (ν : Measure ι) [SFinite ν]
    (s : τ → Set ι)
    (κ : Kernel (ι × α) α) [IsSFiniteKernel κ]
    (hdisj : Set.Pairwise (J : Set τ) (fun i j => Disjoint (s i) (s j)))
    (hmeas : ∀ j ∈ J, MeasurableSet (s j))
    (f : α → ℝ) (hf : Measurable f) :
    (∑ j ∈ J,
      energy π (Kernel.parameterMixture (ν.restrict (s j)) κ) f) ≤
      energy π (Kernel.parameterMixture ν κ) f := by
  exact sum_energy_parameterMixture_le J π ν
    (fun j => ν.restrict (s j)) κ
    (Measure.finsetSum_restrict_le_of_pairwiseDisjoint ν J s hdisj hmeas)
    f hf

end Dirichlet

end

end UniformRandomMALA
