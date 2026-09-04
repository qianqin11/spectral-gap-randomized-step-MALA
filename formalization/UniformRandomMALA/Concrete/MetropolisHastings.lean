import UniformRandomMALA.KernelMixture
import Mathlib.Probability.Kernel.WithDensity

/-!
# A measurable accept--reject construction

This file gives the kernel-theoretic part of the Metropolis--Hastings
construction independently of any particular proposal density.  It is used
later with the Gaussian MALA proposal.  The construction follows the standard
Metropolis--Hastings decomposition into an accepted proposal and a diagonal
rejection measure; see Tierney (1998).
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace MetropolisHastings

variable {α : Type*} [MeasurableSpace α]

/-! ## Kernels given by a density over a common base measure -/

/-- A transition kernel whose density with respect to `μ` is `r x y`. -/
def densityKernel (μ : Measure α) [SFinite μ]
    (r : α → α → ℝ≥0∞) : Kernel α α :=
  Kernel.withDensity (Kernel.const α μ) r

lemma densityKernel_apply (μ : Measure α) [SFinite μ]
    (r : α → α → ℝ≥0∞) (hr : Measurable (Function.uncurry r))
    (x : α) (s : Set α) :
    densityKernel μ r x s = ∫⁻ y in s, r x y ∂μ := by
  rw [densityKernel, Kernel.withDensity_apply' (Kernel.const α μ) hr x s]
  rfl

/-- Pointwise detailed balance of densities implies kernel reversibility.
This is the common-measure form of Tonelli's theorem used by continuous-state
Metropolis--Hastings kernels. -/
theorem densityKernel_isReversible
    (μ : Measure α) [SFinite μ]
    (ρ : α → ℝ≥0∞) (r : α → α → ℝ≥0∞)
    (hρ : Measurable ρ) (hr : Measurable (Function.uncurry r))
    (hbalance : ∀ x y, ρ x * r x y = ρ y * r y x) :
    Kernel.IsReversible (densityKernel μ r) (μ.withDensity ρ) := by
  have hrx (x : α) : Measurable (r x) :=
    hr.comp (measurable_const.prodMk measurable_id)
  have hkernel (s : Set α) (hs : MeasurableSet s) :
      Measurable (fun x => densityKernel μ r x s) :=
    (densityKernel μ r).measurable_coe hs
  intro A B hA hB
  rw [setLIntegral_withDensity_eq_setLIntegral_mul μ hρ (hkernel B hB) hA,
    setLIntegral_withDensity_eq_setLIntegral_mul μ hρ (hkernel A hA) hB]
  simp_rw [densityKernel_apply μ r hr]
  have hmul (x : α) (s : Set α) :
      ρ x * (∫⁻ y in s, r x y ∂μ) = ∫⁻ y in s, ρ x * r x y ∂μ := by
    exact (lintegral_const_mul (ρ x) (hrx x)).symm
  simp_rw [Pi.mul_apply, hmul]
  let e : α × α → ℝ≥0∞ := fun z => ρ z.1 * r z.1 z.2
  have he : Measurable e :=
    (hρ.comp measurable_fst).mul hr
  calc
    (∫⁻ x in A, ∫⁻ y in B, ρ x * r x y ∂μ ∂μ) =
        ∫⁻ z in A ×ˢ B, e z ∂(μ.prod μ) := by
      exact (setLIntegral_prod e he.aemeasurable.restrict).symm
    _ = ∫⁻ y in B, ∫⁻ x in A, ρ x * r x y ∂μ ∂μ := by
      exact setLIntegral_prod_symm e he.aemeasurable.restrict
    _ = ∫⁻ y in B, ∫⁻ x in A, ρ y * r y x ∂μ ∂μ := by
      apply lintegral_congr
      intro y
      apply lintegral_congr
      intro x
      exact hbalance x y

/-! ## Metropolis acceptance algebra -/

/-- Unnormalized oriented edge density `ρ(x) q(x,y)`. -/
def edgeDensity (ρ : α → ℝ≥0∞) (q : α → α → ℝ≥0∞)
    (x y : α) : ℝ≥0∞ :=
  ρ x * q x y

/-- Metropolis acceptance probability `min (1, edge(y,x)/edge(x,y))`. -/
def acceptance (ρ : α → ℝ≥0∞) (q : α → α → ℝ≥0∞)
    (x y : α) : ℝ≥0∞ :=
  (edgeDensity ρ q y x / edgeDensity ρ q x y) ⊓ 1

lemma measurable_uncurry_acceptance
    (ρ : α → ℝ≥0∞) (q : α → α → ℝ≥0∞)
    (hρ : Measurable ρ) (hq : Measurable (Function.uncurry q)) :
    Measurable (Function.uncurry (acceptance ρ q)) := by
  have hedge : Measurable (Function.uncurry (edgeDensity ρ q)) :=
    (hρ.comp measurable_fst).mul hq
  exact (hedge.comp measurable_swap).div hedge |>.inf measurable_const

omit [MeasurableSpace α] in
lemma acceptance_le_one
    (ρ : α → ℝ≥0∞) (q : α → α → ℝ≥0∞) (x y : α) :
    acceptance ρ q x y ≤ 1 :=
  inf_le_right

omit [MeasurableSpace α] in
lemma edgeDensity_mul_acceptance
    (ρ : α → ℝ≥0∞) (q : α → α → ℝ≥0∞)
    (hpos : ∀ x y, edgeDensity ρ q x y ≠ 0)
    (htop : ∀ x y, edgeDensity ρ q x y ≠ ∞)
    (x y : α) :
    edgeDensity ρ q x y * acceptance ρ q x y =
      edgeDensity ρ q x y ⊓ edgeDensity ρ q y x := by
  rw [acceptance, mul_min,
    ENNReal.mul_div_cancel (hpos x y) (htop x y), mul_one]
  exact min_comm _ _

omit [MeasurableSpace α] in
lemma acceptedDensity_balance
    (ρ : α → ℝ≥0∞) (q : α → α → ℝ≥0∞)
    (hpos : ∀ x y, edgeDensity ρ q x y ≠ 0)
    (htop : ∀ x y, edgeDensity ρ q x y ≠ ∞)
    (x y : α) :
    ρ x * (q x y * acceptance ρ q x y) =
      ρ y * (q y x * acceptance ρ q y x) := by
  rw [← mul_assoc, ← mul_assoc]
  rw [show ρ x * q x y = edgeDensity ρ q x y by rfl,
    show ρ y * q y x = edgeDensity ρ q y x by rfl]
  rw [edgeDensity_mul_acceptance ρ q hpos htop,
    edgeDensity_mul_acceptance ρ q hpos htop]
  exact min_comm _ _

/-- Total accepted mass from `x`. -/
def acceptanceMass (q : Kernel α α) (a : α → α → ℝ≥0∞) (x : α) : ℝ≥0∞ :=
  ∫⁻ y, a x y ∂q x

/-- The accepted part of a proposal kernel. -/
def accepted (q : Kernel α α) [IsSFiniteKernel q]
    (a : α → α → ℝ≥0∞) : Kernel α α :=
  Kernel.withDensity q a

/-- The diagonal rejection part. -/
def rejected (q : Kernel α α) (a : α → α → ℝ≥0∞) : Kernel α α :=
  Kernel.withDensity Kernel.id
    (fun x _ => 1 - acceptanceMass q a x)

/-- Accept a proposal with density `a x y` and otherwise stay at `x`. -/
def kernel (q : Kernel α α) [IsSFiniteKernel q]
    (a : α → α → ℝ≥0∞) : Kernel α α :=
  accepted q a + rejected q a

/-- The accepted Metropolis density is reversible because its edge density is
the symmetric minimum of the two oriented proposal flows. -/
theorem accepted_densityKernel_isReversible
    (μ : Measure α) [SFinite μ]
    (ρ : α → ℝ≥0∞) (q : α → α → ℝ≥0∞)
    [IsSFiniteKernel (densityKernel μ q)]
    (hρ : Measurable ρ) (hq : Measurable (Function.uncurry q))
    (hpos : ∀ x y, edgeDensity ρ q x y ≠ 0)
    (htop : ∀ x y, edgeDensity ρ q x y ≠ ∞) :
    Kernel.IsReversible
      (accepted (densityKernel μ q) (acceptance ρ q))
      (μ.withDensity ρ) := by
  have ha : Measurable (Function.uncurry (acceptance ρ q)) :=
    measurable_uncurry_acceptance ρ q hρ hq
  let r : α → α → ℝ≥0∞ := fun x y => q x y * acceptance ρ q x y
  have hr : Measurable (Function.uncurry r) := hq.mul ha
  have heq : accepted (densityKernel μ q) (acceptance ρ q) = densityKernel μ r := by
    ext x : 1
    rw [accepted, Kernel.withDensity_apply _ ha]
    rw [densityKernel, Kernel.withDensity_apply _ hq]
    rw [densityKernel, Kernel.withDensity_apply _ hr]
    simp only [Kernel.const_apply]
    change (μ.withDensity (q x)).withDensity (acceptance ρ q x) =
      μ.withDensity (q x * acceptance ρ q x)
    exact (withDensity_mul μ
      (Measurable.of_uncurry_left hq)
      (Measurable.of_uncurry_left ha)).symm
  rw [heq]
  exact densityKernel_isReversible μ ρ r hρ hr
    (acceptedDensity_balance ρ q hpos htop)

theorem measurable_acceptanceMass
    (q : Kernel α α) [IsSFiniteKernel q] (a : α → α → ℝ≥0∞)
    (ha : Measurable (Function.uncurry a)) :
    Measurable (acceptanceMass q a) := by
  exact ha.lintegral_kernel_prod_right'

theorem measurable_rejectionDensity
    (q : Kernel α α) [IsSFiniteKernel q] (a : α → α → ℝ≥0∞)
    (ha : Measurable (Function.uncurry a)) :
    Measurable (Function.uncurry
      (fun x (_y : α) => 1 - acceptanceMass q a x)) := by
  change Measurable (fun z : α × α => 1 - acceptanceMass q a z.1)
  exact measurable_const.sub
    ((measurable_acceptanceMass q a ha).comp measurable_fst)

theorem acceptanceMass_le_one
    (q : Kernel α α) [IsMarkovKernel q]
    (a : α → α → ℝ≥0∞) (ha_le_one : ∀ x y, a x y ≤ 1)
    (x : α) : acceptanceMass q a x ≤ 1 := by
  calc
    acceptanceMass q a x ≤ ∫⁻ _y, (1 : ℝ≥0∞) ∂q x := by
      exact lintegral_mono fun y => ha_le_one x y
    _ = 1 := by simp

theorem accepted_apply_univ
    (q : Kernel α α) [IsSFiniteKernel q]
    (a : α → α → ℝ≥0∞)
    (ha : Measurable (Function.uncurry a)) (x : α) :
    accepted q a x Set.univ = acceptanceMass q a x := by
  rw [accepted, Kernel.withDensity_apply' q ha x Set.univ]
  simp [acceptanceMass]

theorem rejected_apply_univ
    (q : Kernel α α) [IsSFiniteKernel q] (a : α → α → ℝ≥0∞)
    (ha : Measurable (Function.uncurry a)) (x : α) :
    rejected q a x Set.univ = 1 - acceptanceMass q a x := by
  rw [rejected, Kernel.withDensity_apply' Kernel.id
    (measurable_rejectionDensity q a ha) x Set.univ]
  simp [Kernel.id]

theorem rejected_apply
    (q : Kernel α α) [IsSFiniteKernel q]
    (a : α → α → ℝ≥0∞)
    (ha : Measurable (Function.uncurry a)) (x : α)
    (B : Set α) (hB : MeasurableSet B) :
    rejected q a x B =
      B.indicator (fun _ => 1 - acceptanceMass q a x) x := by
  classical
  rw [rejected, Kernel.withDensity_apply' Kernel.id
    (measurable_rejectionDensity q a ha) x B]
  rw [Kernel.id_apply, setLIntegral_dirac' measurable_const hB]
  by_cases hx : x ∈ B <;> simp [Set.indicator, hx]

/-- The rejection part is supported on the diagonal and is therefore
reversible with respect to every measure. -/
theorem rejected_isReversible
    (π : Measure α) (q : Kernel α α) [IsSFiniteKernel q]
    (a : α → α → ℝ≥0∞)
    (ha : Measurable (Function.uncurry a)) :
    Kernel.IsReversible (rejected q a) π := by
  intro A B hA hB
  simp_rw [rejected_apply q a ha _ _ hB,
    rejected_apply q a ha _ _ hA]
  let r : α → ℝ≥0∞ := fun x => 1 - acceptanceMass q a x
  change (∫⁻ x in A, B.indicator r x ∂π) =
    ∫⁻ x in B, A.indicator r x ∂π
  calc
    (∫⁻ x in A, B.indicator r x ∂π) =
        ∫⁻ x, (A ∩ B).indicator r x ∂π := by
      rw [← lintegral_indicator hA, Set.indicator_indicator]
    _ = ∫⁻ x, (B ∩ A).indicator r x ∂π := by rw [Set.inter_comm A B]
    _ = ∫⁻ x in B, A.indicator r x ∂π := by
      rw [← Set.indicator_indicator, lintegral_indicator hB]

/-- Adding the diagonal rejection part preserves reversibility. -/
theorem kernel_isReversible
    (π : Measure α) (q : Kernel α α) [IsSFiniteKernel q]
    (a : α → α → ℝ≥0∞)
    (ha : Measurable (Function.uncurry a))
    (haccepted : Kernel.IsReversible (accepted q a) π) :
    Kernel.IsReversible (kernel q a) π := by
  intro A B hA hB
  simp_rw [kernel, add_apply, Measure.add_apply]
  rw [lintegral_add_left ((accepted q a).measurable_coe hB),
    lintegral_add_left ((accepted q a).measurable_coe hA),
    haccepted hA hB,
    rejected_isReversible π q a ha hA hB]

instance kernel_isMarkovKernel
    (q : Kernel α α) [IsMarkovKernel q]
    (a : α → α → ℝ≥0∞)
    [ha : Fact (Measurable (Function.uncurry a))]
    [ha_le_one : Fact (∀ x y, a x y ≤ 1)] :
    IsMarkovKernel (kernel q a) := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [kernel, add_apply, Measure.add_apply,
    accepted_apply_univ q a ha.out x,
    rejected_apply_univ q a ha.out x]
  exact add_tsub_cancel_of_le (acceptanceMass_le_one q a ha_le_one.out x)

end MetropolisHastings

end

end UniformRandomMALA
