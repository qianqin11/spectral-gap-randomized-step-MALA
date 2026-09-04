import UniformRandomMALA.KernelMixture
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Stationary flow and conductance

This file gives the set-wise objects used in the conductance/coarea part of
the paper directly in terms of a measure and a Markov kernel.  No analytic
interface is used here: reversibility is Mathlib's equality of the two
set-wise stationary flows.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace Concrete

variable {α : Type*} [MeasurableSpace α]

/-- The stationary edge measure `π(dx) K(x,dy)`. -/
def edgeMeasure (π : Measure α) (K : Kernel α α) : Measure (α × α) :=
  π ⊗ₘ K

/-- Stationary mass transported from `A` to `B` in one kernel step. -/
def flow (π : Measure α) (K : Kernel α α) (A B : Set α) : ℝ≥0∞ :=
  ∫⁻ x in A, K x B ∂π

/-- The stationary one-step flow crossing the cut `A | Aᶜ`. -/
def boundaryFlow (π : Measure α) (K : Kernel α α) (A : Set α) : ℝ≥0∞ :=
  flow π K A Aᶜ

/-- A Markov transition carries at most the stationary mass of its source
set.  Keeping this elementary estimate next to `flow` makes all later
`ENNReal.toReal` conversions explicit and local. -/
theorem flow_le_measure_left
    (π : Measure α) (K : Kernel α α) [IsMarkovKernel K]
    (A B : Set α) (hA : MeasurableSet A) :
    flow π K A B ≤ π A := by
  calc
    flow π K A B ≤ ∫⁻ _x in A, (1 : ℝ≥0∞) ∂π := by
      apply setLIntegral_mono' hA
      exact fun x _hx => prob_le_one (μ := K x)
    _ = π A := by simp

theorem flow_ne_top
    (π : Measure α) [IsFiniteMeasure π]
    (K : Kernel α α) [IsMarkovKernel K]
    (A B : Set α) (hA : MeasurableSet A) :
    flow π K A B ≠ ∞ := by
  exact ne_of_lt ((flow_le_measure_left π K A B hA).trans_lt
    (measure_lt_top π A))

theorem edgeMeasure_apply_prod
    (π : Measure α) [SFinite π]
    (K : Kernel α α) [IsSFiniteKernel K]
    {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    edgeMeasure π K (A ×ˢ B) = flow π K A B := by
  exact Measure.compProd_apply_prod hA hB

/-- Reversibility is precisely symmetry of the measurable set-wise flow. -/
theorem flow_symm
    (π : Measure α) (K : Kernel α α)
    (hrev : Kernel.IsReversible K π)
    {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    flow π K A B = flow π K B A := by
  exact hrev hA hB

/-- For a finite stationary measure and a Markov kernel, detailed balance
upgrades from rectangles to symmetry of the entire stationary edge
measure. -/
theorem edgeMeasure_map_swap
    (π : Measure α) [IsFiniteMeasure π]
    (K : Kernel α α) [IsMarkovKernel K]
    (hrev : Kernel.IsReversible K π) :
    (edgeMeasure π K).map Prod.swap = edgeMeasure π K := by
  letI : IsFiniteMeasure (edgeMeasure π K) :=
    ⟨by
      rw [edgeMeasure, Measure.compProd_apply_univ]
      exact measure_lt_top π Set.univ⟩
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.map_apply measurable_swap (hA.prod hB), Set.preimage_swap_prod,
    edgeMeasure_apply_prod π K hB hA, edgeMeasure_apply_prod π K hA hB]
  exact hrev hB hA

/-- Integration against a reversible stationary edge measure is unchanged
when the two endpoints are exchanged. -/
theorem lintegral_edgeMeasure_swap
    (π : Measure α) [IsFiniteMeasure π]
    (K : Kernel α α) [IsMarkovKernel K]
    (hrev : Kernel.IsReversible K π)
    {g : α × α → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ z, g (z.2, z.1) ∂edgeMeasure π K) =
      ∫⁻ z, g z ∂edgeMeasure π K := by
  calc
    (∫⁻ z, g (z.2, z.1) ∂edgeMeasure π K) =
        ∫⁻ z, g z ∂(edgeMeasure π K).map Prod.swap :=
      (lintegral_map hg measurable_swap).symm
    _ = ∫⁻ z, g z ∂edgeMeasure π K := by
      rw [edgeMeasure_map_swap π K hrev]

/-- The first marginal of the stationary edge measure is the stationary
measure.  This integral form is more convenient than repeatedly rewriting
through `Measure.fst`. -/
theorem lintegral_edgeMeasure_fst
    (π : Measure α) [IsFiniteMeasure π]
    (K : Kernel α α) [IsMarkovKernel K]
    {g : α → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ z, g z.1 ∂edgeMeasure π K) = ∫⁻ x, g x ∂π := by
  calc
    (∫⁻ z, g z.1 ∂edgeMeasure π K) =
        ∫⁻ x, g x ∂(edgeMeasure π K).fst :=
      (lintegral_map hg measurable_fst).symm
    _ = ∫⁻ x, g x ∂π := by
      rw [edgeMeasure, Measure.fst_compProd]

/-- Reversibility makes the second edge marginal equal to the first one. -/
theorem lintegral_edgeMeasure_snd
    (π : Measure α) [IsFiniteMeasure π]
    (K : Kernel α α) [IsMarkovKernel K]
    (hrev : Kernel.IsReversible K π)
    {g : α → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ z, g z.2 ∂edgeMeasure π K) = ∫⁻ x, g x ∂π := by
  calc
    (∫⁻ z, g z.2 ∂edgeMeasure π K) =
        ∫⁻ z, g z.1 ∂edgeMeasure π K :=
      lintegral_edgeMeasure_swap π K hrev (hg.comp measurable_fst)
    _ = ∫⁻ x, g x ∂π := lintegral_edgeMeasure_fst π K hg

/-- The squared endpoint sum has edge second moment at most four times the
stationary second moment.  This is the elementary `(a+b)² ≤ 2(a²+b²)` block
used after Cauchy--Schwarz in the coarea argument. -/
theorem lintegral_edgeMeasure_sq_add_le_four
    (π : Measure α) [IsFiniteMeasure π]
    (K : Kernel α α) [IsMarkovKernel K]
    (hrev : Kernel.IsReversible K π)
    (g : α → ℝ) (hg : Measurable g) :
    (∫⁻ z, ENNReal.ofReal ((g z.1 + g z.2) ^ 2) ∂edgeMeasure π K) ≤
      (4 : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂π := by
  let s : α → ℝ≥0∞ := fun x => ENNReal.ofReal (g x ^ 2)
  have hs : Measurable s :=
    ENNReal.measurable_ofReal.comp (hg.pow_const 2)
  calc
    (∫⁻ z, ENNReal.ofReal ((g z.1 + g z.2) ^ 2) ∂edgeMeasure π K) ≤
        ∫⁻ z, (2 : ℝ≥0∞) * (s z.1 + s z.2) ∂edgeMeasure π K := by
      apply lintegral_mono
      intro z
      calc
        ENNReal.ofReal ((g z.1 + g z.2) ^ 2) ≤
            ENNReal.ofReal (2 * (g z.1 ^ 2 + g z.2 ^ 2)) := by
          apply ENNReal.ofReal_le_ofReal
          nlinarith [sq_nonneg (g z.1 - g z.2)]
        _ = (2 : ℝ≥0∞) * (s z.1 + s z.2) := by
          simp only [s]
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
          norm_num
    _ = (2 : ℝ≥0∞) *
        ((∫⁻ z, s z.1 ∂edgeMeasure π K) +
          ∫⁻ z, s z.2 ∂edgeMeasure π K) := by
      rw [lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
      exact congrArg ((2 : ℝ≥0∞) * ·)
        (lintegral_add_left (hs.comp measurable_fst) (fun z => s z.2))
    _ = (4 : ℝ≥0∞) * ∫⁻ x, s x ∂π := by
      rw [lintegral_edgeMeasure_fst π K hs,
        lintegral_edgeMeasure_snd π K hrev hs]
      ring
    _ = (4 : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂π := rfl

/-- The nested-integral definition of Dirichlet energy is the integral of
the squared increment against the stationary edge measure. -/
theorem energy_eq_edgeMeasure_lintegral
    (π : Measure α) [SFinite π]
    (K : Kernel α α) [IsSFiniteKernel K]
    (f : α → ℝ) (hf : Measurable f) :
    Dirichlet.energy π K f =
      (2 : ℝ≥0∞)⁻¹ *
        ∫⁻ z, ENNReal.ofReal ((f z.1 - f z.2) ^ 2) ∂edgeMeasure π K := by
  unfold Dirichlet.energy edgeMeasure
  rw [Measure.lintegral_compProd (Dirichlet.measurable_sqDiff hf)]

lemma ofReal_sub_add_ofReal_sub_rev (a b : ℝ) :
    ENNReal.ofReal (a - b) + ENNReal.ofReal (b - a) =
      ENNReal.ofReal |a - b| := by
  by_cases h : b ≤ a
  · have hab : 0 ≤ a - b := sub_nonneg.mpr h
    have hba : b - a ≤ 0 := sub_nonpos.mpr h
    rw [ENNReal.ofReal_of_nonpos hba, add_zero, abs_of_nonneg hab]
  · have hab : a - b ≤ 0 := sub_nonpos.mpr (le_of_not_ge h)
    have hba : 0 ≤ b - a := sub_nonneg.mpr (le_of_not_ge h)
    rw [ENNReal.ofReal_of_nonpos hab, zero_add,
      abs_of_nonpos hab, neg_sub]

/-- Symmetry turns the oriented positive square difference into half of the
unoriented absolute square difference.  This is the algebraic half of the
reversible coarea identity used in the component-aggregation proof. -/
theorem half_lintegral_abs_sqDiff_eq_lintegral_pos_sqDiff
    (π : Measure α) [IsFiniteMeasure π]
    (K : Kernel α α) [IsMarkovKernel K]
    (hrev : Kernel.IsReversible K π)
    (g : α → ℝ) (hg : Measurable g) :
    (2 : ℝ≥0∞)⁻¹ *
        (∫⁻ z, ENNReal.ofReal |g z.1 ^ 2 - g z.2 ^ 2| ∂edgeMeasure π K) =
      ∫⁻ z, ENNReal.ofReal (g z.1 ^ 2 - g z.2 ^ 2) ∂edgeMeasure π K := by
  let p : α × α → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (g z.1 ^ 2 - g z.2 ^ 2)
  have hp : Measurable p := by
    exact ENNReal.measurable_ofReal.comp
      (((hg.comp measurable_fst).pow_const 2).sub
        ((hg.comp measurable_snd).pow_const 2))
  have habs :
      (∫⁻ z, ENNReal.ofReal |g z.1 ^ 2 - g z.2 ^ 2| ∂edgeMeasure π K) =
        (2 : ℝ≥0∞) * ∫⁻ z, p z ∂edgeMeasure π K := by
    calc
      (∫⁻ z, ENNReal.ofReal |g z.1 ^ 2 - g z.2 ^ 2| ∂edgeMeasure π K) =
          ∫⁻ z, p z + p (z.2, z.1) ∂edgeMeasure π K := by
        apply lintegral_congr
        intro z
        exact (ofReal_sub_add_ofReal_sub_rev (g z.1 ^ 2) (g z.2 ^ 2)).symm
      _ = (∫⁻ z, p z ∂edgeMeasure π K) +
          ∫⁻ z, p (z.2, z.1) ∂edgeMeasure π K := by
        rw [lintegral_add_left hp]
      _ = (∫⁻ z, p z ∂edgeMeasure π K) +
          ∫⁻ z, p z ∂edgeMeasure π K := by
        rw [lintegral_edgeMeasure_swap π K hrev hp]
      _ = (2 : ℝ≥0∞) * ∫⁻ z, p z ∂edgeMeasure π K := by
        rw [two_mul]
  rw [habs, ← mul_assoc,
    ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞), one_mul]

/-- Strict superlevel sets of the squared function. -/
def sqSuperlevel (g : α → ℝ) (r : ℝ) : Set α :=
  {x | r < g x ^ 2}

lemma measurableSet_sqSuperlevel
    {g : α → ℝ} (hg : Measurable g) (r : ℝ) :
    MeasurableSet (sqSuperlevel g r) := by
  exact measurableSet_lt measurable_const (hg.pow_const 2)

/-- Measurability in the level parameter of the cut flow through squared
superlevels.  Exposing this fact avoids rebuilding the measurable-section
argument when finite component sums are integrated. -/
theorem measurable_boundaryFlow_sqSuperlevel
    (π : Measure α) [IsFiniteMeasure π]
    (K : Kernel α α) [IsMarkovKernel K]
    (g : α → ℝ) (hg : Measurable g) :
    Measurable (fun r : ℝ => boundaryFlow π K (sqSuperlevel g r)) := by
  let C : Set (ℝ × (α × α)) :=
    {w | w.1 < g w.2.1 ^ 2 ∧ g w.2.2 ^ 2 ≤ w.1}
  have hC : MeasurableSet C := by
    apply MeasurableSet.inter
    · exact measurableSet_lt measurable_fst
        ((hg.comp (measurable_fst.comp measurable_snd)).pow_const 2)
    · exact measurableSet_le
        ((hg.comp (measurable_snd.comp measurable_snd)).pow_const 2)
        measurable_fst
  letI : SFinite (edgeMeasure π K) := by
    unfold edgeMeasure
    infer_instance
  have hm : Measurable (fun r : ℝ =>
      edgeMeasure π K (Prod.mk r ⁻¹' C)) :=
    measurable_measure_prodMk_left hC
  convert hm using 1
  funext r
  rw [show Prod.mk r ⁻¹' C =
      sqSuperlevel g r ×ˢ (sqSuperlevel g r)ᶜ by
        ext z
        simp [C, sqSuperlevel]]
  exact (edgeMeasure_apply_prod π K
    (measurableSet_sqSuperlevel hg r)
    (measurableSet_sqSuperlevel hg r).compl).symm

/-- The oriented coarea/layer-cake identity.  Integrating the flow across
all squared superlevel cuts gives the positive square difference on the
stationary edge measure. -/
theorem lintegral_boundaryFlow_sqSuperlevel
    (π : Measure α) [IsFiniteMeasure π]
    (K : Kernel α α) [IsMarkovKernel K]
    (g : α → ℝ) (hg : Measurable g) :
    (∫⁻ r in Set.Ici (0 : ℝ),
        boundaryFlow π K (sqSuperlevel g r) ∂volume) =
      ∫⁻ z, ENNReal.ofReal (g z.1 ^ 2 - g z.2 ^ 2) ∂edgeMeasure π K := by
  let C : Set (ℝ × (α × α)) :=
    {w | w.1 < g w.2.1 ^ 2 ∧ g w.2.2 ^ 2 ≤ w.1}
  let c : ℝ × (α × α) → ℝ≥0∞ := C.indicator (fun _ => 1)
  have hC : MeasurableSet C := by
    apply MeasurableSet.inter
    · exact measurableSet_lt measurable_fst
        ((hg.comp (measurable_fst.comp measurable_snd)).pow_const 2)
    · exact measurableSet_le
        ((hg.comp (measurable_snd.comp measurable_snd)).pow_const 2)
        measurable_fst
  have hc : Measurable c := measurable_const.indicator hC
  have hc_rectangle (r : ℝ) :
      (fun z => c (r, z)) =
        (sqSuperlevel g r ×ˢ (sqSuperlevel g r)ᶜ).indicator
          (fun _ => (1 : ℝ≥0∞)) := by
    funext z
    simp only [c, C, Set.indicator_apply, Set.mem_ofPred_eq,
      Set.mem_prod, Set.mem_compl_iff, sqSuperlevel]
    by_cases hx : r < g z.1 ^ 2 <;>
      by_cases hy : r < g z.2 ^ 2 <;> simp [hx, hy]
  calc
    (∫⁻ r in Set.Ici (0 : ℝ),
        boundaryFlow π K (sqSuperlevel g r) ∂volume) =
        ∫⁻ r in Set.Ici (0 : ℝ),
          edgeMeasure π K
            (sqSuperlevel g r ×ˢ (sqSuperlevel g r)ᶜ) ∂volume := by
      apply setLIntegral_congr_fun measurableSet_Ici
      intro r hr
      unfold boundaryFlow
      exact (edgeMeasure_apply_prod π K
        (measurableSet_sqSuperlevel hg r)
        (measurableSet_sqSuperlevel hg r).compl).symm
    _ = ∫⁻ r in Set.Ici (0 : ℝ),
          ∫⁻ z, c (r, z) ∂edgeMeasure π K ∂volume := by
      apply setLIntegral_congr_fun measurableSet_Ici
      intro r hr
      change edgeMeasure π K
          (sqSuperlevel g r ×ˢ (sqSuperlevel g r)ᶜ) =
        ∫⁻ z, c (r, z) ∂edgeMeasure π K
      rw [hc_rectangle r,
        lintegral_indicator
          ((measurableSet_sqSuperlevel hg r).prod
            (measurableSet_sqSuperlevel hg r).compl),
        setLIntegral_one]
    _ = ∫⁻ z, ∫⁻ r in Set.Ici (0 : ℝ), c (r, z) ∂volume
          ∂edgeMeasure π K := by
      letI : SFinite (edgeMeasure π K) := by
        unfold edgeMeasure
        infer_instance
      exact lintegral_lintegral_swap hc.aemeasurable
    _ = ∫⁻ z, ENNReal.ofReal (g z.1 ^ 2 - g z.2 ^ 2)
          ∂edgeMeasure π K := by
      apply lintegral_congr
      intro z
      have hc_interval :
          (fun r => c (r, z)) =
            (Set.Ico (g z.2 ^ 2) (g z.1 ^ 2)).indicator
              (fun _ => (1 : ℝ≥0∞)) := by
        funext r
        simp only [c, C, Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_Ico,
          and_comm]
      rw [hc_interval, setLIntegral_indicator measurableSet_Ico]
      have hsubset :
          Set.Ico (g z.2 ^ 2) (g z.1 ^ 2) ⊆ Set.Ici (0 : ℝ) := by
        intro r hr
        exact (sq_nonneg (g z.2)).trans hr.1
      rw [Set.inter_eq_left.mpr hsubset, setLIntegral_one, Real.volume_Ico]

/-- Standard reversible coarea identity for squared superlevel cuts. -/
theorem coarea_sqSuperlevel
    (π : Measure α) [IsFiniteMeasure π]
    (K : Kernel α α) [IsMarkovKernel K]
    (hrev : Kernel.IsReversible K π)
    (g : α → ℝ) (hg : Measurable g) :
    (∫⁻ r in Set.Ici (0 : ℝ),
        boundaryFlow π K (sqSuperlevel g r) ∂volume) =
      (2 : ℝ≥0∞)⁻¹ *
        ∫⁻ z, ENNReal.ofReal |g z.1 ^ 2 - g z.2 ^ 2|
          ∂edgeMeasure π K := by
  calc
    (∫⁻ r in Set.Ici (0 : ℝ),
        boundaryFlow π K (sqSuperlevel g r) ∂volume) =
        ∫⁻ z, ENNReal.ofReal (g z.1 ^ 2 - g z.2 ^ 2)
          ∂edgeMeasure π K :=
      lintegral_boundaryFlow_sqSuperlevel π K g hg
    _ = (2 : ℝ≥0∞)⁻¹ *
        ∫⁻ z, ENNReal.ofReal |g z.1 ^ 2 - g z.2 ^ 2|
          ∂edgeMeasure π K :=
      (half_lintegral_abs_sqDiff_eq_lintegral_pos_sqDiff π K hrev g hg).symm

theorem boundaryFlow_compl
    (π : Measure α) (K : Kernel α α)
    (hrev : Kernel.IsReversible K π)
    {A : Set α} (hA : MeasurableSet A) :
    boundaryFlow π K Aᶜ = boundaryFlow π K A := by
  unfold boundaryFlow
  rw [compl_compl]
  exact flow_symm π K hrev hA.compl hA

/-- A Markov kernel cannot send more stationary mass across a cut than the
mass on the departing side. -/
theorem boundaryFlow_le_measure
    (π : Measure α) (K : Kernel α α) [IsMarkovKernel K]
    {A : Set α} (hA : MeasurableSet A) :
    boundaryFlow π K A ≤ π A := by
  unfold boundaryFlow flow
  calc
    (∫⁻ x in A, K x Aᶜ ∂π) ≤ ∫⁻ _x in A, 1 ∂π :=
      setLIntegral_mono' (μ := π) (s := A) hA
        (fun _x _hx => prob_le_one)
    _ = π A := setLIntegral_one A

/-- `c` is a conductance lower bound if every measurable cut carries at
least `c` times the smaller side of the cut.  The `ℝ≥0∞` statement is valid
without finiteness side conditions. -/
def ConductanceLower (π : Measure α) (K : Kernel α α) (c : ℝ≥0∞) : Prop :=
  ∀ A : Set α, MeasurableSet A →
    c * (π A ⊓ π Aᶜ) ≤ boundaryFlow π K A

/-- Variational conductance: the supremum of all certified lower bounds. -/
def conductance (π : Measure α) (K : Kernel α α) : ℝ≥0∞ :=
  sSup {c : ℝ≥0∞ | ConductanceLower π K c}

lemma conductanceLower_zero (π : Measure α) (K : Kernel α α) :
    ConductanceLower π K 0 := by
  intro A hA
  simp

lemma conductance_nonneg (π : Measure α) (K : Kernel α α) :
    0 ≤ conductance π K := bot_le

/-- Every uniform cut-flow estimate is bounded by the variational
conductance. -/
theorem le_conductance
    (π : Measure α) (K : Kernel α α) {c : ℝ≥0∞}
    (hc : ConductanceLower π K c) :
    c ≤ conductance π K := by
  exact le_sSup hc

/-- A real-valued indicator, convenient for the concrete Dirichlet energy. -/
def indicatorReal (A : Set α) (x : α) : ℝ :=
  by
    classical
    exact if x ∈ A then 1 else 0

lemma measurable_indicatorReal {A : Set α} (hA : MeasurableSet A) :
    Measurable (indicatorReal A : α → ℝ) := by
  classical
  unfold indicatorReal
  exact Measurable.ite hA measurable_const measurable_const

lemma lintegral_sqDiff_indicatorReal_of_mem
    (K : Kernel α α) {A : Set α} (hA : MeasurableSet A)
    {x : α} (hx : x ∈ A) :
    (∫⁻ y, ENNReal.ofReal
        ((indicatorReal A x - indicatorReal A y) ^ 2) ∂K x) =
      K x Aᶜ := by
  classical
  calc
    (∫⁻ y, ENNReal.ofReal
        ((indicatorReal A x - indicatorReal A y) ^ 2) ∂K x) =
        ∫⁻ y, Aᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y ∂K x := by
      apply lintegral_congr
      intro y
      by_cases hy : y ∈ A
      · simp [indicatorReal, hx, hy]
      · simp [indicatorReal, hx, hy]
    _ = ∫⁻ _y in Aᶜ, (1 : ℝ≥0∞) ∂K x :=
      lintegral_indicator hA.compl _
    _ = K x Aᶜ := setLIntegral_one Aᶜ

lemma lintegral_sqDiff_indicatorReal_of_notMem
    (K : Kernel α α) {A : Set α} (hA : MeasurableSet A)
    {x : α} (hx : x ∉ A) :
    (∫⁻ y, ENNReal.ofReal
        ((indicatorReal A x - indicatorReal A y) ^ 2) ∂K x) =
      K x A := by
  classical
  calc
    (∫⁻ y, ENNReal.ofReal
        ((indicatorReal A x - indicatorReal A y) ^ 2) ∂K x) =
        ∫⁻ y, A.indicator (fun _ => (1 : ℝ≥0∞)) y ∂K x := by
      apply lintegral_congr
      intro y
      by_cases hy : y ∈ A
      · simp [indicatorReal, hx, hy]
      · simp [indicatorReal, hx, hy]
    _ = ∫⁻ _y in A, (1 : ℝ≥0∞) ∂K x :=
      lintegral_indicator hA _
    _ = K x A := setLIntegral_one A

/-- The Dirichlet energy of a measurable cut indicator is exactly its
boundary flow for a reversible kernel.  This is the first concrete bridge
between the spectral and conductance variational problems. -/
theorem energy_indicatorReal
    (π : Measure α) (K : Kernel α α)
    (hrev : Kernel.IsReversible K π)
    {A : Set α} (hA : MeasurableSet A) :
    Dirichlet.energy π K (indicatorReal A) = boundaryFlow π K A := by
  let e : α → ℝ≥0∞ := fun x =>
    ∫⁻ y, ENNReal.ofReal
      ((indicatorReal A x - indicatorReal A y) ^ 2) ∂K x
  have h_on_A : (∫⁻ x in A, e x ∂π) = flow π K A Aᶜ := by
    apply setLIntegral_congr_fun hA
    intro x hx
    exact lintegral_sqDiff_indicatorReal_of_mem K hA hx
  have h_on_compl : (∫⁻ x in Aᶜ, e x ∂π) = flow π K Aᶜ A := by
    apply setLIntegral_congr_fun hA.compl
    intro x hx
    exact lintegral_sqDiff_indicatorReal_of_notMem K hA hx
  unfold Dirichlet.energy
  change (2 : ℝ≥0∞)⁻¹ * (∫⁻ x, e x ∂π) = boundaryFlow π K A
  rw [← lintegral_add_compl e hA, h_on_A, h_on_compl,
    flow_symm π K hrev hA.compl hA]
  unfold boundaryFlow
  rw [← two_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞), one_mul]

end Concrete

end

end UniformRandomMALA
