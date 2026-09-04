import UniformRandomMALA.Assembly
import UniformRandomMALA.AggregationArithmetic
import UniformRandomMALA.ExceptionalBudgetArithmetic
import UniformRandomMALA.DiscreteTime.StationaryRejection
import UniformRandomMALA.Constants

/-!
# Explicit analytic interfaces

The still-unproved finite discrete-time probability, weak-convergence,
Gaussian-isoperimetric, defective-conductance, and harmonic-aggregation parts
of the paper are not hidden behind proof placeholders.  This file records
them as named, typed propositions.
Concrete target/MALA kernels, stationary edge measures, coarea, and the
geometric ladder are developed separately under `Concrete/`; a future
end-to-end theorem must connect those constructions to the remaining fields
of these structures.

The algebraic main theorem in `MainTheorem.lean` is proved from the final
safe and ladder certificates.  The interfaces below document exactly which
analytic results must be formalized to construct those certificates.
-/

namespace UniformRandomMALA

open scoped BigOperators

noncomputable section

/-- Abstract state-space objects needed by overlap and conductance. -/
structure KernelObjects where
  State : Type
  Kernel : Type
  dist : State → State → ℝ
  mass : Set State → ℝ
  setDistance : Set State → Set State → ℝ
  tv : Kernel → State → State → ℝ
  flow : Kernel → Set State → ℝ
  dirichlet : Kernel → (State → ℝ) → ℝ
  variance : (State → ℝ) → ℝ
  spectralGap : Kernel → ℝ
  reversible : Kernel → Prop
  averagedMALA : ℝ → Kernel
  uniformMALA : ℝ → Kernel

namespace KernelObjects

/-- Three sets form a measurable partition at the level used in the paper. -/
def Partition3 (o : KernelObjects) (A B C : Set o.State) : Prop :=
  Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧ A ∪ B ∪ C = Set.univ

end KernelObjects

/-- Moment-indexed local overlap, Proposition `prop:overlap`. -/
def MomentIndexedLocalOverlap
    (p : Parameters) (o : KernelObjects) : Prop :=
  ∃ cr Cr : ℝ, 0 < cr ∧ 0 < Cr ∧
    ∀ moment t : ℝ, 2 ≤ moment → 0 < t →
      t ≤ cr / (p.L * Real.sqrt (moment * (p.d + moment))) →
      ∃ G : Set o.State,
        o.mass Gᶜ ≤ Real.rpow
          (Cr * p.L * t * Real.sqrt (moment * (p.d + moment))) moment ∧
        ∀ x ∈ G, ∀ y ∈ G,
          o.dist x y ≤ Real.sqrt t / 16 →
          o.tv (o.averagedMALA t) x y ≤ 3 / 4

/-- Global safe overlap, the second assertion of Proposition `prop:overlap`. -/
def GlobalSafeOverlap (p : Parameters) (o : KernelObjects) : Prop :=
  ∀ t : ℝ, 0 < t → t ≤ 1 / (2 * p.L * p.d) →
    ∀ x y : o.State,
      o.dist x y ≤ Real.sqrt t / 16 →
      o.tv (o.averagedMALA t) x y ≤ 3 / 4

/-- The analytic inputs in Appendix B.4 after the stationary rejection
estimate: Markov's good-set bound, nearby Gaussian proposal comparison, the
rejection/TV identity, and the globally safe acceptance estimate.  Their
measure-theoretic proofs remain explicit fields; the final constants and the
two assertions of Proposition 3.2 are assembled below. -/
structure Proposition32Inputs
    (p : Parameters) (o : KernelObjects)
    (s : DiscreteTime.StationaryRejectionObjects) where
  cr : ℝ
  Cr : ℝ
  cr_pos : 0 < cr
  Cr_pos : 0 < Cr
  goodSet : ℝ → ℝ → Set o.State
  exceptionalMass :
    DiscreteTime.StationaryRejectionBound p s →
    ∀ moment t : ℝ, 2 ≤ moment → 0 < t →
      t ≤ cr / (p.L * Real.sqrt (moment * (p.d + moment))) →
      o.mass (goodSet moment t)ᶜ ≤ Real.rpow
        (Cr * p.L * t * Real.sqrt (moment * (p.d + moment))) moment
  localTVRaw :
    ∀ moment t : ℝ, 2 ≤ moment → 0 < t →
      t ≤ cr / (p.L * Real.sqrt (moment * (p.d + moment))) →
      ∀ x ∈ goodSet moment t, ∀ y ∈ goodSet moment t,
        o.dist x y ≤ Real.sqrt t / 16 →
        o.tv (o.averagedMALA t) x y ≤
          (1 / 3 : ℝ) + 1 / 32 + 1 / 3
  safeTVRaw :
    ∀ t : ℝ, 0 < t → t ≤ 1 / (2 * p.L * p.d) →
      ∀ x y : o.State,
        o.dist x y ≤ Real.sqrt t / 16 →
        o.tv (o.averagedMALA t) x y ≤
          2 * (1 - Real.exp (-(1 / 4 : ℝ))) + 1 / 32

namespace Proposition32Inputs

/-- The first assertion of Proposition 3.2. -/
theorem momentIndexedLocalOverlap
    (p : Parameters) (o : KernelObjects)
    (s : DiscreteTime.StationaryRejectionObjects)
    (a : Proposition32Inputs p o s)
    (hrej : DiscreteTime.StationaryRejectionBound p s) :
    MomentIndexedLocalOverlap p o := by
  refine ⟨a.cr, a.Cr, a.cr_pos, a.Cr_pos, ?_⟩
  intro moment t hp ht hstep
  refine ⟨a.goodSet moment t,
    a.exceptionalMass hrej moment t hp ht hstep, ?_⟩
  intro x hx y hy hxy
  calc
    o.tv (o.averagedMALA t) x y ≤
        (1 / 3 : ℝ) + 1 / 32 + 1 / 3 :=
      a.localTVRaw moment t hp ht hstep x hx y hy hxy
    _ = 67 / 96 := moment_overlap_numeric
    _ ≤ 3 / 4 := le_of_lt sixty_seven_over_ninety_six_lt_three_quarters

/-- The globally safe assertion of Proposition 3.2. -/
theorem globalSafeOverlap
    (p : Parameters) (o : KernelObjects)
    (s : DiscreteTime.StationaryRejectionObjects)
    (a : Proposition32Inputs p o s) :
    GlobalSafeOverlap p o := by
  intro t ht hstep x y hxy
  exact le_of_lt (lt_of_le_of_lt
    (a.safeTVRaw t ht hstep x y hxy) safe_overlap_numeric)

/-- Both assertions of Proposition 3.2 in the current draft. -/
theorem proposition32
    (p : Parameters) (o : KernelObjects)
    (s : DiscreteTime.StationaryRejectionObjects)
    (a : Proposition32Inputs p o s)
    (hrej : DiscreteTime.StationaryRejectionBound p s) :
    MomentIndexedLocalOverlap p o ∧ GlobalSafeOverlap p o :=
  ⟨a.momentIndexedLocalOverlap p o s hrej, a.globalSafeOverlap p o s⟩

end Proposition32Inputs

/-- Bakry--Ledoux enlargement, kept as an imported geometric interface. -/
def GaussianEnlargement
    (p : Parameters) (o : KernelObjects)
    (Phi PhiInv : ℝ → ℝ) (enlargement : Set o.State → ℝ → Set o.State) : Prop :=
  ∀ A : Set o.State, ∀ r : ℝ, 0 ≤ r →
    o.mass (enlargement A r) ≥
      Phi (PhiInv (o.mass A) + Real.sqrt p.m * r)

/-- Lemma `lem:gaussian-shift`, abstracted from a concrete normal-CDF API. -/
def GaussianShiftBound (Phi PhiInv : ℝ → ℝ) : Prop :=
  ∀ q s : ℝ, 0 < q → q ≤ 1 / 2 → 0 ≤ s →
    q / 4 * min 1 (s * Real.sqrt (Real.log (1 / q))) ≤
      Phi (PhiInv q + s) - q

/-- Proposition `prop:separated`. -/
def SeparatedSetInequality (p : Parameters) (o : KernelObjects) : Prop :=
  ∀ A B C : Set o.State, ∀ r : ℝ,
    o.Partition3 A B C → 0 ≤ r → o.setDistance A B ≥ r →
    let q := min (o.mass A) (o.mass B)
    0 < q → q ≤ 1 / 2 →
      q / 4 * min 1 (r * Real.sqrt (p.m * Real.log (1 / q))) ≤ o.mass C

/-- Lemma `lem:defective`. -/
def DefectiveConductance (p : Parameters) (o : KernelObjects) : Prop :=
  ∀ K : o.Kernel, ∀ t : ℝ, ∀ G S : Set o.State,
    o.reversible K → 0 < t →
    (∀ x ∈ G, ∀ y ∈ G,
      o.dist x y ≤ Real.sqrt t / 16 → o.tv K x y ≤ 3 / 4) →
    0 < o.mass S → o.mass S ≤ 1 / 2 →
    o.mass Gᶜ ≤ (1 / (2 : ℝ) ^ 13) * o.mass S *
      min 1 (Real.sqrt (p.m * t * Real.log (1 / o.mass S))) →
    (1 / (2 : ℝ) ^ 13) * o.mass S *
      min 1 (Real.sqrt (p.m * t * Real.log (1 / o.mass S))) ≤
      o.flow K S

/-- Theorem `thm:aggregation`, expressed without committing to a kernel API. -/
def ComponentAggregation (o : KernelObjects) : Prop :=
  ∀ N : ℕ, 0 < N →
  ∀ P : o.Kernel, ∀ K : Fin N → o.Kernel,
  ∀ gamma phi : Fin N → ℝ,
    o.reversible P → (∀ j, o.reversible (K j)) →
    (∀ j, 0 < gamma j) → (∀ j, 0 < phi j) →
    (∀ f : o.State → ℝ,
      (∑ j, gamma j * o.dirichlet (K j) f) ≤ o.dirichlet P f) →
    (∀ S : Set o.State, 0 < o.mass S → o.mass S ≤ 1 / 2 →
      ∃ j : Fin N, phi j * o.mass S ≤ o.flow (K j) S) →
    1 / (2 * ∑ j, 1 / (gamma j * (phi j) ^ 2)) ≤ o.spectralGap P


/--
Concrete one-component hypotheses after safe overlap and defective
conductance have been applied.
-/
structure SafeComponentData (p : Parameters) (o : KernelObjects) where
  K : o.Kernel
  targetReversible : o.reversible (o.uniformMALA p.H)
  componentReversible : o.reversible K
  dirichletDomination :
    ∀ f : o.State → ℝ,
      componentWeight p.H p.safeEndpoint * o.dirichlet K f ≤
        o.dirichlet (o.uniformMALA p.H) f
  flowLower :
    ∀ S : Set o.State, 0 < o.mass S → o.mass S ≤ 1 / 2 →
      Real.sqrt (safePhiSq p.m p.safeEndpoint) * o.mass S ≤ o.flow K S

namespace SafeComponentData

/-- Instantiate `thm:aggregation` with the single globally safe component. -/
theorem aggregationLower
    (p : Parameters) (o : KernelObjects) (d : SafeComponentData p o)
    (hagg : ComponentAggregation o) :
    oneComponentAggregation
        (componentWeight p.H p.safeEndpoint)
        (safePhiSq p.m p.safeEndpoint) ≤
      o.spectralGap (o.uniformMALA p.H) := by
  have hphi : 0 < Real.sqrt (safePhiSq p.m p.safeEndpoint) :=
    Real.sqrt_pos.2 p.safePhiSq_pos
  have h := hagg 1 (by norm_num)
    (o.uniformMALA p.H) (fun _ : Fin 1 => d.K)
    (fun _ : Fin 1 => componentWeight p.H p.safeEndpoint)
    (fun _ : Fin 1 => Real.sqrt (safePhiSq p.m p.safeEndpoint))
    d.targetReversible
    (fun _ => d.componentReversible)
    (fun _ => p.safeComponentWeight_pos)
    (fun _ => hphi)
    (fun f => by simpa using d.dirichletDomination f)
    (fun S hS hShalf => by
      refine ⟨0, ?_⟩
      simpa using d.flowLower S hS hShalf)
  simpa [oneComponentAggregation, Real.sq_sqrt p.safePhiSq_nonneg] using h

end SafeComponentData

/--
Concrete finite family used by the geometric moment ladder.  The flow
assignment and Dirichlet domination are the outputs of local overlap,
defective conductance, and disjoint interval selection.
-/
structure LadderComponentData
    (p : Parameters) (o : KernelObjects) (N : ℕ) where
  hN : 0 < N
  K : Fin N → o.Kernel
  gamma : Fin N → ℝ
  phi : Fin N → ℝ
  C : ℝ
  hC : 0 < C
  targetReversible : o.reversible (o.uniformMALA p.H)
  componentReversible : ∀ j, o.reversible (K j)
  gammaPos : ∀ j, 0 < gamma j
  phiPos : ∀ j, 0 < phi j
  dirichletDomination :
    ∀ f : o.State → ℝ,
      (∑ j, gamma j * o.dirichlet (K j) f) ≤
        o.dirichlet (o.uniformMALA p.H) f
  flowAssignment :
    ∀ S : Set o.State, 0 < o.mass S → o.mass S ≤ 1 / 2 →
      ∃ j : Fin N, phi j * o.mass S ≤ o.flow (K j) S
  harmonicPos : 0 < ∑ j, 1 / (gamma j * (phi j) ^ 2)
  harmonicUpper :
    (∑ j, 1 / (gamma j * (phi j) ^ 2)) ≤
      C * p.H * p.L ^ 2 * p.pStar * (p.d + p.pStar) /
        (p.m * p.ladderTheta ^ 2 * p.b0 ^ 2)
  c0_le : p.c0 ≤ 1 / (2 * C)

namespace LadderComponentData

/-- Apply component aggregation and package its output for `Assembly.lean`. -/
def toEvidence
    (p : Parameters) (o : KernelObjects) (N : ℕ)
    (d : LadderComponentData p o N) (hagg : ComponentAggregation o) :
    LadderEvidence p (o.spectralGap (o.uniformMALA p.H)) where
  C := d.C
  harmonic := ∑ j, 1 / (d.gamma j * (d.phi j) ^ 2)
  hC := d.hC
  hharmonic := d.harmonicPos
  harmonicUpper := d.harmonicUpper
  aggregationLower := hagg N d.hN
    (o.uniformMALA p.H) d.K d.gamma d.phi
    d.targetReversible d.componentReversible d.gammaPos d.phiPos
    d.dirichletDomination d.flowAssignment

end LadderComponentData

/-- Lemma `lem:exceptional-budget`. -/
def ExceptionalSetBudget (p : Parameters) : Prop :=
  ∀ moment theta u : ℝ,
    p.pStar ≤ moment → 0 < theta → theta ≤ 1 →
    Real.log 2 ≤ u → u ≤ moment / 2 →
    let t := theta * p.b0 /
      (p.L * Real.sqrt (moment * (p.d + moment)))
    Real.rpow (theta / 16) moment ≤
      (1 / (2 : ℝ) ^ 13) * Real.exp (-u) * Real.sqrt (p.m * t * u) ∧
    p.m * t * u ≤ p.b0 / 2

/-- The final harmonic-sum estimate `lem:ladder-sum`. -/
def HarmonicLadderSum (p : Parameters) : Prop :=
  p.pStar < p.d →
  ∃ J : ℕ, ∃ gamma phiSq : Fin (J + 1) → ℝ,
    (∀ j, 0 < gamma j) ∧ (∀ j, 0 < phiSq j) ∧
    ∃ C : ℝ, 0 < C ∧
      (∑ j, 1 / (gamma j * phiSq j)) ≤
        C * p.H * p.L ^ 2 * p.pStar * (p.d + p.pStar) /
          (p.m * p.ladderTheta ^ 2 * p.b0 ^ 2)

/--
All analytic and measure-theoretic obligations, including the two final
component gap estimates consumed by the algebraic theorem.
-/
structure PaperAnalyticInterfaces (p : Parameters) where
  discreteObjects : DiscreteTime.StationaryRejectionObjects
  discreteStationaryRejection :
    DiscreteTime.StationaryRejectionInterfaces p discreteObjects
  kernelObjects : KernelObjects
  /-- The measure/TV inputs used in Appendix B.4 to finish Proposition 3.2. -/
  proposition32Inputs :
    Proposition32Inputs p kernelObjects discreteObjects
  normalCDF : ℝ → ℝ
  normalQuantile : ℝ → ℝ
  enlargement : Set kernelObjects.State → ℝ → Set kernelObjects.State
  gaussianEnlargement :
    GaussianEnlargement p kernelObjects normalCDF normalQuantile enlargement
  gaussianShift : GaussianShiftBound normalCDF normalQuantile
  /-- Gaussian enlargement plus the Gaussian-shift estimate imply `prop:separated`. -/
  separatedSets :
    GaussianEnlargement p kernelObjects normalCDF normalQuantile enlargement →
    GaussianShiftBound normalCDF normalQuantile →
      SeparatedSetInequality p kernelObjects
  /-- The separated-set inequality implies defective conductance. -/
  defectiveConductance :
    SeparatedSetInequality p kernelObjects →
      DefectiveConductance p kernelObjects
  componentAggregation : ComponentAggregation kernelObjects
  exceptionalBudget : ExceptionalSetBudget p
  harmonicLadderSum : HarmonicLadderSum p
  /--
  Build the globally safe component from safe overlap and defective
  conductance.  This is the measure/kernel bridge in Section 4.1.
  -/
  safeComponent :
    GlobalSafeOverlap p kernelObjects →
    DefectiveConductance p kernelObjects →
      SafeComponentData p kernelObjects
  /-- The common proof constant is below the exact safe coefficient. -/
  c0_le_safe : p.c0 ≤ Real.log 2 / (2 : ℝ) ^ 28
  /--
  Build the finite geometric ladder from all preceding overlap,
  conductance, exceptional-budget, and harmonic-sum inputs.
  -/
  ladderComponents :
    MomentIndexedLocalOverlap p kernelObjects →
    GlobalSafeOverlap p kernelObjects →
    DefectiveConductance p kernelObjects →
    ExceptionalSetBudget p →
    HarmonicLadderSum p →
    ∀ h : p.pStar < p.d,
      Σ N : ℕ, LadderComponentData p kernelObjects N

namespace PaperAnalyticInterfaces

/--
Construct the two raw gap estimates from the component-aggregation lemma
and the concrete safe/ladder component data.
-/
def gapAssembly
    (p : Parameters) (a : PaperAnalyticInterfaces p) :
    GapAssembly p
      (a.kernelObjects.spectralGap (a.kernelObjects.uniformMALA p.H)) := by
  let hRejection :
      DiscreteTime.StationaryRejectionBound p a.discreteObjects :=
    a.discreteStationaryRejection.stationaryRejection
  let hProposition32 :
      MomentIndexedLocalOverlap p a.kernelObjects ∧
        GlobalSafeOverlap p a.kernelObjects :=
    a.proposition32Inputs.proposition32 p a.kernelObjects
      a.discreteObjects hRejection
  let hMoment : MomentIndexedLocalOverlap p a.kernelObjects :=
    hProposition32.1
  let hSafe : GlobalSafeOverlap p a.kernelObjects := hProposition32.2
  let hSeparated : SeparatedSetInequality p a.kernelObjects :=
    a.separatedSets a.gaussianEnlargement a.gaussianShift
  let hDefective : DefectiveConductance p a.kernelObjects :=
    a.defectiveConductance hSeparated
  let safeData : SafeComponentData p a.kernelObjects :=
    a.safeComponent hSafe hDefective
  let ladderData :
      ∀ h : p.pStar < p.d,
        Σ N : ℕ, LadderComponentData p a.kernelObjects N :=
    a.ladderComponents hMoment hSafe hDefective
      a.exceptionalBudget a.harmonicLadderSum
  exact
    { safeAggregation := SafeComponentData.aggregationLower
        p a.kernelObjects safeData a.componentAggregation
      ladder := fun hsmall =>
        let packed := ladderData hsmall
        LadderComponentData.toEvidence
          p a.kernelObjects packed.1 packed.2 a.componentAggregation
      c0_le_safe := a.c0_le_safe
      c0_le_ladder := by
        intro hsmall
        change p.c0 ≤ 1 / (2 * (ladderData hsmall).2.C)
        exact (ladderData hsmall).2.c0_le }

/-- Proposition 3.2, packaged as its moment-indexed and globally safe
assertions, follows from the current elementary stationary-rejection route
and the final Appendix B.4 overlap bridge. -/
theorem elementary_proof_implies_proposition32
    (p : Parameters) (a : PaperAnalyticInterfaces p) :
    MomentIndexedLocalOverlap p a.kernelObjects ∧
      GlobalSafeOverlap p a.kernelObjects := by
  exact a.proposition32Inputs.proposition32 p a.kernelObjects
    a.discreteObjects a.discreteStationaryRejection.stationaryRejection

end PaperAnalyticInterfaces

end

end UniformRandomMALA
