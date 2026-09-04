import UniformRandomMALA.DiscreteTime.EulerRWMPairChain
import UniformRandomMALA.DiscreteTime.ProkhorovBridge
import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# Endpoint-edge coupling with the initial point retained

The pair chain in `EulerRWMPairChain` records only the two current endpoints.
For the weak-limit argument one instead needs a coupling of the two *edge*
laws `(X₀, Xₙ)` and `(Y₀, Yₙ)`.  This file retains the common initial point
outside the pair chain and packages the resulting finite law.

Everything here is finite-time measure and kernel algebra.  In particular,
there is no path-space construction.
-/

namespace UniformRandomMALA

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ProbabilityTheory

noncomputable section

namespace DiscreteTime

open Concrete

variable {d : ℕ}

section ReversibleIterates

variable {E : Type*} [MeasurableSpace E]

/-- Detailed balance in measure form: starting the kernel from the target
restricted to `A` gives the target weighted by the reverse probability of
returning to `A`. -/
lemma reversible_comp_restrict_eq_withDensity
    (K : Kernel E E) [IsMarkovKernel K]
    (mu : Measure E) [IsFiniteMeasure mu]
    (hK : Kernel.IsReversible K mu)
    {A : Set E} (hA : MeasurableSet A) :
    K ∘ₘ mu.restrict A = mu.withDensity (fun y => K y A) := by
  ext B hB
  rw [Measure.bind_apply hB K.aemeasurable,
    withDensity_apply _ hB]
  exact hK hA hB

/-- Commuting reversible Markov kernels have reversible composition.  The
proof is an elementary two-use detailed-balance calculation. -/
lemma isReversible_comp_of_commute
    (K L : Kernel E E) [IsMarkovKernel K] [IsMarkovKernel L]
    (mu : Measure E) [IsFiniteMeasure mu]
    (hK : Kernel.IsReversible K mu)
    (hL : Kernel.IsReversible L mu)
    (hcomm : K ∘ₖ L = L ∘ₖ K) :
    Kernel.IsReversible (K ∘ₖ L) mu := by
  intro A B hA hB
  calc
    (∫⁻ x in A, (K ∘ₖ L) x B ∂mu) =
        ((K ∘ₖ L) ∘ₘ mu.restrict A) B := by
      rw [Measure.bind_apply hB (K ∘ₖ L).aemeasurable]
    _ = (K ∘ₘ (L ∘ₘ mu.restrict A)) B := by
      rw [Measure.comp_assoc]
    _ = (K ∘ₘ mu.withDensity (fun y => L y A)) B := by
      rw [reversible_comp_restrict_eq_withDensity L mu hL hA]
    _ = ∫⁻ y, L y A * K y B ∂mu := by
      rw [Measure.bind_apply hB K.aemeasurable,
        lintegral_withDensity_eq_lintegral_mul mu (L.measurable_coe hA)
          (K.measurable_coe hB)]
      rfl
    _ = ∫⁻ y, K y B * L y A ∂mu := by
      apply lintegral_congr
      intro y
      exact mul_comm _ _
    _ = (L ∘ₘ mu.withDensity (fun y => K y B)) A := by
      rw [Measure.bind_apply hA L.aemeasurable,
        lintegral_withDensity_eq_lintegral_mul mu (K.measurable_coe hB)
          (L.measurable_coe hA)]
      rfl
    _ = (L ∘ₘ (K ∘ₘ mu.restrict B)) A := by
      rw [reversible_comp_restrict_eq_withDensity K mu hK hB]
    _ = ((L ∘ₖ K) ∘ₘ mu.restrict B) A := by
      rw [Measure.comp_assoc]
    _ = ((K ∘ₖ L) ∘ₘ mu.restrict B) A := by rw [hcomm]
    _ = ∫⁻ x in B, (K ∘ₖ L) x A ∂mu := by
      rw [Measure.bind_apply hA (K ∘ₖ L).aemeasurable]

/-- A finite iterate commutes with one further copy of its kernel. -/
lemma finiteKernelIterate_comp_self
    (K : Kernel E E) [IsMarkovKernel K] : ∀ n,
    finiteKernelIterate K n ∘ₖ K =
      K ∘ₖ finiteKernelIterate K n := by
  intro n
  induction n with
  | zero => simp [finiteKernelIterate]
  | succ n ih =>
      simp only [finiteKernelIterate]
      rw [Kernel.comp_assoc, ih, ← Kernel.comp_assoc]

/-- Every finite iterate of a reversible Markov kernel is reversible. -/
lemma finiteKernelIterate_isReversible
    (K : Kernel E E) [IsMarkovKernel K]
    (mu : Measure E) [IsFiniteMeasure mu]
    (hK : Kernel.IsReversible K mu) : ∀ n,
    Kernel.IsReversible (finiteKernelIterate K n) mu := by
  intro n
  induction n with
  | zero =>
      intro A B hA hB
      simp [finiteKernelIterate, Kernel.id_apply, hA, hB, inter_comm]
  | succ n ih =>
      simp only [finiteKernelIterate]
      letI : IsMarkovKernel (finiteKernelIterate K n) := by infer_instance
      exact isReversible_comp_of_commute K (finiteKernelIterate K n)
        mu hK ih (finiteKernelIterate_comp_self K n).symm

end ReversibleIterates

/-- Start the finite pair chain from `(x₀, x₀)`, but expose `x₀` as the input
of the resulting kernel. -/
def diagonalStartedEulerRWMPairKernel
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ) :
    Kernel (State d) (State d × State d) :=
  eulerRWMPairChainKernel V δ n ∘ₖ Kernel.copy (State d)

instance diagonalStartedEulerRWMPairKernel_isMarkovKernel
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ) :
    IsMarkovKernel (diagonalStartedEulerRWMPairKernel V δ n) := by
  unfold diagonalStartedEulerRWMPairKernel
  infer_instance

/-- The RWM terminal marginal of the diagonally started pair kernel is the
finite iterate of the explicit RWM kernel. -/
theorem snd_diagonalStartedEulerRWMPairKernel
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ) :
    Kernel.snd (diagonalStartedEulerRWMPairKernel V δ n) =
      finiteKernelIterate (explicitRWMKernel V δ) n := by
  ext x : 1
  rw [Kernel.snd_apply]
  unfold diagonalStartedEulerRWMPairKernel
  rw [Kernel.copy, Kernel.comp_deterministic_eq_comap,
    Kernel.comap_apply, map_snd_eulerRWMPairChainKernel]
  rfl

/-- The joint finite law of `(x₀, (Xₙ, Yₙ))`, where `x₀` has the target law
and the pair chain starts from `(x₀, x₀)`. -/
def retainedInitialEulerRWMPairMeasure
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ) :
    Measure (State d × (State d × State d)) :=
  (V.target : Measure (State d)) ⊗ₘ
    diagonalStartedEulerRWMPairKernel V δ n

instance retainedInitialEulerRWMPairMeasure_isProbabilityMeasure
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ) :
    IsProbabilityMeasure (retainedInitialEulerRWMPairMeasure V δ n) := by
  unfold retainedInitialEulerRWMPairMeasure
  infer_instance

/-- Projection `(x₀, (x, y)) ↦ (x₀, x)` to the Euler edge. -/
def retainInitialFst {E : Type*} : E × (E × E) → E × E :=
  Prod.map id Prod.fst

/-- Projection `(x₀, (x, y)) ↦ (x₀, y)` to the RWM edge. -/
def retainInitialSnd {E : Type*} : E × (E × E) → E × E :=
  Prod.map id Prod.snd

lemma measurable_retainInitialFst
    {E : Type*} [MeasurableSpace E] : Measurable (@retainInitialFst E) := by
  exact measurable_id.prodMap measurable_fst

lemma measurable_retainInitialSnd
    {E : Type*} [MeasurableSpace E] : Measurable (@retainInitialSnd E) := by
  exact measurable_id.prodMap measurable_snd

/-- The finite Euler edge law `(X₀, Xₙ)`.  It is deliberately defined as a
finite kernel composition, so later work can identify its second endpoint
with any independently developed Euler recursion without changing this
coupling layer. -/
def finiteEulerEdgeMeasure
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ) :
    Measure (State d × State d) :=
  (V.target : Measure (State d)) ⊗ₘ
    Kernel.fst (diagonalStartedEulerRWMPairKernel V δ n)

instance finiteEulerEdgeMeasure_isProbabilityMeasure
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ) :
    IsProbabilityMeasure (finiteEulerEdgeMeasure V δ n) := by
  unfold finiteEulerEdgeMeasure
  infer_instance

/-- The finite stationary RWM edge law `(Y₀, Yₙ)`. -/
def finiteRWMEdgeMeasure
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ) :
    Measure (State d × State d) :=
  (V.target : Measure (State d)) ⊗ₘ
    finiteKernelIterate (explicitRWMKernel V δ) n

instance finiteRWMEdgeMeasure_isProbabilityMeasure
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ) :
    IsProbabilityMeasure (finiteRWMEdgeMeasure V δ n) := by
  letI : IsMarkovKernel (explicitRWMKernel V δ) :=
    explicitRWMKernel_isMarkovKernel V δ
  letI : IsMarkovKernel
      (finiteKernelIterate (explicitRWMKernel V δ) n) := by
    infer_instance
  unfold finiteRWMEdgeMeasure
  infer_instance

/-- The retained-initial law pushes forward to the Euler edge law. -/
theorem map_retainInitialFst_retainedInitialEulerRWMPairMeasure
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ) :
    Measure.map retainInitialFst
        (retainedInitialEulerRWMPairMeasure V δ n) =
      finiteEulerEdgeMeasure V δ n := by
  calc
    Measure.map retainInitialFst
        (retainedInitialEulerRWMPairMeasure V δ n) =
        (V.target : Measure (State d)) ⊗ₘ
          (diagonalStartedEulerRWMPairKernel V δ n).map Prod.fst :=
      (Measure.compProd_map measurable_fst).symm
    _ = finiteEulerEdgeMeasure V δ n := by
      rw [← Kernel.fst_eq]
      rfl

/-- The retained-initial law pushes forward to the stationary RWM edge law. -/
theorem map_retainInitialSnd_retainedInitialEulerRWMPairMeasure
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ) :
    Measure.map retainInitialSnd
        (retainedInitialEulerRWMPairMeasure V δ n) =
      finiteRWMEdgeMeasure V δ n := by
  calc
    Measure.map retainInitialSnd
        (retainedInitialEulerRWMPairMeasure V δ n) =
        (V.target : Measure (State d)) ⊗ₘ
          (diagonalStartedEulerRWMPairKernel V δ n).map Prod.snd :=
      (Measure.compProd_map measurable_snd).symm
    _ = (V.target : Measure (State d)) ⊗ₘ
          Kernel.snd (diagonalStartedEulerRWMPairKernel V δ n) := by
      rw [Kernel.snd_eq]
    _ = finiteRWMEdgeMeasure V δ n := by
      rw [snd_diagonalStartedEulerRWMPairKernel]
      rfl

/-- Duplicate the retained initial point into the two edges, sending
`(x₀, (x, y))` to `((x₀, x), (x₀, y))`. -/
def retainedInitialEdges {E : Type*} :
    E × (E × E) → (E × E) × (E × E) :=
  fun z => (retainInitialFst z, retainInitialSnd z)

lemma measurable_retainedInitialEdges
    {E : Type*} [MeasurableSpace E] :
    Measurable (@retainedInitialEdges E) :=
  measurable_retainInitialFst.prodMk measurable_retainInitialSnd

/-- Because the two edges share their initial endpoint, their product-space
distance is exactly the distance between the two terminal endpoints. -/
theorem dist_retainInitialFst_retainInitialSnd
    (z : State d × (State d × State d)) :
    dist (retainInitialFst z) (retainInitialSnd z) =
      dist z.2.1 z.2.2 := by
  simp [retainInitialFst, retainInitialSnd, Prod.dist_eq]

/-- Squared-distance form matching the norm convention used by the pair
recurrence. -/
theorem sq_dist_retainInitialFst_retainInitialSnd_eq_norm_sq
    (z : State d × (State d × State d)) :
    dist (retainInitialFst z) (retainInitialSnd z) ^ 2 =
      ‖z.2.1 - z.2.2‖ ^ 2 := by
  simpa only [dist_eq_norm] using congrArg (fun r : ℝ => r ^ 2)
    (dist_retainInitialFst_retainInitialSnd z)

/-- A literal coupling of the finite Euler and RWM edge laws.  Its sample
space contains two copies of the initial point, but they agree everywhere by
construction. -/
def finiteEulerRWMEdgeCouplingMeasure
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ) :
    Measure ((State d × State d) × (State d × State d)) :=
  Measure.map retainedInitialEdges
    (retainedInitialEulerRWMPairMeasure V δ n)

instance finiteEulerRWMEdgeCouplingMeasure_isProbabilityMeasure
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ) :
    IsProbabilityMeasure (finiteEulerRWMEdgeCouplingMeasure V δ n) := by
  constructor
  rw [finiteEulerRWMEdgeCouplingMeasure,
    Measure.map_apply measurable_retainedInitialEdges MeasurableSet.univ]
  simp

/-- The second-moment cost of the edge coupling is exactly the terminal
pair-chain second-moment cost. -/
theorem lintegral_sq_dist_finiteEulerRWMEdgeCouplingMeasure
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ) :
    (∫⁻ e : (State d × State d) × (State d × State d),
        ENNReal.ofReal (dist e.1 e.2 ^ 2)
        ∂finiteEulerRWMEdgeCouplingMeasure V δ n) =
      ∫⁻ z : State d × (State d × State d),
        ENNReal.ofReal (dist z.2.1 z.2.2 ^ 2)
        ∂retainedInitialEulerRWMPairMeasure V δ n := by
  rw [finiteEulerRWMEdgeCouplingMeasure]
  have hcost : Measurable
      (fun e : (State d × State d) × (State d × State d) =>
        ENNReal.ofReal (dist e.1 e.2 ^ 2)) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_fst.dist continuous_snd).pow 2).measurable
  calc
    (∫⁻ e : (State d × State d) × (State d × State d),
        ENNReal.ofReal (dist e.1 e.2 ^ 2)
        ∂Measure.map retainedInitialEdges
          (retainedInitialEulerRWMPairMeasure V δ n)) =
      ∫⁻ z : State d × (State d × State d),
        ENNReal.ofReal
          (dist (retainedInitialEdges z).1 (retainedInitialEdges z).2 ^ 2)
        ∂retainedInitialEulerRWMPairMeasure V δ n :=
      lintegral_map hcost measurable_retainedInitialEdges
    _ = _ := by
      apply lintegral_congr
      intro z
      rw [show (retainedInitialEdges z).1 = retainInitialFst z by rfl,
        show (retainedInitialEdges z).2 = retainInitialSnd z by rfl,
        dist_retainInitialFst_retainInitialSnd]

/-- Norm-squared version of
`lintegral_sq_dist_finiteEulerRWMEdgeCouplingMeasure`. -/
theorem lintegral_sq_dist_finiteEulerRWMEdgeCouplingMeasure_eq_norm
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ) :
    (∫⁻ e : (State d × State d) × (State d × State d),
        ENNReal.ofReal (dist e.1 e.2 ^ 2)
        ∂finiteEulerRWMEdgeCouplingMeasure V δ n) =
      ∫⁻ z : State d × (State d × State d),
        ENNReal.ofReal (‖z.2.1 - z.2.2‖ ^ 2)
        ∂retainedInitialEulerRWMPairMeasure V δ n := by
  rw [lintegral_sq_dist_finiteEulerRWMEdgeCouplingMeasure]
  apply lintegral_congr
  intro z
  rw [dist_eq_norm]

/-- The first marginal of the edge coupling is the Euler edge law. -/
theorem fst_finiteEulerRWMEdgeCouplingMeasure
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ) :
    (finiteEulerRWMEdgeCouplingMeasure V δ n).fst =
      finiteEulerEdgeMeasure V δ n := by
  unfold finiteEulerRWMEdgeCouplingMeasure retainedInitialEdges
  rw [Measure.fst_map_prodMk measurable_retainInitialSnd]
  exact map_retainInitialFst_retainedInitialEulerRWMPairMeasure V δ n

/-- The second marginal of the edge coupling is the stationary RWM edge
law. -/
theorem snd_finiteEulerRWMEdgeCouplingMeasure
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ) :
    (finiteEulerRWMEdgeCouplingMeasure V δ n).snd =
      finiteRWMEdgeMeasure V δ n := by
  unfold finiteEulerRWMEdgeCouplingMeasure retainedInitialEdges
  rw [Measure.snd_map_prodMk measurable_retainInitialFst]
  exact map_retainInitialSnd_retainedInitialEulerRWMPairMeasure V δ n

/-- A terminal pair-chain second-moment estimate immediately gives the
Levy--Prokhorov estimate between the two edge laws. -/
theorem levyProkhorovEDist_finiteEulerEdgeMeasure_finiteRWMEdgeMeasure_le
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hsecond :
      (∫⁻ z : State d × (State d × State d),
        ENNReal.ofReal (‖z.2.1 - z.2.2‖ ^ 2)
        ∂retainedInitialEulerRWMPairMeasure V δ n) ≤
          ENNReal.ofReal (epsilon ^ 3)) :
    levyProkhorovEDist
        (finiteEulerEdgeMeasure V δ n)
        (finiteRWMEdgeMeasure V δ n) ≤
      ENNReal.ofReal epsilon := by
  apply levyProkhorovEDist_le_of_coupling_lintegral_sq_le_cube
    (finiteEulerEdgeMeasure V δ n)
    (finiteRWMEdgeMeasure V δ n)
    (finiteEulerRWMEdgeCouplingMeasure V δ n)
    (fst_finiteEulerRWMEdgeCouplingMeasure V δ n)
    (snd_finiteEulerRWMEdgeCouplingMeasure V δ n)
    hepsilon
  rw [lintegral_sq_dist_finiteEulerRWMEdgeCouplingMeasure_eq_norm]
  exact hsecond

/-- The initial endpoint of the Euler edge has the target law. -/
theorem fst_finiteEulerEdgeMeasure
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ) :
    (finiteEulerEdgeMeasure V δ n).fst =
      (V.target : Measure (State d)) := by
  unfold finiteEulerEdgeMeasure
  exact Measure.fst_compProd _ _

/-- The initial endpoint of the RWM edge has the target law. -/
theorem fst_finiteRWMEdgeMeasure
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ) :
    (finiteRWMEdgeMeasure V δ n).fst =
      (V.target : Measure (State d)) := by
  letI : IsMarkovKernel (explicitRWMKernel V δ) :=
    explicitRWMKernel_isMarkovKernel V δ
  letI : IsMarkovKernel
      (finiteKernelIterate (explicitRWMKernel V δ) n) := by
    infer_instance
  unfold finiteRWMEdgeMeasure
  exact Measure.fst_compProd _ _

/-- Stationarity identifies the terminal endpoint of the finite RWM edge
with the target law. -/
theorem snd_finiteRWMEdgeMeasure
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ) :
    (finiteRWMEdgeMeasure V δ n).snd =
      (V.target : Measure (State d)) := by
  letI : IsMarkovKernel (explicitRWMKernel V δ) :=
    explicitRWMKernel_isMarkovKernel V δ
  letI : IsMarkovKernel
      (finiteKernelIterate (explicitRWMKernel V δ) n) := by
    infer_instance
  unfold finiteRWMEdgeMeasure
  rw [Measure.snd_compProd]
  exact explicitRWMKernel_finiteIterate_invariant V δ n

/-- The finite explicit-RWM iterate remains reversible with respect to the
target. -/
theorem explicitRWMKernel_finiteIterate_isReversible
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ) :
    Kernel.IsReversible (finiteKernelIterate (explicitRWMKernel V δ) n)
      (V.target : Measure (State d)) := by
  letI : IsMarkovKernel (explicitRWMKernel V δ) :=
    explicitRWMKernel_isMarkovKernel V δ
  exact finiteKernelIterate_isReversible (explicitRWMKernel V δ)
    (V.target : Measure (State d))
    (explicitRWMKernel_isReversible V δ) n

/-- Consequently every stationary finite RWM edge law is invariant under
swapping its two endpoints. -/
theorem map_swap_finiteRWMEdgeMeasure
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ) :
    Measure.map Prod.swap (finiteRWMEdgeMeasure V δ n) =
      finiteRWMEdgeMeasure V δ n := by
  symm
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.map_apply measurable_swap (hA.prod hB),
    Set.preimage_swap_prod]
  unfold finiteRWMEdgeMeasure
  letI : IsMarkovKernel (explicitRWMKernel V δ) :=
    explicitRWMKernel_isMarkovKernel V δ
  letI : IsMarkovKernel
      (finiteKernelIterate (explicitRWMKernel V δ) n) := by infer_instance
  rw [Measure.compProd_apply_prod hA hB,
    Measure.compProd_apply_prod hB hA]
  exact explicitRWMKernel_finiteIterate_isReversible V δ n hA hB

/-- Probability-measure packaging of the finite Euler edge law. -/
def finiteEulerEdgeLaw
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ) :
    ProbabilityMeasure (State d × State d) :=
  ⟨finiteEulerEdgeMeasure V δ n, by infer_instance⟩

/-- Probability-measure packaging of the stationary finite RWM edge law. -/
def finiteRWMEdgeLaw
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ) :
    ProbabilityMeasure (State d × State d) :=
  ⟨finiteRWMEdgeMeasure V δ n, by infer_instance⟩

/-- Measure-level swap symmetry for the packaged stationary RWM edge law. -/
theorem map_swap_finiteRWMEdgeLaw
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ) :
    Measure.map Prod.swap
        (finiteRWMEdgeLaw V δ n : Measure (State d × State d)) =
      (finiteRWMEdgeLaw V δ n : Measure (State d × State d)) := by
  change Measure.map Prod.swap (finiteRWMEdgeMeasure V δ n) =
    finiteRWMEdgeMeasure V δ n
  exact map_swap_finiteRWMEdgeMeasure V δ n

/-- Probability-measure packaging of the concrete edge coupling. -/
def finiteEulerRWMEdgeCouplingLaw
    (V : FirstOrderPotential d) (δ : ℝ) (n : ℕ) :
    ProbabilityMeasure ((State d × State d) × (State d × State d)) :=
  ⟨finiteEulerRWMEdgeCouplingMeasure V δ n, by infer_instance⟩

/-! ## Tightness and subsequences -/

/-- Levy--Prokhorov shortcut: if `eta k` converges weakly and the
Levy--Prokhorov distance from `mu k` to `eta k` tends to zero, then `mu k`
has the same weak limit.  The proof is the triangle inequality in the
Levy--Prokhorov metric, transported through Mathlib's homeomorphism with the
weak topology. -/
theorem probabilityMeasure_tendsto_of_tendsto_of_levyProkhorovEDist_tendsto_zero
    {X : Type*}
    [PseudoMetricSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X] [OpensMeasurableSpace X]
    (mu eta : ℕ → ProbabilityMeasure X)
    (etaLimit : ProbabilityMeasure X)
    (heta : Tendsto eta atTop (nhds etaLimit))
    (hdist : Tendsto
      (fun k => levyProkhorovEDist
        (mu k : Measure X) (eta k : Measure X))
      atTop (nhds 0)) :
    Tendsto mu atTop (nhds etaLimit) := by
  have hetaLP : Tendsto
      (fun k => LevyProkhorov.ofMeasure (eta k)) atTop
      (nhds (LevyProkhorov.ofMeasure etaLimit)) :=
    (LevyProkhorov.probabilityMeasureHomeomorph (Ω := X)).continuous
      |>.continuousAt.tendsto.comp heta
  have hetaDist : Tendsto
      (fun k => edist (LevyProkhorov.ofMeasure (eta k))
        (LevyProkhorov.ofMeasure etaLimit)) atTop (nhds 0) :=
    tendsto_iff_edist_tendsto_0.mp hetaLP
  have hmuEtaDist : Tendsto
      (fun k => edist (LevyProkhorov.ofMeasure (mu k))
        (LevyProkhorov.ofMeasure (eta k))) atTop (nhds 0) := by
    change Tendsto
      (fun k => levyProkhorovEDist
        (mu k : Measure X) (eta k : Measure X)) atTop (nhds 0)
    exact hdist
  have hsum : Tendsto
      (fun k => edist (LevyProkhorov.ofMeasure (mu k))
          (LevyProkhorov.ofMeasure (eta k)) +
        edist (LevyProkhorov.ofMeasure (eta k))
          (LevyProkhorov.ofMeasure etaLimit)) atTop (nhds (0 + 0)) :=
    hmuEtaDist.add hetaDist
  have hmuDist : Tendsto
      (fun k => edist (LevyProkhorov.ofMeasure (mu k))
        (LevyProkhorov.ofMeasure etaLimit)) atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hsum)
    · intro k
      exact bot_le
    · intro k
      exact edist_triangle _ _ _
  have hmuLP : Tendsto
      (fun k => LevyProkhorov.ofMeasure (mu k)) atTop
      (nhds (LevyProkhorov.ofMeasure etaLimit)) :=
    tendsto_iff_edist_tendsto_0.mpr hmuDist
  exact (LevyProkhorov.probabilityMeasureHomeomorph (Ω := X)).symm.continuous
    |>.continuousAt.tendsto.comp hmuLP

/-- Edge-law specialization of the Levy--Prokhorov shortcut.  A vanishing
positive error schedule and a terminal pair cost bounded by its cube force
the Euler edge laws to have every weak limit possessed by the stationary RWM
edge laws. -/
theorem finiteEulerEdgeLaw_tendsto_of_finiteRWMEdgeLaw_tendsto_of_cost
    (V : FirstOrderPotential d) (δ : ℕ → ℝ) (steps : ℕ → ℕ)
    (epsilon : ℕ → ℝ) (etaLimit : ProbabilityMeasure (State d × State d))
    (hepsilon_pos : ∀ k, 0 < epsilon k)
    (hepsilon_zero : Tendsto epsilon atTop (nhds 0))
    (hsecond : ∀ k,
      (∫⁻ z : State d × (State d × State d),
        ENNReal.ofReal (‖z.2.1 - z.2.2‖ ^ 2)
        ∂retainedInitialEulerRWMPairMeasure V (δ k) (steps k)) ≤
          ENNReal.ofReal (epsilon k ^ 3))
    (heta : Tendsto
      (fun k => finiteRWMEdgeLaw V (δ k) (steps k))
      atTop (nhds etaLimit)) :
    Tendsto (fun k => finiteEulerEdgeLaw V (δ k) (steps k))
      atTop (nhds etaLimit) := by
  have hepsilonENN : Tendsto (fun k => ENNReal.ofReal (epsilon k))
      atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal hepsilon_zero
  have hlp : ∀ k,
      levyProkhorovEDist
          (finiteEulerEdgeLaw V (δ k) (steps k) :
            Measure (State d × State d))
          (finiteRWMEdgeLaw V (δ k) (steps k) :
            Measure (State d × State d)) ≤
        ENNReal.ofReal (epsilon k) := by
    intro k
    change levyProkhorovEDist
        (finiteEulerEdgeMeasure V (δ k) (steps k))
        (finiteRWMEdgeMeasure V (δ k) (steps k)) ≤
      ENNReal.ofReal (epsilon k)
    exact levyProkhorovEDist_finiteEulerEdgeMeasure_finiteRWMEdgeMeasure_le
      V (δ k) (steps k) (hepsilon_pos k) (hsecond k)
  have hlp_zero : Tendsto
      (fun k => levyProkhorovEDist
        (finiteEulerEdgeLaw V (δ k) (steps k) :
          Measure (State d × State d))
        (finiteRWMEdgeLaw V (δ k) (steps k) :
          Measure (State d × State d))) atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      hepsilonENN
    · intro k
      exact bot_le
    · exact hlp
  exact probabilityMeasure_tendsto_of_tendsto_of_levyProkhorovEDist_tendsto_zero
    (fun k => finiteEulerEdgeLaw V (δ k) (steps k))
    (fun k => finiteRWMEdgeLaw V (δ k) (steps k))
    etaLimit heta hlp_zero

/-- Explicit subsequence form: any weak subsequential limit of the stationary
RWM edge laws is the weak limit of the Euler edge laws along the very same
subsequence, provided the terminal coupling cost vanishes at the supplied
rate. -/
theorem finiteEulerEdgeLaw_subseq_tendsto_of_finiteRWMEdgeLaw_subseq_tendsto_of_cost
    (V : FirstOrderPotential d) (δ : ℕ → ℝ) (steps : ℕ → ℕ)
    (epsilon : ℕ → ℝ) (subseq : ℕ → ℕ)
    (etaLimit : ProbabilityMeasure (State d × State d))
    (hepsilon_pos : ∀ k, 0 < epsilon k)
    (hepsilon_zero : Tendsto epsilon atTop (nhds 0))
    (hsecond : ∀ k,
      (∫⁻ z : State d × (State d × State d),
        ENNReal.ofReal (‖z.2.1 - z.2.2‖ ^ 2)
        ∂retainedInitialEulerRWMPairMeasure V (δ k) (steps k)) ≤
          ENNReal.ofReal (epsilon k ^ 3))
    (hsubseq : StrictMono subseq)
    (heta : Tendsto
      ((fun k => finiteRWMEdgeLaw V (δ k) (steps k)) ∘ subseq)
      atTop (nhds etaLimit)) :
    Tendsto
      ((fun k => finiteEulerEdgeLaw V (δ k) (steps k)) ∘ subseq)
      atTop (nhds etaLimit) := by
  have heta' := heta
  change Tendsto
    (fun k => finiteRWMEdgeLaw V (δ (subseq k)) (steps (subseq k)))
    atTop (nhds etaLimit) at heta'
  have h := finiteEulerEdgeLaw_tendsto_of_finiteRWMEdgeLaw_tendsto_of_cost
    V (δ ∘ subseq) (steps ∘ subseq) (epsilon ∘ subseq) etaLimit
    (fun k => hepsilon_pos (subseq k))
    (hepsilon_zero.comp hsubseq.tendsto_atTop)
    (fun k => hsecond (subseq k))
    heta'
  change Tendsto
    (fun k => finiteEulerEdgeLaw V (δ (subseq k)) (steps (subseq k)))
    atTop (nhds etaLimit)
  exact h

/-- A sequence of stationary finite RWM edge laws is tight for arbitrary
step sizes and iteration counts: both endpoint marginals are always the
fixed target measure. -/
theorem isTightMeasureSet_range_finiteRWMEdgeMeasure
    (V : FirstOrderPotential d) (δ : ℕ → ℝ) (steps : ℕ → ℕ) :
    IsTightMeasureSet
      (Set.range (fun k => finiteRWMEdgeMeasure V (δ k) (steps k))) := by
  apply (isTightMeasureSet_probability_couplings_of_fixed_marginals
    V.target V.target).subset
  rintro eta ⟨k, rfl⟩
  exact ⟨fst_finiteRWMEdgeMeasure V (δ k) (steps k),
    snd_finiteRWMEdgeMeasure V (δ k) (steps k)⟩

/-- Concrete sequential Prokhorov extraction for stationary RWM edge laws.
No estimate is needed: stationarity fixes both one-coordinate marginals. -/
theorem exists_tendsto_subseq_finiteRWMEdgeLaw
    (V : FirstOrderPotential d) (δ : ℕ → ℝ) (steps : ℕ → ℕ) :
    ∃ etaLimit ∈
        closure (Set.range (fun k => finiteRWMEdgeLaw V (δ k) (steps k))),
      ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
        Tendsto
          ((fun k => finiteRWMEdgeLaw V (δ k) (steps k)) ∘ subseq)
          atTop (nhds etaLimit) := by
  let S : Set (ProbabilityMeasure (State d × State d)) :=
    Set.range (fun k => finiteRWMEdgeLaw V (δ k) (steps k))
  have hfst : IsTightMeasureSet
      (Measure.fst ''
        {((eta : ProbabilityMeasure (State d × State d)) :
            Measure (State d × State d)) | eta ∈ S}) := by
    apply (isTightMeasureSet_singleton
      (μ := (V.target : Measure (State d)))).subset
    rintro mu ⟨rho, ⟨eta, heta, rfl⟩, rfl⟩
    rcases heta with ⟨k, rfl⟩
    change (finiteRWMEdgeMeasure V (δ k) (steps k)).fst =
      (V.target : Measure (State d))
    simpa only [mem_singleton_iff] using
      fst_finiteRWMEdgeMeasure V (δ k) (steps k)
  have hsnd : IsTightMeasureSet
      (Measure.snd ''
        {((eta : ProbabilityMeasure (State d × State d)) :
            Measure (State d × State d)) | eta ∈ S}) := by
    apply (isTightMeasureSet_singleton
      (μ := (V.target : Measure (State d)))).subset
    rintro mu ⟨rho, ⟨eta, heta, rfl⟩, rfl⟩
    rcases heta with ⟨k, rfl⟩
    change (finiteRWMEdgeMeasure V (δ k) (steps k)).snd =
      (V.target : Measure (State d))
    simpa only [mem_singleton_iff] using
      snd_finiteRWMEdgeMeasure V (δ k) (steps k)
  exact exists_tendsto_subseq_of_tight_marginals hfst hsnd
    (fun k => finiteRWMEdgeLaw V (δ k) (steps k))
    (fun k => Set.mem_range_self k)

/-- Every weak limit of a (possibly selected) sequence of stationary RWM
edge laws is swap invariant and has the target as both endpoint marginals. -/
theorem finiteRWMEdgeLaw_limit_swap_fst_snd
    (V : FirstOrderPotential d) (δ : ℕ → ℝ) (steps : ℕ → ℕ)
    (subseq : ℕ → ℕ)
    (etaLimit : ProbabilityMeasure (State d × State d))
    (heta : Tendsto
      ((fun k => finiteRWMEdgeLaw V (δ k) (steps k)) ∘ subseq)
      atTop (nhds etaLimit)) :
    Measure.map Prod.swap
        (etaLimit : Measure (State d × State d)) =
        (etaLimit : Measure (State d × State d)) ∧
      (etaLimit : Measure (State d × State d)).fst =
        (V.target : Measure (State d)) ∧
      (etaLimit : Measure (State d × State d)).snd =
        (V.target : Measure (State d)) := by
  have hsymm : Measure.map Prod.swap
      (etaLimit : Measure (State d × State d)) =
      (etaLimit : Measure (State d × State d)) := by
    apply map_swap_eq_self_of_probabilityMeasure_tendsto heta
    intro k
    change Measure.map Prod.swap
        (finiteRWMEdgeMeasure V (δ (subseq k)) (steps (subseq k))) =
      finiteRWMEdgeMeasure V (δ (subseq k)) (steps (subseq k))
    exact map_swap_finiteRWMEdgeMeasure V (δ (subseq k)) (steps (subseq k))
  have hfst : (etaLimit : Measure (State d × State d)).fst =
      (V.target : Measure (State d)) := by
    apply fst_eq_of_probabilityMeasure_tendsto heta tendsto_const_nhds
    intro k
    change (finiteRWMEdgeMeasure V (δ (subseq k)) (steps (subseq k))).fst =
      (V.target : Measure (State d))
    exact fst_finiteRWMEdgeMeasure V (δ (subseq k)) (steps (subseq k))
  have hsnd : (etaLimit : Measure (State d × State d)).snd =
      (V.target : Measure (State d)) := by
    apply snd_eq_of_probabilityMeasure_tendsto heta tendsto_const_nhds
    intro k
    change (finiteRWMEdgeMeasure V (δ (subseq k)) (steps (subseq k))).snd =
      (V.target : Measure (State d))
    exact snd_finiteRWMEdgeMeasure V (δ (subseq k)) (steps (subseq k))
  exact ⟨hsymm, hfst, hsnd⟩

/-- The complete compactness shortcut.  Stationarity supplies an RWM-edge
subsequence unconditionally; the vanishing terminal coupling cost transfers
that convergence to the Euler edge laws along the same subsequence.  Thus no
tightness theorem for Euler edge laws and no weak limit of joint couplings is
needed. -/
theorem exists_common_tendsto_subseq_finiteEulerEdgeLaw_finiteRWMEdgeLaw_of_cost
    (V : FirstOrderPotential d) (δ : ℕ → ℝ) (steps : ℕ → ℕ)
    (epsilon : ℕ → ℝ)
    (hepsilon_pos : ∀ k, 0 < epsilon k)
    (hepsilon_zero : Tendsto epsilon atTop (nhds 0))
    (hsecond : ∀ k,
      (∫⁻ z : State d × (State d × State d),
        ENNReal.ofReal (‖z.2.1 - z.2.2‖ ^ 2)
        ∂retainedInitialEulerRWMPairMeasure V (δ k) (steps k)) ≤
          ENNReal.ofReal (epsilon k ^ 3)) :
    ∃ etaLimit ∈
        closure (Set.range (fun k => finiteRWMEdgeLaw V (δ k) (steps k))),
      ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
        Tendsto
          ((fun k => finiteRWMEdgeLaw V (δ k) (steps k)) ∘ subseq)
          atTop (nhds etaLimit) ∧
        Tendsto
          ((fun k => finiteEulerEdgeLaw V (δ k) (steps k)) ∘ subseq)
          atTop (nhds etaLimit) := by
  obtain ⟨etaLimit, hetaLimit, subseq, hsubseq, heta⟩ :=
    exists_tendsto_subseq_finiteRWMEdgeLaw V δ steps
  refine ⟨etaLimit, hetaLimit, subseq, hsubseq, heta, ?_⟩
  exact
    finiteEulerEdgeLaw_subseq_tendsto_of_finiteRWMEdgeLaw_subseq_tendsto_of_cost
      V δ steps epsilon subseq etaLimit hepsilon_pos hepsilon_zero hsecond
      hsubseq heta

/-- Structured form of the complete shortcut: in addition to common weak
convergence, the selected limit is a symmetric self-coupling of the target. -/
theorem exists_common_tendsto_subseq_finiteEulerEdgeLaw_finiteRWMEdgeLaw_with_structure
    (V : FirstOrderPotential d) (δ : ℕ → ℝ) (steps : ℕ → ℕ)
    (epsilon : ℕ → ℝ)
    (hepsilon_pos : ∀ k, 0 < epsilon k)
    (hepsilon_zero : Tendsto epsilon atTop (nhds 0))
    (hsecond : ∀ k,
      (∫⁻ z : State d × (State d × State d),
        ENNReal.ofReal (‖z.2.1 - z.2.2‖ ^ 2)
        ∂retainedInitialEulerRWMPairMeasure V (δ k) (steps k)) ≤
          ENNReal.ofReal (epsilon k ^ 3)) :
    ∃ etaLimit ∈
        closure (Set.range (fun k => finiteRWMEdgeLaw V (δ k) (steps k))),
      ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
        Tendsto
          ((fun k => finiteRWMEdgeLaw V (δ k) (steps k)) ∘ subseq)
          atTop (nhds etaLimit) ∧
        Tendsto
          ((fun k => finiteEulerEdgeLaw V (δ k) (steps k)) ∘ subseq)
          atTop (nhds etaLimit) ∧
        Measure.map Prod.swap
          (etaLimit : Measure (State d × State d)) =
          (etaLimit : Measure (State d × State d)) ∧
        (etaLimit : Measure (State d × State d)).fst =
          (V.target : Measure (State d)) ∧
        (etaLimit : Measure (State d × State d)).snd =
          (V.target : Measure (State d)) := by
  obtain ⟨etaLimit, hetaLimit, subseq, hsubseq, heta, heuler⟩ :=
    exists_common_tendsto_subseq_finiteEulerEdgeLaw_finiteRWMEdgeLaw_of_cost
      V δ steps epsilon hepsilon_pos hepsilon_zero hsecond
  obtain ⟨hsymm, hfst, hsnd⟩ :=
    finiteRWMEdgeLaw_limit_swap_fst_snd V δ steps subseq etaLimit heta
  exact ⟨etaLimit, hetaLimit, subseq, hsubseq, heta, heuler,
    hsymm, hfst, hsnd⟩

/-- Prokhorov extraction for the concrete couplings of Euler and RWM edge
laws.  The sole remaining compactness input is tightness of the Euler edge
laws.  Tightness of the RWM edge laws is automatic from stationarity. -/
theorem exists_tendsto_subseq_finiteEulerRWMEdgeCouplingLaw
    (V : FirstOrderPotential d) (δ : ℕ → ℝ) (steps : ℕ → ℕ)
    (hEuler : IsTightMeasureSet
      (Set.range (fun k => finiteEulerEdgeMeasure V (δ k) (steps k)))) :
    ∃ couplingLimit ∈ closure
        (Set.range (fun k =>
          finiteEulerRWMEdgeCouplingLaw V (δ k) (steps k))),
      ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
        Tendsto
          ((fun k => finiteEulerRWMEdgeCouplingLaw V (δ k) (steps k)) ∘
            subseq)
          atTop (nhds couplingLimit) := by
  let S : Set
      (ProbabilityMeasure
        ((State d × State d) × (State d × State d))) :=
    Set.range (fun k =>
      finiteEulerRWMEdgeCouplingLaw V (δ k) (steps k))
  have hfst : IsTightMeasureSet
      (Measure.fst ''
        {((kappa : ProbabilityMeasure
            ((State d × State d) × (State d × State d))) :
              Measure ((State d × State d) × (State d × State d))) |
          kappa ∈ S}) := by
    apply hEuler.subset
    rintro mu ⟨rho, ⟨kappa, hkappa, rfl⟩, rfl⟩
    rcases hkappa with ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    change finiteEulerEdgeMeasure V (δ k) (steps k) =
      (finiteEulerRWMEdgeCouplingMeasure V (δ k) (steps k)).fst
    exact (fst_finiteEulerRWMEdgeCouplingMeasure V (δ k) (steps k)).symm
  have hsnd : IsTightMeasureSet
      (Measure.snd ''
        {((kappa : ProbabilityMeasure
            ((State d × State d) × (State d × State d))) :
              Measure ((State d × State d) × (State d × State d))) |
          kappa ∈ S}) := by
    apply (isTightMeasureSet_range_finiteRWMEdgeMeasure V δ steps).subset
    rintro mu ⟨rho, ⟨kappa, hkappa, rfl⟩, rfl⟩
    rcases hkappa with ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    change finiteRWMEdgeMeasure V (δ k) (steps k) =
      (finiteEulerRWMEdgeCouplingMeasure V (δ k) (steps k)).snd
    exact (snd_finiteEulerRWMEdgeCouplingMeasure V (δ k) (steps k)).symm
  exact exists_tendsto_subseq_of_tight_marginals hfst hsnd
    (fun k => finiteEulerRWMEdgeCouplingLaw V (δ k) (steps k))
    (fun k => Set.mem_range_self k)

end DiscreteTime

end

end UniformRandomMALA
