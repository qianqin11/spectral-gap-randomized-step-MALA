import UniformRandomMALA.Concrete.FiniteEulerEnlargement
import UniformRandomMALA.DiscreteTime.FiniteEulerEdgeBridge
import UniformRandomMALA.DiscreteTime.EulerRWMEdgeVanishing

/-!
# Identifying finite Euler endpoints with the target

This module supplies the discrete interfaces needed to replace an SDE
identification argument.  It regroups the flat Euclidean Gaussian source into
independent innovation blocks, identifies the flat-Gaussian Euler endpoint
with the already constructed Euler kernel iterate, and records the
synchronous initial-condition contraction at the level of finite paths.
-/

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal ProbabilityTheory RealInnerProductSpace

noncomputable section

namespace DiscreteTime

open Concrete

variable {d n : ℕ}

/-- Regrouping a finite scalar product measure by its first coordinate does
not change the product law. -/
lemma map_curry_pi_gaussianReal {n d : ℕ} :
    Measure.map (fun x : Fin n × Fin d → ℝ => fun j i => x (j, i))
        (Measure.pi (fun _ : Fin n × Fin d => gaussianReal 0 1)) =
      Measure.pi (fun _ : Fin n =>
        Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := by
  let nested : Measure (Fin n → Fin d → ℝ) :=
    Measure.pi (fun _ : Fin n =>
      Measure.pi (fun _ : Fin d => gaussianReal 0 1))
  have huncurry :
      Measure.map (fun x : Fin n → Fin d → ℝ => fun p => x p.1 p.2) nested =
        Measure.pi (fun _ : Fin n × Fin d => gaussianReal 0 1) := by
    symm
    apply Measure.pi_eq
    intro s hs
    rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
    have hpre : (fun x : Fin n → Fin d → ℝ => fun p => x p.1 p.2) ⁻¹'
          Set.univ.pi s =
        Set.univ.pi (fun j : Fin n =>
          Set.univ.pi (fun i : Fin d => s (j, i))) := by
      ext x
      simp [Set.mem_pi]
    rw [hpre]
    dsimp [nested]
    rw [Measure.pi_pi]
    simp_rw [Measure.pi_pi]
    simpa only [Finset.univ_product_univ] using
      (Finset.prod_product (Finset.univ : Finset (Fin n))
        (Finset.univ : Finset (Fin d))
        (fun p : Fin n × Fin d => gaussianReal 0 1 (s p))) |>.symm
  calc
    Measure.map (fun x : Fin n × Fin d → ℝ => fun j i => x (j, i))
        (Measure.pi (fun _ : Fin n × Fin d => gaussianReal 0 1)) =
        Measure.map (fun x : Fin n × Fin d → ℝ => fun j i => x (j, i))
          (Measure.map (fun x : Fin n → Fin d → ℝ => fun p => x p.1 p.2) nested) := by
            rw [huncurry]
    _ = nested := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      have hfun :
          (fun x : Fin n × Fin d → ℝ => fun j i => x (j, i)) ∘
              (fun x : Fin n → Fin d → ℝ => fun p => x p.1 p.2) = id := by
        funext x
        rfl
      rw [hfun, Measure.map_id]
    _ = _ := rfl

/-- Splitting a flat Euclidean standard Gaussian into `n` blocks of
dimension `d` gives the finite product of standard Gaussian block laws. -/
theorem map_euclideanInnovationBlocks_stdGaussian {n d : ℕ} :
    Measure.map (euclideanInnovationBlocks (n := n) (d := d))
        (stdGaussian (EuclideanSpace ℝ (Fin n × Fin d))) =
      Measure.pi (fun _ : Fin n => stdGaussian (State d)) := by
  let flat : Measure (Fin n × Fin d → ℝ) :=
    Measure.pi (fun _ : Fin n × Fin d => gaussianReal 0 1)
  let nested : Measure (Fin n → Fin d → ℝ) :=
    Measure.pi (fun _ : Fin n =>
      Measure.pi (fun _ : Fin d => gaussianReal 0 1))
  let curryMap : (Fin n × Fin d → ℝ) → (Fin n → Fin d → ℝ) :=
    fun x j i => x (j, i)
  have hcurry : Measure.map curryMap flat = nested := by
    simpa only [curryMap, flat, nested] using
      (map_curry_pi_gaussianReal (n := n) (d := d))
  have hblocks : Measurable
      (euclideanInnovationBlocks (n := n) (d := d)) := by
    unfold euclideanInnovationBlocks
    fun_prop
  calc
    Measure.map euclideanInnovationBlocks
        (stdGaussian (EuclideanSpace ℝ (Fin n × Fin d))) =
        Measure.map euclideanInnovationBlocks
          (Measure.map (WithLp.toLp 2) flat) := by
            rw [map_pi_eq_stdGaussian]
    _ = Measure.map (fun x : Fin n × Fin d → ℝ =>
          fun j => WithLp.toLp 2 (fun i => x (j, i))) flat := by
      rw [Measure.map_map hblocks (by fun_prop)]
      rfl
    _ = Measure.map (fun x : Fin n → Fin d → ℝ =>
          fun j => WithLp.toLp 2 (x j)) nested := by
      rw [← hcurry, Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = Measure.pi (fun _ : Fin n =>
          Measure.map (WithLp.toLp 2)
            (Measure.pi (fun _ : Fin d => gaussianReal 0 1))) := by
      dsimp [nested]
      exact Measure.pi_map_pi
        (fun _ => WithLp.measurable_toLp 2 _ |>.aemeasurable)
    _ = Measure.pi (fun _ : Fin n => stdGaussian (State d)) := by
      congr 1
      funext j
      exact map_pi_eq_stdGaussian

section Recursion

variable (V : FirstOrderPotential d)

/-- Removing the first innovation and using it for the first Euler step
commutes with every shorter prefix of the finite recursion. -/
lemma finiteEulerState_head_shift
    (delta : ℝ) : ∀ (k n : ℕ) (hk : k ≤ n) (x : State d)
      (z : Fin (n + 1) → State d),
    finiteEulerState V delta x z (k + 1) =
      finiteEulerState V delta
        (finiteEulerStep V delta x (z 0)) (Fin.tail z) k := by
  intro k
  induction k with
  | zero =>
      intro n _hk x z
      simp [finiteEulerState]
  | succ k ih =>
      intro n hk x z
      rw [finiteEulerState_succ_eq_innovationNat]
      rw [finiteEulerState_succ_eq_innovationNat V delta
        (finiteEulerStep V delta x (z 0)) (Fin.tail z) k]
      rw [ih n (Nat.le_trans (Nat.le_succ k) hk) x z]
      have hklt : k + 1 < n + 1 := Nat.add_lt_add_right hk 1
      have hklt' : k < n := Nat.lt_of_succ_le hk
      simp only [finiteInnovationNat_of_lt _ hklt,
        finiteInnovationNat_of_lt _ hklt']
      rfl

/-- The path-state and chronological endpoint recursions are pointwise
identical at their common terminal time. -/
lemma finiteEulerState_eq_endpointRec
    (delta : ℝ) : ∀ (n : ℕ) (x : State d) (z : Fin n → State d),
    finiteEulerState V delta x z n = finiteEulerEndpointRec V delta x z := by
  intro n
  induction n with
  | zero =>
      intro x z
      rfl
  | succ n ih =>
      intro x z
      rw [finiteEulerState_head_shift V delta n n (le_refl n) x z]
      rw [ih]
      rfl

/-- The flat-Gaussian Euler endpoint law is exactly the finite iterate of
the one-step Euler kernel. -/
theorem map_finiteEulerEuclideanEndpoint_eq_finiteKernelIterate
    (delta : ℝ) (n : ℕ) (x : State d) :
    Measure.map (finiteEulerEuclideanEndpoint V delta x)
        (stdGaussian (EuclideanSpace ℝ (Fin n × Fin d))) =
      finiteKernelIterate (explicitEulerKernel V delta) n x := by
  have hblocks : Measurable
      (euclideanInnovationBlocks (n := n) (d := d)) := by
    unfold euclideanInnovationBlocks
    fun_prop
  have hendpoint : Measurable (finiteEulerEndpointRec V delta x :
      (Fin n → State d) → State d) :=
    measurable_finiteEulerEndpointRec V delta x n
  calc
    Measure.map (finiteEulerEuclideanEndpoint V delta x)
        (stdGaussian (EuclideanSpace ℝ (Fin n × Fin d))) =
        Measure.map (finiteEulerEndpointRec V delta x)
          (Measure.map euclideanInnovationBlocks
            (stdGaussian (EuclideanSpace ℝ (Fin n × Fin d)))) := by
      rw [Measure.map_map hendpoint hblocks]
      congr 1
      funext z
      exact finiteEulerState_eq_endpointRec V delta n x
        (euclideanInnovationBlocks z)
    _ = Measure.map (finiteEulerEndpointRec V delta x)
          (Measure.pi (fun _ : Fin n => stdGaussian (State d))) := by
      rw [map_euclideanInnovationBlocks_stdGaussian]
    _ = finiteKernelIterate (explicitEulerKernel V delta) n x :=
      map_finiteEulerEndpointRec_eq_finiteKernelIterate V delta n x

/-- Probability-measure packaging of the stationary-start Euler terminal
law, presented as the first marginal of the Euler/RWM pair chain. -/
def stationaryFiniteEulerEndpointLaw
    (delta : ℝ) (n : ℕ) : ProbabilityMeasure (State d) :=
  ⟨Measure.map Prod.fst (stationaryEulerRWMPairChainLaw V delta n),
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable⟩

@[simp] theorem stationaryFiniteEulerEndpointLaw_toMeasure
    (delta : ℝ) (n : ℕ) :
    (stationaryFiniteEulerEndpointLaw V delta n : Measure (State d)) =
      Measure.map Prod.fst (stationaryEulerRWMPairChainLaw V delta n) := rfl

/-- Kernel-mixture form of the stationary-start Euler endpoint law. -/
theorem stationaryFiniteEulerEndpointLaw_eq_kernelIterate_comp_target
    (delta : ℝ) (n : ℕ) :
    (stationaryFiniteEulerEndpointLaw V delta n : Measure (State d)) =
      finiteKernelIterate (explicitEulerKernel V delta) n ∘ₘ
        (V.target : Measure (State d)) := by
  rw [stationaryFiniteEulerEndpointLaw_toMeasure]
  unfold stationaryEulerRWMPairChainLaw
  rw [Measure.map_comp _ _ measurable_fst, ← Kernel.fst_eq,
    fst_eulerRWMPairChainKernel, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map]
  have hdiag : Measurable (fun x : State d => (x, x)) :=
    measurable_id.prodMk measurable_id
  unfold diagonalTargetPairLaw
  rw [Measure.map_map measurable_fst hdiag]
  change finiteKernelIterate (explicitEulerKernel V delta) n ∘ₘ
      Measure.map id (V.target : Measure (State d)) = _
  rw [Measure.map_id]

/-- The pair-chain real energy is the `toReal` presentation of its
nonnegative `ENNReal` squared-distance cost. -/
theorem lintegral_pairCost_stationaryEulerRWMPairChainLaw_eq_ofReal_energy
    (delta : ℝ) (n : ℕ)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdeltaL : delta ≤ 2 / V.L) :
    (∫⁻ xy : State d × State d,
        ENNReal.ofReal (dist xy.1 xy.2 ^ 2)
        ∂stationaryEulerRWMPairChainLaw V delta n) =
      ENNReal.ofReal
        (∫ xy, pairSquaredDistance xy
          ∂stationaryEulerRWMPairChainLaw V delta n) := by
  rw [ofReal_integral_eq_lintegral_ofReal
    (integrable_pairSquaredDistance_stationaryEulerRWMPairChainLaw
      V delta hdelta hdeltaOne hdeltaL n)
    (ae_of_all _ fun xy => sq_nonneg _)]
  apply lintegral_congr
  intro xy
  rw [dist_eq_norm]
  rfl

/-- A real second-moment bound on the stationary Euler/RWM pair gives a
Lévy--Prokhorov bound between the stationary Euler endpoint and the target. -/
theorem levyProkhorovEDist_stationaryFiniteEulerEndpointLaw_target_le
    (delta : ℝ) (n : ℕ)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdeltaL : delta ≤ 2 / V.L)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (henergy :
      (∫ xy, pairSquaredDistance xy
        ∂stationaryEulerRWMPairChainLaw V delta n) ≤ epsilon ^ 3) :
    levyProkhorovEDist
        (stationaryFiniteEulerEndpointLaw V delta n : Measure (State d))
        (V.target : Measure (State d)) ≤ ENNReal.ofReal epsilon := by
  apply levyProkhorovEDist_le_of_coupling_lintegral_sq_le_cube
    (stationaryFiniteEulerEndpointLaw V delta n : Measure (State d))
    (V.target : Measure (State d))
    (stationaryEulerRWMPairChainLaw V delta n)
  · rfl
  · exact map_snd_stationaryEulerRWMPairChainLaw V delta n
  · exact hepsilon
  · rw [lintegral_pairCost_stationaryEulerRWMPairChainLaw_eq_ofReal_energy
      V delta n hdelta hdeltaOne hdeltaL]
    exact ENNReal.ofReal_le_ofReal henergy

/-- Strong convexity controls centered position by the gradient. -/
lemma norm_sub_minimizer_sq_le_gradU_div
    (x : State d) :
    ‖x - V.minimizer‖ ^ 2 ≤ (‖V.gradU x‖ / V.m) ^ 2 := by
  have hstrong := V.gradU_strongMonotone x V.minimizer
  rw [V.gradU_minimizer, sub_zero] at hstrong
  have hcauchy := abs_real_inner_le_norm
    (V.gradU x) (x - V.minimizer)
  have hinner :
      @inner ℝ (State d) _ (V.gradU x) (x - V.minimizer) ≤
        ‖V.gradU x‖ * ‖x - V.minimizer‖ :=
    (le_abs_self _).trans hcauchy
  have hprod : V.m * ‖x - V.minimizer‖ ^ 2 ≤
      ‖V.gradU x‖ * ‖x - V.minimizer‖ := hstrong.trans hinner
  by_cases hx : ‖x - V.minimizer‖ = 0
  · simp [hx, sq_nonneg]
  · have hxpos : 0 < ‖x - V.minimizer‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
    have hlin : V.m * ‖x - V.minimizer‖ ≤ ‖V.gradU x‖ := by
      have hprod' : (V.m * ‖x - V.minimizer‖) *
          ‖x - V.minimizer‖ ≤
          ‖V.gradU x‖ * ‖x - V.minimizer‖ := by
        simpa only [pow_two, mul_assoc] using hprod
      exact le_of_mul_le_mul_right hprod' hxpos
    have hdiv : ‖x - V.minimizer‖ ≤ ‖V.gradU x‖ / V.m :=
      (le_div_iff₀ V.hm).2 (by simpa [mul_comm] using hlin)
    exact (sq_le_sq₀ (norm_nonneg _)
      (div_nonneg (norm_nonneg _) V.hm.le)).2 hdiv

/-- Every squared distance from a deterministic initial point is integrable
under the target. -/
lemma integrable_target_initialDistanceSq (x0 : State d) :
    Integrable (fun x : State d => ‖x0 - x‖ ^ 2)
      (V.target : Measure (State d)) := by
  let C : ℝ := 2 * ‖x0 - V.minimizer‖ ^ 2
  let A : ℝ := 2 / V.m ^ 2
  have hmajor : Integrable (fun x : State d =>
      C + A * ‖V.gradU x‖ ^ 2) (V.target : Measure (State d)) :=
    (integrable_const C).add
      ((integrable_target_gradU_norm_sq V).const_mul A)
  apply hmajor.mono
  · exact ((continuous_const.sub continuous_id).norm.pow 2).aestronglyMeasurable
  · exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
        Real.norm_eq_abs]
      have hA : 0 ≤ A := by dsimp [A]; positivity
      have hC : 0 ≤ C := by dsimp [C]; positivity
      rw [abs_of_nonneg (add_nonneg hC
        (mul_nonneg hA (sq_nonneg _)))]
      have htri : ‖x0 - x‖ ≤
          ‖x0 - V.minimizer‖ + ‖x - V.minimizer‖ := by
        calc
          ‖x0 - x‖ = ‖(x0 - V.minimizer) - (x - V.minimizer)‖ := by
            congr 1
            module
          _ ≤ _ := norm_sub_le _ _
      have hsq : ‖x0 - x‖ ^ 2 ≤
          2 * ‖x0 - V.minimizer‖ ^ 2 +
            2 * ‖x - V.minimizer‖ ^ 2 := by
        have := (sq_le_sq₀ (norm_nonneg _)
          (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 htri
        nlinarith [sq_nonneg
          (‖x0 - V.minimizer‖ - ‖x - V.minimizer‖)]
      have hgrad := norm_sub_minimizer_sq_le_gradU_div V x
      dsimp [A, C]
      calc
        ‖x0 - x‖ ^ 2 ≤ _ := hsq
        _ ≤ 2 * ‖x0 - V.minimizer‖ ^ 2 +
            2 * (‖V.gradU x‖ / V.m) ^ 2 := by gcongr
        _ = 2 * ‖x0 - V.minimizer‖ ^ 2 +
            (2 / V.m ^ 2) * ‖V.gradU x‖ ^ 2 := by field_simp

/-- The product-noise and flat-Euclidean presentations of a fixed-start
Euler endpoint have the same law. -/
theorem map_finiteEulerEndpointRec_pi_eq_euclidean
    (delta : ℝ) (n : ℕ) (x : State d) :
    Measure.map (finiteEulerEndpointRec V delta x)
        (Measure.pi (fun _ : Fin n => stdGaussian (State d))) =
      Measure.map (finiteEulerEuclideanEndpoint V delta x)
        (stdGaussian (EuclideanSpace ℝ (Fin n × Fin d))) := by
  calc
    Measure.map (finiteEulerEndpointRec V delta x)
        (Measure.pi (fun _ : Fin n => stdGaussian (State d))) =
        finiteKernelIterate (explicitEulerKernel V delta) n x :=
      map_finiteEulerEndpointRec_eq_finiteKernelIterate V delta n x
    _ = Measure.map (finiteEulerEuclideanEndpoint V delta x)
        (stdGaussian (EuclideanSpace ℝ (Fin n × Fin d))) :=
      (map_finiteEulerEuclideanEndpoint_eq_finiteKernelIterate
        V delta n x).symm

/-- The terminal marginal of the stationary Euler edge is the first
marginal of the stationary Euler/RWM pair chain. -/
theorem snd_finiteEulerEdgeMeasure_eq_stationaryFiniteEulerEndpointLaw
    (delta : ℝ) (n : ℕ) :
    (finiteEulerEdgeMeasure V delta n).snd =
      (stationaryFiniteEulerEndpointLaw V delta n : Measure (State d)) := by
  rw [stationaryFiniteEulerEndpointLaw_eq_kernelIterate_comp_target]
  unfold finiteEulerEdgeMeasure
  rw [Measure.snd_compProd, fst_diagonalStartedEulerRWMPairKernel]

/-- Synchronous coupling of a deterministic-start Euler endpoint and a
target-start Euler endpoint, using the same finite Gaussian innovations. -/
def fixedStationaryFiniteEulerEndpointCoupling
    (delta : ℝ) (n : ℕ) (x0 : State d) : Measure (State d × State d) :=
  Measure.map
    (fun p : State d × (Fin n → State d) =>
      (finiteEulerEndpointRec V delta x0 p.2,
        finiteEulerEndpointRec V delta p.1 p.2))
    (finiteEulerBaseJointMeasure (n := n) V)

instance fixedStationaryFiniteEulerEndpointCoupling_isProbabilityMeasure
    (delta : ℝ) (n : ℕ) (x0 : State d) :
    IsProbabilityMeasure
      (fixedStationaryFiniteEulerEndpointCoupling V delta n x0) := by
  unfold fixedStationaryFiniteEulerEndpointCoupling finiteEulerBaseJointMeasure
  apply Measure.isProbabilityMeasure_map
  exact ((measurable_finiteEulerEndpointRec V delta x0 n).comp
      measurable_snd).prodMk
    (measurable_finiteEulerEndpointRec_joint V delta n) |>.aemeasurable

theorem fst_fixedStationaryFiniteEulerEndpointCoupling
    (delta : ℝ) (n : ℕ) (x0 : State d) :
    (fixedStationaryFiniteEulerEndpointCoupling V delta n x0).fst =
      Measure.map (finiteEulerEuclideanEndpoint V delta x0)
        (stdGaussian (EuclideanSpace ℝ (Fin n × Fin d))) := by
  unfold fixedStationaryFiniteEulerEndpointCoupling
  have hpair : Measurable
      (fun p : State d × (Fin n → State d) =>
        (finiteEulerEndpointRec V delta x0 p.2,
          finiteEulerEndpointRec V delta p.1 p.2)) :=
    ((measurable_finiteEulerEndpointRec V delta x0 n).comp
      measurable_snd).prodMk
        (measurable_finiteEulerEndpointRec_joint V delta n)
  rw [Measure.fst, Measure.map_map measurable_fst hpair]
  unfold finiteEulerBaseJointMeasure
  change Measure.map
      (finiteEulerEndpointRec V delta x0 ∘ Prod.snd)
      ((V.target : Measure (State d)).prod
        (Measure.pi (fun _ : Fin n => stdGaussian (State d)))) = _
  rw [← Measure.map_map (measurable_finiteEulerEndpointRec V delta x0 n)
    measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]
  exact map_finiteEulerEndpointRec_pi_eq_euclidean V delta n x0

theorem snd_fixedStationaryFiniteEulerEndpointCoupling
    (delta : ℝ) (n : ℕ) (x0 : State d) :
    (fixedStationaryFiniteEulerEndpointCoupling V delta n x0).snd =
      (stationaryFiniteEulerEndpointLaw V delta n : Measure (State d)) := by
  unfold fixedStationaryFiniteEulerEndpointCoupling
  have hpair : Measurable
      (fun p : State d × (Fin n → State d) =>
        (finiteEulerEndpointRec V delta x0 p.2,
          finiteEulerEndpointRec V delta p.1 p.2)) :=
    ((measurable_finiteEulerEndpointRec V delta x0 n).comp
      measurable_snd).prodMk
        (measurable_finiteEulerEndpointRec_joint V delta n)
  rw [Measure.snd, Measure.map_map measurable_snd hpair]
  have hedge := measurable_finiteEulerLikelihoodEdgeMap
    (n := n) V delta
  change Measure.map
      (Prod.snd ∘ finiteEulerLikelihoodEdgeMap V delta)
      (finiteEulerBaseJointMeasure V) = _
  rw [← Measure.map_map measurable_snd hedge]
  change (finiteEulerLikelihoodEdgeLaw V n delta).snd = _
  rw [finiteEulerLikelihoodEdgeLaw_eq_finiteEulerEdgeMeasure,
    snd_finiteEulerEdgeMeasure_eq_stationaryFiniteEulerEndpointLaw]

/-- Synchronous contraction in the chronological endpoint-recursion
presentation. -/
lemma finiteEulerEndpointRec_initialSensitivity_sq_le_exp
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hmesh : V.L ^ 2 * delta ≤ V.m)
    (x0 y0 : State d) (z : Fin n → State d) :
    ‖finiteEulerEndpointRec V delta x0 z -
        finiteEulerEndpointRec V delta y0 z‖ ^ 2 ≤
      Real.exp (-V.m * ((n : ℝ) * delta)) * ‖x0 - y0‖ ^ 2 := by
  simpa only [finiteEulerState_eq_endpointRec V delta n x0 z,
    finiteEulerState_eq_endpointRec V delta n y0 z] using
    (finiteEulerState_initialSensitivity_sq_le_exp V delta hdelta hmesh
      x0 y0 z n)

/-- The finite second moment of the target around a deterministic point. -/
def targetInitialDistanceSq (x0 : State d) : ℝ :=
  ∫ x, ‖x0 - x‖ ^ 2 ∂(V.target : Measure (State d))

lemma targetInitialDistanceSq_nonneg (x0 : State d) :
    0 ≤ targetInitialDistanceSq V x0 := by
  unfold targetInitialDistanceSq
  exact integral_nonneg fun _ => sq_nonneg _

/-- Integrated form of the synchronous initial-condition contraction. -/
theorem lintegral_fixedStationaryFiniteEulerEndpointCoupling_le
    (delta : ℝ) (n : ℕ) (x0 : State d)
    (hdelta : 0 ≤ delta) (hmesh : V.L ^ 2 * delta ≤ V.m) :
    (∫⁻ xy : State d × State d,
        ENNReal.ofReal (dist xy.1 xy.2 ^ 2)
        ∂fixedStationaryFiniteEulerEndpointCoupling V delta n x0) ≤
      ENNReal.ofReal
        (Real.exp (-V.m * ((n : ℝ) * delta)) *
          targetInitialDistanceSq V x0) := by
  let gamma : Measure (Fin n → State d) :=
    Measure.pi (fun _ : Fin n => stdGaussian (State d))
  let c : ℝ := Real.exp (-V.m * ((n : ℝ) * delta))
  have hpair : Measurable
      (fun p : State d × (Fin n → State d) =>
        (finiteEulerEndpointRec V delta x0 p.2,
          finiteEulerEndpointRec V delta p.1 p.2)) :=
    ((measurable_finiteEulerEndpointRec V delta x0 n).comp
      measurable_snd).prodMk
        (measurable_finiteEulerEndpointRec_joint V delta n)
  have hcost : Measurable (fun xy : State d × State d =>
      ENNReal.ofReal (dist xy.1 xy.2 ^ 2)) := by fun_prop
  rw [fixedStationaryFiniteEulerEndpointCoupling,
    lintegral_map hcost hpair]
  change (∫⁻ p : State d × (Fin n → State d),
      ENNReal.ofReal
        (dist (finiteEulerEndpointRec V delta x0 p.2)
          (finiteEulerEndpointRec V delta p.1 p.2) ^ 2)
      ∂(V.target : Measure (State d)).prod gamma) ≤ _
  calc
    (∫⁻ p : State d × (Fin n → State d),
        ENNReal.ofReal
          (dist (finiteEulerEndpointRec V delta x0 p.2)
            (finiteEulerEndpointRec V delta p.1 p.2) ^ 2)
        ∂(V.target : Measure (State d)).prod gamma) ≤
        ∫⁻ p : State d × (Fin n → State d),
          ENNReal.ofReal (c * ‖x0 - p.1‖ ^ 2)
          ∂(V.target : Measure (State d)).prod gamma := by
      apply lintegral_mono
      intro p
      apply ENNReal.ofReal_le_ofReal
      rw [dist_eq_norm]
      exact finiteEulerEndpointRec_initialSensitivity_sq_le_exp
        V delta hdelta hmesh x0 p.1 p.2
    _ = ∫⁻ x : State d,
          ENNReal.ofReal (c * ‖x0 - x‖ ^ 2)
          ∂(V.target : Measure (State d)) := by
      rw [lintegral_prod]
      · apply lintegral_congr
        intro x
        simp [gamma]
      · fun_prop
    _ = ENNReal.ofReal
          (∫ x : State d, c * ‖x0 - x‖ ^ 2
            ∂(V.target : Measure (State d))) := by
      rw [ofReal_integral_eq_lintegral_ofReal
        ((integrable_target_initialDistanceSq V x0).const_mul c)
        (ae_of_all _ fun x =>
          mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    _ = ENNReal.ofReal (c * targetInitialDistanceSq V x0) := by
      rw [integral_const_mul]
      rfl
    _ = _ := rfl

/-- A synchronous-contraction second-moment bound gives a
Lévy--Prokhorov estimate from the deterministic-start Euler endpoint to the
stationary-start Euler endpoint. -/
theorem levyProkhorovEDist_fixedEuler_stationaryEuler_le
    (delta : ℝ) (n : ℕ) (x0 : State d)
    (hdelta : 0 ≤ delta) (hmesh : V.L ^ 2 * delta ≤ V.m)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hcontract :
      Real.exp (-V.m * ((n : ℝ) * delta)) *
          targetInitialDistanceSq V x0 ≤ epsilon ^ 3) :
    levyProkhorovEDist
        (Measure.map (finiteEulerEuclideanEndpoint V delta x0)
          (stdGaussian (EuclideanSpace ℝ (Fin n × Fin d))))
        (stationaryFiniteEulerEndpointLaw V delta n : Measure (State d)) ≤
      ENNReal.ofReal epsilon := by
  have hblocks : Measurable
      (euclideanInnovationBlocks (n := n) (d := d)) := by
    unfold euclideanInnovationBlocks
    fun_prop
  have hendpoint : Measurable
      (finiteEulerEuclideanEndpoint V delta x0 :
        EuclideanSpace ℝ (Fin n × Fin d) → State d) := by
    unfold finiteEulerEuclideanEndpoint
    exact (measurable_finiteEulerState V delta x0 n).comp hblocks
  letI : IsProbabilityMeasure
      (Measure.map (finiteEulerEuclideanEndpoint V delta x0)
        (stdGaussian (EuclideanSpace ℝ (Fin n × Fin d)))) :=
    Measure.isProbabilityMeasure_map hendpoint.aemeasurable
  apply levyProkhorovEDist_le_of_coupling_lintegral_sq_le_cube
    (Measure.map (finiteEulerEuclideanEndpoint V delta x0)
      (stdGaussian (EuclideanSpace ℝ (Fin n × Fin d))))
    (stationaryFiniteEulerEndpointLaw V delta n : Measure (State d))
    (fixedStationaryFiniteEulerEndpointCoupling V delta n x0)
    (fst_fixedStationaryFiniteEulerEndpointCoupling V delta n x0)
    (snd_fixedStationaryFiniteEulerEndpointCoupling V delta n x0)
    hepsilon
  exact (lintegral_fixedStationaryFiniteEulerEndpointCoupling_le
    V delta n x0 hdelta hmesh).trans (ENNReal.ofReal_le_ofReal hcontract)

/-- Triangle combination of the deterministic-start contraction and the
stationary Euler/RWM approximation. -/
theorem levyProkhorovEDist_finiteEuler_target_le
    (delta : ℝ) (n : ℕ) (x0 : State d)
    (hdelta : 0 < delta) (hmesh : V.L ^ 2 * delta ≤ V.m)
    (hdeltaOne : delta ≤ 1) (hdeltaL : delta ≤ 2 / V.L)
    {epsilonContract epsilonStationary : ℝ}
    (hepsilonContract : 0 < epsilonContract)
    (hepsilonStationary : 0 < epsilonStationary)
    (hcontract :
      Real.exp (-V.m * ((n : ℝ) * delta)) *
          targetInitialDistanceSq V x0 ≤ epsilonContract ^ 3)
    (henergy :
      (∫ xy, pairSquaredDistance xy
        ∂stationaryEulerRWMPairChainLaw V delta n) ≤
          epsilonStationary ^ 3) :
    levyProkhorovEDist
        (Measure.map (finiteEulerEuclideanEndpoint V delta x0)
          (stdGaussian (EuclideanSpace ℝ (Fin n × Fin d))))
        (V.target : Measure (State d)) ≤
      ENNReal.ofReal epsilonContract + ENNReal.ofReal epsilonStationary := by
  calc
    levyProkhorovEDist
        (Measure.map (finiteEulerEuclideanEndpoint V delta x0)
          (stdGaussian (EuclideanSpace ℝ (Fin n × Fin d))))
        (V.target : Measure (State d)) ≤
        levyProkhorovEDist
          (Measure.map (finiteEulerEuclideanEndpoint V delta x0)
            (stdGaussian (EuclideanSpace ℝ (Fin n × Fin d))))
          (stationaryFiniteEulerEndpointLaw V delta n : Measure (State d)) +
        levyProkhorovEDist
          (stationaryFiniteEulerEndpointLaw V delta n : Measure (State d))
          (V.target : Measure (State d)) :=
      levyProkhorovEDist_triangle _ _ _
    _ ≤ ENNReal.ofReal epsilonContract +
        ENNReal.ofReal epsilonStationary := add_le_add
      (levyProkhorovEDist_fixedEuler_stationaryEuler_le V delta n x0
        hdelta.le hmesh hepsilonContract hcontract)
      (levyProkhorovEDist_stationaryFiniteEulerEndpointLaw_target_le
        V delta n hdelta hdeltaOne hdeltaL hepsilonStationary henergy)

/-- A purely discrete convergence criterion for deterministic-start Euler
endpoints.  It asks only for vanishing synchronous-contraction and
stationary Euler/RWM energy schedules. -/
theorem tendsto_finiteEulerEuclideanEndpointLaw_target_of_discreteBounds
    (delta : ℕ → ℝ) (steps : ℕ → ℕ) (x0 : State d)
    (hdelta : ∀ k, 0 < delta k)
    (hmesh : ∀ k, V.L ^ 2 * delta k ≤ V.m)
    (hdeltaOne : ∀ k, delta k ≤ 1)
    (hdeltaL : ∀ k, delta k ≤ 2 / V.L)
    (epsilonContract epsilonStationary : ℕ → ℝ)
    (hepsilonContract : ∀ k, 0 < epsilonContract k)
    (hepsilonStationary : ∀ k, 0 < epsilonStationary k)
    (hepsilonContractZero :
      Tendsto epsilonContract atTop (nhds 0))
    (hepsilonStationaryZero :
      Tendsto epsilonStationary atTop (nhds 0))
    (hcontract : ∀ k,
      Real.exp (-V.m * (((steps k : ℕ) : ℝ) * delta k)) *
          targetInitialDistanceSq V x0 ≤ epsilonContract k ^ 3)
    (henergy : ∀ k,
      (∫ xy, pairSquaredDistance xy
        ∂stationaryEulerRWMPairChainLaw V (delta k) (steps k)) ≤
          epsilonStationary k ^ 3) :
    Tendsto
      (fun k => finiteEulerEuclideanEndpointLaw V (steps k) (delta k)
        (hdelta k) (by nlinarith [hmesh k, V.hm]) x0)
      atTop (nhds V.target) := by
  have hsmall (k : ℕ) : V.L ^ 2 * delta k < 2 * V.m := by
    nlinarith [hmesh k, V.hm]
  let mu : ℕ → ProbabilityMeasure (State d) := fun k =>
    finiteEulerEuclideanEndpointLaw V (steps k) (delta k)
      (hdelta k) (hsmall k) x0
  let muLP : ℕ → LevyProkhorov (ProbabilityMeasure (State d)) :=
    fun k => LevyProkhorov.ofMeasure (mu k)
  let targetLP : LevyProkhorov (ProbabilityMeasure (State d)) :=
    LevyProkhorov.ofMeasure V.target
  have hbound (k : ℕ) :
      edist (muLP k) targetLP ≤
        ENNReal.ofReal (epsilonContract k) +
          ENNReal.ofReal (epsilonStationary k) := by
    rw [LevyProkhorov.edist_probabilityMeasure_def]
    simpa only [muLP, targetLP, mu,
      finiteEulerEuclideanEndpointLaw_toMeasure] using
      (levyProkhorovEDist_finiteEuler_target_le V
        (delta k) (steps k) x0 (hdelta k) (hmesh k)
        (hdeltaOne k) (hdeltaL k)
        (hepsilonContract k) (hepsilonStationary k)
        (hcontract k) (henergy k))
  have hupper : Tendsto (fun k =>
      ENNReal.ofReal (epsilonContract k) +
        ENNReal.ofReal (epsilonStationary k)) atTop (nhds 0) := by
    simpa using
      (ENNReal.tendsto_ofReal hepsilonContractZero).add
        (ENNReal.tendsto_ofReal hepsilonStationaryZero)
  have hedistZero : Tendsto (fun k => edist (muLP k) targetLP)
      atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _k : ℕ => (0 : ℝ≥0∞))
        atTop (nhds 0)) hupper
    · exact Eventually.of_forall fun _ => bot_le
    · exact Eventually.of_forall hbound
  have hLP : Tendsto muLP atTop (nhds targetLP) := by
    apply EMetric.tendsto_atTop.2
    intro epsilon hepsilon
    exact Filter.eventually_atTop.1
      ((tendsto_order.1 hedistZero).2 epsilon hepsilon)
  have hback :=
    LevyProkhorov.continuous_toMeasure_probabilityMeasure.continuousAt.tendsto.comp hLP
  have hfun : LevyProkhorov.toMeasure ∘ muLP = mu := by
    funext k
    rfl
  have htarget : LevyProkhorov.toMeasure targetLP = V.target := rfl
  rw [hfun, htarget] at hback
  simpa only [mu] using hback

/-! ## A diagonal long-time/fine-mesh schedule -/

/-- At every positive physical horizon and positive requested error, a
fine enough reciprocal mesh satisfies all small-step conditions and the
requested stationary Euler/RWM energy bound. -/
lemma exists_fineMesh_stationaryEnergy_le
    (h eta : ℝ) (hh : 0 < h) (heta : 0 < eta) :
    ∃ N : ℕ,
      let steps := N + 1
      let delta := h / (steps : ℝ)
      0 < delta ∧
      V.L ^ 2 * delta ≤ V.m ∧
      delta ≤ 1 ∧
      delta ≤ 2 / V.L ∧
      delta ≤ eta ∧
      (∫ xy, pairSquaredDistance xy
        ∂stationaryEulerRWMPairChainLaw V delta steps) ≤ eta ^ 3 ∧
      (steps : ℝ) * delta = h := by
  let deltaSeq : ℕ → ℝ := fun N => h / (((N + 1 : ℕ) : ℝ))
  have hdeltaZero : Tendsto deltaSeq atTop (nhds 0) := by
    dsimp [deltaSeq]
    exact (tendsto_const_div_atTop_nhds_zero_nat h).comp
      (tendsto_add_atTop_nat 1)
  have henergyZero :=
    tendsto_stationaryEulerRWMPairChain_energy_fixedHorizon V h hh
  have hmL : 0 < V.m / V.L ^ 2 :=
    div_pos V.hm (sq_pos_of_pos V.hL)
  have htwoL : 0 < 2 / V.L := div_pos (by norm_num) V.hL
  have hevMesh : ∀ᶠ N in atTop, deltaSeq N < V.m / V.L ^ 2 :=
    (tendsto_order.1 hdeltaZero).2 _ hmL
  have hevOne : ∀ᶠ N in atTop, deltaSeq N < 1 :=
    (tendsto_order.1 hdeltaZero).2 _ zero_lt_one
  have hevL : ∀ᶠ N in atTop, deltaSeq N < 2 / V.L :=
    (tendsto_order.1 hdeltaZero).2 _ htwoL
  have hevEta : ∀ᶠ N in atTop, deltaSeq N < eta :=
    (tendsto_order.1 hdeltaZero).2 _ heta
  have hevEnergy : ∀ᶠ N in atTop,
      (∫ xy, pairSquaredDistance xy
        ∂stationaryEulerRWMPairChainLaw V
          (deltaSeq N) (N + 1)) < eta ^ 3 :=
    (tendsto_order.1 henergyZero).2 _ (pow_pos heta 3)
  have hev : ∀ᶠ N in atTop,
      deltaSeq N < V.m / V.L ^ 2 ∧
      deltaSeq N < 1 ∧ deltaSeq N < 2 / V.L ∧
      deltaSeq N < eta ∧
      (∫ xy, pairSquaredDistance xy
        ∂stationaryEulerRWMPairChainLaw V
          (deltaSeq N) (N + 1)) < eta ^ 3 := by
    filter_upwards [hevMesh, hevOne, hevL, hevEta, hevEnergy]
      with N hM h1 hL hEta hE
    exact ⟨hM, h1, hL, hEta, hE⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N, ?_⟩
  have hprops := hN N (le_refl N)
  dsimp only [deltaSeq] at hprops ⊢
  have hdeltaPos : 0 < h / (((N + 1 : ℕ) : ℝ)) :=
    div_pos hh (by positivity)
  refine ⟨hdeltaPos, ?_, hprops.2.1.le, hprops.2.2.1.le,
    hprops.2.2.2.1.le, hprops.2.2.2.2.le, ?_⟩
  · have hmul := (lt_div_iff₀ (sq_pos_of_pos V.hL)).mp hprops.1
    nlinarith
  · field_simp

/-- Increasing physical horizon used by the diagonal endpoint schedule. -/
def finiteEulerTargetDiagonalHorizon (k : ℕ) : ℝ := ((k + 1 : ℕ) : ℝ)

/-- Common reciprocal tolerance used for mesh size and stationary energy. -/
def finiteEulerTargetDiagonalTolerance (k : ℕ) : ℝ :=
  1 / ((k + 1 : ℕ) : ℝ)

lemma finiteEulerTargetDiagonalHorizon_pos (k : ℕ) :
    0 < finiteEulerTargetDiagonalHorizon k := by
  unfold finiteEulerTargetDiagonalHorizon
  positivity

lemma finiteEulerTargetDiagonalTolerance_pos (k : ℕ) :
    0 < finiteEulerTargetDiagonalTolerance k := by
  unfold finiteEulerTargetDiagonalTolerance
  positivity

theorem tendsto_finiteEulerTargetDiagonalTolerance :
    Tendsto finiteEulerTargetDiagonalTolerance atTop (nhds 0) := by
  unfold finiteEulerTargetDiagonalTolerance
  exact (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
    (tendsto_add_atTop_nat 1)

/-- Noncomputable diagonal choice of a sufficiently fine reciprocal mesh
for horizon `k+1` and tolerance `1/(k+1)`. -/
def finiteEulerTargetDiagonalMeshIndex (V : FirstOrderPotential d)
    (k : ℕ) : ℕ :=
  Classical.choose (exists_fineMesh_stationaryEnergy_le V
    (finiteEulerTargetDiagonalHorizon k)
    (finiteEulerTargetDiagonalTolerance k)
    (finiteEulerTargetDiagonalHorizon_pos k)
    (finiteEulerTargetDiagonalTolerance_pos k))

def finiteEulerTargetDiagonalSteps (V : FirstOrderPotential d)
    (k : ℕ) : ℕ :=
  finiteEulerTargetDiagonalMeshIndex V k + 1

def finiteEulerTargetDiagonalDelta (V : FirstOrderPotential d)
    (k : ℕ) : ℝ :=
  finiteEulerTargetDiagonalHorizon k /
    (finiteEulerTargetDiagonalSteps V k : ℝ)

/-- All pointwise numerical facts furnished by the diagonal mesh choice. -/
theorem finiteEulerTargetDiagonal_spec (k : ℕ) :
    0 < finiteEulerTargetDiagonalDelta V k ∧
    V.L ^ 2 * finiteEulerTargetDiagonalDelta V k ≤ V.m ∧
    finiteEulerTargetDiagonalDelta V k ≤ 1 ∧
    finiteEulerTargetDiagonalDelta V k ≤ 2 / V.L ∧
    finiteEulerTargetDiagonalDelta V k ≤
      finiteEulerTargetDiagonalTolerance k ∧
    (∫ xy, pairSquaredDistance xy
      ∂stationaryEulerRWMPairChainLaw V
        (finiteEulerTargetDiagonalDelta V k)
        (finiteEulerTargetDiagonalSteps V k)) ≤
      finiteEulerTargetDiagonalTolerance k ^ 3 ∧
    (finiteEulerTargetDiagonalSteps V k : ℝ) *
      finiteEulerTargetDiagonalDelta V k =
        finiteEulerTargetDiagonalHorizon k := by
  simpa only [finiteEulerTargetDiagonalDelta,
    finiteEulerTargetDiagonalSteps, finiteEulerTargetDiagonalMeshIndex] using
    (Classical.choose_spec (exists_fineMesh_stationaryEnergy_le V
      (finiteEulerTargetDiagonalHorizon k)
      (finiteEulerTargetDiagonalTolerance k)
      (finiteEulerTargetDiagonalHorizon_pos k)
      (finiteEulerTargetDiagonalTolerance_pos k)))

theorem tendsto_finiteEulerTargetDiagonalDelta :
    Tendsto (finiteEulerTargetDiagonalDelta V) atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _k : ℕ => (0 : ℝ))
      atTop (nhds 0)) tendsto_finiteEulerTargetDiagonalTolerance
  · exact Eventually.of_forall fun k =>
      (finiteEulerTargetDiagonal_spec V k).1.le
  · exact Eventually.of_forall fun k =>
      (finiteEulerTargetDiagonal_spec V k).2.2.2.2.1

lemma finiteEulerTargetDiagonalDelta_pos (k : ℕ) :
    0 < finiteEulerTargetDiagonalDelta V k :=
  (finiteEulerTargetDiagonal_spec V k).1

lemma finiteEulerTargetDiagonal_mesh (k : ℕ) :
    V.L ^ 2 * finiteEulerTargetDiagonalDelta V k ≤ V.m :=
  (finiteEulerTargetDiagonal_spec V k).2.1

lemma finiteEulerTargetDiagonalDelta_le_one (k : ℕ) :
    finiteEulerTargetDiagonalDelta V k ≤ 1 :=
  (finiteEulerTargetDiagonal_spec V k).2.2.1

lemma finiteEulerTargetDiagonalDelta_le_two_div_L (k : ℕ) :
    finiteEulerTargetDiagonalDelta V k ≤ 2 / V.L :=
  (finiteEulerTargetDiagonal_spec V k).2.2.2.1

lemma finiteEulerTargetDiagonal_energy (k : ℕ) :
    (∫ xy, pairSquaredDistance xy
      ∂stationaryEulerRWMPairChainLaw V
        (finiteEulerTargetDiagonalDelta V k)
        (finiteEulerTargetDiagonalSteps V k)) ≤
      finiteEulerTargetDiagonalTolerance k ^ 3 :=
  (finiteEulerTargetDiagonal_spec V k).2.2.2.2.2.1

lemma finiteEulerTargetDiagonal_horizon (k : ℕ) :
    (finiteEulerTargetDiagonalSteps V k : ℝ) *
      finiteEulerTargetDiagonalDelta V k =
        finiteEulerTargetDiagonalHorizon k :=
  (finiteEulerTargetDiagonal_spec V k).2.2.2.2.2.2

/-- Initial-condition discrepancy at diagonal horizon `k+1`. -/
def finiteEulerTargetDiagonalContractionEnergy
    (V : FirstOrderPotential d) (x0 : State d) (k : ℕ) : ℝ :=
  Real.exp (-V.m * finiteEulerTargetDiagonalHorizon k) *
    targetInitialDistanceSq V x0

lemma finiteEulerTargetDiagonalContractionEnergy_nonneg
    (x0 : State d) (k : ℕ) :
    0 ≤ finiteEulerTargetDiagonalContractionEnergy V x0 k := by
  unfold finiteEulerTargetDiagonalContractionEnergy
  exact mul_nonneg (Real.exp_pos _).le
    (targetInitialDistanceSq_nonneg V x0)

theorem tendsto_finiteEulerTargetDiagonalContractionEnergy
    (x0 : State d) :
    Tendsto (finiteEulerTargetDiagonalContractionEnergy V x0)
      atTop (nhds 0) := by
  have hhorizon : Tendsto finiteEulerTargetDiagonalHorizon
      atTop atTop := by
    unfold finiteEulerTargetDiagonalHorizon
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hneg : Tendsto
      (fun k => -V.m * finiteEulerTargetDiagonalHorizon k)
      atTop atBot :=
    hhorizon.const_mul_atTop_of_neg (neg_lt_zero.mpr V.hm)
  have hexp : Tendsto
      (fun k => Real.exp (-V.m * finiteEulerTargetDiagonalHorizon k))
      atTop (nhds 0) := Real.tendsto_exp_atBot.comp hneg
  change Tendsto (fun k =>
    Real.exp (-V.m * finiteEulerTargetDiagonalHorizon k) *
      targetInitialDistanceSq V x0) atTop (nhds 0)
  simpa only [zero_mul] using
    hexp.mul_const (targetInitialDistanceSq V x0)

/-- Positive cube-dominating contraction tolerance. -/
def finiteEulerTargetDiagonalContractionEpsilon
    (V : FirstOrderPotential d) (x0 : State d) (k : ℕ) : ℝ :=
  finiteEulerTargetDiagonalContractionEnergy V x0 k +
    Real.sqrt (Real.sqrt
      (finiteEulerTargetDiagonalContractionEnergy V x0 k)) +
    finiteEulerTargetDiagonalTolerance k

lemma finiteEulerTargetDiagonalContractionEpsilon_pos
    (x0 : State d) (k : ℕ) :
    0 < finiteEulerTargetDiagonalContractionEpsilon V x0 k := by
  unfold finiteEulerTargetDiagonalContractionEpsilon
  have ha := finiteEulerTargetDiagonalContractionEnergy_nonneg V x0 k
  have hs := Real.sqrt_nonneg
    (Real.sqrt (finiteEulerTargetDiagonalContractionEnergy V x0 k))
  have hr := finiteEulerTargetDiagonalTolerance_pos k
  linarith

lemma finiteEulerTargetDiagonalContractionEnergy_le_epsilon_cube
    (x0 : State d) (k : ℕ) :
    finiteEulerTargetDiagonalContractionEnergy V x0 k ≤
      finiteEulerTargetDiagonalContractionEpsilon V x0 k ^ 3 := by
  exact le_cube_self_add_sqrt_sqrt_add
    (finiteEulerTargetDiagonalContractionEnergy V x0 k)
    (finiteEulerTargetDiagonalTolerance k)
    (finiteEulerTargetDiagonalContractionEnergy_nonneg V x0 k)
    (finiteEulerTargetDiagonalTolerance_pos k)

theorem tendsto_finiteEulerTargetDiagonalContractionEpsilon
    (x0 : State d) :
    Tendsto (finiteEulerTargetDiagonalContractionEpsilon V x0)
      atTop (nhds 0) := by
  have henergy :=
    tendsto_finiteEulerTargetDiagonalContractionEnergy V x0
  change Tendsto (fun k =>
    finiteEulerTargetDiagonalContractionEnergy V x0 k +
      Real.sqrt (Real.sqrt
        (finiteEulerTargetDiagonalContractionEnergy V x0 k)) +
      finiteEulerTargetDiagonalTolerance k) atTop (nhds 0)
  simpa only [Real.sqrt_zero, add_zero] using
    (henergy.add henergy.sqrt.sqrt).add
      tendsto_finiteEulerTargetDiagonalTolerance

/-- The explicit diagonal finite Euler endpoint laws converge weakly to the
normalized target.  This is the elementary discrete-time replacement for an
SDE endpoint-identification theorem. -/
theorem tendsto_finiteEulerTargetDiagonalEndpointLaw
    (x0 : State d) :
    Tendsto
      (fun k => finiteEulerEuclideanEndpointLaw V
        (finiteEulerTargetDiagonalSteps V k)
        (finiteEulerTargetDiagonalDelta V k)
        (finiteEulerTargetDiagonalDelta_pos V k)
        (by nlinarith [finiteEulerTargetDiagonal_mesh V k, V.hm]) x0)
      atTop (nhds V.target) := by
  apply tendsto_finiteEulerEuclideanEndpointLaw_target_of_discreteBounds
    V (finiteEulerTargetDiagonalDelta V)
    (finiteEulerTargetDiagonalSteps V) x0
    (finiteEulerTargetDiagonalDelta_pos V)
    (finiteEulerTargetDiagonal_mesh V)
    (finiteEulerTargetDiagonalDelta_le_one V)
    (finiteEulerTargetDiagonalDelta_le_two_div_L V)
    (finiteEulerTargetDiagonalContractionEpsilon V x0)
    finiteEulerTargetDiagonalTolerance
    (finiteEulerTargetDiagonalContractionEpsilon_pos V x0)
    finiteEulerTargetDiagonalTolerance_pos
    (tendsto_finiteEulerTargetDiagonalContractionEpsilon V x0)
    tendsto_finiteEulerTargetDiagonalTolerance
  · intro k
    rw [finiteEulerTargetDiagonal_horizon V k]
    exact finiteEulerTargetDiagonalContractionEnergy_le_epsilon_cube V x0 k
  · exact finiteEulerTargetDiagonal_energy V

/-- The explicit diagonal Euler construction transfers the finite-dimensional
canonical Gaussian interpolation certificate to the normalized target.  All
endpoint identification and weak-limit hypotheses are discharged here; the
only remaining analytic input is the canonical Gaussian certificate in each
finite innovation dimension. -/
theorem target_bakryLedoux_of_canonicalInterpolations
    (x0 : State d)
    (hcanonical : ∀ k,
      CanonicalGaussianBobkovInterpolationProperty
        (E := EuclideanSpace ℝ
          (Fin (finiteEulerTargetDiagonalSteps V k) × Fin d))) :
    BakryLedouxEnlargement (V.target : Measure (State d)) V.m
      (cdf standardGaussianMeasure)
      (lowerQuantile standardGaussianMeasure) := by
  apply finiteEulerEndpointLimit_bakryLedoux_of_canonicalInterpolations
    V (finiteEulerTargetDiagonalSteps V)
    (finiteEulerTargetDiagonalDelta V)
    (finiteEulerTargetDiagonalDelta_pos V)
    (fun k => by
      have hmesh := finiteEulerTargetDiagonal_mesh V k
      nlinarith [V.hm])
    (tendsto_finiteEulerTargetDiagonalDelta V)
    x0 hcanonical
    (tendsto_finiteEulerTargetDiagonalEndpointLaw V x0)

end Recursion

end DiscreteTime
end
end UniformRandomMALA
