import UniformRandomMALA.Concrete.BakryLedouxReduction
import UniformRandomMALA.Concrete.FiniteEulerEnergyMGF

/-!
# Finite Euler endpoints as Lipschitz Gaussian images

This file contains the deterministic core of the discrete Langevin route to
Bakry--Ledoux.  It compares two finite Euler paths driven by different finite
innovation tuples.  No stochastic process, limiting argument, or
isoperimetric theorem is used here.
-/

namespace UniformRandomMALA

noncomputable section

namespace DiscreteTime

open Concrete Finset

/-- Reverse geometric accumulation.  This is the solution of the finite
affine recursion `s (n+1) = rho * s n + b n`, `s 0 = 0`. -/
def reverseGeometricAccum (rho : ℝ) (b : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => rho * reverseGeometricAccum rho b n + b n

@[simp] lemma reverseGeometricAccum_zero (rho : ℝ) (b : ℕ → ℝ) :
    reverseGeometricAccum rho b 0 = 0 := rfl

@[simp] lemma reverseGeometricAccum_succ (rho : ℝ) (b : ℕ → ℝ) (n : ℕ) :
    reverseGeometricAccum rho b (n + 1) =
      rho * reverseGeometricAccum rho b n + b n := rfl

/-- Exact finite solution of an affine upper recursion. -/
lemma affine_recursion_le_reverseGeometricAccum
    (a b : ℕ → ℝ) (rho c : ℝ)
    (hrho : 0 ≤ rho)
    (ha0 : a 0 ≤ 0)
    (hstep : ∀ k, a (k + 1) ≤ rho * a k + c * b k) :
    ∀ n, a n ≤ c * reverseGeometricAccum rho b n := by
  intro n
  induction n with
  | zero => simpa using ha0
  | succ n ih =>
      calc
        a (n + 1) ≤ rho * a n + c * b n := hstep n
        _ ≤ rho * (c * reverseGeometricAccum rho b n) + c * b n :=
          by simpa [add_comm] using
            add_le_add_right (mul_le_mul_of_nonneg_left ih hrho) (c * b n)
        _ = c * reverseGeometricAccum rho b (n + 1) := by
          rw [reverseGeometricAccum_succ]
          ring

lemma reverseGeometricAccum_nonneg
    (rho : ℝ) (b : ℕ → ℝ) (hrho : 0 ≤ rho)
    (hb : ∀ k, 0 ≤ b k) :
    ∀ n, 0 ≤ reverseGeometricAccum rho b n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [reverseGeometricAccum_succ]
      exact add_nonneg (mul_nonneg hrho ih) (hb n)

/-- Closed finite-sum form of `reverseGeometricAccum`. -/
lemma reverseGeometricAccum_eq_sum (rho : ℝ) (b : ℕ → ℝ) :
    ∀ n, reverseGeometricAccum rho b n =
      ∑ j ∈ range n, rho ^ (n - 1 - j) * b j := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [reverseGeometricAccum_succ, ih, sum_range_succ, mul_sum]
      simp only [Nat.add_sub_cancel]
      congr 1
      · apply sum_congr rfl
        intro j hj
        have hjn : j < n := mem_range.mp hj
        have hexp : n - 1 - j + 1 = n - j := by omega
        rw [← mul_assoc, ← pow_succ', hexp]
      · simp

/-- Finite Cauchy--Schwarz for the reverse geometric accumulation. -/
lemma reverseGeometricAccum_sq_le (rho : ℝ) (b : ℕ → ℝ) (n : ℕ) :
    reverseGeometricAccum rho b n ^ 2 ≤
      (∑ j ∈ range n, (rho ^ (n - 1 - j)) ^ 2) *
        ∑ j ∈ range n, (b j) ^ 2 := by
  rw [reverseGeometricAccum_eq_sum]
  exact sum_mul_sq_le_sq_mul_sq (range n)
    (fun j => rho ^ (n - 1 - j)) b

/-- The reverse geometric sum is the usual geometric sum.  Keeping this as a
separate finite identity avoids any appeal to infinite series. -/
lemma reverseGeometricAccum_one_eq_geomSum (rho : ℝ) :
    ∀ n, reverseGeometricAccum rho (fun _ => 1) n =
      ∑ j ∈ range n, rho ^ j := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [reverseGeometricAccum_succ, ih, sum_range_succ]
      have hgeom := geom_sum_mul_neg rho n
      nlinarith

/-- Reversing the finite powers does not change their sum.  The squared form
is the one occurring in the endpoint sensitivity coefficient. -/
lemma sum_reverse_pow_sq_eq_geomSum (rho : ℝ) (n : ℕ) :
    (∑ j ∈ range n, (rho ^ (n - 1 - j)) ^ 2) =
      ∑ j ∈ range n, (rho ^ 2) ^ j := by
  calc
    (∑ j ∈ range n, (rho ^ (n - 1 - j)) ^ 2) =
        ∑ j ∈ range n, (rho ^ 2) ^ (n - 1 - j) := by
          apply sum_congr rfl
          intro j _
          rw [← pow_mul, ← pow_mul]
          congr 1
          omega
    _ = reverseGeometricAccum (rho ^ 2) (fun _ => 1) n := by
          rw [reverseGeometricAccum_eq_sum]
          simp
    _ = ∑ j ∈ range n, (rho ^ 2) ^ j :=
          reverseGeometricAccum_one_eq_geomSum (rho ^ 2) n

/-- Split a single Euclidean vector indexed by `Fin n × Fin d` into its `n`
Euclidean innovation blocks. -/
def euclideanInnovationBlocks {n d : ℕ}
    (z : EuclideanSpace ℝ (Fin n × Fin d)) : Fin n → State d :=
  fun j => WithLp.toLp 2 (fun i => z (j, i))

@[simp] lemma euclideanInnovationBlocks_apply {n d : ℕ}
    (z : EuclideanSpace ℝ (Fin n × Fin d)) (j : Fin n) (i : Fin d) :
    euclideanInnovationBlocks z j i = z (j, i) := rfl

/-- The block decomposition preserves the squared Euclidean product norm. -/
lemma sum_norm_euclideanInnovationBlocks_sub_sq {n d : ℕ}
    (z w : EuclideanSpace ℝ (Fin n × Fin d)) :
    (∑ j, ‖euclideanInnovationBlocks z j -
        euclideanInnovationBlocks w j‖ ^ 2) = ‖z - w‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq,
    euclideanInnovationBlocks_apply, PiLp.sub_apply]
  symm
  simpa using (Finset.sum_product (Finset.univ : Finset (Fin n))
    (Finset.univ : Finset (Fin d))
    (fun p : Fin n × Fin d => (z p - w p) ^ 2))

/-- The natural-number sum over all totalized blocks is the Euclidean source
norm. -/
lemma sum_range_finiteInnovationBlocks_sub_sq {n d : ℕ}
    (z w : EuclideanSpace ℝ (Fin n × Fin d)) :
    (∑ j ∈ range n,
        ‖finiteInnovationNat (euclideanInnovationBlocks z) j -
          finiteInnovationNat (euclideanInnovationBlocks w) j‖ ^ 2) =
      ‖z - w‖ ^ 2 := by
  rw [← sum_norm_euclideanInnovationBlocks_sub_sq]
  rw [Finset.sum_fin_eq_sum_range]
  apply sum_congr rfl
  intro j hj
  have hjn : j < n := mem_range.mp hj
  simp only [dif_pos hjn, finiteInnovationNat_of_lt _ hjn]

section Euler

variable {d n : ℕ} (V : FirstOrderPotential d)

/-- Synchronous finite Euler paths contract their initial separation by the
finite power of the one-step Euler contraction factor.  The innovations are
identical, so this is a completely deterministic discrete-time substitute
for the corresponding SDE contraction. -/
lemma finiteEulerState_initialSensitivity
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (x0 y0 : State d) (z : Fin n → State d) (k : ℕ) :
    ‖finiteEulerState V delta x0 z k -
        finiteEulerState V delta y0 z k‖ ≤
      V.eulerContractionFactor delta ^ k * ‖x0 - y0‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [finiteEulerState_succ_eq_innovationNat,
        finiteEulerState_succ_eq_innovationNat]
      have hcancel :
          (finiteEulerState V delta x0 z k -
                delta • V.gradU (finiteEulerState V delta x0 z k) +
              Real.sqrt (2 * delta) • finiteInnovationNat z k) -
            (finiteEulerState V delta y0 z k -
                delta • V.gradU (finiteEulerState V delta y0 z k) +
              Real.sqrt (2 * delta) • finiteInnovationNat z k) =
          (finiteEulerState V delta x0 z k -
              delta • V.gradU (finiteEulerState V delta x0 z k)) -
            (finiteEulerState V delta y0 z k -
              delta • V.gradU (finiteEulerState V delta y0 z k)) := by
        module
      rw [hcancel]
      calc
        ‖(finiteEulerState V delta x0 z k -
              delta • V.gradU (finiteEulerState V delta x0 z k)) -
            (finiteEulerState V delta y0 z k -
              delta • V.gradU (finiteEulerState V delta y0 z k))‖ ≤
            V.eulerContractionFactor delta *
              ‖finiteEulerState V delta x0 z k -
                finiteEulerState V delta y0 z k‖ :=
          V.eulerDrift_norm_le delta hdelta _ _
        _ ≤ V.eulerContractionFactor delta *
            (V.eulerContractionFactor delta ^ k * ‖x0 - y0‖) :=
          mul_le_mul_of_nonneg_left ih
            (V.eulerContractionFactor_nonneg delta)
        _ = V.eulerContractionFactor delta ^ (k + 1) * ‖x0 - y0‖ := by
          rw [pow_succ]
          ring

/-- Exponential squared contraction at physical time `k * delta`.  The
slightly stronger mesh condition `L² delta ≤ m` makes the elementary
finite-product comparison transparent. -/
lemma finiteEulerState_initialSensitivity_sq_le_exp
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hmesh : V.L ^ 2 * delta ≤ V.m)
    (x0 y0 : State d) (z : Fin n → State d) (k : ℕ) :
    ‖finiteEulerState V delta x0 z k -
        finiteEulerState V delta y0 z k‖ ^ 2 ≤
      Real.exp (-V.m * ((k : ℝ) * delta)) * ‖x0 - y0‖ ^ 2 := by
  let q := V.eulerContractionFactor delta
  have hq0 : 0 ≤ q := V.eulerContractionFactor_nonneg delta
  have hqbase : q ^ 2 ≤ 1 - V.m * delta := by
    rw [V.eulerContractionFactor_sq]
    unfold FirstOrderPotential.eulerContractionFactorSq
    nlinarith
  have hbase0 : 0 ≤ 1 - V.m * delta :=
    (sq_nonneg q).trans hqbase
  have hpowbase : (q ^ 2) ^ k ≤ (1 - V.m * delta) ^ k :=
    pow_le_pow_left₀ (sq_nonneg q) hqbase k
  have hbaseexp : 1 - V.m * delta ≤ Real.exp (-(V.m * delta)) :=
    Real.one_sub_le_exp_neg (V.m * delta)
  have hpowexp : (1 - V.m * delta) ^ k ≤
      (Real.exp (-(V.m * delta))) ^ k :=
    pow_le_pow_left₀ hbase0 hbaseexp k
  have hqexp : q ^ (2 * k) ≤
      Real.exp (-V.m * ((k : ℝ) * delta)) := by
    calc
      q ^ (2 * k) = (q ^ 2) ^ k := by rw [pow_mul]
      _ ≤ (1 - V.m * delta) ^ k := hpowbase
      _ ≤ (Real.exp (-(V.m * delta))) ^ k := hpowexp
      _ = Real.exp (-V.m * ((k : ℝ) * delta)) := by
        rw [show -V.m * ((k : ℝ) * delta) =
          (k : ℝ) * (-(V.m * delta)) by ring]
        rw [Real.exp_nat_mul]
  have hsens := finiteEulerState_initialSensitivity V
    delta hdelta x0 y0 z k
  have hsq :
      ‖finiteEulerState V delta x0 z k -
          finiteEulerState V delta y0 z k‖ ^ 2 ≤
        (q ^ k * ‖x0 - y0‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (pow_nonneg hq0 k) (norm_nonneg _))).2 hsens
  calc
    ‖finiteEulerState V delta x0 z k -
        finiteEulerState V delta y0 z k‖ ^ 2 ≤
        (q ^ k * ‖x0 - y0‖) ^ 2 := hsq
    _ = q ^ (2 * k) * ‖x0 - y0‖ ^ 2 := by ring
    _ ≤ Real.exp (-V.m * ((k : ℝ) * delta)) *
        ‖x0 - y0‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hqexp (sq_nonneg _)

/-- The norm of the difference of two finite Euler paths is bounded by the
reverse geometric accumulation of the innovation differences.  The paths
start from the same point. -/
lemma finiteEulerState_innovationSensitivity
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (x0 : State d) (z w : Fin n → State d) (k : ℕ) :
    ‖finiteEulerState V delta x0 z k -
        finiteEulerState V delta x0 w k‖ ≤
      Real.sqrt (2 * delta) *
        reverseGeometricAccum (V.eulerContractionFactor delta)
          (fun j => ‖finiteInnovationNat z j - finiteInnovationNat w j‖) k := by
  let a : ℕ → ℝ := fun j =>
    ‖finiteEulerState V delta x0 z j - finiteEulerState V delta x0 w j‖
  let b : ℕ → ℝ := fun j =>
    ‖finiteInnovationNat z j - finiteInnovationNat w j‖
  apply affine_recursion_le_reverseGeometricAccum a b
      (V.eulerContractionFactor delta) (Real.sqrt (2 * delta))
      (V.eulerContractionFactor_nonneg delta)
  · simp [a]
  · intro j
    dsimp [a, b]
    rw [finiteEulerState_succ_eq_innovationNat,
      finiteEulerState_succ_eq_innovationNat]
    have hdecomp :
        (finiteEulerState V delta x0 z j -
              delta • V.gradU (finiteEulerState V delta x0 z j) +
            Real.sqrt (2 * delta) • finiteInnovationNat z j) -
          (finiteEulerState V delta x0 w j -
              delta • V.gradU (finiteEulerState V delta x0 w j) +
            Real.sqrt (2 * delta) • finiteInnovationNat w j) =
        ((finiteEulerState V delta x0 z j -
              delta • V.gradU (finiteEulerState V delta x0 z j)) -
          (finiteEulerState V delta x0 w j -
              delta • V.gradU (finiteEulerState V delta x0 w j))) +
          Real.sqrt (2 * delta) •
            (finiteInnovationNat z j - finiteInnovationNat w j) := by
      module
    rw [hdecomp]
    calc
      ‖((finiteEulerState V delta x0 z j -
              delta • V.gradU (finiteEulerState V delta x0 z j)) -
          (finiteEulerState V delta x0 w j -
              delta • V.gradU (finiteEulerState V delta x0 w j))) +
          Real.sqrt (2 * delta) •
            (finiteInnovationNat z j - finiteInnovationNat w j)‖
          ≤ ‖(finiteEulerState V delta x0 z j -
                delta • V.gradU (finiteEulerState V delta x0 z j)) -
              (finiteEulerState V delta x0 w j -
                delta • V.gradU (finiteEulerState V delta x0 w j))‖ +
              ‖Real.sqrt (2 * delta) •
                (finiteInnovationNat z j - finiteInnovationNat w j)‖ :=
            norm_add_le _ _
      _ ≤ V.eulerContractionFactor delta *
              ‖finiteEulerState V delta x0 z j -
                finiteEulerState V delta x0 w j‖ +
            Real.sqrt (2 * delta) *
              ‖finiteInnovationNat z j - finiteInnovationNat w j‖ := by
          gcongr
          · exact V.eulerDrift_norm_le delta hdelta _ _
          · rw [norm_smul, Real.norm_eq_abs,
              abs_of_nonneg (Real.sqrt_nonneg _)]
      _ = V.eulerContractionFactor delta * a j +
            Real.sqrt (2 * delta) * b j := rfl

/-- Squared `ℓ²` form of `finiteEulerState_innovationSensitivity`.  This is
the exact deterministic estimate needed to view a finite Euler endpoint as a
Lipschitz image of its finite Gaussian innovation vector. -/
lemma finiteEulerState_innovationSensitivity_sq
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (x0 : State d) (z w : Fin n → State d) (k : ℕ) :
    ‖finiteEulerState V delta x0 z k -
        finiteEulerState V delta x0 w k‖ ^ 2 ≤
      (2 * delta *
          ∑ j ∈ range k,
            (V.eulerContractionFactor delta ^ (k - 1 - j)) ^ 2) *
        ∑ j ∈ range k,
          ‖finiteInnovationNat z j - finiteInnovationNat w j‖ ^ 2 := by
  let b : ℕ → ℝ := fun j =>
    ‖finiteInnovationNat z j - finiteInnovationNat w j‖
  let R : ℝ := reverseGeometricAccum (V.eulerContractionFactor delta) b k
  have hR0 : 0 ≤ R := by
    apply reverseGeometricAccum_nonneg
    · exact V.eulerContractionFactor_nonneg delta
    · intro j
      exact norm_nonneg _
  have hsens := finiteEulerState_innovationSensitivity V
    delta hdelta x0 z w k
  change ‖finiteEulerState V delta x0 z k -
        finiteEulerState V delta x0 w k‖ ≤ Real.sqrt (2 * delta) * R at hsens
  have hsquare :
      ‖finiteEulerState V delta x0 z k -
          finiteEulerState V delta x0 w k‖ ^ 2 ≤
        (Real.sqrt (2 * delta) * R) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) hR0)).2 hsens
  have hcs := reverseGeometricAccum_sq_le
    (V.eulerContractionFactor delta) b k
  change R ^ 2 ≤
    (∑ j ∈ range k,
        (V.eulerContractionFactor delta ^ (k - 1 - j)) ^ 2) *
      ∑ j ∈ range k, (b j) ^ 2 at hcs
  have htwo : 0 ≤ 2 * delta := mul_nonneg (by norm_num) hdelta
  have hmul :
      (2 * delta) * R ^ 2 ≤
        (2 * delta) *
          ((∑ j ∈ range k,
              (V.eulerContractionFactor delta ^ (k - 1 - j)) ^ 2) *
            ∑ j ∈ range k, (b j) ^ 2) :=
    mul_le_mul_of_nonneg_left hcs htwo
  calc
    ‖finiteEulerState V delta x0 z k -
        finiteEulerState V delta x0 w k‖ ^ 2
        ≤ (Real.sqrt (2 * delta) * R) ^ 2 := hsquare
    _ = (2 * delta) * R ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num) hdelta)]
    _ ≤ (2 * delta) *
        ((∑ j ∈ range k,
            (V.eulerContractionFactor delta ^ (k - 1 - j)) ^ 2) *
          ∑ j ∈ range k, (b j) ^ 2) := hmul
    _ = (2 * delta *
          ∑ j ∈ range k,
            (V.eulerContractionFactor delta ^ (k - 1 - j)) ^ 2) *
        ∑ j ∈ range k,
          ‖finiteInnovationNat z j - finiteInnovationNat w j‖ ^ 2 := by
      dsimp [b]
      ring

/-- The finite geometric coefficient in the squared endpoint sensitivity is
bounded by the resolvent-like constant `2 / (2m - L²δ)`.  This is a purely
finite identity and inequality: no infinite geometric series is used. -/
lemma finiteEuler_geometricCoefficient_le
    (delta : ℝ)
    (hsmall : V.L ^ 2 * delta < 2 * V.m) (k : ℕ) :
    2 * delta *
        (∑ j ∈ range k,
          (V.eulerContractionFactor delta ^ (k - 1 - j)) ^ 2) ≤
      2 / (2 * V.m - V.L ^ 2 * delta) := by
  let q : ℝ := V.eulerContractionFactor delta ^ 2
  have hq0 : 0 ≤ q := sq_nonneg _
  have hdenom : 0 < 2 * V.m - V.L ^ 2 * delta := sub_pos.mpr hsmall
  have hfactor :
      delta * (2 * V.m - V.L ^ 2 * delta) = 1 - q := by
    dsimp [q]
    rw [V.eulerContractionFactor_sq]
    unfold FirstOrderPotential.eulerContractionFactorSq
    ring
  have hgeom := geom_sum_mul_neg q k
  have hpow : 0 ≤ q ^ k := pow_nonneg hq0 k
  rw [sum_reverse_pow_sq_eq_geomSum]
  apply (le_div_iff₀ hdenom).2
  calc
    (2 * delta * (∑ j ∈ range k, q ^ j)) *
          (2 * V.m - V.L ^ 2 * delta) =
        2 * ((∑ j ∈ range k, q ^ j) * (1 - q)) := by
          rw [← hfactor]
          ring
    _ = 2 * (1 - q ^ k) := by rw [hgeom]
    _ ≤ 2 := by nlinarith

/-- The finite-Euler squared sensitivity constant tends to the sharp
Bakry--Ledoux value `1 / m` as the mesh tends to zero. -/
lemma tendsto_finiteEulerSensitivityCoefficient_zero :
    Filter.Tendsto
      (fun delta : ℝ => 2 / (2 * V.m - V.L ^ 2 * delta))
      (nhds 0) (nhds (1 / V.m)) := by
  have hden : 2 * V.m - V.L ^ 2 * (0 : ℝ) ≠ 0 := by
    norm_num [V.hm.ne']
  have hdencont : ContinuousAt
      (fun delta : ℝ => 2 * V.m - V.L ^ 2 * delta) 0 := by
    fun_prop
  have hcont : ContinuousAt
      (fun delta : ℝ => 2 / (2 * V.m - V.L ^ 2 * delta)) 0 := by
    exact continuousAt_const.div hdencont hden
  have hvalue :
      2 / (2 * V.m - V.L ^ 2 * (0 : ℝ)) = 1 / V.m := by
    norm_num
    field_simp [V.hm.ne']
  rw [← hvalue]
  exact hcont.tendsto

/-- Fixed physical time `T` and mesh `T/(N+1)`: the same coefficient tends
to `1/m`.  The deliberately coarser geometric bound removes the otherwise
unnecessary limit of `rho_N^(2N)`. -/
lemma tendsto_finiteEulerSensitivityCoefficient_fixedTime (T : ℝ) :
    Filter.Tendsto
      (fun N : ℕ =>
        2 / (2 * V.m - V.L ^ 2 * (T / ((N : ℝ) + 1))))
      Filter.atTop (nhds (1 / V.m)) := by
  have hmesh : Filter.Tendsto
      (fun N : ℕ => T / ((N : ℝ) + 1)) Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul T)
  exact (tendsto_finiteEulerSensitivityCoefficient_zero V).comp hmesh

/-- For every fixed physical time, all sufficiently fine meshes satisfy the
small-step hypothesis used by the finite endpoint estimate. -/
lemma eventually_finiteEuler_fixedTime_smallStep (T : ℝ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      V.L ^ 2 * (T / ((N : ℝ) + 1)) < 2 * V.m := by
  have hmesh : Filter.Tendsto
      (fun N : ℕ => T / ((N : ℝ) + 1)) Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul T)
  have hscaled : Filter.Tendsto
      (fun N : ℕ => V.L ^ 2 * (T / ((N : ℝ) + 1)))
      Filter.atTop (nhds 0) := by
    simpa using hmesh.const_mul (V.L ^ 2)
  exact (tendsto_order.mp hscaled).2 (2 * V.m)
    (mul_pos (by norm_num) V.hm)

/-- Final finite-dimensional `ℓ²` endpoint estimate.  Under the usual
small-step condition, the Euler endpoint map has squared Lipschitz constant
at most `2 / (2m - L²δ)` with respect to all innovations used up to time
`k`. -/
lemma finiteEulerState_innovationSensitivity_sq_le
    (delta : ℝ) (hdelta : 0 < delta)
    (hsmall : V.L ^ 2 * delta < 2 * V.m)
    (x0 : State d) (z w : Fin n → State d) (k : ℕ) :
    ‖finiteEulerState V delta x0 z k -
        finiteEulerState V delta x0 w k‖ ^ 2 ≤
      (2 / (2 * V.m - V.L ^ 2 * delta)) *
        ∑ j ∈ range k,
          ‖finiteInnovationNat z j - finiteInnovationNat w j‖ ^ 2 := by
  have hsens := finiteEulerState_innovationSensitivity_sq V
    delta hdelta.le x0 z w k
  have hcoef := finiteEuler_geometricCoefficient_le V
    delta hsmall k
  have hsum0 :
      0 ≤ ∑ j ∈ range k,
        ‖finiteInnovationNat z j - finiteInnovationNat w j‖ ^ 2 := by
    positivity
  exact hsens.trans (mul_le_mul_of_nonneg_right hcoef hsum0)

/-- The Euler endpoint as a map from one ordinary finite-dimensional
Euclidean Gaussian source. -/
def finiteEulerEuclideanEndpoint
    (delta : ℝ) (x0 : State d)
    (z : EuclideanSpace ℝ (Fin n × Fin d)) : State d :=
  finiteEulerState V delta x0 (euclideanInnovationBlocks z) n

/-- Squared Euclidean Lipschitz estimate for the packaged endpoint map. -/
lemma finiteEulerEuclideanEndpoint_sq_le
    (delta : ℝ) (hdelta : 0 < delta)
    (hsmall : V.L ^ 2 * delta < 2 * V.m) (x0 : State d)
    (z w : EuclideanSpace ℝ (Fin n × Fin d)) :
    ‖finiteEulerEuclideanEndpoint V delta x0 z -
        finiteEulerEuclideanEndpoint V delta x0 w‖ ^ 2 ≤
      (2 / (2 * V.m - V.L ^ 2 * delta)) * ‖z - w‖ ^ 2 := by
  have hsens := finiteEulerState_innovationSensitivity_sq_le V
    delta hdelta hsmall x0 (euclideanInnovationBlocks z)
      (euclideanInnovationBlocks w) n
  simpa only [finiteEulerEuclideanEndpoint,
    sum_range_finiteInnovationBlocks_sub_sq] using hsens

/-- The finite Euler endpoint is a Lipschitz map of a standard Euclidean
Gaussian innovation vector. -/
lemma finiteEulerEuclideanEndpoint_lipschitzWith
    (delta : ℝ) (hdelta : 0 < delta)
    (hsmall : V.L ^ 2 * delta < 2 * V.m) (x0 : State d) :
    LipschitzWith
      (⟨Real.sqrt (2 / (2 * V.m - V.L ^ 2 * delta)),
        Real.sqrt_nonneg _⟩ : NNReal)
      (finiteEulerEuclideanEndpoint V delta x0 :
        EuclideanSpace ℝ (Fin n × Fin d) → State d) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [dist_eq_norm, dist_eq_norm]
  have hdenom : 0 < 2 * V.m - V.L ^ 2 * delta := sub_pos.mpr hsmall
  have hcoef0 : 0 ≤ 2 / (2 * V.m - V.L ^ 2 * delta) :=
    div_nonneg (by norm_num) hdenom.le
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hcoef0]
  exact finiteEulerEuclideanEndpoint_sq_le V
    delta hdelta hsmall x0 z w

end Euler
end DiscreteTime
end
end UniformRandomMALA
