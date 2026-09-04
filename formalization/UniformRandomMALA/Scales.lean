import UniformRandomMALA.Prelude

/-!
# Parameters and scales

The paper's main estimate depends only on positive real parameters once the
analytic estimates have been established.  We therefore keep the algebraic
layer independent of the representation of `ℝ^d`: `d` is the real coercion
of the positive integer dimension, and `pStar` is the moment threshold

`A0 * (1 + log (d + 1) + log kappa)`.

The equality defining `pStar` is retained as data even though the final
min/max assembly uses only its positivity and its comparison with `d`.
-/

namespace UniformRandomMALA

noncomputable section

/-- Positive parameters in the global spectral-gap theorem. -/
structure Parameters where
  d : ℝ
  m : ℝ
  L : ℝ
  kappa : ℝ
  H : ℝ
  A0 : ℝ
  b0 : ℝ
  c0 : ℝ
  pStar : ℝ
  hd : 0 < d
  hd_one : 1 ≤ d
  hm : 0 < m
  hL : 0 < L
  hH : 0 < H
  hA0 : 2 ≤ A0
  hb0 : 0 < b0
  hb0_half : b0 ≤ 1 / 2
  hb0_lt_one : b0 < 1
  hc0 : 0 < c0
  hkappa : kappa = L / m
  hkappa_one : 1 ≤ kappa
  hpStar : pStar = A0 * (1 + Real.log (d + 1) + Real.log kappa)
  hpStar_pos : 0 < pStar

namespace Parameters

/-- The common factor `b₀/L` in both certified step-size scales. -/
def baseFactor (p : Parameters) : ℝ := p.b0 / p.L

/-- The rejection-controlled dimension/moment shape. -/
def rejectionShape (p : Parameters) : ℝ :=
  1 / Real.sqrt (p.pStar * (p.d + p.pStar))

/-- The globally safe shape. -/
def safeShape (p : Parameters) : ℝ := 1 / p.d

/-- The larger of the rejection-controlled and globally safe shapes. -/
def certifiedShape (p : Parameters) : ℝ :=
  max p.rejectionShape p.safeShape

/-- The rejection-controlled certified endpoint. -/
def rejectionScale (p : Parameters) : ℝ :=
  p.baseFactor * p.rejectionShape

/-- The globally safe certified endpoint. -/
def safeScale (p : Parameters) : ℝ :=
  p.baseFactor * p.safeShape

/-- The endpoint appearing in the paper's master bound. -/
def certifiedScale (p : Parameters) : ℝ :=
  p.baseFactor * p.certifiedShape

/-- The right-hand side of Theorem 2.1 (`thm:main`) in the current paper. -/
def masterRHS (p : Parameters) : ℝ :=
  p.c0 * (p.m / p.H) * (min p.H p.certifiedScale) ^ 2

lemma d_nonneg (p : Parameters) : 0 ≤ p.d := le_of_lt p.hd

lemma m_nonneg (p : Parameters) : 0 ≤ p.m := le_of_lt p.hm

lemma L_nonneg (p : Parameters) : 0 ≤ p.L := le_of_lt p.hL

lemma H_nonneg (p : Parameters) : 0 ≤ p.H := le_of_lt p.hH

lemma pStar_nonneg (p : Parameters) : 0 ≤ p.pStar := le_of_lt p.hpStar_pos

/-- The paper's definition and `A₀ ≥ 2` imply the moment threshold is at
least two.  Recording this once avoids repeating logarithm monotonicity in
the multiscale assignment. -/
lemma two_le_pStar (p : Parameters) : 2 ≤ p.pStar := by
  have hdlog : 0 ≤ Real.log (p.d + 1) := by
    exact Real.log_nonneg (by linarith [p.hd_one])
  have hklog : 0 ≤ Real.log p.kappa := Real.log_nonneg p.hkappa_one
  have hfactor : 1 ≤ 1 + Real.log (p.d + 1) + Real.log p.kappa := by
    linarith
  have hA0 : 0 ≤ p.A0 := le_trans (by norm_num) p.hA0
  have hmul := mul_le_mul_of_nonneg_left hfactor hA0
  rw [← p.hpStar] at hmul
  exact p.hA0.trans (by simpa using hmul)

lemma baseFactor_pos (p : Parameters) : 0 < p.baseFactor := by
  exact div_pos p.hb0 p.hL

lemma baseFactor_nonneg (p : Parameters) : 0 ≤ p.baseFactor :=
  le_of_lt p.baseFactor_pos

lemma rejectionArgument_pos (p : Parameters) :
    0 < p.pStar * (p.d + p.pStar) := by
  have hsum : 0 < p.d + p.pStar := add_pos p.hd p.hpStar_pos
  exact mul_pos p.hpStar_pos hsum

lemma rejectionSqrt_pos (p : Parameters) :
    0 < Real.sqrt (p.pStar * (p.d + p.pStar)) := by
  exact Real.sqrt_pos.2 p.rejectionArgument_pos

lemma rejectionShape_pos (p : Parameters) : 0 < p.rejectionShape := by
  exact one_div_pos.mpr p.rejectionSqrt_pos

lemma rejectionShape_nonneg (p : Parameters) : 0 ≤ p.rejectionShape :=
  le_of_lt p.rejectionShape_pos

lemma safeShape_pos (p : Parameters) : 0 < p.safeShape := by
  exact one_div_pos.mpr p.hd

lemma safeShape_nonneg (p : Parameters) : 0 ≤ p.safeShape :=
  le_of_lt p.safeShape_pos

lemma certifiedShape_pos (p : Parameters) : 0 < p.certifiedShape := by
  exact lt_of_lt_of_le p.rejectionShape_pos (le_max_left _ _)

lemma certifiedShape_nonneg (p : Parameters) : 0 ≤ p.certifiedShape :=
  le_of_lt p.certifiedShape_pos

lemma rejectionScale_pos (p : Parameters) : 0 < p.rejectionScale := by
  exact mul_pos p.baseFactor_pos p.rejectionShape_pos

lemma rejectionScale_nonneg (p : Parameters) : 0 ≤ p.rejectionScale :=
  le_of_lt p.rejectionScale_pos

lemma safeScale_pos (p : Parameters) : 0 < p.safeScale := by
  exact mul_pos p.baseFactor_pos p.safeShape_pos

lemma safeScale_nonneg (p : Parameters) : 0 ≤ p.safeScale :=
  le_of_lt p.safeScale_pos

lemma certifiedScale_pos (p : Parameters) : 0 < p.certifiedScale := by
  exact mul_pos p.baseFactor_pos p.certifiedShape_pos

lemma certifiedScale_nonneg (p : Parameters) : 0 ≤ p.certifiedScale :=
  le_of_lt p.certifiedScale_pos

lemma gapPrefactor_pos (p : Parameters) : 0 < p.c0 * (p.m / p.H) := by
  exact mul_pos p.hc0 (div_pos p.hm p.hH)

lemma gapPrefactor_nonneg (p : Parameters) : 0 ≤ p.c0 * (p.m / p.H) :=
  le_of_lt p.gapPrefactor_pos

end Parameters

end

end UniformRandomMALA
