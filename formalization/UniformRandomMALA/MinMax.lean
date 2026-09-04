import UniformRandomMALA.Scales

/-!
# Elementary min/max lemmas

These are the exact order-theoretic identities used when the safe component
and the moment-ladder component are combined at the end of the paper.
-/

namespace UniformRandomMALA

noncomputable section

lemma min_nonneg_of_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ min x y := by
  exact le_min hx hy

lemma sq_le_sq_of_nonneg {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    x ^ 2 ≤ y ^ 2 := by
  nlinarith

/-- Multiplication by a nonnegative number commutes with `max`. -/
lemma mul_max_of_nonneg' (k x y : ℝ) (hk : 0 ≤ k) :
    k * max x y = max (k * x) (k * y) := by
  rcases le_total x y with hxy | hyx
  · have hkxy : k * x ≤ k * y := mul_le_mul_of_nonneg_left hxy hk
    rw [max_eq_right hxy, max_eq_right hkxy]
  · have hkyx : k * y ≤ k * x := mul_le_mul_of_nonneg_left hyx hk
    rw [max_eq_left hyx, max_eq_left hkyx]

/-- Multiplication by a nonnegative number commutes with `min`. -/
lemma mul_min_of_nonneg' (k x y : ℝ) (hk : 0 ≤ k) :
    k * min x y = min (k * x) (k * y) := by
  rcases le_total x y with hxy | hyx
  · have hkxy : k * x ≤ k * y := mul_le_mul_of_nonneg_left hxy hk
    rw [min_eq_left hxy, min_eq_left hkxy]
  · have hkyx : k * y ≤ k * x := mul_le_mul_of_nonneg_left hyx hk
    rw [min_eq_right hyx, min_eq_right hkyx]

/-- Right multiplication by a nonnegative number commutes with `min`. -/
lemma min_mul_of_nonneg' (x y k : ℝ) (hk : 0 ≤ k) :
    min (x * k) (y * k) = min x y * k := by
  rcases le_total x y with hxy | hyx
  · have hkxy : x * k ≤ y * k := mul_le_mul_of_nonneg_right hxy hk
    rw [min_eq_left hxy, min_eq_left hkxy]
  · have hkyx : y * k ≤ x * k := mul_le_mul_of_nonneg_right hyx hk
    rw [min_eq_right hyx, min_eq_right hkyx]

/--
For nonnegative `H`, `a`, and `b`, squaring after truncating at `H`
commutes with taking the larger certified scale.
-/
lemma max_sq_min_eq_min_max_sq
    (H a b : ℝ) (hH : 0 ≤ H) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    max ((min H a) ^ 2) ((min H b) ^ 2) =
      (min H (max a b)) ^ 2 := by
  rcases le_total a b with hab | hba
  · have hmin : min H a ≤ min H b :=
      min_le_min (le_refl H) hab
    have hmin_nonneg : 0 ≤ min H a := min_nonneg_of_nonneg hH ha
    have hsq : (min H a) ^ 2 ≤ (min H b) ^ 2 :=
      sq_le_sq_of_nonneg hmin_nonneg hmin
    rw [max_eq_right hab, max_eq_right hsq]
  · have hmin : min H b ≤ min H a :=
      min_le_min (le_refl H) hba
    have hmin_nonneg : 0 ≤ min H b := min_nonneg_of_nonneg hH hb
    have hsq : (min H b) ^ 2 ≤ (min H a) ^ 2 :=
      sq_le_sq_of_nonneg hmin_nonneg hmin
    rw [max_eq_left hba, max_eq_left hsq]

namespace Parameters

lemma certifiedScale_eq_max_scales (p : Parameters) :
    p.certifiedScale = max p.rejectionScale p.safeScale := by
  unfold certifiedScale certifiedShape rejectionScale safeScale
  exact mul_max_of_nonneg' _ _ _ p.baseFactor_nonneg

/-- If `p⋆ ≥ d`, the rejection-controlled shape is no larger than `1/d`. -/
lemma rejectionShape_le_safeShape_of_dim_le_moment
    (p : Parameters) (hdp : p.d ≤ p.pStar) :
    p.rejectionShape ≤ p.safeShape := by
  let z : ℝ := p.pStar * (p.d + p.pStar)
  have hzpos : 0 < z := by
    simpa [z] using p.rejectionArgument_pos
  have hznonneg : 0 ≤ z := le_of_lt hzpos
  have hpd : p.d * p.d ≤ p.pStar * p.d := by
    exact mul_le_mul_of_nonneg_right hdp p.d_nonneg
  have hpp : 0 ≤ p.pStar * p.pStar := mul_self_nonneg p.pStar
  have hdsq : p.d ^ 2 ≤ z := by
    dsimp [z]
    nlinarith
  have hsqrt_sq : (Real.sqrt z) ^ 2 = z := by
    simpa using Real.sq_sqrt hznonneg
  have hsqrt_nonneg : 0 ≤ Real.sqrt z := Real.sqrt_nonneg z
  have hdroot : p.d ≤ Real.sqrt z := by
    nlinarith [p.d_nonneg]
  have hrootpos : 0 < Real.sqrt z := Real.sqrt_pos.2 hzpos
  have hrecip : 1 / Real.sqrt z ≤ 1 / p.d := by
    apply (div_le_div_iff₀ hrootpos p.hd).2
    simpa using hdroot
  simpa [Parameters.rejectionShape, Parameters.safeShape, z] using hrecip

lemma rejectionScale_le_safeScale_of_dim_le_moment
    (p : Parameters) (hdp : p.d ≤ p.pStar) :
    p.rejectionScale ≤ p.safeScale := by
  unfold rejectionScale safeScale
  exact mul_le_mul_of_nonneg_left
    (p.rejectionShape_le_safeShape_of_dim_le_moment hdp)
    p.baseFactor_nonneg

lemma certifiedScale_eq_safeScale_of_dim_le_moment
    (p : Parameters) (hdp : p.d ≤ p.pStar) :
    p.certifiedScale = p.safeScale := by
  rw [p.certifiedScale_eq_max_scales]
  exact max_eq_right (p.rejectionScale_le_safeScale_of_dim_le_moment hdp)

lemma masterRHS_nonneg (p : Parameters) : 0 ≤ p.masterRHS := by
  unfold masterRHS
  exact mul_nonneg p.gapPrefactor_nonneg (sq_nonneg _)

end Parameters

end

end UniformRandomMALA
