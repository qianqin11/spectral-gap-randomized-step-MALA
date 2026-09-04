import UniformRandomMALA.Concrete.GaussianProposal
import UniformRandomMALA.Concrete.Cocoercivity
import UniformRandomMALA.Concrete.SetwiseTV

namespace UniformRandomMALA

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

namespace Concrete

open FirstOrderPotential

/-- For two integrable densities of the same total mass, every setwise
difference is at most one half of their `L¹` distance.  The proof only splits
the integral over a set and its complement. -/
theorem abs_setIntegral_sub_le_half_integral_abs_sub
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hmass : ∫ x, f x ∂μ = ∫ x, g x ∂μ)
    {s : Set α} (hs : MeasurableSet s) :
    |(∫ x in s, f x ∂μ) - ∫ x in s, g x ∂μ| ≤
      (1 / 2 : ℝ) * ∫ x, |f x - g x| ∂μ := by
  let q : α → ℝ := fun x => f x - g x
  have hq : Integrable q μ := hf.sub hg
  have hqtotal : ∫ x, q x ∂μ = 0 := by
    rw [show q = fun x => f x - g x by rfl, integral_sub hf hg, hmass, sub_self]
  have hcomp : (∫ x in sᶜ, q x ∂μ) = -(∫ x in s, q x ∂μ) := by
    rw [setIntegral_compl hs hq, hqtotal]
    ring
  have hsAbs := abs_integral_le_integral_abs
    (μ := μ.restrict s) (f := q)
  have hscAbs := abs_integral_le_integral_abs
    (μ := μ.restrict sᶜ) (f := q)
  have hsplit :
      (∫ x, |q x| ∂μ) =
        (∫ x in s, |q x| ∂μ) + ∫ x in sᶜ, |q x| ∂μ := by
    rw [setIntegral_compl hs hq.abs]
    ring
  rw [hcomp, abs_neg] at hscAbs
  have hhalf : |∫ x in s, q x ∂μ| ≤
      (1 / 2 : ℝ) * ∫ x, |q x| ∂μ := by
    rw [hsplit]
    nlinarith
  simpa [q, integral_sub hf.restrict hg.restrict] using hhalf

/-- Cauchy--Schwarz for two nonnegative real functions, packaged in the
precise form used by the Hellinger argument. -/
theorem integral_mul_le_rpow_half_integral_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ}
    (hf_meas : AEStronglyMeasurable f μ)
    (hg_meas : AEStronglyMeasurable g μ)
    (hf_nonneg : 0 ≤ᵐ[μ] f) (hg_nonneg : 0 ≤ᵐ[μ] g)
    (hf_sq : Integrable (fun x => f x ^ 2) μ)
    (hg_sq : Integrable (fun x => g x ^ 2) μ) :
    (∫ x, f x * g x ∂μ) ≤
      (∫ x, f x ^ 2 ∂μ) ^ (1 / 2 : ℝ) *
        (∫ x, g x ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  have hf_mem : MemLp f (ENNReal.ofReal 2) μ := by
    refine ⟨hf_meas, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by simp)]
    have hfin := hf_sq.lintegral_lt_top
    apply lt_of_eq_of_lt _ hfin
    apply lintegral_congr
    intro x
    rw [← ofReal_norm]
    norm_num [ENNReal.ofReal_rpow_of_nonneg, sq_nonneg,
      ← ENNReal.ofReal_pow (abs_nonneg _) 2]
  have hg_mem : MemLp g (ENNReal.ofReal 2) μ := by
    refine ⟨hg_meas, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by simp)]
    have hfin := hg_sq.lintegral_lt_top
    apply lt_of_eq_of_lt _ hfin
    apply lintegral_congr
    intro x
    rw [← ofReal_norm]
    norm_num [ENNReal.ofReal_rpow_of_nonneg, sq_nonneg,
      ← ENNReal.ofReal_pow (abs_nonneg _) 2]
  simpa [Real.norm_of_nonneg, hf_nonneg, hg_nonneg] using
    (integral_mul_le_Lp_mul_Lq_of_nonneg
      (p := 2) (q := 2) (μ := μ) Real.HolderConjugate.two_two
      hf_nonneg hg_nonneg hf_mem hg_mem)

/-- The elementary Hellinger-to-`L¹` estimate.  All density and affinity
integrals remain explicit; no information-theoretic divergence is used. -/
theorem integral_abs_sub_le_hellinger_product
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p q : α → ℝ}
    (hp_meas : Measurable p) (hq_meas : Measurable q)
    (hp_nonneg : ∀ x, 0 ≤ p x) (hq_nonneg : ∀ x, 0 ≤ q x)
    (hp_int : Integrable p μ) (hq_int : Integrable q μ)
    (hp_mass : ∫ x, p x ∂μ = 1) (hq_mass : ∫ x, q x ∂μ = 1)
    (hr_int : Integrable (fun x => Real.sqrt (p x * q x)) μ) :
    (∫ x, |p x - q x| ∂μ) ≤
      (2 - 2 * ∫ x, Real.sqrt (p x * q x) ∂μ) ^ (1 / 2 : ℝ) *
        (2 + 2 * ∫ x, Real.sqrt (p x * q x) ∂μ) ^ (1 / 2 : ℝ) := by
  let u : α → ℝ := fun x => |Real.sqrt (p x) - Real.sqrt (q x)|
  let v : α → ℝ := fun x => Real.sqrt (p x) + Real.sqrt (q x)
  let r : α → ℝ := fun x => Real.sqrt (p x * q x)
  have hu_meas : Measurable u := by
    dsimp [u]
    fun_prop
  have hv_meas : Measurable v := by
    dsimp [v]
    fun_prop
  have hu_nonneg : ∀ x, 0 ≤ u x := fun x => abs_nonneg _
  have hv_nonneg : ∀ x, 0 ≤ v x := fun x =>
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hu_sq_point : ∀ x, u x ^ 2 = p x + q x - 2 * r x := by
    intro x
    dsimp [u, r]
    rw [sq_abs, sub_sq, Real.sq_sqrt (hp_nonneg x),
      Real.sq_sqrt (hq_nonneg x), Real.sqrt_mul (hp_nonneg x)]
    ring
  have hv_sq_point : ∀ x, v x ^ 2 = p x + q x + 2 * r x := by
    intro x
    dsimp [v, r]
    rw [add_sq, Real.sq_sqrt (hp_nonneg x),
      Real.sq_sqrt (hq_nonneg x), Real.sqrt_mul (hp_nonneg x)]
    ring
  have hu_sq : Integrable (fun x => u x ^ 2) μ := by
    have hbase : Integrable (fun x => p x + q x - 2 * r x) μ :=
      (hp_int.add hq_int).sub (hr_int.const_mul 2)
    exact hbase.congr (ae_of_all _ fun x => (hu_sq_point x).symm)
  have hv_sq : Integrable (fun x => v x ^ 2) μ := by
    have hbase : Integrable (fun x => p x + q x + 2 * r x) μ :=
      (hp_int.add hq_int).add (hr_int.const_mul 2)
    exact hbase.congr (ae_of_all _ fun x => (hv_sq_point x).symm)
  have huv_point : ∀ x, u x * v x = |p x - q x| := by
    intro x
    dsimp [u, v]
    calc
      |Real.sqrt (p x) - Real.sqrt (q x)| *
          (Real.sqrt (p x) + Real.sqrt (q x)) =
          |Real.sqrt (p x) - Real.sqrt (q x)| *
            |Real.sqrt (p x) + Real.sqrt (q x)| := by
              rw [abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
      _ = |(Real.sqrt (p x) - Real.sqrt (q x)) *
          (Real.sqrt (p x) + Real.sqrt (q x))| := (abs_mul _ _).symm
      _ = |p x - q x| := by
        congr 1
        calc
          (Real.sqrt (p x) - Real.sqrt (q x)) *
              (Real.sqrt (p x) + Real.sqrt (q x)) =
              Real.sqrt (p x) * Real.sqrt (p x) -
                Real.sqrt (q x) * Real.sqrt (q x) := by ring
          _ = p x - q x := by
            rw [Real.mul_self_sqrt (hp_nonneg x),
              Real.mul_self_sqrt (hq_nonneg x)]
  have hcs := integral_mul_le_rpow_half_integral_sq
    hu_meas.aestronglyMeasurable hv_meas.aestronglyMeasurable
    (ae_of_all _ hu_nonneg) (ae_of_all _ hv_nonneg) hu_sq hv_sq
  rw [integral_congr_ae (ae_of_all _ huv_point)] at hcs
  have hu_eval : (∫ x, u x ^ 2 ∂μ) =
      2 - 2 * ∫ x, Real.sqrt (p x * q x) ∂μ := by
    rw [integral_congr_ae (ae_of_all _ hu_sq_point)]
    change (∫ x, (p x + q x) - 2 * Real.sqrt (p x * q x) ∂μ) = _
    calc
      (∫ x, (p x + q x) - 2 * Real.sqrt (p x * q x) ∂μ) =
          (∫ x, p x + q x ∂μ) - ∫ x, 2 * Real.sqrt (p x * q x) ∂μ :=
        integral_sub (hp_int.add hq_int) (hr_int.const_mul 2)
      _ = _ := by
        rw [integral_add hp_int hq_int, integral_const_mul, hp_mass, hq_mass]
        ring
  have hv_eval : (∫ x, v x ^ 2 ∂μ) =
      2 + 2 * ∫ x, Real.sqrt (p x * q x) ∂μ := by
    rw [integral_congr_ae (ae_of_all _ hv_sq_point)]
    change (∫ x, (p x + q x) + 2 * Real.sqrt (p x * q x) ∂μ) = _
    calc
      (∫ x, (p x + q x) + 2 * Real.sqrt (p x * q x) ∂μ) =
          (∫ x, p x + q x ∂μ) + ∫ x, 2 * Real.sqrt (p x * q x) ∂μ :=
        integral_add (hp_int.add hq_int) (hr_int.const_mul 2)
      _ = _ := by
        rw [integral_add hp_int hq_int, integral_const_mul, hp_mass, hq_mass]
        ring
  simpa [hu_eval, hv_eval] using hcs

lemma sq_norm_sub_add_sq_norm_sub {d : ℕ} (z m n : State d) :
    ‖z - m‖ ^ 2 + ‖z - n‖ ^ 2 =
      2 * ‖z - (2 : ℝ)⁻¹ • (m + n)‖ ^ 2 + (1 / 2 : ℝ) * ‖m - n‖ ^ 2 := by
  have hp := parallelogram_law_with_norm ℝ (z - m) (z - n)
  have hadd : (z - m) + (z - n) =
      (2 : ℝ) • (z - (2 : ℝ)⁻¹ • (m + n)) := by
    module
  have hsub : (z - m) - (z - n) = n - m := by abel
  rw [hadd, hsub, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hp
  rw [norm_sub_rev n m] at hp
  nlinarith

/-- The same real Gaussian density used by the MALA proposal, with its mean
left as an explicit parameter. -/
def equalCovGaussianDensityReal {d : ℕ} (h : ℝ) (m z : State d) : ℝ :=
  Real.exp (-(1 / (4 * h)) * ‖z - m‖ ^ 2) /
    FirstOrderPotential.proposalNormalizer (d := d) h

lemma equalCovGaussianDensityReal_pos {d : ℕ} {h : ℝ} (hh : 0 < h)
    (m z : State d) : 0 < equalCovGaussianDensityReal h m z :=
  div_pos (Real.exp_pos _)
    (FirstOrderPotential.proposalNormalizer_pos (d := d) hh)

lemma measurable_equalCovGaussianDensityReal {d : ℕ} (h : ℝ) (m : State d) :
    Measurable (equalCovGaussianDensityReal h m) := by
  unfold equalCovGaussianDensityReal
  fun_prop

lemma equalCovGaussianDensityReal_integrable {d : ℕ} {h : ℝ} (hh : 0 < h)
    (m : State d) : Integrable (equalCovGaussianDensityReal h m) := by
  have hb : 0 < 1 / (4 * h) := one_div_pos.mpr (mul_pos (by norm_num) hh)
  have hc := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := State d) (b := ((1 / (4 * h) : ℝ) : ℂ)) (c := 0) (w := 0)
    (by exact_mod_cast hb)
  have hg : Integrable
      (fun z : State d => Real.exp (-(1 / (4 * h)) * ‖z‖ ^ 2)) := by
    refine hc.norm.congr ?_
    filter_upwards with z
    rw [show (↑‖z‖ : ℂ) ^ 2 = ↑(‖z‖ ^ 2) by norm_cast]
    simp [Complex.norm_exp]
    left
    simp [pow_two, Complex.mul_re]
  unfold equalCovGaussianDensityReal
  exact (hg.comp_sub_right m).div_const _

lemma equalCovGaussianDensityReal_integral {d : ℕ} {h : ℝ} (hh : 0 < h)
    (m : State d) :
    ∫ z, equalCovGaussianDensityReal h m z = 1 := by
  have hb : 0 < 1 / (4 * h) := one_div_pos.mpr (mul_pos (by norm_num) hh)
  have hgauss := GaussianFourier.integral_rexp_neg_mul_sq_norm
    (V := State d) hb
  have hshift := integral_sub_right_eq_self (μ := volume)
    (fun z : State d => Real.exp (-(1 / (4 * h)) * ‖z‖ ^ 2)) m
  have hcenter :
      (∫ z : State d, Real.exp (-(1 / (4 * h)) * ‖z‖ ^ 2)) =
        FirstOrderPotential.proposalNormalizer (d := d) h := by
    simpa [FirstOrderPotential.proposalNormalizer] using hgauss
  unfold equalCovGaussianDensityReal
  rw [integral_div, hshift]
  rw [hcenter]
  exact div_self (FirstOrderPotential.proposalNormalizer_pos (d := d) hh).ne'

/-- Explicit geometric-mean integrand for two equal-covariance Gaussians. -/
def equalCovGaussianAffinityIntegrand {d : ℕ} (h : ℝ)
    (m n z : State d) : ℝ :=
  Real.exp (-(1 / (8 * h)) * (‖z - m‖ ^ 2 + ‖z - n‖ ^ 2)) /
    FirstOrderPotential.proposalNormalizer (d := d) h

lemma equalCovGaussianAffinityIntegrand_pos {d : ℕ} {h : ℝ} (hh : 0 < h)
    (m n z : State d) : 0 < equalCovGaussianAffinityIntegrand h m n z :=
  div_pos (Real.exp_pos _)
    (FirstOrderPotential.proposalNormalizer_pos (d := d) hh)

lemma equalCovGaussianAffinityIntegrand_eq_sqrt_mul {d : ℕ} {h : ℝ}
    (hh : 0 < h) (m n z : State d) :
    equalCovGaussianAffinityIntegrand h m n z =
      Real.sqrt (equalCovGaussianDensityReal h m z *
        equalCovGaussianDensityReal h n z) := by
  symm
  apply (Real.sqrt_eq_iff_mul_self_eq_of_pos
    (equalCovGaussianAffinityIntegrand_pos hh m n z)).2
  unfold equalCovGaussianAffinityIntegrand equalCovGaussianDensityReal
  field_simp [FirstOrderPotential.proposalNormalizer_pos (d := d) hh |>.ne']
  rw [pow_two, ← Real.exp_add]
  field_simp
  rw [← Real.exp_add]
  congr 1
  ring

lemma equalCovGaussianAffinityIntegrand_eq {d : ℕ} {h : ℝ} (hh : 0 < h)
    (m n z : State d) :
    equalCovGaussianAffinityIntegrand h m n z =
      Real.exp (-(1 / (16 * h)) * ‖m - n‖ ^ 2) *
        equalCovGaussianDensityReal h ((2 : ℝ)⁻¹ • (m + n)) z := by
  rw [equalCovGaussianAffinityIntegrand, equalCovGaussianDensityReal,
    sq_norm_sub_add_sq_norm_sub z m n]
  have hexp :
      -(1 / (8 * h)) *
          (2 * ‖z - (2 : ℝ)⁻¹ • (m + n)‖ ^ 2 +
            (1 / 2 : ℝ) * ‖m - n‖ ^ 2) =
        -(1 / (16 * h)) * ‖m - n‖ ^ 2 +
          -(1 / (4 * h)) * ‖z - (2 : ℝ)⁻¹ • (m + n)‖ ^ 2 := by
    field_simp
    ring
  rw [hexp, Real.exp_add]
  ring

theorem integral_equalCovGaussianAffinityIntegrand {d : ℕ} {h : ℝ}
    (hh : 0 < h) (m n : State d) :
    (∫ z, equalCovGaussianAffinityIntegrand h m n z) =
      Real.exp (-(1 / (16 * h)) * ‖m - n‖ ^ 2) := by
  simp_rw [equalCovGaussianAffinityIntegrand_eq hh m n]
  rw [integral_const_mul, equalCovGaussianDensityReal_integral hh]
  ring

lemma equalCovGaussianAffinityIntegrand_integrable {d : ℕ} {h : ℝ}
    (hh : 0 < h) (m n : State d) :
    Integrable (equalCovGaussianAffinityIntegrand h m n) := by
  refine (equalCovGaussianDensityReal_integrable hh
    ((2 : ℝ)⁻¹ • (m + n))).const_mul
      (Real.exp (-(1 / (16 * h)) * ‖m - n‖ ^ 2)) |>.congr ?_
  filter_upwards with z
  exact (equalCovGaussianAffinityIntegrand_eq hh m n z).symm

/-- `L¹` discrepancy of two equal-covariance Gaussian densities, expressed
through their explicit Hellinger affinity. -/
theorem integral_abs_equalCovGaussianDensityReal_sub_le {d : ℕ} {h : ℝ}
    (hh : 0 < h) (m n : State d) :
    (∫ z, |equalCovGaussianDensityReal h m z -
        equalCovGaussianDensityReal h n z|) ≤
      (2 - 2 * Real.exp (-(1 / (16 * h)) * ‖m - n‖ ^ 2)) ^ (1 / 2 : ℝ) *
        (2 + 2 * Real.exp (-(1 / (16 * h)) * ‖m - n‖ ^ 2)) ^
          (1 / 2 : ℝ) := by
  have hr : Integrable (fun z : State d =>
      Real.sqrt (equalCovGaussianDensityReal h m z *
        equalCovGaussianDensityReal h n z)) :=
    (equalCovGaussianAffinityIntegrand_integrable hh m n).congr
      (ae_of_all _ fun z => equalCovGaussianAffinityIntegrand_eq_sqrt_mul hh m n z)
  have hbound := integral_abs_sub_le_hellinger_product
    (measurable_equalCovGaussianDensityReal h m)
    (measurable_equalCovGaussianDensityReal h n)
    (fun z => (equalCovGaussianDensityReal_pos hh m z).le)
    (fun z => (equalCovGaussianDensityReal_pos hh n z).le)
    (equalCovGaussianDensityReal_integrable hh m)
    (equalCovGaussianDensityReal_integrable hh n)
    (equalCovGaussianDensityReal_integral hh m)
    (equalCovGaussianDensityReal_integral hh n) hr
  rw [show (∫ z : State d,
      Real.sqrt (equalCovGaussianDensityReal h m z *
        equalCovGaussianDensityReal h n z)) =
      Real.exp (-(1 / (16 * h)) * ‖m - n‖ ^ 2) by
        rw [← integral_equalCovGaussianAffinityIntegrand hh m n]
        apply integral_congr_ae
        exact ae_of_all _ fun z =>
          (equalCovGaussianAffinityIntegrand_eq_sqrt_mul hh m n z).symm] at hbound
  exact hbound

/-- A linear-in-mean-separation consequence of the preceding Hellinger
identity.  It is deliberately left with one square root; this form is the
most convenient for the paper's `h ≥ t/2` arithmetic. -/
theorem integral_abs_equalCovGaussianDensityReal_sub_le_sqrt {d : ℕ} {h : ℝ}
    (hh : 0 < h) (m n : State d) :
    (∫ z, |equalCovGaussianDensityReal h m z -
        equalCovGaussianDensityReal h n z|) ≤
      2 * Real.sqrt (‖m - n‖ ^ 2 / (8 * h)) := by
  let x : ℝ := ‖m - n‖ ^ 2 / (16 * h)
  have hx : 0 ≤ x := div_nonneg (sq_nonneg _) (by positivity)
  have hA0 : 0 ≤ Real.exp (-x) := (Real.exp_pos _).le
  have hA1 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)
  have hfirst0 : 0 ≤ 2 - 2 * Real.exp (-x) := by nlinarith
  have hsecond0 : 0 ≤ 2 + 2 * Real.exp (-x) := by nlinarith
  have hfirst : 2 - 2 * Real.exp (-x) ≤ ‖m - n‖ ^ 2 / (8 * h) := by
    have hexp := Real.one_sub_le_exp_neg x
    have hid : ‖m - n‖ ^ 2 / (8 * h) = 2 * x := by
      dsimp [x]
      field_simp
      ring
    rw [hid]
    nlinarith
  have hsecond : 2 + 2 * Real.exp (-x) ≤ 4 := by nlinarith
  have hsqrtFirst := Real.sqrt_le_sqrt hfirst
  have hsqrtSecond := Real.sqrt_le_sqrt hsecond
  have hbase := integral_abs_equalCovGaussianDensityReal_sub_le hh m n
  have hxexp : -(1 / (16 * h)) * ‖m - n‖ ^ 2 = -x := by
    dsimp [x]
    field_simp
  rw [hxexp] at hbase
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hbase
  calc
    (∫ z, |equalCovGaussianDensityReal h m z -
        equalCovGaussianDensityReal h n z|) ≤
        Real.sqrt (2 - 2 * Real.exp (-x)) *
          Real.sqrt (2 + 2 * Real.exp (-x)) := hbase
    _ ≤ Real.sqrt (‖m - n‖ ^ 2 / (8 * h)) * Real.sqrt 4 := by
      exact mul_le_mul hsqrtFirst hsqrtSecond
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt (‖m - n‖ ^ 2 / (8 * h)) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      ring

/-- Setwise discrepancy of two equal-covariance Gaussian densities.  The
factor `1/2` comes only from splitting a set and its complement. -/
theorem abs_setIntegral_equalCovGaussianDensityReal_sub_le_sqrt
    {d : ℕ} {h : ℝ} (hh : 0 < h) (m n : State d)
    {s : Set (State d)} (hs : MeasurableSet s) :
    |(∫ z in s, equalCovGaussianDensityReal h m z) -
        ∫ z in s, equalCovGaussianDensityReal h n z| ≤
      Real.sqrt (‖m - n‖ ^ 2 / (8 * h)) := by
  have hhalf := abs_setIntegral_sub_le_half_integral_abs_sub
    (equalCovGaussianDensityReal_integrable hh m)
    (equalCovGaussianDensityReal_integrable hh n)
    (by rw [equalCovGaussianDensityReal_integral hh m,
      equalCovGaussianDensityReal_integral hh n]) hs
  have hL1 := integral_abs_equalCovGaussianDensityReal_sub_le_sqrt hh m n
  calc
    |(∫ z in s, equalCovGaussianDensityReal h m z) -
        ∫ z in s, equalCovGaussianDensityReal h n z| ≤
        (1 / 2 : ℝ) *
          ∫ z, |equalCovGaussianDensityReal h m z -
            equalCovGaussianDensityReal h n z| := hhalf
    _ ≤ (1 / 2 : ℝ) *
        (2 * Real.sqrt (‖m - n‖ ^ 2 / (8 * h))) := by
      exact mul_le_mul_of_nonneg_left hL1 (by norm_num)
    _ = _ := by ring

namespace FirstOrderPotential

lemma gaussianDensityProposal_apply_toReal {d : ℕ}
    (V : FirstOrderPotential d) {h : ℝ} (hh : 0 < h)
    (x : State d) {s : Set (State d)} (_hs : MeasurableSet s) :
    (V.gaussianDensityProposal h x s).toReal =
      ∫ z in s, V.proposalDensityReal h x z := by
  rw [V.gaussianDensityProposal_apply]
  change (∫⁻ z in s, ENNReal.ofReal (V.proposalDensityReal h x z) ∂volume).toReal = _
  rw [← ofReal_integral_eq_lintegral_ofReal
    (V.proposalDensityReal_integrable hh x).restrict
    (ae_of_all _ fun z => V.proposalDensityReal_nonneg hh x z)]
  rw [ENNReal.toReal_ofReal]
  exact integral_nonneg fun z => V.proposalDensityReal_nonneg hh x z

lemma proposalDensityReal_eq_equalCovGaussianDensityReal {d : ℕ}
    (V : FirstOrderPotential d) (h : ℝ) (x z : State d) :
    V.proposalDensityReal h x z =
      equalCovGaussianDensityReal h (V.proposalMean h x) z := rfl

/-- Concrete setwise comparison of two MALA Gaussian proposals before using
nonexpansiveness of the proposal mean. -/
theorem abs_gaussianDensityProposal_apply_toReal_sub_le_sqrt {d : ℕ}
    (V : FirstOrderPotential d) {h : ℝ} (hh : 0 < h)
    (x y : State d) {s : Set (State d)} (hs : MeasurableSet s) :
    |(V.gaussianDensityProposal h x s).toReal -
        (V.gaussianDensityProposal h y s).toReal| ≤
      Real.sqrt (‖V.proposalMean h x - V.proposalMean h y‖ ^ 2 / (8 * h)) := by
  rw [V.gaussianDensityProposal_apply_toReal hh x hs,
    V.gaussianDensityProposal_apply_toReal hh y hs]
  simp_rw [V.proposalDensityReal_eq_equalCovGaussianDensityReal]
  exact abs_setIntegral_equalCovGaussianDensityReal_sub_le_sqrt hh _ _ hs

/-- Under the elementary step restriction `h ≤ 2/L`, cocoercivity makes the
proposal mean nonexpansive, so the Gaussian comparison depends only on the
separation of the starting points. -/
theorem abs_gaussianDensityProposal_apply_toReal_sub_le_startingDistance
    {d : ℕ} (V : FirstOrderPotential d) {h : ℝ} (hh : 0 < h)
    (hhL : h ≤ 2 / V.L) (x y : State d)
    {s : Set (State d)} (hs : MeasurableSet s) :
    |(V.gaussianDensityProposal h x s).toReal -
        (V.gaussianDensityProposal h y s).toReal| ≤
      Real.sqrt (‖x - y‖ ^ 2 / (8 * h)) := by
  have hmean : ‖V.proposalMean h x - V.proposalMean h y‖ ≤ ‖x - y‖ := by
    simpa [proposalMean] using V.norm_proposalMean_sub_le h hh.le hhL x y
  have hsq : ‖V.proposalMean h x - V.proposalMean h y‖ ^ 2 ≤ ‖x - y‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hmean
  have hquot :
      ‖V.proposalMean h x - V.proposalMean h y‖ ^ 2 / (8 * h) ≤
        ‖x - y‖ ^ 2 / (8 * h) := by
    exact div_le_div_of_nonneg_right hsq (mul_nonneg (by norm_num) hh.le)
  exact (V.abs_gaussianDensityProposal_apply_toReal_sub_le_sqrt hh x y hs).trans
    (Real.sqrt_le_sqrt hquot)

/-- The numerical Gaussian proposal bound used in Proposition 3.2.  The
proof is just the preceding setwise estimate plus squaring; it assumes the
actual proposal step lies in the upper half of the scale interval. -/
theorem abs_gaussianDensityProposal_apply_toReal_sub_le_one_div_32
    {d : ℕ} (V : FirstOrderPotential d) {t h : ℝ}
    (ht : 0 < t) (hh : 0 < h) (hhalf : t / 2 ≤ h)
    (hhL : h ≤ 2 / V.L) (x y : State d)
    (hxy : ‖x - y‖ ≤ Real.sqrt t / 16)
    {s : Set (State d)} (hs : MeasurableSet s) :
    |(V.gaussianDensityProposal h x s).toReal -
        (V.gaussianDensityProposal h y s).toReal| ≤ 1 / 32 := by
  have hraw := V.abs_gaussianDensityProposal_apply_toReal_sub_le_startingDistance
    hh hhL x y hs
  apply hraw.trans
  rw [Real.sqrt_le_iff]
  constructor
  · norm_num
  · have hsq := (sq_le_sq₀ (norm_nonneg _) (div_nonneg (Real.sqrt_nonneg _) (by norm_num))).2 hxy
    have hsqrt : (Real.sqrt t / 16) ^ 2 = t / 256 := by
      rw [div_pow, Real.sq_sqrt ht.le]
      norm_num
    rw [hsqrt] at hsq
    apply (div_le_iff₀ (mul_pos (by norm_num) hh)).2
    norm_num at hsq ⊢
    nlinarith

/-- Total-variation packaging of the nonexpansive Gaussian proposal bound,
using the probability convention `sup_A |μ(A)-ν(A)|`. -/
theorem setwiseTV_gaussianDensityProposal_le_startingDistance
    {d : ℕ} (V : FirstOrderPotential d) {h : ℝ} (hh : 0 < h)
    (hhL : h ≤ 2 / V.L) (x y : State d) :
    setwiseTV (V.gaussianDensityProposal h x)
        (V.gaussianDensityProposal h y) ≤
      Real.sqrt (‖x - y‖ ^ 2 / (8 * h)) := by
  apply setwiseTV_le_of_forall
  intro s hs
  simpa [Measure.real_def] using
    V.abs_gaussianDensityProposal_apply_toReal_sub_le_startingDistance
      hh hhL x y hs

/-- The `1/32` nearby-proposal estimate as an actual supremum-over-measurable-
sets total-variation statement. -/
theorem setwiseTV_gaussianDensityProposal_le_one_div_32
    {d : ℕ} (V : FirstOrderPotential d) {t h : ℝ}
    (ht : 0 < t) (hh : 0 < h) (hhalf : t / 2 ≤ h)
    (hhL : h ≤ 2 / V.L) (x y : State d)
    (hxy : ‖x - y‖ ≤ Real.sqrt t / 16) :
    setwiseTV (V.gaussianDensityProposal h x)
        (V.gaussianDensityProposal h y) ≤ 1 / 32 := by
  apply setwiseTV_le_of_forall
  intro s hs
  simpa [Measure.real_def] using
    V.abs_gaussianDensityProposal_apply_toReal_sub_le_one_div_32
      ht hh hhalf hhL x y hxy hs

end FirstOrderPotential

end Concrete
end
end UniformRandomMALA
