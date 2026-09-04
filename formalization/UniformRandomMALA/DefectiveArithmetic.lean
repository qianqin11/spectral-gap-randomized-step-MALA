import UniformRandomMALA.GaussianShiftArithmetic

/-!
# Numerical core of defective conductance

The measure-theoretic construction of the sets `S₁,S₂` is an analytic
interface.  The constant bookkeeping after those estimates is formalized
here.
-/

namespace UniformRandomMALA

noncomputable section

/-- The removed mass from either side is strictly less than half of `s`. -/
theorem retained_mass_at_least_half
    (s beta exceptional flow : ℝ)
    (hs : 0 < s) (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (hexceptional : exceptional ≤ s * beta / (2 : ℝ) ^ 13)
    (hflow : flow < s * beta / (2 : ℝ) ^ 13) :
    s / 2 < s - exceptional - 16 * flow := by
  have hsbeta : s * beta ≤ s := by
    have := mul_le_mul_of_nonneg_left hbeta1 (le_of_lt hs)
    nlinarith
  have hc := seventeen_times_two_pow_neg_thirteen_lt_half
  nlinarith

/-- Upper bound on the complement of `S₁ ∪ S₂`. -/
theorem removed_mass_upper
    (s beta exceptional flow : ℝ)
    (hsbeta : 0 ≤ s * beta)
    (hexceptional : exceptional ≤ s * beta / (2 : ℝ) ^ 13)
    (hflow : flow < s * beta / (2 : ℝ) ^ 13) :
    exceptional + 32 * flow < s * beta / 128 := by
  have hc := thirty_three_times_two_pow_neg_thirteen_lt_one_over_128
  nlinarith

/-- Final contradiction in Lemma `lem:defective`. -/
theorem defective_conductance_constant_contradiction
    (s beta complement exceptional flow : ℝ)
    (hs : 0 < s) (hbeta : 0 < beta)
    (hlower : s * beta / 128 ≤ complement)
    (hupper : complement ≤ exceptional + 32 * flow)
    (hexceptional : exceptional ≤ s * beta / (2 : ℝ) ^ 13)
    (hflow : flow < s * beta / (2 : ℝ) ^ 13) : False := by
  have hsbeta : 0 ≤ s * beta := by positivity
  have hremoved := removed_mass_upper
    s beta exceptional flow hsbeta hexceptional hflow
  nlinarith

/--
Abstract contradiction wrapper for the last paragraph of
`lem:defective`.  The two implications are exactly the lower and upper
bounds on the complement of `S₁ ∪ S₂` obtained under the contrary flow
assumption.
-/
theorem defective_flow_lower_of_complement_bounds
    (s beta exceptional flow complement : ℝ)
    (hs : 0 < s) (hbeta : 0 < beta)
    (hexceptional : exceptional ≤ s * beta / (2 : ℝ) ^ 13)
    (hlower :
      flow < s * beta / (2 : ℝ) ^ 13 →
        s * beta / 128 ≤ complement)
    (hupper :
      flow < s * beta / (2 : ℝ) ^ 13 →
        complement ≤ exceptional + 32 * flow) :
    s * beta / (2 : ℝ) ^ 13 ≤ flow := by
  by_contra hnot
  have hflow : flow < s * beta / (2 : ℝ) ^ 13 := lt_of_not_ge hnot
  exact defective_conductance_constant_contradiction
    s beta complement exceptional flow hs hbeta
    (hlower hflow) (hupper hflow) hexceptional hflow

/-- The constant extraction after applying the separated-set inequality to
two retained sets of mass at least `s/2`.  The hypothesis `hscale` is the
single square-root/log monotonicity step, kept separate from this linear
arithmetic. -/
theorem retained_separation_constant
    (s q beta separatedScale complement : ℝ)
    (hs : 0 < s) (hbeta0 : 0 ≤ beta)
    (hq : s / 2 ≤ q)
    (hscale : beta / 16 ≤ separatedScale)
    (hsep : q / 4 * separatedScale ≤ complement) :
    s * beta / 128 ≤ complement := by
  have hq4 : s / 8 ≤ q / 4 := by linarith
  calc
    s * beta / 128 = (s / 8) * (beta / 16) := by ring
    _ ≤ (q / 4) * separatedScale :=
      mul_le_mul hq4 hscale (by positivity) (by linarith)
    _ ≤ complement := hsep

end

end UniformRandomMALA
