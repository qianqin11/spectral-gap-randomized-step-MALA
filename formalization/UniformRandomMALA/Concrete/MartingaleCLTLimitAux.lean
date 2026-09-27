import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Removing a small truncation parameter from asymptotic bounds

Each positive truncation parameter supplies a convergent upper bound.
When the limiting upper bounds tend to zero as that parameter decreases
to zero, the nonnegative quantity being bounded also tends to zero.
-/

namespace UniformRandomMALA.Concrete

open Filter Set
open scoped Topology

/-- A nonnegative family tends to zero if every positive parameter supplies
an eventual asymptotic bound whose limiting value tends to zero from the right. -/
theorem tendsto_zero_of_small_parameter_eventual_bound
    {ι : Type*} {l : Filter ι} {a : ι → ℝ} {b : ℝ → ι → ℝ} {c : ℝ → ℝ}
    (ha : ∀ᶠ n in l, 0 ≤ a n)
    (hle : ∀ δ > 0, ∀ᶠ n in l, a n ≤ b δ n)
    (hb : ∀ δ > 0, Tendsto (b δ) l (𝓝 (c δ)))
    (hc : Tendsto c (𝓝[>] 0) (𝓝 0)) :
    Tendsto a l (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro z hz
    exact ha.mono fun n hn => hz.trans_le hn
  · intro ε hε
    have hsmall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), c δ < ε :=
      hc.eventually (eventually_lt_nhds hε)
    obtain ⟨δ, hδsmall, hδpos⟩ :=
      (hsmall.and (self_mem_nhdsWithin : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Ioi 0)).exists
    exact (hle δ hδpos).and (hb δ hδpos |>.eventually (eventually_lt_nhds hδsmall))
      |>.mono fun n hn => hn.1.trans_lt hn.2

/-- A sequential form convenient for finite-row martingale CLT estimates. -/
theorem tendsto_zero_of_small_parameter_bound
    {a : ℕ → ℝ} {b : ℝ → ℕ → ℝ} {c : ℝ → ℝ}
    (ha : ∀ n, 0 ≤ a n)
    (hle : ∀ δ > 0, ∀ n, a n ≤ b δ n)
    (hb : ∀ δ > 0, Tendsto (b δ) atTop (𝓝 (c δ)))
    (hc : ContinuousAt c 0) (hc0 : c 0 = 0) :
    Tendsto a atTop (𝓝 0) := by
  apply tendsto_zero_of_small_parameter_eventual_bound
    (Eventually.of_forall ha) (fun δ hδ => Eventually.of_forall (hle δ hδ)) hb
  simpa only [hc0] using hc.tendsto.mono_left nhdsWithin_le_nhds

end UniformRandomMALA.Concrete
