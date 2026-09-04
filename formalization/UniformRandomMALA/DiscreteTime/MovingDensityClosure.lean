import UniformRandomMALA.DiscreteTime.DensityTestHolder

/-!
# Closure of uniformly `L^p` densities under a moving reference

This module composes the finite density-to-test Hölder estimate with the
elementary moving-reference closure theorem.  The numerator measure is
constant, while its reference probability measures converge weakly.  No
varying-`L^p` compactness theorem is used: bounded continuous tests are the
only objects passed to the limit.
-/

namespace UniformRandomMALA

open Filter MeasureTheory

noncomputable section

namespace DiscreteTime

variable {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]

/-- A constant probability measure with uniformly centered `L^p` densities
against weakly convergent reference measures has an `L^p` density against
the limiting reference.

The conclusion names the canonical limiting density explicitly as Mathlib's
Radon--Nikodym derivative.  Besides its density identity, it records the
centered `L^p` membership and the quantitative norm bound.
-/
theorem rnDeriv_memLp_of_moving_withDensity
    (mu sigma : ProbabilityMeasure E)
    (nu : ℕ → ProbabilityMeasure E)
    (F : ℕ → E → ℝ)
    {p q C : ℝ}
    (hp : 2 ≤ p) (hpq : p.HolderConjugate q) (hC : 0 ≤ C)
    (hnu : Tendsto nu atTop (nhds sigma))
    (hF_meas : ∀ n, Measurable (F n))
    (hF_nonneg : ∀ n x, 0 ≤ F n x)
    (hDensity : ∀ n, (mu : Measure E) =
      (nu n : Measure E).withDensity (fun x => ENNReal.ofReal (F n x)))
    (hMoment : ∀ n,
      Integrable (fun x => |F n x - 1| ^ p) (nu n : Measure E))
    (hRoot : ∀ n,
      (∫ x, |F n x - 1| ^ p ∂(nu n : Measure E)) ^ (1 / p) ≤ C) :
    (mu : Measure E) ≪ (sigma : Measure E) ∧
      (sigma : Measure E).withDensity
          ((mu : Measure E).rnDeriv (sigma : Measure E)) = (mu : Measure E) ∧
      MemLp
        (fun x => ((mu : Measure E).rnDeriv (sigma : Measure E) x).toReal - 1)
        (ENNReal.ofReal p) (sigma : Measure E) ∧
      (∫ x,
          |((mu : Measure E).rnDeriv (sigma : Measure E) x).toReal - 1| ^ p
          ∂(sigma : Measure E)) ^ (1 / p) ≤ C := by
  have hmu : Tendsto (fun _ : ℕ => mu) atTop (nhds mu) := tendsto_const_nhds
  have hq : 1 ≤ q := hpq.symm.lt.le
  have hconj : 1 / p + 1 / q = 1 := by
    simpa only [one_div] using hpq.inv_add_inv_eq_one
  have hbound (n : ℕ) (f : BoundedContinuousFunction E ℝ) :
      |(∫ x, f x ∂(mu : Measure E)) -
          ∫ x, f x ∂(nu n : Measure E)| ≤
        C * (∫ x, |f x| ^ q ∂(nu n : Measure E)) ^ (1 / q) :=
    boundedContinuous_holder_of_withDensity_moment
      mu (nu n) hpq (hF_meas n) (hF_nonneg n) (hDensity n)
        (hMoment n) (hRoot n) f
  have hlimitBound (f : BoundedContinuousFunction E ℝ) :
      |(∫ x, f x ∂(mu : Measure E)) -
          ∫ x, f x ∂(sigma : Measure E)| ≤
        C * (∫ x, |f x| ^ q ∂(sigma : Measure E)) ^ (1 / q) :=
    boundedContinuous_holder_bound_of_weakLimit hmu hnu f hpq.symm.pos
      (fun n => hbound n f)
  have hac : (mu : Measure E) ≪ (sigma : Measure E) :=
    absolutelyContinuous_of_boundedContinuous_holder mu sigma hq hlimitBound
  have hcenter := centeredRNDeriv_memLp_of_weakLimit
    (mu := fun _ : ℕ => mu) (nu := nu) (muLimit := mu) (nuLimit := sigma)
    hp hq hconj hC hmu hnu hbound
  refine ⟨hac, Measure.withDensity_rnDeriv_eq _ _ hac, ?_, ?_⟩
  · change MemLp (centeredRNDeriv (mu : Measure E) (sigma : Measure E))
      (ENNReal.ofReal p) (sigma : Measure E)
    exact hcenter.1
  · change (∫ x, |centeredRNDeriv (mu : Measure E) (sigma : Measure E) x| ^ p
        ∂(sigma : Measure E)) ^ (1 / p) ≤ C
    exact hcenter.2

end DiscreteTime

end

end UniformRandomMALA
