import UniformRandomMALA.Concrete.MarkovInfinitePath

/-! # Extending the finite path by its next Markov transition -/

namespace UniformRandomMALA.Concrete
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
noncomputable section
variable {α : Type*} [MeasurableSpace α]

theorem measurable_markovPathSnoc (n : ℕ) :
    Measurable (fun z : (Fin n → α) × α => (Fin.snoc z.1 z.2 : Fin (n + 1) → α)) := by
  apply measurable_pi_iff.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using (measurable_snd : Measurable (Prod.snd : (Fin n → α) × α → α))
  · simpa only [Fin.snoc_castSucc, Function.comp_def] using
      (measurable_pi_apply j).comp (measurable_fst : Measurable (Prod.fst : (Fin n → α) × α → Fin n → α))

theorem lintegral_finiteMarkovPathKernel_succ (K : Kernel α α) [IsMarkovKernel K]
    (n : ℕ) (x : α) {F : (Fin (n + 1) → α) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ path, F path ∂finiteMarkovPathKernel K (n + 1) x =
      ∫⁻ y, ∫⁻ path, F (Fin.cons x path) ∂finiteMarkovPathKernel K n y ∂K x := by
  have hc : Measurable (fun path : Fin n → α => (Fin.cons x path : Fin (n + 1) → α)) :=
    (measurable_markovPathCons n).comp measurable_prodMk_left
  rw [finiteMarkovPathKernel_succ_apply, lintegral_map hF hc]
  exact Kernel.lintegral_comp _ _ _ (hF.comp hc)

theorem lintegral_finiteMarkovPathKernel_one (K : Kernel α α) [IsMarkovKernel K]
    (x : α) {F : (Fin 1 → α) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ path, F path ∂finiteMarkovPathKernel K 1 x = F (fun _ => x) := by
  rw [lintegral_finiteMarkovPathKernel_succ K 0 x hF]
  simp only [finiteMarkovPathKernel, Kernel.deterministic_apply]
  have heq : (Fin.cons x Fin.elim0 : Fin 1 → α) = fun _ => x := by ext i; fin_cases i; rfl
  simp [heq]

theorem measurable_finitePathNextIntegral (K : Kernel α α) [IsMarkovKernel K]
    (n : ℕ) {F : (Fin (n + 2) → α) → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun path : Fin (n + 1) → α => ∫⁻ y, F (Fin.snoc path y) ∂K (path (Fin.last n))) := by
  exact (hF.comp (measurable_markovPathSnoc (n + 1))).lintegral_kernel_prod_right'
    (κ := K.comap (fun path => path (Fin.last n)) (measurable_pi_apply _))

/-- The reverse recursive finite-path construction also has the forward
transition rule: retain the prefix, then sample its final successor. -/
theorem lintegral_finiteMarkovPathKernel_append (K : Kernel α α) [IsMarkovKernel K]
    (n : ℕ) (x : α) {F : (Fin (n + 2) → α) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ path, F path ∂finiteMarkovPathKernel K (n + 2) x =
      ∫⁻ path, ∫⁻ y, F (Fin.snoc path y) ∂K (path (Fin.last n))
        ∂finiteMarkovPathKernel K (n + 1) x := by
  induction n generalizing x with
  | zero =>
    rw [lintegral_finiteMarkovPathKernel_succ K 1 x hF,
      lintegral_finiteMarkovPathKernel_one K x (measurable_finitePathNextIntegral K 0 hF)]
    apply lintegral_congr
    intro y
    rw [lintegral_finiteMarkovPathKernel_one K y (F := fun path => F (Fin.cons x path))
      (hF.comp ((measurable_markovPathCons 1).comp (measurable_const.prodMk measurable_id)))]
    congr 1
    ext i
    fin_cases i <;> simp [Fin.snoc]
  | succ n ih =>
    rw [lintegral_finiteMarkovPathKernel_succ K (n + 2) x hF,
      lintegral_finiteMarkovPathKernel_succ K (n + 1) x
        (measurable_finitePathNextIntegral K (n + 1) hF)]
    apply lintegral_congr
    intro y
    rw [ih y (F := fun path => F (Fin.cons x path))
      (hF.comp ((measurable_markovPathCons (n + 2)).comp (measurable_const.prodMk measurable_id)))]
    apply lintegral_congr
    intro path
    simp only [Fin.cons_last, Fin.cons_snoc_eq_snoc_cons]

def finitePathNextKernel (K : Kernel α α) (n : ℕ) : Kernel (Fin (n + 1) → α) α :=
  K.comap (fun path => path (Fin.last n)) (measurable_pi_apply _)

instance finitePathNextKernel_isMarkovKernel (K : Kernel α α) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (finitePathNextKernel K n) := by unfold finitePathNextKernel; infer_instance

theorem finiteMarkovPathLaw_append (μ : Measure α) [IsProbabilityMeasure μ]
    (K : Kernel α α) [IsMarkovKernel K] (n : ℕ) :
    finiteMarkovPathLaw μ K (n + 2) =
      ((finiteMarkovPathLaw μ K (n + 1)) ⊗ₘ finitePathNextKernel K n).map
        (fun z => Fin.snoc z.1 z.2) := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (measurable_markovPathSnoc (n + 1))]
  rw [Measure.lintegral_compProd (f := fun z => F (Fin.snoc z.1 z.2))
    (hF.comp (measurable_markovPathSnoc (n + 1)))]
  change (∫⁻ path, F path ∂finiteMarkovPathKernel K (n + 2) ∘ₘ μ) =
    ∫⁻ path, (∫⁻ y, F (Fin.snoc path y) ∂K (path (Fin.last n)))
      ∂finiteMarkovPathKernel K (n + 1) ∘ₘ μ
  rw [Measure.lintegral_bind (finiteMarkovPathKernel K (n + 2)).aemeasurable hF.aemeasurable,
    Measure.lintegral_bind (finiteMarkovPathKernel K (n + 1)).aemeasurable
      (measurable_finitePathNextIntegral K n hF).aemeasurable]
  apply lintegral_congr
  intro x
  exact lintegral_finiteMarkovPathKernel_append K n x hF

end
end UniformRandomMALA.Concrete
