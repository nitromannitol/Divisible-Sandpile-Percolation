import Sandpile.Support.BrownianRestart
import LatticeProb.Prob.BrownianRestartBound
import Sandpile.Support.StoppingDyadicBounded

/-!
# Restarting a superharmonic Brownian function

Superharmonicity at every starting point gives a stopped-time comparison on
events measurable at the earlier stopping time.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

/-- A superharmonic time-state function has nonincreasing expected value
between bounded stopping times, on events known at the earlier time. -/
theorem Sandpile.Support.setIntegral_superharmonic_restart_le
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Sandpile.Continuum.Space d → ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (hB : ∀ y, Sandpile.Continuum.IsBrownian d y (B y) P)
    (hBm : ∀ y t, StronglyMeasurable (B y t))
    (hBc : ∀ y ω, Continuous fun t => B y t ω)
    (T : ℝ) (hT : 0 ≤ T) (V : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hVc : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => V p.1 p.2)
      (Set.Icc 0 T ×ˢ Set.univ))
    (hsuper : ∀ y, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ρ : Ω → ℝ≥0,
      Sandpile.Continuum.IsBrownianStopping (B y) ρ → (∀ ω, (ρ ω : ℝ) ≤ s) →
      Integrable (fun ω => V (s - ρ ω) (B y (ρ ω) ω)) P →
      (∫ ω, V (s - ρ ω) (B y (ρ ω) ω) ∂P) ≤ V s y)
    (x : Sandpile.Continuum.Space d) (D : Ω → ℝ) (hDi : Integrable D P)
    (hD : ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ s : ℝ≥0,
      (s : ℝ) ≤ T → ‖V t (B x s ω)‖ ≤ D ω)
    (σ τ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (LatticeProb.natFiltration (B x) (hBm x))
      (fun ω => (σ ω : ℝ≥0∞)))
    (hτ : IsStoppingTime (LatticeProb.natFiltration (B x) (hBm x))
      (fun ω => (τ ω : ℝ≥0∞)))
    (hτT : ∀ ω, (τ ω : ℝ) ≤ T)
    (E : Set Ω) (hE : MeasurableSet[hσ.measurableSpace] E)
    (hστ : ∀ ω ∈ E, σ ω ≤ τ ω) :
    (∫ ω in E, (V (T - τ ω) (B x (τ ω) ω) - V (T - σ ω) (B x (σ ω) ω)) ∂P) ≤ 0 := by
  let Vneg : ℝ → Sandpile.Continuum.Space d → ℝ := fun t y => -V t y
  have hnegc : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => Vneg p.1 p.2)
      (Set.Icc 0 T ×ˢ Set.univ) := hVc.neg
  have hneg : ∀ y ∈ (Set.univ : Set (Sandpile.Continuum.Space d)),
      ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ρ : Ω → ℝ≥0,
      IsStoppingTime (LatticeProb.natFiltration (B y) (hBm y)) (fun ω => (ρ ω : ℝ≥0∞)) →
      (∀ ω, (ρ ω : ℝ) ≤ s) → Integrable (fun ω => Vneg (s - ρ ω) (B y (ρ ω) ω)) P →
      Vneg s y - ∫ ω, Vneg (s - ρ ω) (B y (ρ ω) ω) ∂P ≤ 0 := by
    intro y _ s hs ρ hρ hρs hint
    have hi : Integrable (fun ω => V (s - ρ ω) (B y (ρ ω) ω)) P := by
      have hi' := hint.neg
      change Integrable (fun ω => -(-V (s - ρ ω) (B y (ρ ω) ω))) P at hi'
      simpa only [neg_neg] using hi'
    have hh := hsuper y s hs ρ hρ hρs hi
    simp only [Vneg, integral_neg]
    linarith
  have hDneg : ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ s : ℝ≥0,
      (s : ℝ) ≤ T → ‖Vneg t (B x s ω)‖ ≤ D ω := by
    filter_upwards [hD] with ω hω t ht s hs
    simpa only [Vneg, norm_neg] using hω t ht s hs
  let H : ℝ≥0 := ⟨T, hT⟩
  have hτH : ∀ ω, τ ω ≤ H := fun ω => NNReal.coe_le_coe.mp (hτT ω)
  obtain ⟨ρ, hρ, hρfin, hρbound, hρlim⟩ :=
    Sandpile.Support.exists_finite_stoppingTime_approximation
      (LatticeProb.natFiltration (B x) (hBm x)) τ hτ H hτH
  have hρT : ∀ n ω, (ρ n ω : ℝ) ≤ T := fun n ω =>
    NNReal.coe_le_coe.mpr (hρbound n ω).2
  have hfinite : ∀ n, (∫ ω in E, (Vneg (T - σ ω) (B x (σ ω) ω) -
      Vneg (T - ρ n ω) (B x (ρ n ω) ω)) ∂P) ≤ 0 := by
    intro n
    have hh := LatticeProb.IsBrownianSpace.setIntegral_sub_le_of_restart_bound
      P B (fun y => (hB y).toIsBrownianSpace) hBm hBc T hT Vneg hnegc Set.univ 0 hneg
      x D hDi hDneg σ (ρ n) hσ (hρ n) (hρT n) (hρfin n) E hE
      (fun ω hω => (hστ ω hω).trans (hρbound n ω).1)
      (Eventually.of_forall fun _ _ => Set.mem_univ _)
    simpa only [mul_zero] using hh
  let G : ℝ → Sandpile.Continuum.Space d → ℝ := fun t y => Vneg (Set.projIcc 0 T hT t) y
  have hGc : Continuous fun q : ℝ × Sandpile.Continuum.Space d => G q.1 q.2 :=
    hnegc.comp_continuous
      ((continuous_subtype_val.comp (continuous_projIcc (h := hT))).prodMap continuous_id)
      fun q => ⟨(Set.projIcc 0 T hT q.1).2, Set.mem_univ _⟩
  have hGg : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ y, G t y = Vneg t y := fun t ht y => by
    simp only [G, Set.projIcc_of_mem hT ht]
  have hmem : ∀ r : ℝ≥0, (r : ℝ) ≤ T → T - r ∈ Set.Icc (0 : ℝ) T := fun r hr =>
    ⟨sub_nonneg.mpr hr, sub_le_self _ r.coe_nonneg⟩
  have hEm : MeasurableSet E := hσ.measurableSpace_le E hE
  have hσT : ∀ ω ∈ E, (σ ω : ℝ) ≤ T := fun ω hω =>
    (NNReal.coe_le_coe.mpr (hστ ω hω)).trans (hτT ω)
  have hBm' : Measurable (Function.uncurry (B x)) :=
    measurable_uncurry_of_continuous_of_measurable (hBc x) fun r => (hBm x r).measurable
  have hpay : ∀ ρ' : Ω → ℝ≥0, Measurable ρ' →
      Measurable fun ω => G (T - ρ' ω) (B x (ρ' ω) ω) := fun ρ' h =>
    hGc.measurable.comp ((measurable_const.sub h.coe_nnreal_real).prodMk
      (hBm'.comp (h.prodMk measurable_id)))
  have hcr : ∀ ω, Continuous fun r : ℝ≥0 => G (T - r) (B x r ω) := fun ω =>
    hGc.comp ((continuous_const.sub NNReal.continuous_coe).prodMk (hBc x ω))
  let F : ℕ → Ω → ℝ := fun n ω => G (T - σ ω) (B x (σ ω) ω) - G (T - ρ n ω) (B x (ρ n ω) ω)
  have hFeq : ∀ n, ∫ ω in E, F n ω ∂P =
      ∫ ω in E, (Vneg (T - σ ω) (B x (σ ω) ω) - Vneg (T - ρ n ω) (B x (ρ n ω) ω)) ∂P := fun n =>
    setIntegral_congr_fun hEm fun ω hω => by
      simp only [F, hGg _ (hmem _ (hσT ω hω)), hGg _ (hmem _ (hρT n ω))]
  have hlim : Tendsto (fun n => ∫ ω in E, F n ω ∂P) atTop
      (𝓝 (∫ ω in E, (G (T - σ ω) (B x (σ ω) ω) - G (T - τ ω) (B x (τ ω) ω)) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => D ω + D ω)
      (fun n => ((hpay σ (LatticeProb.measurable_of_isStoppingTime hσ)).sub
        (hpay (ρ n) (LatticeProb.measurable_of_isStoppingTime (hρ n)))).aestronglyMeasurable)
      (hDi.add hDi).integrableOn (fun n => ?_)
      (Eventually.of_forall fun ω =>
        tendsto_const_nhds.sub (((hcr ω).tendsto (τ ω)).comp (hρlim ω)))
    filter_upwards [ae_restrict_mem hEm, ae_restrict_of_ae hDneg] with ω hω hd
    have h1 : ‖G (T - σ ω) (B x (σ ω) ω)‖ ≤ D ω := by
      rw [hGg _ (hmem _ (hσT ω hω))]
      exact hd _ (hmem _ (hσT ω hω)) _ (hσT ω hω)
    have h2 : ‖G (T - ρ n ω) (B x (ρ n ω) ω)‖ ≤ D ω := by
      rw [hGg _ (hmem _ (hρT n ω))]
      exact hd _ (hmem _ (hρT n ω)) _ (hρT n ω)
    exact (norm_sub_le _ _).trans (add_le_add h1 h2)
  have hτeq : ∫ ω in E, (G (T - σ ω) (B x (σ ω) ω) - G (T - τ ω) (B x (τ ω) ω)) ∂P =
      ∫ ω in E, (Vneg (T - σ ω) (B x (σ ω) ω) - Vneg (T - τ ω) (B x (τ ω) ω)) ∂P :=
    setIntegral_congr_fun hEm fun ω hω => by
      simp only [hGg _ (hmem _ (hσT ω hω)), hGg _ (hmem _ (hτT ω))]
  have hh : (∫ ω in E, (Vneg (T - σ ω) (B x (σ ω) ω) -
      Vneg (T - τ ω) (B x (τ ω) ω)) ∂P) ≤ 0 := by
    rw [← hτeq]
    exact le_of_tendsto' hlim fun n => (hFeq n).trans_le (hfinite n)
  simpa only [Vneg, neg_sub_neg] using hh
