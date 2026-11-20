import Sandpile.Support.BrownianCompactContinuation
import Sandpile.Support.IntegrablePositionTail
import Sandpile.Support.StoppedExpectationExtension
import Sandpile.Support.BrownianValueProcessAdapted

/-!
# Brownian stopped-value expectation bound

Near-optimal continuation on compact events and integrable path envelopes give
the stopped-value expectation bound, first for countable-range stops and then
for all bounded raw stopping times.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- The Brownian value process has expectation at most its initial value at
any bounded countable-range raw stopping time. -/
theorem Sandpile.Support.brownian_stopped_value_le_of_countable_range
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Sandpile.Continuum.Space d → ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (hB : ∀ y, Sandpile.Continuum.IsBrownian d y (B y) P)
    (hBc : ∀ y ω, Continuous fun t => B y t ω)
    (hBm : ∀ y t, StronglyMeasurable (B y t))
    (x : Sandpile.Continuum.Space d) (T : ℝ≥0)
    (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hG : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (T : ℝ) ×ˢ Set.univ))
    (hgrow : ∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (T : ℝ),
      ∀ y, |G t y| ≤ C * (1 + ‖y‖) ^ k)
    (M : ℝ≥0 → Ω → ℝ) (hMm : ∀ s, Measurable (M s))
    (hMc : ∀ ω, Continuous fun s => M s ω)
    (hMval : ∀ s ≤ T, ∀ ω, M s ω =
      Sandpile.External.Snell.snellValue (B (B x s ω)) P G ((T : ℝ) - s))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (LatticeProb.natFiltration (B x) (hBm x))
      (fun ω => (τ ω : ℝ≥0∞)))
    (hcount : (Set.range τ).Countable) (hτT : ∀ ω, τ ω ≤ T) :
    Integrable (fun ω => M (τ ω) ω) P ∧
      (∫ ω, M (τ ω) ω ∂P) ≤ Sandpile.External.Snell.snellValue (B x) P G T := by
  have hτm : Measurable τ := LatticeProb.measurable_of_isStoppingTime hτ
  let Y : Ω → Sandpile.Continuum.Space d := fun ω => B x (τ ω) ω
  have hYm : Measurable Y := Sandpile.Continuum.measurable_stopped_position
    (fun t => (hBm x t).measurable) (hBc x) hτm
  obtain ⟨D₁, hD₁i, hD₁, hMint⟩ :=
    Sandpile.Support.exists_integrable_brownian_value_process_bound
      P B hB hBc hBm x T G hG hgrow M hMm hMc hMval
  obtain ⟨D₂, hD₂i, hD₂⟩ := Sandpile.Support.exists_integrable_brownian_reward_bound
    x P (B x) (hB x) (hBm x) (hBc x) T G hgrow
  let D : Ω → ℝ := fun ω => ‖D₁ ω‖ + ‖D₂ ω‖
  have hDi : Integrable D P := hD₁i.norm.add hD₂i.norm
  have hD0 : ∀ ω, 0 ≤ D ω := fun ω => add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hMi : Integrable (fun ω => M (τ ω) ω) P := hMint τ hτm hτT
  obtain ⟨_, hbd⟩ := Sandpile.Support.brownian_stopping_payoffs_integrable_and_bddAbove
    x P (B x) (hB x) (hBm x) (hBc x) T G hG hgrow
  refine ⟨hMi, le_of_forall_pos_le_add fun δ hδ => ?_⟩
  have htail := Sandpile.Support.tendsto_integral_norm_on_position_tail P Y hYm D hDi
  have hev := htail.eventually (isOpen_Iio.mem_nhds (half_pos hδ))
  obtain ⟨n, hn⟩ := hev.exists
  let K : Set (Sandpile.Continuum.Space d) := Metric.closedBall 0 (n : ℝ)
  have hK : IsCompact K := isCompact_closedBall 0 (n : ℝ)
  let E : Set Ω := {ω | Y ω ∈ K}
  have hEm : MeasurableSet E := hYm measurableSet_closedBall
  have hEc : Eᶜ = {ω | (n : ℝ) < ‖Y ω‖} := by
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, E, K, Metric.mem_closedBall,
      dist_zero_right, not_le]
  have htail' : (∫ ω in Eᶜ, D ω ∂P) < δ / 2 := by
    rw [hEc]
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hD0 _)] using hn
  obtain ⟨ρ, hρ, hρbounds, hcompact⟩ :=
    Sandpile.Support.exists_compact_near_optimal_continuation
      P B hB hBc hBm x T G hG hgrow M hMm hMc hMval τ hτ hcount hτT K hK (δ / 2) (half_pos hδ)
  change (∫ ω in E, M (τ ω) ω ∂P) ≤
    (∫ ω in E, G ((T : ℝ) - ρ ω) (B x (ρ ω) ω) ∂P) + P.real E * (δ / 2) at hcompact
  have hρT : ∀ ω, ρ ω ≤ T := fun ω => (hρbounds ω).2
  have hRi : Integrable (fun ω => G ((T : ℝ) - ρ ω) (B x (ρ ω) ω)) P :=
    (Sandpile.Support.brownian_stopping_payoffs_integrable_and_bddAbove
      x P (B x) (hB x) (hBm x) (hBc x) T G hG hgrow).1 ρ hρ hρT
  have hρval : (∫ ω, G ((T : ℝ) - ρ ω) (B x (ρ ω) ω) ∂P) ≤
      Sandpile.External.Snell.snellValue (B x) P G T := by
    apply le_csSup hbd
    exact ⟨ρ, hρ, (fun ω => by exact_mod_cast hρT ω), rfl⟩
  have hdiff : (∫ ω in Eᶜ, (M (τ ω) ω - G ((T : ℝ) - ρ ω) (B x (ρ ω) ω)) ∂P) ≤
      ∫ ω in Eᶜ, D ω ∂P := by
    apply integral_mono_ae (hMi.sub hRi).integrableOn hDi.integrableOn
    filter_upwards [ae_restrict_of_ae hD₁, ae_restrict_of_ae hD₂] with ω hω₁ hω₂
    have hv := hω₁ (τ ω) (hτT ω)
    have hr := hω₂ (ρ ω) (hρT ω)
    change M (τ ω) ω - G ((T : ℝ) - ρ ω) (B x (ρ ω) ω) ≤ ‖D₁ ω‖ + ‖D₂ ω‖
    have hv' : M (τ ω) ω ≤ ‖D₁ ω‖ := by
      have hh : M (τ ω) ω ≤ D₁ ω := (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hv)
      exact hh.trans (by simpa only [Real.norm_eq_abs] using le_abs_self (D₁ ω))
    have hr' : -G ((T : ℝ) - ρ ω) (B x (ρ ω) ω) ≤ ‖D₂ ω‖ := by
      have hh : -G ((T : ℝ) - ρ ω) (B x (ρ ω) ω) ≤ D₂ ω :=
        (neg_le_abs _).trans (by simpa only [Real.norm_eq_abs] using hr)
      exact hh.trans (by simpa only [Real.norm_eq_abs] using le_abs_self (D₂ ω))
    linarith
  have hMsplit := integral_add_compl hEm hMi
  have hRsplit := integral_add_compl hEm hRi
  have hdiffsplit := integral_sub hMi.integrableOn hRi.integrableOn
    (μ := P.restrict Eᶜ)
  have hP : P.real E * (δ / 2) ≤ δ / 2 := by
    nlinarith [measureReal_le_one (μ := P) (s := E)]
  linarith

/-- The Brownian value process has expectation at most its initial value at
any bounded raw stopping time. -/
theorem Sandpile.Support.brownian_stopped_value_expectation_bound
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Sandpile.Continuum.Space d → ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (hB : ∀ y, Sandpile.Continuum.IsBrownian d y (B y) P)
    (hBc : ∀ y ω, Continuous fun t => B y t ω)
    (hBm : ∀ y t, StronglyMeasurable (B y t))
    (x : Sandpile.Continuum.Space d) (T : ℝ≥0)
    (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hG : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (T : ℝ) ×ˢ Set.univ))
    (hgrow : ∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (T : ℝ),
      ∀ y, |G t y| ≤ C * (1 + ‖y‖) ^ k)
    (M : ℝ≥0 → Ω → ℝ) (hMm : ∀ s, Measurable (M s))
    (hMc : ∀ ω, Continuous fun s => M s ω)
    (hMval : ∀ s ≤ T, ∀ ω, M s ω =
      Sandpile.External.Snell.snellValue (B (B x s ω)) P G ((T : ℝ) - s))
    (τ : Ω → ℝ≥0) (hτ : Sandpile.Continuum.IsBrownianStopping (B x) τ)
    (hτT : ∀ ω, τ ω ≤ T) :
    Integrable (fun ω => M (τ ω) ω) P ∧
      (∫ ω, M (τ ω) ω ∂P) ≤ Sandpile.External.Snell.snellValue (B x) P G T := by
  obtain ⟨D, hDi, hD, _⟩ := Sandpile.Support.exists_integrable_brownian_value_process_bound
    P B hB hBc hBm x T G hG hgrow M hMm hMc hMval
  apply Sandpile.Support.stopped_expectation_le_of_finite_range P
    (LatticeProb.natFiltration (B x) (hBm x)) M (fun s => (hMm s).stronglyMeasurable)
    hMc T D hDi hD _ ?_ τ hτ hτT
  intro σ hσ hσfin hσT
  exact (Sandpile.Support.brownian_stopped_value_le_of_countable_range
    P B hB hBc hBm x T G hG hgrow M hMm hMc hMval σ hσ hσfin.countable hσT).2

/-- The Brownian stopping value is superharmonic for every bounded raw
stopping time. -/
theorem Sandpile.Support.brownian_snellValue_superharmonic
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Sandpile.Continuum.Space d → ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (hB : ∀ y, Sandpile.Continuum.IsBrownian d y (B y) P)
    (hBc : ∀ y ω, Continuous fun t => B y t ω)
    (hBm : ∀ y t, StronglyMeasurable (B y t))
    (x : Sandpile.Continuum.Space d) (T : ℝ≥0)
    (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hG : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (T : ℝ) ×ˢ Set.univ))
    (hgrow : ∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (T : ℝ),
      ∀ y, |G t y| ≤ C * (1 + ‖y‖) ^ k)
    (τ : Ω → ℝ≥0) (hτ : Sandpile.Continuum.IsBrownianStopping (B x) τ)
    (hτT : ∀ ω, τ ω ≤ T) :
    Integrable (fun ω => Sandpile.External.Snell.snellValue (B (B x (τ ω) ω)) P G
      ((T : ℝ) - τ ω)) P ∧
    (∫ ω, Sandpile.External.Snell.snellValue (B (B x (τ ω) ω)) P G
      ((T : ℝ) - τ ω) ∂P) ≤ Sandpile.External.Snell.snellValue (B x) P G T := by
  obtain ⟨M, _, _, hMm, hMval, hMc, _, _, _, _⟩ :=
    Sandpile.Support.exists_adapted_brownian_value_process P B hB hBc hBm x T G hG hgrow
  have hh := Sandpile.Support.brownian_stopped_value_expectation_bound
    P B hB hBc hBm x T G hG hgrow M hMm hMc hMval τ hτ hτT
  have heq : (fun ω => M (τ ω) ω) = fun ω =>
      Sandpile.External.Snell.snellValue (B (B x (τ ω) ω)) P G ((T : ℝ) - τ ω) :=
    funext fun ω => hMval (τ ω) (hτT ω) ω
  rwa [heq] at hh
