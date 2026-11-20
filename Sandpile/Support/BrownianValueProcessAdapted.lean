import Sandpile.Support.BrownianValueAdapted
import Sandpile.Support.BrownianValueProcessBound

/-!
# The adapted Brownian value process

The Brownian value process may be frozen after the horizon while retaining
continuity, raw adaptation, an integrable path bound and first contact.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- The Brownian stopping value admits a continuous, adapted and integrably
dominated process with a pointwise least raw first-contact time. -/
theorem Sandpile.Support.exists_adapted_brownian_value_process
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
      ∀ y, |G t y| ≤ C * (1 + ‖y‖) ^ k) :
    ∃ (M : ℝ≥0 → Ω → ℝ) (D : Ω → ℝ),
      Integrable D P ∧ (∀ s, Measurable (M s)) ∧
      (∀ s ≤ T, ∀ ω, M s ω =
        Sandpile.External.Snell.snellValue (B (B x s ω)) P G ((T : ℝ) - s)) ∧
      (∀ ω, Continuous fun s => M s ω) ∧
      StronglyAdapted (Sandpile.Continuum.brownianFiltration (B x)) M ∧
      (∀ᵐ ω ∂P, ∀ s, ‖M s ω‖ ≤ D ω) ∧
      (∀ s ≤ T, ∀ ω, G ((T : ℝ) - s) (B x s ω) ≤ M s ω) ∧
      ∃ τ : Ω → ℝ≥0,
        (∀ ω, IsLeast {s : ℝ≥0 | s ≤ T ∧
          M s ω = G ((T : ℝ) - s) (B x s ω)} (τ ω)) ∧
        Sandpile.Continuum.IsBrownianStopping (B x) τ := by
  obtain ⟨M₀, hMm, hMval, hMc, hMdom, τ, hτfirst, hτstop⟩ :=
    Sandpile.Support.exists_brownian_value_process_dominating_reward
      P B hB hBc hBm x T G hG hgrow
  obtain ⟨D, hDi, hD, _⟩ := Sandpile.Support.exists_integrable_brownian_value_process_bound
    P B hB hBc hBm x T G hG hgrow M₀ hMm hMc hMval
  let M : ℝ≥0 → Ω → ℝ := fun s ω => M₀ (min s T) ω
  have hMs : ∀ s ≤ T, M s = M₀ s := by
    intro s hs
    simp only [M, min_eq_left hs]
  have hMad : StronglyAdapted (Sandpile.Continuum.brownianFiltration (B x)) M :=
    Sandpile.Support.stronglyAdapted_brownian_value_process P B hB hBc hBm x T G hG hgrow M₀ hMval
  refine ⟨M, D, hDi, (fun s => hMm (min s T)), ?_, ?_, hMad, ?_, ?_, τ, ?_, hτstop⟩
  · intro s hs ω
    rw [hMs s hs]
    exact hMval s hs ω
  · intro ω
    exact (hMc ω).comp (continuous_id.min continuous_const)
  · filter_upwards [hD] with ω hω s
    exact hω (min s T) (min_le_right _ _)
  · intro s hs ω
    rw [hMs s hs]
    exact hMdom s hs ω
  · intro ω
    have he : {s : ℝ≥0 | s ≤ T ∧ M s ω = G ((T : ℝ) - s) (B x s ω)} =
        {s : ℝ≥0 | s ≤ T ∧ M₀ s ω = G ((T : ℝ) - s) (B x s ω)} := by
      ext s
      simp only [Set.mem_ofPred_eq, and_congr_right_iff]
      intro hs
      rw [hMs s hs]
    exact he.symm ▸ hτfirst ω
