import Sandpile.Support.BrownianValueContinuity
import Sandpile.Support.ValueProcessFirstContact
import Sandpile.Support.BrownianValueAboveGain

/-!
# Brownian value process and first contact

A polynomial-growth Brownian stopping value has a measurable continuous value
process and a pointwise least natural-filtration contact time.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Brownian stopping values produce a measurable continuous value process and
a pointwise least natural-filtration contact time. -/
theorem Sandpile.Support.exists_brownian_snell_value_process_first_contact
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
    ∃ M : ℝ≥0 → Ω → ℝ,
      (∀ s, Measurable (M s)) ∧
      (∀ s ≤ T, ∀ ω, M s ω =
        Sandpile.External.Snell.snellValue (B (B x s ω)) P G ((T : ℝ) - s)) ∧
      (∀ ω, Continuous fun s => M s ω) ∧
      ∃ τ : Ω → ℝ≥0,
        (∀ ω, IsLeast {s : ℝ≥0 | s ≤ T ∧
          M s ω = G ((T : ℝ) - s) (B x s ω)} (τ ω)) ∧
        Sandpile.Continuum.IsBrownianStopping (B x) τ := by
  exact Sandpile.Support.exists_snell_value_process_first_contact_of_continuous
    P B hB x (hBc x) (hBm x) T G hG
    (Sandpile.Support.continuousOn_brownian_snellValue P B hB hBm hBc T G hG hgrow)

/-- The Brownian value process dominates the reward and has a pointwise least
natural-filtration contact time. -/
theorem Sandpile.Support.exists_brownian_value_process_dominating_reward
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
    ∃ M : ℝ≥0 → Ω → ℝ,
      (∀ s, Measurable (M s)) ∧
      (∀ s ≤ T, ∀ ω, M s ω =
        Sandpile.External.Snell.snellValue (B (B x s ω)) P G ((T : ℝ) - s)) ∧
      (∀ ω, Continuous fun s => M s ω) ∧
      (∀ s ≤ T, ∀ ω, G ((T : ℝ) - s) (B x s ω) ≤ M s ω) ∧
      ∃ τ : Ω → ℝ≥0,
        (∀ ω, IsLeast {s : ℝ≥0 | s ≤ T ∧
          M s ω = G ((T : ℝ) - s) (B x s ω)} (τ ω)) ∧
        Sandpile.Continuum.IsBrownianStopping (B x) τ := by
  obtain ⟨M, hMm, hMval, hMc, τ, hτfirst, hτstop⟩ :=
    Sandpile.Support.exists_brownian_snell_value_process_first_contact
      P B hB hBc hBm x T G hG hgrow
  refine ⟨M, hMm, hMval, hMc, ?_, τ, hτfirst, hτstop⟩
  intro s hs ω
  let y := B x s ω
  have hle : ((T - s : ℝ≥0) : ℝ) ≤ (T : ℝ) := by exact_mod_cast (tsub_le_self : T - s ≤ T)
  have hGs : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 ((T - s : ℝ≥0) : ℝ) ×ˢ Set.univ) := hG.mono (by
    intro p hp
    exact ⟨⟨hp.1.1, hp.1.2.trans hle⟩, hp.2⟩)
  have hgs : ∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) ((T - s : ℝ≥0) : ℝ),
      ∀ z, |G t z| ≤ C * (1 + ‖z‖) ^ k := by
    obtain ⟨C, k, hk⟩ := hgrow
    exact ⟨C, k, fun t ht z => hk t ⟨ht.1, ht.2.trans hle⟩ z⟩
  rw [hMval s hs ω, ← NNReal.coe_sub hs]
  exact Sandpile.Support.le_brownian_snellValue y P (B y) (hB y) (hBm y) (hBc y) (T - s) G hGs hgs
