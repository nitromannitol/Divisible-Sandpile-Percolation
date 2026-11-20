import Sandpile.Support.BrownianValueProcessBound
import Sandpile.Support.FirstContactMinimality

/-!
# Optimality and minimality from value-process estimates

An optimal first contact and an upper bound on expected stopped value-process
values imply attainment and minimality among optimal stopping times.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- First-contact optimality and the stopped value-process upper bound imply
attainment of the stopping value and minimality among optimal stops. -/
theorem Sandpile.Support.first_contact_greatest_and_minimal_of_expectation_bounds
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
    (hMdom : ∀ s ≤ T, ∀ ω, G ((T : ℝ) - s) (B x s ω) ≤ M s ω)
    (τ : Ω → ℝ≥0)
    (hfirst : ∀ ω, IsLeast {s : ℝ≥0 | s ≤ T ∧
      M s ω = G ((T : ℝ) - s) (B x s ω)} (τ ω))
    (hτstop : Sandpile.Continuum.IsBrownianStopping (B x) τ)
    (hopt : (∫ ω, G ((T : ℝ) - τ ω) (B x (τ ω) ω) ∂P) =
      Sandpile.External.Snell.snellValue (B x) P G T)
    (hupper : ∀ σ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping (B x) σ →
      (∀ ω, σ ω ≤ T) → Integrable (fun ω => M (σ ω) ω) P ∧
        (∫ ω, M (σ ω) ω ∂P) ≤ Sandpile.External.Snell.snellValue (B x) P G T) :
    IsGreatest (Sandpile.External.Snell.attainable (B x) P G T)
      (∫ ω, G ((T : ℝ) - τ ω) (B x (τ ω) ω) ∂P) ∧
    ∀ σ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping (B x) σ →
      (∀ ω, σ ω ≤ T) →
      (∫ ω, G ((T : ℝ) - σ ω) (B x (σ ω) ω) ∂P) =
        Sandpile.External.Snell.snellValue (B x) P G T →
      ∀ᵐ ω ∂P, τ ω ≤ σ ω := by
  have hτT : ∀ ω, τ ω ≤ T := fun ω => (hfirst ω).1.1
  obtain ⟨_, hBdd⟩ := Sandpile.Support.brownian_stopping_payoffs_integrable_and_bddAbove
    x P (B x) (hB x) (hBm x) (hBc x) T G hG hgrow
  obtain ⟨_, _, _, hMint⟩ :=
    Sandpile.Support.exists_integrable_brownian_value_process_bound
      P B hB hBc hBm x T G hG hgrow M hMm hMc hMval
  constructor
  · refine ⟨⟨τ, hτstop, ?_, rfl⟩, ?_⟩
    · intro ω
      exact_mod_cast hτT ω
    · intro a ha
      rw [hopt]
      exact le_csSup hBdd ha
  · intro σ hσ hσT hσopt
    have hσm := hσ.measurable (hBm x)
    have hσMi : Integrable (fun ω => M (σ ω) ω) P := hMint σ hσm hσT
    have hσRi : Integrable (fun ω => G ((T : ℝ) - σ ω) (B x (σ ω) ω)) P :=
      (Sandpile.Support.brownian_stopping_payoffs_integrable_and_bddAbove
        x P (B x) (hB x) (hBm x) (hBc x) T G hG hgrow).1 σ hσ hσT
    exact Sandpile.Support.ae_first_contact_le_of_integral_bound P M
      (fun s ω => G ((T : ℝ) - s) (B x s ω)) T τ σ hfirst hσT hσMi hσRi
      (ae_of_all _ fun ω => hMdom (σ ω) (hσT ω) ω) _ (hupper σ hσ hσT).2 hσopt
