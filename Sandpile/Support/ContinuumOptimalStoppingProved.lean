import Sandpile.External.ContinuumOptimalStoppingOfContinuous
import Sandpile.Support.BrownianValueProcessAdapted
import Sandpile.Support.BrownianFirstContactMartingale
import Sandpile.Support.BrownianOptimalityReduction

/-!
# Brownian optimal stopping for continuous paths

For Brownian paths that are continuous at every sample point and have
measurable time slices, first contact attains the stopping value and is
minimal among optimal stopping times.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- The finite-horizon Brownian optimal-stopping theorem holds for continuous
paths and strongly measurable time slices. -/
theorem Sandpile.External.continuumOptimalStoppingOfContinuous_holds
    {Ω : Type*} [MeasurableSpace Ω] :
    Sandpile.External.ContinuumOptimalStoppingOfContinuous Ω := by
  intro d T hT G hG hgrow x P _ B hB hBc hBm
  let T' : ℝ≥0 := ⟨T, hT.le⟩
  have hG' : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (T' : ℝ) ×ˢ Set.univ) := hG
  have hgrow' : ∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (T' : ℝ),
      ∀ y, |G t y| ≤ C * (1 + ‖y‖) ^ k := hgrow
  obtain ⟨M, D, hDi, hMm, hMval, hMc, hMad, hD, hMdom, τ, hfirst, hτstop⟩ :=
    Sandpile.Support.exists_adapted_brownian_value_process P B hB hBc hBm x T' G hG' hgrow'
  have hτmart := Sandpile.Support.brownian_first_contact_stopped_martingale
    P B hB hBc hBm x T' G hG' hgrow' M hMm hMc hMad hMval hMdom τ hτstop hfirst
  have hupper : ∀ σ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping (B x) σ →
      (∀ ω, σ ω ≤ T') → Integrable (fun ω => M (σ ω) ω) P ∧
        (∫ ω, M (σ ω) ω ∂P) ≤ Sandpile.External.Snell.snellValue (B x) P G T' := by
    intro σ hσ hσT
    exact Sandpile.Support.brownian_stopped_value_expectation_bound
      P B hB hBc hBm x T' G hG' hgrow' M hMm hMc hMval σ hσ hσT
  obtain ⟨hgreat, hminimal⟩ :=
    Sandpile.Support.first_contact_greatest_and_minimal_of_stopped_martingale
      P B hB hBc hBm x T' G hG' hgrow' M hMm hMc hMval hMdom τ hfirst hτstop hτmart hupper
  refine ⟨M, hMm, ?_, ?_, τ, ?_, hτstop, hgreat, ?_⟩
  · intro s hs
    exact ae_of_all P (hMval s (by exact_mod_cast hs))
  · intro ω s
    exact (hMc ω).continuousWithinAt
  · intro ω
    have he : {s : ℝ≥0 | s ≤ T' ∧ M s ω = G ((T' : ℝ) - s) (B x s ω)} =
        {s : ℝ≥0 | (s : ℝ) ≤ T ∧ M s ω = G (T - (s : ℝ)) (B x s ω)} := by
      ext s
      simp only [Set.mem_ofPred_eq]
      rfl
    exact he ▸ hfirst ω
  · intro σ hσ hσT hσopt
    exact hminimal σ hσ (fun ω => by exact_mod_cast hσT ω) hσopt
