import Sandpile.External.Stopping.TimeChange

/-!
# Oscillations after a stopping time

The diffusive walk has uniformly small maximal displacement over a short
interval following a bounded stopping time. This strengthens the increment
estimate used in the tightness criterion of Coquet and Toldo, *Convergence of
values in optimal stopping and convergence of optimal stopping times*, Section 2.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Maximal displacement on a short interval after a bounded stopping time is
uniformly small in probability. -/
theorem diffusiveWalk_interval_increment_small (d : ℕ) (hd : 1 ≤ d) (ε η : ℝ)
    (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ R₀ : ℝ, 0 < δ ∧ 0 < R₀ ∧
      ∀ (R : ℝ), R₀ ≤ R → ∀ (H : ℝ≥0) (x : Site d)
        (τ : (ℕ → Site d) → ℝ≥0),
        Continuum.IsBrownianStopping (diffusiveWalk R) τ →
        (∀ X, τ X ≤ H) →
        walkLaw d x {X | ∃ t : ℝ≥0, τ X ≤ t ∧ (t : ℝ) ≤ (τ X : ℝ) + δ ∧
          ε ≤ ‖diffusiveWalk R t X - diffusiveWalk R (τ X) X‖} ≤ ENNReal.ofReal η := by
  classical
  obtain ⟨δ, R₀, hδ, hR₀, hsmall⟩ := diffusiveWalk_increment_small d hd ε η hε hη
  refine ⟨δ, R₀, hδ, hR₀, ?_⟩
  intro R hR H x τ hτ hτH
  let P : (ℕ → Site d) → ℝ≥0 → Prop := fun X t =>
    τ X ≤ t ∧ (t : ℝ) ≤ (τ X : ℝ) + δ ∧
      ε ≤ ‖diffusiveWalk R t X - diffusiveWalk R (τ X) X‖
  let σ : (ℕ → Site d) → ℝ≥0 := fun X =>
    if h : ∃ t, P X t then Classical.choose h else τ X
  have hσ : ∀ X, τ X ≤ σ X ∧ (σ X : ℝ) ≤ (τ X : ℝ) + δ := by
    intro X
    by_cases h : ∃ t, P X t
    · have hw := Classical.choose_spec h
      simpa only [σ, dite_eq_left h] using And.intro hw.1 hw.2.1
    · simp only [σ, dite_eq_right h, le_refl, true_and]
      linarith
  have hsub : {X | ∃ t : ℝ≥0, P X t} ⊆
      {X | ε ≤ ‖diffusiveWalk R (σ X) X - diffusiveWalk R (τ X) X‖} := by
    intro X hX
    have hX' : ∃ t, P X t := hX
    have hw := Classical.choose_spec hX'
    change ε ≤ ‖diffusiveWalk R (σ X) X - diffusiveWalk R (τ X) X‖
    simpa only [σ, dite_eq_left hX'] using hw.2.2
  exact (measure_mono hsub).trans (hsmall R hR H x τ σ hτ hτH hσ)

end Sandpile.External.Stopping
