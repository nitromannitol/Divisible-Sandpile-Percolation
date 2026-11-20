import Sandpile.External.Stopping.IndistinguishableStoppingValue
import Sandpile.External.Stopping.AECubeStoppingValue

/-!
# Killed stopping values of indistinguishable processes

Almost-sure stopping payoff sets with almost-sure killing constraints depend
only on the indistinguishability classes of the process and killing clock.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace Sandpile.External.Stopping

/-- Indistinguishable processes and almost-surely equal clocks have equal
almost-sure killed payoff sets. -/
theorem aeClockPayoffs_eq_of_indistinguishable
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    (B C : ℝ≥0 → Ω → Continuum.Space d)
    (hBC : ∀ᵐ ω ∂P, ∀ t, B t ω = C t ω)
    (κ ℓ : Ω → ℝ≥0) (hκℓ : κ =ᵐ[P] ℓ)
    (T : ℝ≥0) (G : ℝ → Continuum.Space d → ℝ) :
    aeClockPayoffs B P T G κ = aeClockPayoffs C P T G ℓ := by
  ext a
  constructor
  · rintro ⟨τ, hτ, hτT, hτκ, ha⟩
    refine ⟨τ, (ae_stopping_events_iff_of_indistinguishable B C hBC τ).mp hτ, hτT, ?_, ?_⟩
    · filter_upwards [hτκ, hκℓ] with ω hle heq
      simpa only [heq] using hle
    · rw [ha]
      apply integral_congr_ae
      filter_upwards [hBC] with ω hω
      rw [hω (τ ω)]
  · rintro ⟨τ, hτ, hτT, hτℓ, ha⟩
    refine ⟨τ, (ae_stopping_events_iff_of_indistinguishable B C hBC τ).mpr hτ, hτT, ?_, ?_⟩
    · filter_upwards [hτℓ, hκℓ] with ω hle heq
      rw [heq]
      exact hle
    · rw [ha]
      apply integral_congr_ae
      filter_upwards [hBC] with ω hω
      rw [hω (τ ω)]

/-- The completed-event cube-killed value of a process agrees with the raw
value of an indistinguishable, everywhere-continuous Brownian realization. -/
theorem sSup_aeCubeClockPayoffs_eq_of_indistinguishable
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} [NeZero d]
    (P : Measure Ω) [IsProbabilityMeasure P] (x : Continuum.Space d)
    (B C : ℝ≥0 → Ω → Continuum.Space d)
    (hBC : ∀ᵐ ω ∂P, ∀ t, B t ω = C t ω)
    (hC : Continuum.IsBrownian d x C P) (hm : ∀ t, Measurable (C t))
    (hc : ∀ ω, Continuous fun t => C t ω) (T : ℝ≥0)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) :
    sSup (aeClockPayoffs B P T G
      (fun ω => (min (LatticeProb.openExitTime B (openUnitCube x) ω) (T : ℝ≥0∞)).toNNReal)) =
      Continuum.brownianDiscountCube C P (fun s z => -G s z) T 1 x := by
  have hclock : (fun ω => (min (LatticeProb.openExitTime B (openUnitCube x) ω)
      (T : ℝ≥0∞)).toNNReal) =ᵐ[P]
      fun ω => (min (LatticeProb.openExitTime C (openUnitCube x) ω) (T : ℝ≥0∞)).toNNReal := by
    filter_upwards [hBC] with ω hω
    have hpath : (fun s => B s ω) = fun s => C s ω := funext hω
    have hexit : LatticeProb.openExitTime B (openUnitCube x) ω =
        LatticeProb.openExitTime C (openUnitCube x) ω := by
      exact congrArg (fun f : ℝ≥0 → Continuum.Space d =>
        LatticeProb.openExitTime (fun s (_ : Unit) => f s) (openUnitCube x) ()) hpath
    rw [hexit]
  rw [aeClockPayoffs_eq_of_indistinguishable B C hBC _ _ hclock T G]
  exact sSup_aeCubeClockPayoffs_eq_brownianDiscountCube P x C hC hm hc T G hGc M hG

end Sandpile.External.Stopping
