import Sandpile.External.Stopping.BrownianCubeExit
import Sandpile.External.Stopping.RegularExitTime

/-!
# Brownian cube exit times

The first exit from an open cube is finite and regular. In particular, the
Brownian path crosses strictly outside the corresponding closed cube before
any time later than the exit. This supplies the boundary regularity used in
continuous-path convergence at a cube exit.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- The first exit of a finite Brownian coordinate family from a centered open
cube is finite, and it crosses the closed cube immediately after the exit. -/
theorem ae_brownian_cube_openExitTime_regular {ι Ω : Type*} [Finite ι] [Nonempty ι]
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : ι → ℝ≥0 → Ω → ℝ) (a : ℝ)
    (hB : ∀ i, IsBrownianReal (B i) P)
    (hm : ∀ i t, Measurable (B i t))
    (hc : ∀ i ω, Continuous fun t => B i t ω) :
    ∀ᵐ ω ∂P,
      let X : ℝ≥0 → Ω → (ι → ℝ) := fun t ω i => B i t ω
      let U : Set (ι → ℝ) := {z | ∀ i, |z i| < a}
      let τ := LatticeProb.openExitTime X U ω
      τ ≠ ⊤ ∧
        (∀ s : ℝ≥0, s < τ.toNNReal → ∀ i, |B i s ω| < a) ∧
        (∀ t : ℝ≥0, τ.toNNReal < t → ∃ s : ℝ≥0, s < t ∧ ∃ i, a < |B i s ω|) := by
  filter_upwards [ae_brownian_cube_regular B a hB hm hc] with ω hω
  obtain ⟨σ, hbefore, hafter⟩ := hω
  let X : ℝ≥0 → Ω → (ι → ℝ) := fun t ω i => B i t ω
  let U : Set (ι → ℝ) := {z | ∀ i, |z i| < a}
  have heq : LatticeProb.openExitTime X U ω = (σ : ℝ≥0∞) := by
    apply openExitTime_eq_of_regular X U ω σ
    · exact hbefore
    · intro t ht
      obtain ⟨s, hs, i, hi⟩ := hafter t ht
      exact ⟨s, hs, fun h => (not_lt_of_ge (h i).le) hi⟩
  change LatticeProb.openExitTime X U ω ≠ ⊤ ∧ _
  rw [heq]
  refine ⟨ENNReal.coe_ne_top, ?_, ?_⟩
  · simpa only [ENNReal.toNNReal_coe] using hbefore
  · simpa only [ENNReal.toNNReal_coe] using hafter

end Sandpile.External.Stopping
