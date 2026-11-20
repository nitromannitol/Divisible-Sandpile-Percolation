import Sandpile.External.CubeStoppingStability
import Sandpile.External.Stopping.CubeUniformUpperCompleted

/-!
# Cube stability from completion of stopping events

The uniform lower and upper estimates imply cube stopping stability once
completed-event and raw Brownian cube values are identified.
-/

open MeasureTheory Set
open scoped NNReal ENNReal

namespace Sandpile.External

/-- Equality of completed and raw Brownian cube values supplies the remaining
identification needed for cube stopping stability. -/
theorem cubeStoppingStability_of_completed_value_eq
    (heq : ∀ (d : ℕ) [NeZero d] (Ω : Type) [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (x : Continuum.Space d)
      (B : ℝ≥0 → Ω → Continuum.Space d), Continuum.IsBrownian d x B P →
      ∀ (T : ℝ≥0) (G : ℝ → Continuum.Space d → ℝ),
      Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2) →
      ∀ M : ℝ, (∀ s z, |G s z| ≤ M) →
      sSup (Stopping.aeClockPayoffs B P T G
        (fun ω => (min (LatticeProb.openExitTime B (Stopping.openUnitCube x) ω)
          (T : ℝ≥0∞)).toNNReal)) =
      Continuum.brownianDiscountCube B P (fun s z => -G s z) T 1 x) :
    CubeStoppingStability := by
  intro d hd Ω mΩ P hP B hB T₀ T₁ hT₀ hT K hK G hGc G' M hG hG' happrox ε hε
  let : NeZero d := ⟨by omega⟩
  obtain ⟨R₁, hR₁, hlower⟩ := Stopping.exists_uniform_brownian_cube_le_killed_grid_value_real
    P B hB T₀ T₁ hT₀ hT K hK G hGc G' M hG hG' happrox ε hε
  have hT₁ : 0 ≤ T₁ := hT₀.le.trans hT
  obtain ⟨R₂, hR₂, hupper⟩ := Stopping.exists_uniform_killed_grid_value_le_completed_cube
    P B hB (Real.toNNReal T₀) (Real.toNNReal T₁) K hK G hGc G' M hG hG'
      (by simpa only [Real.coe_toNNReal _ hT₁] using happrox) ε hε
  refine ⟨max R₁ R₂, lt_of_lt_of_le hR₁ (le_max_left _ _), ?_⟩
  intro R hR T hTK x hxK
  have hTpos : 0 ≤ T := hT₀.le.trans hTK.1
  have hTmem : Real.toNNReal T ∈ Icc (Real.toNNReal T₀) (Real.toNNReal T₁) :=
    ⟨Real.toNNReal_le_toNNReal hTK.1, Real.toNNReal_le_toNNReal hTK.2⟩
  have hl := hlower R ((le_max_left _ _).trans hR) T hTK x hxK
  have hu := hupper R ((le_max_right _ _).trans hR) (Real.toNNReal T) hTmem x hxK
  rw [heq d Ω P x (B x) (hB x) (Real.toNNReal T) G hGc M hG] at hu
  simp only [Real.coe_toNNReal _ hTpos] at hu
  rw [abs_le]
  constructor <;> linarith

end Sandpile.External
