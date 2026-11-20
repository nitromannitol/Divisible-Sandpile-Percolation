import Sandpile.External.ContStoppingStability
import Sandpile.External.Stopping.WalkUniformUpper

/-!
# Continuum stopping stability

The bounded-reward optimal-stopping stability statement follows from the
uniform lower and upper bounds for diffusively rescaled lattice walks. The
upper bound uses the joint path-clock compactness and causal randomized-stop
argument of Coquet and Toldo, Section 2.3.1.
-/

open MeasureTheory Set

universe u

namespace Sandpile.External

/-- The continuum stopping stability input holds for Brownian motion in every
positive dimension. -/
theorem continuumStoppingStability_holds : ContinuumStoppingStability.{u} := by
  intro d hd ΩB mΩB PB hPB B hB T₀ T₁ hT₀ hT K hK G hGc G' M hG hG' happrox ε hε
  let : NeZero d := ⟨by omega⟩
  obtain ⟨R₁, hR₁, hlower⟩ := Stopping.exists_uniform_brownian_le_grid_value_real
    PB B hB T₀ T₁ hT₀ hT K hK G hGc G' M hG hG' happrox ε hε
  obtain ⟨R₂, hR₂, hupper⟩ := Stopping.exists_uniform_grid_value_le_brownian_real
    PB B hB T₀ T₁ hT₀ hT K hK G hGc G' M hG hG' happrox ε hε
  refine ⟨max R₁ R₂, lt_of_lt_of_le hR₁ (le_max_left _ _), ?_⟩
  intro R hR T hTK x hxK
  have hl := hlower R ((le_max_left _ _).trans hR) T hTK x hxK
  have hu := hupper R ((le_max_right _ _).trans hR) T hTK x hxK
  rw [abs_le]
  constructor <;> linarith

end Sandpile.External
