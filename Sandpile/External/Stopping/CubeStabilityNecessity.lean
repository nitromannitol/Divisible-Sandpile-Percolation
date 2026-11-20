import Sandpile.External.CubeStoppingStability

/-!
# Realization invariance required by cube stability

The uniform cube-stability statement entails equality of the cube-killed
Brownian values for any two admissible Brownian families.
-/

open MeasureTheory Set
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Cube stability forces equal cube-killed values for any two admissible
Brownian realizations at the same start and positive horizon. -/
theorem brownianDiscountCube_eq_of_cubeStoppingStability
    (h : Sandpile.External.CubeStoppingStability) (d : ℕ) (hd : 1 ≤ d)
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Ω') [IsProbabilityMeasure Q]
    (B : Continuum.Space d → ℝ≥0 → Ω → Continuum.Space d)
    (C : Continuum.Space d → ℝ≥0 → Ω' → Continuum.Space d)
    (hB : ∀ x, Continuum.IsBrownian d x (B x) P)
    (hC : ∀ x, Continuum.IsBrownian d x (C x) Q)
    (T : ℝ) (hT : 0 < T) (x : Continuum.Space d)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ t z, |G t z| ≤ M) :
    Continuum.brownianDiscountCube (B x) P (fun s z => -G s z) T 1 x =
      Continuum.brownianDiscountCube (C x) Q (fun s z => -G s z) T 1 x := by
  have hdist (ε : ℝ) (hε : 0 < ε) :
      |Continuum.brownianDiscountCube (B x) P (fun s z => -G s z) T 1 x -
        Continuum.brownianDiscountCube (C x) Q (fun s z => -G s z) T 1 x| ≤ ε := by
    let H : ℝ → ℝ → Continuum.Space d → ℝ := fun _ s z => G s z
    have happrox : ∀ η : ℝ, 0 < η → ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ R : ℝ, R₁ ≤ R →
        ∀ s ∈ Icc (0 : ℝ) T, ∀ z, |H R s z - G s z| ≤ η := by
      intro η hη
      refine ⟨1, zero_lt_one, ?_⟩
      intro R hR s hs z
      simpa only [H, sub_self, abs_zero] using hη.le
    obtain ⟨R₁, hR₁, h₁⟩ := h d hd Ω P B hB T T hT le_rfl {x} isCompact_singleton
      G hGc H M hG (fun R s z => hG s z) happrox (ε / 2) (by positivity)
    obtain ⟨R₂, hR₂, h₂⟩ := h d hd Ω' Q C hC T T hT le_rfl {x} isCompact_singleton
      G hGc H M hG (fun R s z => hG s z) happrox (ε / 2) (by positivity)
    let R := max R₁ R₂
    have hfirst := h₁ R (le_max_left _ _) T ⟨le_rfl, le_rfl⟩ x (mem_singleton x)
    have hsecond := h₂ R (le_max_right _ _) T ⟨le_rfl, le_rfl⟩ x (mem_singleton x)
    exact (abs_sub_le _ _ _).trans (by
      rw [abs_sub_comm (Continuum.brownianDiscountCube (B x) P (fun s z => -G s z) T 1 x)]
      linarith)
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    have h := (abs_le.mp (hdist ε hε)).2
    linarith
  · apply le_of_forall_pos_le_add
    intro ε hε
    have h := (abs_le.mp (hdist ε hε)).1
    linarith

end Sandpile.External.Stopping
