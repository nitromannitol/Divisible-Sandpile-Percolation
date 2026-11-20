import Sandpile.External.Stopping.CubeGridRounding

/-!
# Cube-killed rounding with approximating rewards

Uniform convergence of bounded rewards can be combined with the cube-killed
grid rounding comparison, without assuming the approximating rewards are
continuous or measurable.
-/

open MeasureTheory Set
open scoped NNReal

namespace Sandpile.External.Stopping

/-- Uniformly approximating bounded rewards may replace the limiting reward
in the lattice cube-killed value, uniformly over compact starts and bounded
horizons. -/
theorem exists_large_scale_cube_grid_comparison_of_uniform_reward {d : ℕ} [NeZero d]
    (K : Set (Continuum.Space d)) (hK : IsCompact K) (T₁ M : ℝ)
    (G : ℝ → Continuum.Space d → ℝ)
    (hG : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (H : ℝ → ℝ → Continuum.Space d → ℝ)
    (hGbound : ∀ s z, |G s z| ≤ M) (hHbound : ∀ R s z, |H R s z| ≤ M)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ R₁ > 0, ∀ R ≥ R₁,
      ∀ s ∈ Icc (0 : ℝ) T₁, ∀ z, |H R s z - G s z| ≤ ε)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ > 0, ∀ R ≥ R₀, ∀ T ∈ Icc (0 : ℝ) T₁, ∀ x ∈ K,
      |sSup (killedStepTimePayoffs R (supBox (fun i => ⌊R * x i⌋) R)
          (fun i => ⌊R * x i⌋) T G) -
        killedStoppingSup (supBox (fun i => ⌊R * x i⌋) R) ⌊R ^ 2 * T⌋₊
          (fun i => ⌊R * x i⌋) (fun k X =>
            H R (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
              (Lclt.scaledSite R (X k)))| ≤ ε := by
  obtain ⟨R₁, hR₁, hround⟩ :=
    exists_large_scale_cube_grid_comparison K hK T₁ M G hG hGbound (half_pos hε)
  obtain ⟨R₂, hR₂, hclose⟩ := happrox (ε / 2) (half_pos hε)
  refine ⟨max R₁ R₂, hR₁.trans_le (le_max_left _ _), ?_⟩
  intro R hR T hT x hx
  have hR₁' : R₁ ≤ R := (le_max_left _ _).trans hR
  have hR₂' : R₂ ≤ R := (le_max_right _ _).trans hR
  have hRpos : 0 < R := hR₂.trans_le hR₂'
  let q : Site d := fun i => ⌊R * x i⌋
  let V := killedStoppingSup (supBox q R) ⌊R ^ 2 * T⌋₊ q (fun k X =>
    G (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2) (Lclt.scaledSite R (X k)))
  have h₁ : |sSup (killedStepTimePayoffs R (supBox q R) q T G) - V| ≤ ε / 2 :=
    hround R hR₁' T hT x hx
  have h₂ : |V - killedStoppingSup (supBox q R) ⌊R ^ 2 * T⌋₊ q (fun k X =>
      H R (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
        (Lclt.scaledSite R (X k)))| ≤ ε / 2 := by
    apply abs_killedGridReward_sub_le_of_uniform hRpos (supBox q R) q T M (ε / 2)
      hT.1 G (H R) hGbound (hHbound R)
    intro s hs z
    rw [abs_sub_comm]
    exact hclose R hR₂' s ⟨hs.1, hs.2.trans hT.2⟩ z
  exact (abs_sub_le _ _ _).trans (by linarith)

end Sandpile.External.Stopping
