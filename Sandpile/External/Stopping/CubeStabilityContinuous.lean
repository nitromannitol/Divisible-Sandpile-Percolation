import Sandpile.External.Stopping.CubeStabilityFromCompleted
import Sandpile.External.Stopping.ApproximatedCubeValue

/-!
# Cube stability for continuous realizations

The killed optimal-stopping stability estimate holds for Brownian families
whose paths are continuous at every sample point.
-/

open MeasureTheory Set
open scoped NNReal ENNReal Topology

namespace Sandpile.External.Stopping

/-- Completing stopping events preserves the cube value when all paths are
continuous, without requiring measurable process sections. -/
theorem sSup_aeCubeClockPayoffs_eq_of_continuous
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} [NeZero d]
    (P : Measure Ω) [IsProbabilityMeasure P] (x : Continuum.Space d)
    (B : ℝ≥0 → Ω → Continuum.Space d) (hB : Continuum.IsBrownian d x B P)
    (hc : ∀ ω, Continuous fun t => B t ω) (T : ℝ≥0)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) :
    sSup (aeClockPayoffs B P T G
      (fun ω => (min (LatticeProb.openExitTime B (openUnitCube x) ω)
        (T : ℝ≥0∞)).toNNReal)) =
      Continuum.brownianDiscountCube B P (fun s z => -G s z) T 1 x := by
  let κ : Ω → ℝ≥0 := fun ω =>
    (min (LatticeProb.openExitTime B (openUnitCube x) ω) (T : ℝ≥0∞)).toNNReal
  have hκT (ω : Ω) : κ ω ≤ T := by
    apply ENNReal.coe_le_coe.mp
    rw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))]
    exact min_le_right _ _
  exact sSup_aeCubeClockPayoffs_eq_brownianDiscountCube_of_approximation P x B hB T G hGc M hG
    (fun _ => κ) (fun _ => isBrownianStopping_openUnitCubeExitTrunc B hc x T)
    (fun _ => hκT) (fun _ => Filter.Eventually.of_forall fun _ => le_rfl)
    (Filter.Eventually.of_forall fun _ => tendsto_const_nhds)

/-- Uniform cube-killed stopping stability for everywhere-continuous Brownian
families, under the same bounds and approximation conditions as the lattice
and Brownian values. -/
theorem exists_uniform_killed_grid_value_approx_brownian_cube_of_continuous
    {d : ℕ} [NeZero d] {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Continuum.Space d → ℝ≥0 → Ω → Continuum.Space d)
    (hB : ∀ x, Continuum.IsBrownian d x (B x) P)
    (hc : ∀ x ω, Continuous fun t => B x t ω)
    (T₀ T₁ : ℝ) (hT₀ : 0 < T₀) (hT : T₀ ≤ T₁)
    (K : Set (Continuum.Space d)) (hK : IsCompact K)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (G' : ℝ → ℝ → Continuum.Space d → ℝ) (M : ℝ)
    (hG : ∀ s z, |G s z| ≤ M) (hG' : ∀ R s z, |G' R s z| ≤ M)
    (happrox : ∀ ε > 0, ∃ R₁ > 0, ∀ R ≥ R₁,
      ∀ s ∈ Icc (0 : ℝ) T₁, ∀ z, |G' R s z - G s z| ≤ ε) :
    ∀ ε > 0, ∃ R₀ > 0, ∀ R ≥ R₀, ∀ T ∈ Icc T₀ T₁, ∀ x ∈ K,
      |killedStoppingSup (supBox (fun i => ⌊R * x i⌋) R) ⌊R ^ 2 * T⌋₊
        (fun i => ⌊R * x i⌋) (fun k X =>
          G' R (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
            (Lclt.scaledSite R (X k))) -
      Continuum.brownianDiscountCube (B x) P (fun s z => -G s z) T 1 x| ≤ ε := by
  intro ε hε
  obtain ⟨R₁, hR₁, hlower⟩ := exists_uniform_brownian_cube_le_killed_grid_value_real
    P B hB T₀ T₁ hT₀ hT K hK G hGc G' M hG hG' happrox ε hε
  have hT₁ : 0 ≤ T₁ := hT₀.le.trans hT
  obtain ⟨R₂, hR₂, hupper⟩ := exists_uniform_killed_grid_value_le_completed_cube
    P B hB (Real.toNNReal T₀) (Real.toNNReal T₁) K hK G hGc G' M hG hG'
      (by simpa only [Real.coe_toNNReal _ hT₁] using happrox) ε hε
  refine ⟨max R₁ R₂, lt_of_lt_of_le hR₁ (le_max_left _ _), ?_⟩
  intro R hR T hTK x hxK
  have hTpos : 0 ≤ T := hT₀.le.trans hTK.1
  have hTmem : Real.toNNReal T ∈ Icc (Real.toNNReal T₀) (Real.toNNReal T₁) :=
    ⟨Real.toNNReal_le_toNNReal hTK.1, Real.toNNReal_le_toNNReal hTK.2⟩
  have hl := hlower R ((le_max_left _ _).trans hR) T hTK x hxK
  have hu := hupper R ((le_max_right _ _).trans hR) (Real.toNNReal T) hTmem x hxK
  rw [sSup_aeCubeClockPayoffs_eq_of_continuous P x (B x) (hB x) (hc x)
    (Real.toNNReal T) G hGc M hG] at hu
  simp only [Real.coe_toNNReal _ hTpos] at hu
  rw [abs_le]
  constructor <;> linarith

end Sandpile.External.Stopping
