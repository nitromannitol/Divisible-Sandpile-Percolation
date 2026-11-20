import Sandpile.External.Stopping.CoupledKilledStepLowerValue
import Sandpile.External.Stopping.TruncatedDiffusiveExitLimit

/-!
# Lower cube-stopping bounds for coupled walks

The lattice cube-exit clocks supplied by the stopped-walk coupling satisfy the
hypotheses of the lower killed stopping-value comparison.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Coupled step walks have asymptotic cube-killed values at least as large as
the cube-killed value of their continuous limit. -/
theorem eventually_coupled_cube_value_ge_limit
    {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} [NeZero d] (R : ℕ → ℝ) (q : ℕ → Site d)
    (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop)
    (W : ℕ → Ω → (ℕ → Site d)) (Y : Ω → C(ℝ≥0, Continuum.Space d))
    (hWm : ∀ n, Measurable (W n)) (hYm : Measurable Y)
    (hWlaw : ∀ n, P.map (W n) = walkLaw d (q n))
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => centeredWalkPath (R n) (q n) (W n ω)) atTop (𝓝 (Y ω)))
    (hclocks : ∀ᵐ ω ∂P,
      let τ := LatticeProb.openExitTime (fun t ω => Y ω t) (openUnitCube 0) ω
      τ ≠ ⊤ ∧ (∀ n, Sandpile.exitTime (supBox (q n) (R n)) (W n ω) ≠ ⊤) ∧
      Tendsto (fun n => LatticeProb.ConstantStepInterpolation.knot
        ⟨(R n) ^ 2, sq_nonneg (R n)⟩
        (Sandpile.exitTime (supBox (q n) (R n)) (W n ω)).toNat) atTop (𝓝 τ.toNNReal))
    (T : ℝ≥0) (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ t z, |G t z| ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : ℕ → Filtration ℝ≥0 m,
      (∀ n t, F n t = Continuum.brownianFiltration
        (fun s ω => diffusiveStepWalk (R n) s (W n ω) - Lclt.scaledSite (R n) (q n)) t) ∧
      ∀ᶠ n in atTop,
        sSup (clockPayoffs (fun t ω => Y ω t) P T G
          (fun ω => (min (LatticeProb.openExitTime (fun t ω => Y ω t) (openUnitCube 0) ω)
            (T : ℝ≥0∞)).toNNReal) (Continuum.brownianFiltration (fun t ω => Y ω t))) ≤
        sSup (adaptedClockPayoffs (F n) P
          (fun t ω => diffusiveStepWalk (R n) t (W n ω) - Lclt.scaledSite (R n) (q n)) T G
          (fun ω => walkStopToDiffusiveTime (R n) (hRpos n)
            (stopBeforeExit (supBox (q n) (R n)) ⌊R n ^ 2 * (T : ℝ)⌋₊
              (fun _ => ⌊R n ^ 2 * (T : ℝ)⌋₊)) (W n ω))) + ε := by
  let κn : ℕ → (ℕ → Site d) → ℝ≥0 := fun n =>
    walkStopToDiffusiveTime (R n) (hRpos n)
      (stopBeforeExit (supBox (q n) (R n)) ⌊R n ^ 2 * (T : ℝ)⌋₊
        (fun _ => ⌊R n ^ 2 * (T : ℝ)⌋₊))
  have hκn : ∀ n, Continuum.IsBrownianStopping (diffusiveStepWalk (R n)) (κn n) :=
    fun n => isBrownianStopping_diffusiveExit (hRpos n) _ _
  have hκlim : ∀ᵐ ω ∂P, Tendsto (fun n => κn n (W n ω)) atTop
      (𝓝 ((min (LatticeProb.openExitTime (fun t ω => Y ω t) (openUnitCube 0) ω)
        (T : ℝ≥0∞)).toNNReal)) := by
    filter_upwards [hclocks] with ω hω
    dsimp only at hω
    have h := tendsto_truncated_diffusive_exit R hRpos hR
      (fun n => supBox (q n) (R n)) (fun n => W n ω) T _ hω.2.1 hω.2.2
    have heq : (min (LatticeProb.openExitTime (fun t ω => Y ω t) (openUnitCube 0) ω)
        (T : ℝ≥0∞)).toNNReal =
        min (LatticeProb.openExitTime (fun t ω => Y ω t) (openUnitCube 0) ω).toNNReal T := by
      rw [← ENNReal.coe_toNNReal hω.1, ← ENNReal.coe_min, ENNReal.toNNReal_coe]
      simp only [ENNReal.toNNReal_coe]
    rw [heq]
    exact h
  exact eventually_coupled_killed_step_value_ge_limit P R q hRpos hR W Y hWm hYm hWlaw
    hconv T κn hκn hκlim G hGc M hG ε hε

end Sandpile.External.Stopping
