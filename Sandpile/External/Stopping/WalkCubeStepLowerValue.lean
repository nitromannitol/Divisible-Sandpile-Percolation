import Sandpile.External.Stopping.WalkCubeLowerValue
import Sandpile.External.Stopping.CubeClockStepPayoffs

/-!
# Lower cube bounds for killed step-walk payoffs

The clock-constrained lower comparison gives a bound by the lattice cube
killed step-walk payoff set.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- The continuous cube-killed value is asymptotically at most the killed
step-walk value with the corresponding starting-point translation. -/
theorem eventually_killed_step_value_ge_cube_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
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
    (T : ℝ≥0) (a : Continuum.Space d) (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ t z, |G t z| ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      sSup (clockPayoffs (fun t ω => Y ω t) P T (fun s z => G s (z + a))
        (fun ω => (min (LatticeProb.openExitTime (fun t ω => Y ω t) (openUnitCube 0) ω)
          (T : ℝ≥0∞)).toNNReal) (Continuum.brownianFiltration (fun t ω => Y ω t))) ≤
      sSup (killedStepTimePayoffs (R n) (supBox (q n) (R n)) (q n) T
        (fun s z => G s (z - Lclt.scaledSite (R n) (q n) + a))) + ε := by
  let H : ℝ → Continuum.Space d → ℝ := fun s z => G s (z + a)
  have hHc : Continuous (fun p : ℝ × Continuum.Space d => H p.1 p.2) :=
    hGc.comp (continuous_fst.prodMk (continuous_snd.add continuous_const))
  have hlower := eventually_walk_cube_value_ge_limit P R q hRpos hR W Y hWm hYm hWlaw
    hconv hclocks T H hHc M (fun s z => hG _ _) ε hε
  filter_upwards [hlower] with n hn
  have hsubset := clockPayoffs_subset_killedStepTimePayoffs (hRpos n)
    (supBox (q n) (R n)) ⌊R n ^ 2 * (T : ℝ)⌋₊ (q n) T
    (Lclt.scaledSite (R n) (q n)) H
  have hbd := bddAbove_killedStepTimePayoffs (R n) (supBox (q n) (R n)) (q n) T M
    (fun s z => H s (z - Lclt.scaledSite (R n) (q n))) (fun s z => hG _ _)
  have hne : (clockPayoffs
      (fun t X => diffusiveStepWalk (R n) t X - Lclt.scaledSite (R n) (q n))
      (walkLaw d (q n)) T H
      (walkStopToDiffusiveTime (R n) (hRpos n)
        (stopBeforeExit (supBox (q n) (R n)) ⌊R n ^ 2 * (T : ℝ)⌋₊
          (fun _ => ⌊R n ^ 2 * (T : ℝ)⌋₊)))
      (Continuum.brownianFiltration
        (fun t X => diffusiveStepWalk (R n) t X - Lclt.scaledSite (R n) (q n)))).Nonempty :=
    ⟨_, fun _ => 0, Continuum.isBrownianStopping_const _ 0, (fun _ => bot_le),
      Filter.Eventually.of_forall (fun _ => bot_le), rfl⟩
  have hle := csSup_le_csSup hbd hne hsubset
  change _ ≤ sSup (killedStepTimePayoffs (R n) (supBox (q n) (R n)) (q n) T
    (fun s z => G s (z - Lclt.scaledSite (R n) (q n) + a))) + ε
  dsimp only [H] at hle
  linarith

end Sandpile.External.Stopping
