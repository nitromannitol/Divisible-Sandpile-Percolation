import Sandpile.External.Stopping.CoupledCubeLowerValue
import Sandpile.External.Stopping.RightKilledValueTransfer
import Sandpile.External.Stopping.StepWalkRightContinuous

/-!
# Lower cube-stopping bounds under walk laws

The lower comparison for coupled walks transfers to the original lattice path
laws without changing the killing clocks.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- The cube-killed value of the continuous limit is asymptotically at most
the corresponding centered step-walk value under the original walk laws. -/
theorem eventually_walk_cube_value_ge_limit
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
    (T : ℝ≥0) (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ t z, |G t z| ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      sSup (clockPayoffs (fun t ω => Y ω t) P T G
        (fun ω => (min (LatticeProb.openExitTime (fun t ω => Y ω t) (openUnitCube 0) ω)
          (T : ℝ≥0∞)).toNNReal) (Continuum.brownianFiltration (fun t ω => Y ω t))) ≤
      sSup (clockPayoffs
        (fun t X => diffusiveStepWalk (R n) t X - Lclt.scaledSite (R n) (q n))
        (walkLaw d (q n)) T G
        (walkStopToDiffusiveTime (R n) (hRpos n)
          (stopBeforeExit (supBox (q n) (R n)) ⌊R n ^ 2 * (T : ℝ)⌋₊
            (fun _ => ⌊R n ^ 2 * (T : ℝ)⌋₊)))
        (Continuum.brownianFiltration
          (fun t X => diffusiveStepWalk (R n) t X - Lclt.scaledSite (R n) (q n)))) + ε := by
  obtain ⟨F, hF, hlower⟩ := eventually_coupled_cube_value_ge_limit P R q hRpos hR
    W Y hWm hYm hWlaw hconv hclocks T G hGc M hG ε hε
  filter_upwards [hlower] with n hn
  let Z : ℝ≥0 → (ℕ → Site d) → Continuum.Space d := fun t X =>
    diffusiveStepWalk (R n) t X - Lclt.scaledSite (R n) (q n)
  let κ := walkStopToDiffusiveTime (R n) (hRpos n)
    (stopBeforeExit (supBox (q n) (R n)) ⌊R n ^ 2 * (T : ℝ)⌋₊
      (fun _ => ⌊R n ^ 2 * (T : ℝ)⌋₊))
  have hZm : ∀ t, StronglyMeasurable (Z t) := fun t =>
    ((measurable_diffusiveStepWalk (R n) t).sub_const _).stronglyMeasurable
  have hZj : Measurable (fun p : ℝ≥0 × (ℕ → Site d) => Z p.1 p.2) :=
    (measurable_diffusiveStepWalk_uncurry (R n)).sub_const _
  have hZc : ∀ X t, ContinuousWithinAt (fun s => Z s X) (Set.Ici t) t := fun X t =>
    (continuousWithinAt_diffusiveStepWalk (R n) X t).sub continuousWithinAt_const
  have hκ : Continuum.IsBrownianStopping Z κ :=
    (isBrownianStopping_sub_const_iff (diffusiveStepWalk (R n)) _ κ).2
      (isBrownianStopping_diffusiveExit (hRpos n) _ _)
  let : IsProbabilityMeasure (walkLaw d (q n)) := walkLaw_isProbabilityMeasure d (q n)
  have htransfer := clockStoppingValue_le_of_map P (walkLaw d (q n)) Z hZm hZj hZc
    (W n) (hWm n) (hWlaw n) T κ hκ G hGc M hG
  have hpay : adaptedClockPayoffs (F n) P (fun t ω => Z t (W n ω)) T G (fun ω => κ (W n ω)) =
      clockPayoffs (fun t ω => Z t (W n ω)) P T G (fun ω => κ (W n ω))
        (Continuum.brownianFiltration (fun t ω => Z t (W n ω))) := by
    ext a
    constructor <;> rintro ⟨τ, hτ, hτT, hτκ, rfl⟩ <;> refine ⟨τ, ?_, hτT, hτκ, rfl⟩
    · intro t
      rw [← hF n t]
      exact hτ t
    · intro t
      rw [hF n t]
      exact hτ t
  rw [hpay] at hn
  exact hn.trans (by linarith)

end Sandpile.External.Stopping
