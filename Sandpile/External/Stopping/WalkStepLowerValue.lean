import Sandpile.External.Stopping.CoupledStepLowerValue
import Sandpile.External.Stopping.RightStoppingValueTransfer
import Sandpile.External.Stopping.StepWalkRightContinuous

/-!
# Lower stopping-value bound under the walk law

Transfer the lower bound for coupled walks to the original lattice path laws.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- The natural stopping value of the continuous limit is asymptotically no
greater than the centered step-walk value under the original walk laws. -/
theorem eventually_walk_step_value_ge_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} [NeZero d] (R : ℕ → ℝ) (q : ℕ → Site d)
    (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop)
    (W : ℕ → Ω → (ℕ → Site d)) (Y : Ω → C(ℝ≥0, Continuum.Space d))
    (hWm : ∀ n, Measurable (W n)) (hYm : Measurable Y)
    (hWlaw : ∀ n, P.map (W n) = walkLaw d (q n))
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => centeredWalkPath (R n) (q n) (W n ω)) atTop (𝓝 (Y ω)))
    (T : ℝ≥0) (G : ℝ≥0 → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ≥0 × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ t z, |G t z| ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, sSup (naturalStoppingPayoffs P (fun t ω => Y ω t) T G) ≤
      sSup (naturalStoppingPayoffs (walkLaw d (q n))
        (fun t X => diffusiveStepWalk (R n) t X - Lclt.scaledSite (R n) (q n)) T G) + ε := by
  obtain ⟨F, hF, hlower⟩ := eventually_coupled_step_value_ge_limit P R q hRpos hR
    W Y hWm hYm hWlaw hconv T G hGc M hG ε hε
  filter_upwards [hlower] with n hn
  let Z : ℝ≥0 → (ℕ → Site d) → Continuum.Space d := fun t X =>
    diffusiveStepWalk (R n) t X - Lclt.scaledSite (R n) (q n)
  have hZm : ∀ t, StronglyMeasurable (Z t) := fun t =>
    ((measurable_diffusiveStepWalk (R n) t).sub_const _).stronglyMeasurable
  have hZj : Measurable (fun p : ℝ≥0 × (ℕ → Site d) => Z p.1 p.2) :=
    (measurable_diffusiveStepWalk_uncurry (R n)).sub_const _
  have hZc : ∀ X t, ContinuousWithinAt (fun s => Z s X) (Set.Ici t) t := fun X t =>
    (continuousWithinAt_diffusiveStepWalk (R n) X t).sub continuousWithinAt_const
  let : IsProbabilityMeasure (walkLaw d (q n)) := walkLaw_isProbabilityMeasure d (q n)
  have htransfer := naturalStoppingValue_le_of_map P (walkLaw d (q n)) Z hZm hZj hZc
    (W n) (hWm n) (hWlaw n) T G hGc M hG
  have hpay : filtrationStoppingPayoffs (F n) P (fun t ω => Z t (W n ω)) T G =
      naturalStoppingPayoffs P (fun t ω => Z t (W n ω)) T G := by
    ext a
    constructor <;> rintro ⟨τ, hτ, hτT, rfl⟩ <;> refine ⟨τ, ?_, hτT, rfl⟩
    · intro t
      rw [← hF n t]
      exact hτ t
    · intro t
      rw [hF n t]
      exact hτ t
  rw [hpay] at hn
  exact hn.trans (by linarith)

end Sandpile.External.Stopping
