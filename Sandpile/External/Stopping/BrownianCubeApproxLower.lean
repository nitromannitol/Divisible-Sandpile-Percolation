import Sandpile.External.Stopping.BrownianCubeGeneralLower
import Sandpile.External.Stopping.KilledRewardApproximation

/-!
# Cube lower bounds for uniformly approximating rewards

Uniform reward approximation preserves the Brownian lower bound for lattice
stopping values at varying horizons.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal

namespace Sandpile.External.Stopping

/-- Uniformly approximating bounded rewards have the same lower Brownian value
bound along converging starts and positive horizons. -/
theorem eventually_approx_killed_grid_value_ge_brownian_cube_of_tendsto_horizon
    {d : ℕ} [NeZero d] (R : ℕ → ℝ) (q : ℕ → Site d)
    (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop)
    (a : Continuum.Space d)
    (hstart : Tendsto (fun n => Lclt.scaledSite (R n) (q n)) atTop (𝓝 a))
    {ΩB : Type*} [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → ΩB → Continuum.Space d) (hB : Continuum.IsBrownian d a B PB)
    (T : ℝ≥0) (hT : 0 < T) (Tn : ℕ → ℝ≥0) (hTn : Tendsto Tn atTop (𝓝 T))
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (H : ℕ → ℝ → Continuum.Space d → ℝ) (M : ℝ)
    (hG : ∀ s z, |G s z| ≤ M) (hH : ∀ n s z, |H n s z| ≤ M)
    (happrox : ∀ ε > 0, ∀ᶠ n in atTop, ∀ s ∈ Icc (0 : ℝ) (Tn n : ℝ),
      ∀ z, |G s z - H n s z| ≤ ε)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, Continuum.brownianDiscountCube B PB (fun s z => -G s z) T 1 a ≤
      killedStoppingSup (supBox (q n) (R n)) ⌊R n ^ 2 * (Tn n : ℝ)⌋₊ (q n) (fun k X =>
        H n (((⌊R n ^ 2 * (Tn n : ℝ)⌋₊ : ℕ) - (k : ℝ)) / R n ^ 2)
          (Lclt.scaledSite (R n) (X k))) + ε := by
  have hlower := eventually_killed_grid_value_ge_brownian_cube_of_bounded_reward
    R q hRpos hR a hstart PB B hB T hT Tn hTn G hGc M hG
    (ε / 2) (by positivity)
  filter_upwards [hlower, happrox (ε / 2) (by positivity)] with n hn ha
  have hc := abs_killedGridReward_sub_le_of_uniform (hRpos n) (supBox (q n) (R n)) (q n)
    (Tn n : ℝ) M (ε / 2) (Tn n).property G (H n) hG (hH n)
    (fun s hs z => ha s hs z)
  linarith [(abs_le.mp hc).2]

end Sandpile.External.Stopping
