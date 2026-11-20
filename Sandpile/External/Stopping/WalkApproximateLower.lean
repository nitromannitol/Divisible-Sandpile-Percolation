import Sandpile.External.Stopping.WalkBrownianVaryingLower
import Sandpile.External.Stopping.KilledRewardApproximation

/-!
# Lower bounds for uniformly approximating rewards

Uniform reward approximation preserves the Brownian lower bound for lattice
stopping values at varying horizons.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal

namespace Sandpile.External.Stopping

/-- Uniformly approximating bounded rewards have the same lower Brownian value
bound along converging starts and positive horizons. -/
theorem eventually_approx_grid_value_ge_brownian_of_tendsto_horizon
    {d : ℕ} [NeZero d] (R : ℕ → ℝ) (q : ℕ → Site d)
    (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop)
    (a : Continuum.Space d)
    (hstart : Tendsto (fun n => Lclt.scaledSite (R n) (q n)) atTop (𝓝 a))
    {ΩB : Type*} [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → ΩB → Continuum.Space d) (hB : Continuum.IsBrownian d a B PB)
    (T : ℝ≥0) (hT : 0 < T) (Tn : ℕ → ℝ≥0) (hTn : Tendsto Tn atTop (𝓝 T))
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (K : Set (Continuum.Space d)) (hK : IsCompact K)
    (hsupp : ∀ s z, z ∉ K → G s z = 0)
    (H : ℕ → ℝ → Continuum.Space d → ℝ) (M : ℝ)
    (hG : ∀ s z, |G s z| ≤ M) (hH : ∀ n s z, |H n s z| ≤ M)
    (happrox : ∀ ε > 0, ∀ᶠ n in atTop, ∀ s ∈ Icc (0 : ℝ) ((T : ℝ) + 1),
      ∀ z, |G s z - H n s z| ≤ ε)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, Continuum.brownianDiscount B PB (fun s z => -G s z) T ≤
      stoppingSup ⌊R n ^ 2 * (Tn n : ℝ)⌋₊ (q n) (fun k X =>
        H n (((⌊R n ^ 2 * (Tn n : ℝ)⌋₊ : ℕ) - (k : ℝ)) / R n ^ 2)
          (Lclt.scaledSite (R n) (X k))) + ε := by
  have hlower := eventually_grid_value_ge_brownian_of_tendsto_horizon
    R q hRpos hR a hstart PB B hB T hT Tn hTn G hGc K hK hsupp M hG
    (ε / 2) (by positivity)
  have hbound : ∀ᶠ n in atTop, (Tn n : ℝ) ≤ (T : ℝ) + 1 := by
    have ht : Tendsto (fun n => (Tn n : ℝ)) atTop (𝓝 (T : ℝ)) :=
      NNReal.continuous_coe.continuousAt.tendsto.comp hTn
    exact (ht.eventually (Iio_mem_nhds (show (T : ℝ) < T + 1 by linarith))).mono
      fun _ h => h.le
  filter_upwards [hlower, hbound, happrox (ε / 2) (by positivity)] with n hn hb ha
  have hc := abs_killedGridReward_sub_le_of_uniform (hRpos n) Set.univ (q n)
    (Tn n : ℝ) M (ε / 2) (Tn n).property G (H n) hG (hH n)
    (fun s hs z => ha s ⟨hs.1, hs.2.trans hb⟩ z)
  rw [killedStoppingSup_univ, killedStoppingSup_univ] at hc
  linarith [(abs_le.mp hc).2]

end Sandpile.External.Stopping
