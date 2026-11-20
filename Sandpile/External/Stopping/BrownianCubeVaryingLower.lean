import Sandpile.External.Stopping.BrownianCubeGridLowerValue
import Sandpile.External.Stopping.KilledVaryingHorizon
import Sandpile.External.Stopping.ValueHorizonContinuity

/-!
# Brownian cube lower bound at varying horizons

The lower bound for fixed horizons extends to converging positive horizons by
Brownian value continuity and the temporal modulus of the grid rewards.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal

namespace Sandpile.External.Stopping

/-- Along converging starts and positive horizons, the Brownian stopping value
is asymptotically no larger than the lattice grid-horizon value for a compactly
supported bounded continuous reward. -/
theorem eventually_killed_grid_value_ge_brownian_cube_of_tendsto_horizon
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
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, Continuum.brownianDiscountCube B PB (fun s z => -G s z) T 1 a ≤
      killedStoppingSup (supBox (q n) (R n)) ⌊R n ^ 2 * (Tn n : ℝ)⌋₊ (q n) (fun k X =>
        G (((⌊R n ^ 2 * (Tn n : ℝ)⌋₊ : ℕ) - (k : ℝ)) / R n ^ 2)
          (Lclt.scaledSite (R n) (X k))) + ε := by
  obtain ⟨δ, hδ, hmod⟩ := exists_uniform_temporal_modulus_of_compact_support
    K hK ((T : ℝ) + 1) G hGc hsupp (show 0 < ε / 3 by positivity)
  let S : ℕ → ℝ≥0 := fun n => Real.toNNReal ((T : ℝ) - 1 / ((n : ℝ) + 1))
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hSlim : Tendsto S atTop (𝓝 T) := by
    have hreal : Tendsto (fun n : ℕ => (T : ℝ) - 1 / ((n : ℝ) + 1))
        atTop (𝓝 (T : ℝ)) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub hinv
    have ht := (continuous_real_toNNReal.tendsto (T : ℝ)).comp hreal
    simpa only [Real.toNNReal_coe, Function.comp_def, S] using ht
  have hVlim := tendsto_brownianDiscountCube_of_tendsto_horizon PB a B hB T S hSlim G hGc M hG
  have hVclose := hVlim.eventually (Ioi_mem_nhds
    (show Continuum.brownianDiscountCube B PB (fun s z => -G s z) T 1 a - ε / 3 <
      Continuum.brownianDiscountCube B PB (fun s z => -G s z) T 1 a by linarith))
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast hT
  have hsmall := hinv.eventually (Iio_mem_nhds (lt_min hδ hTpos))
  obtain ⟨j, hj, hj'⟩ := (hVclose.and hsmall).exists
  have hjpos : 0 < 1 / ((j : ℝ) + 1) := by positivity
  have hSj : (S j : ℝ) = (T : ℝ) - 1 / ((j : ℝ) + 1) := by
    dsimp [S]
    rw [max_eq_left]
    have := (lt_min_iff.mp hj').2
    linarith
  have hST : S j < T := by
    apply NNReal.coe_lt_coe.mp
    rw [hSj]
    linarith
  have hgap : (T : ℝ) - S j < δ := by
    rw [hSj]
    have := (lt_min_iff.mp hj').1
    linarith
  have hlower := eventually_killed_grid_value_ge_brownian_cube_of_compact_support R q hRpos hR
    a hstart PB B hB (S j) G hGc K hK hsupp M hG (ε / 3) (by positivity)
  have hcompare := eventually_killed_grid_value_le_of_tendsto_horizon R q hRpos hR
    (fun n => supBox (q n) (R n)) (S j) T Tn hTn hST G M (ε / 3) hG δ hmod hgap
  filter_upwards [hlower, hcompare] with n hn hc
  linarith

end Sandpile.External.Stopping
