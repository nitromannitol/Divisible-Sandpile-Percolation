import Sandpile.External.Stopping.VaryingFloorTime
import Sandpile.External.Stopping.LatticeHorizonComparison

/-!
# Lattice values at converging horizons

The temporal modulus of a spatially localized reward compares lattice values
at nearby horizons along diffusive scales.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal

namespace Sandpile.External.Stopping

/-- Along converging horizons, a fixed smaller horizon gives an asymptotic
lower bound for the grid value, up to a temporal reward error. -/
theorem eventually_grid_value_le_of_tendsto_horizon
    {d : ℕ} [NeZero d] (R : ℕ → ℝ) (q : ℕ → Site d)
    (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop)
    (S T : ℝ≥0) (Tn : ℕ → ℝ≥0) (hTn : Tendsto Tn atTop (𝓝 T))
    (hST : S < T) (G : ℝ → Continuum.Space d → ℝ)
    (M ε : ℝ) (hG : ∀ s z, |G s z| ≤ M) (δ : ℝ)
    (hmod : ∀ s ∈ Icc (0 : ℝ) ((T : ℝ) + 1),
      ∀ u ∈ Icc (0 : ℝ) ((T : ℝ) + 1), ∀ z,
        |s - u| < δ → |G s z - G u z| ≤ ε)
    (hgap : (T : ℝ) - S < δ) :
    ∀ᶠ n in atTop,
      stoppingSup ⌊R n ^ 2 * (S : ℝ)⌋₊ (q n) (fun k X =>
        G (((⌊R n ^ 2 * (S : ℝ)⌋₊ : ℕ) - (k : ℝ)) / R n ^ 2)
          (Lclt.scaledSite (R n) (X k))) ≤
      stoppingSup ⌊R n ^ 2 * (Tn n : ℝ)⌋₊ (q n) (fun k X =>
        G (((⌊R n ^ 2 * (Tn n : ℝ)⌋₊ : ℕ) - (k : ℝ)) / R n ^ 2)
          (Lclt.scaledSite (R n) (X k))) + ε := by
  have hTc : Tendsto (fun n => (Tn n : ℝ)) atTop (𝓝 (T : ℝ)) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp hTn
  have hrounded := tendsto_varying_floor_time_div_sq R (fun n => (Tn n : ℝ)) hR
    (fun n => (Tn n).property) hTc
  have hfixed := tendsto_varying_floor_time_div_sq R (fun _ => (S : ℝ)) hR
    (fun _ => S.property) tendsto_const_nhds
  have hdiff := hrounded.sub hfixed
  have hsmall := hdiff.eventually (Iio_mem_nhds hgap)
  have hbound := hrounded.eventually (Iio_mem_nhds (show (T : ℝ) < T + 1 by linarith))
  have horder := hTn.eventually (Ioi_mem_nhds hST)
  filter_upwards [hsmall, hbound, horder] with n hn hb ho
  have hmn : ⌊R n ^ 2 * (S : ℝ)⌋₊ ≤ ⌊R n ^ 2 * (Tn n : ℝ)⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left (by exact_mod_cast ho.le) (sq_nonneg _))
  apply gridReward_le_of_horizon (hRpos n) hmn (q n) G M ε hG
  intro s hs u hu z hsu
  apply hmod s ⟨hs.1, hs.2.trans hb.le⟩ u ⟨hu.1, hu.2.trans hb.le⟩ z
  apply lt_of_le_of_lt hsu
  simpa only [sub_div] using hn

end Sandpile.External.Stopping
