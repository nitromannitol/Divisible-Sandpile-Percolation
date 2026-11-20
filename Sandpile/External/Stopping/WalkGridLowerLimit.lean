import Sandpile.External.Stopping.WalkLatticeLowerLimit
import Sandpile.External.Stopping.KilledGridReward

/-!
# Lower limit with grid-horizon rewards

The final lattice horizon differs from the continuous horizon by less than
one diffusive grid step. The temporal modulus therefore transfers the lower
value bound to the rounded-horizon reward.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal

namespace Sandpile.External.Stopping

/-- The lower lattice value bound also holds with the remaining time measured
from the rounded lattice horizon. -/
theorem eventually_grid_value_ge_limit_of_start_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} [NeZero d] (R : ℕ → ℝ) (q : ℕ → Site d)
    (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop)
    (W : ℕ → Ω → (ℕ → Site d)) (Y : Ω → C(ℝ≥0, Continuum.Space d))
    (hWm : ∀ n, Measurable (W n)) (hYm : Measurable Y)
    (hWlaw : ∀ n, P.map (W n) = walkLaw d (q n))
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => centeredWalkPath (R n) (q n) (W n ω)) atTop (𝓝 (Y ω)))
    (T : ℝ≥0) (a : Continuum.Space d)
    (hstart : Tendsto (fun n => Lclt.scaledSite (R n) (q n)) atTop (𝓝 a))
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (K : Set (Continuum.Space d)) (hK : IsCompact K)
    (hsupp : ∀ s z, z ∉ K → G s z = 0)
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, sSup (naturalStoppingPayoffs P (fun t ω => Y ω t) T
      (fun t z => G ((T : ℝ) - t) (z + a))) ≤
      stoppingSup ⌊R n ^ 2 * (T : ℝ)⌋₊ (q n) (fun k X =>
        G (((⌊R n ^ 2 * (T : ℝ)⌋₊ : ℕ) - (k : ℝ)) / R n ^ 2)
          (Lclt.scaledSite (R n) (X k))) + ε := by
  have hlower := eventually_lattice_value_ge_limit_of_start_tendsto P R q hRpos hR
    W Y hWm hYm hWlaw hconv T a hstart G hGc K hK hsupp M hG (ε / 2) (by positivity)
  obtain ⟨R₀, _, hmod⟩ := exists_large_scale_uniform_temporal_modulus_of_compact_support
    K hK (T : ℝ) G hGc hsupp (show 0 < ε / 2 by positivity)
  have hlarge : ∀ᶠ n in atTop, R₀ ≤ R n := hR.eventually (eventually_ge_atTop R₀)
  filter_upwards [hlower, hlarge] with n hn hRn
  have hgrid := abs_killedStoppingSup_sub_gridReward_le (hRpos n) Set.univ (q n)
    T M (ε / 2) T.property G hG (hmod (R n) hRn)
  rw [killedStoppingSup_univ, killedStoppingSup_univ] at hgrid
  have hupper := (abs_le.mp hgrid).2
  linarith

end Sandpile.External.Stopping
