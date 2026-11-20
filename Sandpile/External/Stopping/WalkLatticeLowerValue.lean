import Sandpile.External.Stopping.WalkStepLowerValue
import Sandpile.External.Stopping.WalkStepValueRounding
import Sandpile.External.Stopping.CompactRewardModulus

/-!
# Lower bound for lattice stopping values

The lower value inequality of Coquet and Toldo, Section 2.2, combines with
rounding of the diffusive walk to compare a continuous limit with lattice
stopping values. A spatial translation aligns the centered walk with a fixed
starting point.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal

namespace Sandpile.External.Stopping

/-- For a compactly supported reward, the lower value inequality transfers to
lattice stopping values with the starting point aligned by translation. -/
theorem eventually_lattice_value_ge_limit_of_compact_support
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} [NeZero d] (R : ℕ → ℝ) (q : ℕ → Site d)
    (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop)
    (W : ℕ → Ω → (ℕ → Site d)) (Y : Ω → C(ℝ≥0, Continuum.Space d))
    (hWm : ∀ n, Measurable (W n)) (hYm : Measurable Y)
    (hWlaw : ∀ n, P.map (W n) = walkLaw d (q n))
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => centeredWalkPath (R n) (q n) (W n ω)) atTop (𝓝 (Y ω)))
    (T : ℝ≥0) (a : Continuum.Space d) (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (K : Set (Continuum.Space d)) (hK : IsCompact K)
    (hsupp : ∀ s z, z ∉ K → G s z = 0)
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, sSup (naturalStoppingPayoffs P (fun t ω => Y ω t) T
      (fun t z => G ((T : ℝ) - t) (z + a))) ≤
      stoppingSup ⌊R n ^ 2 * (T : ℝ)⌋₊ (q n) (fun k X =>
        G ((T : ℝ) - (k : ℝ) / R n ^ 2)
          (Lclt.scaledSite (R n) (X k) + (a - Lclt.scaledSite (R n) (q n)))) + ε := by
  let H : ℝ≥0 → Continuum.Space d → ℝ := fun t z => G ((T : ℝ) - t) (z + a)
  have hHc : Continuous (fun p : ℝ≥0 × Continuum.Space d => H p.1 p.2) :=
    hGc.comp (((continuous_const : Continuous (fun _ : ℝ≥0 × Continuum.Space d => (T : ℝ))).sub
      (NNReal.continuous_coe.comp continuous_fst)).prodMk (continuous_snd.add continuous_const))
  have hlower := eventually_walk_step_value_ge_limit P R q hRpos hR W Y hWm hYm hWlaw hconv
    T H hHc M (fun t z => hG _ _) (ε / 2) (by positivity)
  obtain ⟨R₀, _, hmod⟩ := exists_large_scale_uniform_temporal_modulus_of_compact_support
    K hK (T : ℝ) G hGc hsupp (show 0 < ε / 2 by positivity)
  have hlarge : ∀ᶠ n in atTop, R₀ ≤ R n := hR.eventually (eventually_ge_atTop R₀)
  filter_upwards [hlower, hlarge] with n hn hRn
  let J : ℝ → Continuum.Space d → ℝ := fun s z =>
    G s (z + (a - Lclt.scaledSite (R n) (q n)))
  have hJc : Continuous (fun p : ℝ × Continuum.Space d => J p.1 p.2) :=
    hGc.comp (continuous_fst.prodMk (continuous_snd.add continuous_const))
  have hround := abs_centeredStepValue_sub_stoppingSup_le (hRpos n) (q n) T M (ε / 2)
    (by positivity) J hJc.measurable (fun s z => hG _ _)
    (fun s hs u hu z hz => hmod (R n) hRn s hs u hu _ hz)
  have heq : (fun (t : ℝ≥0) z => J ((T : ℝ) - t)
      (z + Lclt.scaledSite (R n) (q n))) = H := by
    funext t z
    simp only [J, H]
    congr 1
    abel
  rw [heq] at hround
  have hb := (abs_le.mp hround).2
  change sSup (naturalStoppingPayoffs P (fun t ω => Y ω t) T H) ≤ _ at hn ⊢
  linarith

end Sandpile.External.Stopping
