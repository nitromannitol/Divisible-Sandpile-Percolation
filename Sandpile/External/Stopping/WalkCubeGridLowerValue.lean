import Sandpile.External.Stopping.WalkCubeStepLowerValue
import Sandpile.External.Stopping.CompactRewardTranslation

/-!
# Lower cube bounds for lattice grid rewards

Spatial continuity removes the starting-point translation, and the temporal
modulus transfers the step-walk comparison to the lattice grid reward.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- For a compactly supported reward, the continuous cube-killed value is
asymptotically at most the cube-killed lattice value at convergent starts. -/
theorem eventually_killed_grid_value_ge_cube_limit_of_compact_support
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
    (T : ℝ≥0) (a : Continuum.Space d)
    (hstart : Tendsto (fun n => Lclt.scaledSite (R n) (q n)) atTop (𝓝 a))
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (K : Set (Continuum.Space d)) (hK : IsCompact K)
    (hsupp : ∀ s z, z ∉ K → G s z = 0)
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      sSup (clockPayoffs (fun t ω => Y ω t) P T (fun s z => G s (z + a))
        (fun ω => (min (LatticeProb.openExitTime (fun t ω => Y ω t) (openUnitCube 0) ω)
          (T : ℝ≥0∞)).toNNReal) (Continuum.brownianFiltration (fun t ω => Y ω t))) ≤
      killedStoppingSup (supBox (q n) (R n)) ⌊R n ^ 2 * (T : ℝ)⌋₊ (q n)
        (fun k X => G (((⌊R n ^ 2 * (T : ℝ)⌋₊ : ℕ) - (k : ℝ)) / R n ^ 2)
          (Lclt.scaledSite (R n) (X k))) + ε := by
  have hlower := eventually_killed_step_value_ge_cube_limit P R q hRpos hR W Y hWm hYm hWlaw
    hconv hclocks T a G hGc M hG (ε / 2) (by positivity)
  obtain ⟨R₀, _, hmod⟩ := exists_large_scale_uniform_temporal_modulus_of_compact_support
    K hK (T : ℝ) G hGc hsupp (show 0 < ε / 8 by positivity)
  obtain ⟨δ, hδ, hspatial⟩ := exists_uniform_spatial_translation_of_compact_support
    K hK (T : ℝ) G hGc hsupp (show 0 < ε / 4 by positivity)
  have hshift : Tendsto (fun n => a - Lclt.scaledSite (R n) (q n)) atTop (𝓝 0) := by
    simpa only [sub_self] using (tendsto_const_nhds (x := a)).sub hstart
  have hsmall : ∀ᶠ n in atTop, ‖a - Lclt.scaledSite (R n) (q n)‖ < δ := by
    have h := hshift.eventually (Metric.ball_mem_nhds (0 : Continuum.Space d) hδ)
    simpa only [Metric.mem_ball, dist_zero_right] using h
  have hlarge : ∀ᶠ n in atTop, R₀ ≤ R n := hR.eventually (eventually_ge_atTop R₀)
  filter_upwards [hlower, hlarge, hsmall] with n hn hRn hsmalln
  let J : ℝ → Continuum.Space d → ℝ := fun s z =>
    G s (z - Lclt.scaledSite (R n) (q n) + a)
  have hJc : Continuous (fun p : ℝ × Continuum.Space d => J p.1 p.2) :=
    hGc.comp (continuous_fst.prodMk ((continuous_snd.sub continuous_const).add continuous_const))
  have hround := abs_sSup_killedStepTimePayoffs_sub_killedGridReward_approx_le
    (hRpos n) (supBox (q n) (R n)) (q n) T M (ε / 8) (ε / 4) T.property
    (by positivity) J G hJc.measurable (fun s z => hG _ _) hG
    (fun s hs u hu z hz => hmod (R n) hRn s hs u hu _ hz) (by
      intro s hs z
      have heq : z - Lclt.scaledSite (R n) (q n) + a =
          z + (a - Lclt.scaledSite (R n) (q n)) := by abel
      simpa only [J, heq] using hspatial s hs z (a - Lclt.scaledSite (R n) (q n)) hsmalln)
  have hb := (abs_le.mp hround).2
  change _ ≤ sSup (killedStepTimePayoffs (R n) (supBox (q n) (R n)) (q n) T J) + ε / 2 at hn
  linarith

end Sandpile.External.Stopping
