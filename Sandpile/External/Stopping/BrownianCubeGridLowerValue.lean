import Sandpile.External.Stopping.WalkCubeGridLowerValue
import Sandpile.External.Stopping.KilledWalkCouplingWithPaths
import Sandpile.External.Stopping.CubeClockPathLaw
import Sandpile.External.Stopping.CompletedCubeStartContinuity

/-!
# Brownian lower bounds for cube-killed grid values

The cube-stopped walk coupling identifies the limiting clock value with the
Brownian cube-killed value.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- For a compactly supported reward and convergent lattice starts, the
Brownian cube-killed value is asymptotically bounded by the lattice value. -/
theorem eventually_killed_grid_value_ge_brownian_cube_of_compact_support
    {d : ℕ} [NeZero d] (R : ℕ → ℝ) (q : ℕ → Site d)
    (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop)
    (a : Continuum.Space d)
    (hstart : Tendsto (fun n => Lclt.scaledSite (R n) (q n)) atTop (𝓝 a))
    {ΩB : Type*} [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → ΩB → Continuum.Space d) (hB : Continuum.IsBrownian d a B PB)
    (T : ℝ≥0) (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (K : Set (Continuum.Space d)) (hK : IsCompact K)
    (hsupp : ∀ s z, z ∉ K → G s z = 0)
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, Continuum.brownianDiscountCube B PB (fun s z => -G s z) T 1 a ≤
      killedStoppingSup (supBox (q n) (R n)) ⌊R n ^ 2 * (T : ℝ)⌋₊ (q n)
        (fun k X => G (((⌊R n ^ 2 * (T : ℝ)⌋₊ : ℕ) - (k : ℝ)) / R n ^ 2)
          (Lclt.scaledSite (R n) (X k))) + ε := by
  obtain ⟨B', hBm, hBc, hBB', hB'⟩ := exists_continuous_sandpile_brownian_version hB
  let V : ℝ≥0 → ΩB → Continuum.Space d := fun t ω => B' t ω - a
  have hVm : ∀ t, Measurable (V t) := fun t => (hBm t).sub_const a
  have hVc : ∀ ω, Continuous fun t => V t ω := fun ω => (hBc ω).sub continuous_const
  have hVL := isBrownianSpace_sub_start hB'
  have hV : Continuum.IsBrownian d 0 V PB := ⟨hVL.start, hVL.coord, hVL.indep⟩
  obtain ⟨F, hFm, hF, Ω, mΩ, P, hP, W, Y, hWm, hYm, hWlaw, hYlaw, hconv, hclocks⟩ :=
    exists_cube_stopped_walk_brownian_coupling_with_paths d R q hRpos hR
      (fun _ => T) T tendsto_const_nhds PB V hVL
  have hpath : P.map Y = PB.map (LatticeProb.pathMap V hVc) := by
    have hF' : F =ᵐ[PB] LatticeProb.pathMap V hVc := by
      filter_upwards [hF] with ω hω
      exact ContinuousMap.ext fun t => hω t
    rw [hYlaw, Measure.map_congr hF']
  let H : ℝ → Continuum.Space d → ℝ := fun s z => G s (z + a)
  have hHc : Continuous (fun p : ℝ × Continuum.Space d => H p.1 p.2) :=
    hGc.comp (continuous_fst.prodMk (continuous_snd.add continuous_const))
  have hlaw := cubeClockValue_eq_of_path_law_eq P PB Y (LatticeProb.pathMap V hVc)
    hYm (LatticeProb.measurable_pathMap V hVm hVc) hpath 0 T H hHc M (fun s z => hG _ _)
  have hclock : sSup (clockPayoffs V PB T H
      (fun ω => (min (LatticeProb.openExitTime V (openUnitCube 0) ω)
        (T : ℝ≥0∞)).toNNReal) (Continuum.brownianFiltration V)) =
      Continuum.brownianDiscountCube V PB (fun s z => -H s z) T 1 0 := by
    unfold Continuum.brownianDiscountCube
    rw [cubeStoppingPayoffs_eq_clockPayoffs PB 0 V hV hVm hVc T H]
    rfl
  have hshift : Continuum.brownianDiscountCube V PB (fun s z => -H s z) T 1 0 =
      Continuum.brownianDiscountCube B' PB (fun s z => -G s z) T 1 a := by
    unfold Continuum.brownianDiscountCube
    have h := Sandpile.Support.cubeStoppingPayoffs_add_const PB V (fun s z => -G s z) T 1 a
    have hproc : (fun t ω => a + V t ω) = B' := by
      funext t ω
      dsimp only [V]
      abel
    rw [hproc] at h
    have hrew : (fun s z => -G s (a + z)) = (fun s z => -H s z) := by
      funext s z
      simp only [H, add_comm]
    rw [← hrew]
    exact congrArg sSup h.symm
  have hble := brownianDiscountCube_le_of_indistinguishable PB a B B' hB hB' hBB'
    hBm hBc T G hGc M hG
  have hlower := eventually_killed_grid_value_ge_cube_limit_of_compact_support P R q hRpos hR
    W Y hWm hYm hWlaw hconv (hclocks.mono fun ω hω => ⟨hω.1, hω.2.1, hω.2.2.1⟩)
    T a hstart G hGc K hK hsupp M hG ε hε
  change ∀ᶠ n in atTop, sSup (clockPayoffs (fun t ω => Y ω t) P T H _ _) ≤ _ at hlower
  have hlaw' : sSup (clockPayoffs (fun t ω => Y ω t) P T H
      (fun ω => (min (LatticeProb.openExitTime (fun t ω => Y ω t) (openUnitCube 0) ω)
        (T : ℝ≥0∞)).toNNReal) (Continuum.brownianFiltration (fun t ω => Y ω t))) =
      sSup (clockPayoffs V PB T H
        (fun ω => (min (LatticeProb.openExitTime V (openUnitCube 0) ω)
          (T : ℝ≥0∞)).toNNReal) (Continuum.brownianFiltration V)) := by
    simpa only [LatticeProb.pathMap_apply] using hlaw
  rw [hlaw', hclock, hshift] at hlower
  filter_upwards [hlower] with n hn
  exact hble.trans hn

end Sandpile.External.Stopping
