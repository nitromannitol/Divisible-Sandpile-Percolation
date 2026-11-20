import Sandpile.External.Stopping.WalkValueUpperLimit
import Sandpile.External.Stopping.WalkBrownianInvariance
import Sandpile.External.Stopping.BrownianValueIntrinsic

/-!
# Brownian upper bounds for lattice stopping values

The invariance principle identifies the weak path limit with Brownian motion,
so the general upper bound applies to the original Brownian stopping value.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace Sandpile.External.Stopping

/-- A countable dense family of nonnegative observation times. -/
noncomputable def rationalStoppingTime (q : ℚ) : ℝ≥0 := Real.toNNReal (q : ℝ)

/-- The nonnegative images of rational times are order-dense. -/
theorem rationalStoppingTime_dense (a b : ℝ≥0) (hab : a < b) :
    ∃ q : ℚ, a < rationalStoppingTime q ∧ rationalStoppingTime q < b := by
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  obtain ⟨q, haq, hqb⟩ := exists_rat_btwn hab'
  have hq : 0 ≤ (q : ℝ) := a.property.trans (le_of_lt haq)
  refine ⟨q, ?_, ?_⟩
  · apply NNReal.coe_lt_coe.mp
    simpa only [rationalStoppingTime, Real.coe_toNNReal _ hq] using haq
  · apply NNReal.coe_lt_coe.mp
    simpa only [rationalStoppingTime, Real.coe_toNNReal _ hq] using hqb

/-- The upper lattice value bound for converging starts and horizons. -/
theorem eventually_grid_value_le_brownian_of_tendsto_horizon
    {d : ℕ} [NeZero d] (R : ℕ → ℝ) (q : ℕ → Site d)
    (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop)
    (a : Continuum.Space d)
    (hstart : Tendsto (fun n => Lclt.scaledSite (R n) (q n)) atTop (𝓝 a))
    {ΩB : Type*} [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → ΩB → Continuum.Space d) (hB : Continuum.IsBrownian d a B PB)
    (T : ℝ≥0) (H : ℕ → ℝ≥0) (hH : Tendsto H atTop (𝓝 T))
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, stoppingSup ⌊R n ^ 2 * (H n : ℝ)⌋₊ (q n) (fun k X =>
      G (((⌊R n ^ 2 * (H n : ℝ)⌋₊ : ℕ) - (k : ℝ)) / R n ^ 2)
        (Lclt.scaledSite (R n) (X k))) ≤
      Continuum.brownianDiscount B PB (fun s z => -G s z) T + ε := by
  obtain ⟨B', hBm, hBc, hBB', hB'⟩ := exists_continuous_sandpile_brownian_version hB
  let V : ℝ≥0 → ΩB → Continuum.Space d := fun t ω => B' t ω - a
  obtain ⟨F, hFm, hF, hpath⟩ := exists_brownian_path_limit d R q hR a hstart PB V
    (isBrownianSpace_sub_start hB')
  let ν : ProbabilityMeasure C(ℝ≥0, Continuum.Space d) :=
    ⟨PB.map F, (Measure.isProbabilityMeasure_map_iff hFm.aemeasurable).2 inferInstance⟩
  let E : ℝ≥0 → C(ℝ≥0, Continuum.Space d) → Continuum.Space d := fun t f => f t
  have hEc : ∀ f, Continuous fun t => E t f := fun f => f.continuous
  have hpathmap : PB.map F = PB.map (LatticeProb.pathMap B' hBc) := by
    apply Measure.map_congr
    filter_upwards [hF] with ω hω
    apply ContinuousMap.ext
    intro t
    change F ω t = B' t ω
    rw [hω t]
    dsimp [V]
    exact add_sub_cancel a (B' t ω)
  have hElaw : (ν : Measure C(ℝ≥0, Continuum.Space d)).map (LatticeProb.pathMap E hEc) =
      PB.map (LatticeProb.pathMap B' hBc) := by
    have heq : LatticeProb.pathMap E hEc = id := by
      funext f
      exact ContinuousMap.ext (fun _ => rfl)
    rw [heq, Measure.map_id]
    exact hpathmap
  have hval := brownianDiscount_eq_of_path_law_eq (ν : Measure _) PB E B'
    (fun t => (continuous_eval_const t).measurable.stronglyMeasurable)
    (fun t => (hBm t).stronglyMeasurable) hEc hBc hElaw T G hGc M hG
  have hval' := brownianDiscount_eq_of_indistinguishable hB hB' hBB' T G hGc M hG
  have h := eventually_grid_value_le_path_value R hRpos hR q H T hH ν hpath
    rationalStoppingTime rationalStoppingTime_dense G hGc M hG ε hε
  change ∀ᶠ n in atTop, _ ≤ Continuum.brownianDiscount E (ν : Measure _)
    (fun s z => -G s z) T + ε at h
  rw [hval, ← hval'] at h
  exact h

end Sandpile.External.Stopping
