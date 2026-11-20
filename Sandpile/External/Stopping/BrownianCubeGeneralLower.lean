import Sandpile.External.Stopping.BrownianCubeVaryingLower
import Sandpile.External.Stopping.RewardCutoffConvergence
import Sandpile.External.Stopping.KilledRewardOrder

/-!
# Brownian cube lower bound for bounded rewards

A nonnegative shift and an expanding spatial cutoff reduce bounded continuous
rewards to the compactly supported case.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal

namespace Sandpile.External.Stopping

/-- Along converging starts and positive horizons, the lattice grid values have
the Brownian value as a lower limit for every bounded continuous reward. -/
theorem eventually_killed_grid_value_ge_brownian_cube_of_bounded_reward
    {d : ℕ} [NeZero d] (R : ℕ → ℝ) (q : ℕ → Site d)
    (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop)
    (a : Continuum.Space d)
    (hstart : Tendsto (fun n => Lclt.scaledSite (R n) (q n)) atTop (𝓝 a))
    {ΩB : Type*} [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → ΩB → Continuum.Space d) (hB : Continuum.IsBrownian d a B PB)
    (T : ℝ≥0) (hT : 0 < T) (Tn : ℕ → ℝ≥0) (hTn : Tendsto Tn atTop (𝓝 T))
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, Continuum.brownianDiscountCube B PB (fun s z => -G s z) T 1 a ≤
      killedStoppingSup (supBox (q n) (R n)) ⌊R n ^ 2 * (Tn n : ℝ)⌋₊ (q n) (fun k X =>
        G (((⌊R n ^ 2 * (Tn n : ℝ)⌋₊ : ℕ) - (k : ℝ)) / R n ^ 2)
          (Lclt.scaledSite (R n) (X k))) + ε := by
  have hM0 : 0 ≤ M := (abs_nonneg (G 0 0)).trans (hG 0 0)
  let S := Continuum.cubeStoppingPayoffs B PB (fun s z => -G s z) T 1 a
  have hS : S.Nonempty := ⟨_, fun _ => 0, Continuum.isBrownianStopping_const B 0,
    (fun _ => NNReal.coe_nonneg T), Filter.Eventually.of_forall
      (fun _ s hs => (not_lt_of_ge bot_le hs).elim), rfl⟩
  have hne : Continuum.brownianDiscountCube B PB (fun s z => -G s z) T 1 a - ε / 3 < sSup S := by
    change sSup S - ε / 3 < sSup S
    linarith
  obtain ⟨v, ⟨τ, hτ, hτT, hτkill, rfl⟩, hv⟩ := exists_lt_of_lt_csSup hS hne
  have hτm := Continuum.IsBrownianStopping.aemeasurable hτ PB hB.aemeasurable
  have hBL : LatticeProb.IsBrownianSpace d a B PB := ⟨hB.start, hB.coord, hB.indep⟩
  have hpos := Continuum.aemeasurable_stopped_position PB hB.aemeasurable hBL.cont hτm
  let f : ΩB → ℝ := fun ω => G ((T : ℝ) - τ ω) (B (τ ω) ω)
  have hfm : AEStronglyMeasurable f PB :=
    (hGc.measurable.comp_aemeasurable
      ((aemeasurable_const.sub (measurable_coe_nnreal_real.comp_aemeasurable hτm)).prodMk hpos)).aestronglyMeasurable
  have hfi : Integrable f PB := Integrable.of_bound hfm M (by
    filter_upwards with ω
    simpa only [Real.norm_eq_abs, f] using hG ((T : ℝ) - τ ω) (B (τ ω) ω))
  have hfc : AEStronglyMeasurable (fun ω => f ω + M) PB := hfm.add aestronglyMeasurable_const
  have hlim := tendsto_integral_cutoff_mul PB (fun ω => B (τ ω) ω) hpos
    (fun ω => f ω + M) hfc (2 * M) (by
      filter_upwards with ω
      have hg := abs_le.mp (hG ((T : ℝ) - τ ω) (B (τ ω) ω))
      change |f ω + M| ≤ 2 * M
      dsimp [f]
      rw [abs_of_nonneg (by linarith [hg.1])]
      linarith [hg.2])
  have hint : (∫ ω, f ω + M ∂PB) = (∫ ω, f ω ∂PB) + M := by
    rw [integral_add hfi (integrable_const M)]
    simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  have hnear := hlim.eventually (Ioi_mem_nhds (show (∫ ω, f ω + M ∂PB) - ε / 3 <
    ∫ ω, f ω + M ∂PB by linarith))
  obtain ⟨j, hj⟩ := hnear.exists
  let A : ℝ := (j : ℝ) + 1
  let H : ℝ → Continuum.Space d → ℝ := fun s z => Continuum.cutoff A z * (G s z + M)
  have hA : 0 < A := by dsimp [A]; positivity
  have hHc : Continuous (fun p : ℝ × Continuum.Space d => H p.1 p.2) :=
    ((Continuum.continuous_cutoff A).comp continuous_snd).mul (hGc.add continuous_const)
  have hHbound : ∀ s z, |H s z| ≤ 2 * M := by
    intro s z
    have hg := abs_le.mp (hG s z)
    have hc0 := Continuum.cutoff_nonneg A z
    have hc1 := Continuum.cutoff_le_one A z
    dsimp [H]
    rw [abs_of_nonneg (mul_nonneg hc0 (by linarith [hg.1]))]
    nlinarith [mul_nonneg (sub_nonneg.mpr hc1) (show 0 ≤ G s z + M by linarith [hg.1])]
  have hHle : ∀ s z, H s z ≤ G s z + M := by
    intro s z
    have hg := (abs_le.mp (hG s z)).1
    exact mul_le_of_le_one_left (by linarith) (Continuum.cutoff_le_one A z)
  let K : Set (Continuum.Space d) := Metric.closedBall 0 (2 * A)
  have hK : IsCompact K := isCompact_closedBall 0 (2 * A)
  have hsupp : ∀ s z, z ∉ K → H s z = 0 := by
    intro s z hz
    have hz' : 2 * A ≤ ‖z‖ := by
      have : ¬ dist z 0 ≤ 2 * A := hz
      simpa only [dist_zero_right] using (le_of_lt (lt_of_not_ge this))
    simp only [H, Continuum.cutoff_eq_zero_of_norm_ge A hA z hz', zero_mul]
  have hHb : BddAbove (Continuum.cubeStoppingPayoffs B PB (fun s z => -H s z) T 1 a) := by
    refine ⟨2 * M, ?_⟩
    rintro v ⟨σ, _, _, _, rfl⟩
    simp only [neg_neg]
    have hb := norm_integral_le_of_norm_le_const (μ := PB)
      (f := fun ω => H ((T : ℝ) - σ ω) (B (σ ω) ω)) (C := 2 * M)
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hHbound _ _)
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hb)
  have hvalue : (∫ ω, H ((T : ℝ) - τ ω) (B (τ ω) ω) ∂PB) ≤
      Continuum.brownianDiscountCube B PB (fun s z => -H s z) T 1 a := by
    apply le_csSup hHb
    exact ⟨τ, hτ, hτT, hτkill, by simp⟩
  have hlower := eventually_killed_grid_value_ge_brownian_cube_of_tendsto_horizon
    R q hRpos hR a hstart PB B hB T hT Tn hTn H hHc K hK hsupp (2 * M) hHbound
    (ε / 3) (by positivity)
  filter_upwards [hlower] with n hn
  let N : ℕ := ⌊R n ^ 2 * (Tn n : ℝ)⌋₊
  let J : ℝ := (N : ℝ) / R n ^ 2
  have horder := killedStoppingSup_le_of_reward_le_add (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))
    (supBox (q n) (R n)) N (q n) (fun k X => H (J - (k : ℝ) / R n ^ 2) (Lclt.scaledSite (R n) (X k)))
    (fun k X => G (J - (k : ℝ) / R n ^ 2) (Lclt.scaledSite (R n) (X k))) M
    (bddAbove_killedSet_shiftedReward (R n) (supBox (q n) (R n)) (q n) N J M G hG)
    (fun σ hσ hσN => integrable_stopped_shiftedReward (R n) (q n) N J (2 * M) H hHbound hσ hσN)
    (fun σ hσ hσN => integrable_stopped_shiftedReward (R n) (q n) N J M G hG hσ hσN)
    (fun k _ X => hHle _ _)
  simp only [J, ← sub_div] at horder
  change Continuum.brownianDiscountCube B PB (fun s z => -H s z) T 1 a ≤ _ at hn
  change (∫ ω, f ω + M ∂PB) - ε / 3 <
    ∫ ω, H ((T : ℝ) - τ ω) (B (τ ω) ω) ∂PB at hj
  rw [hint] at hj
  dsimp [f] at hj
  dsimp [N] at horder
  simp only [neg_neg] at hv
  linarith

end Sandpile.External.Stopping
