import Sandpile.External.Stopping.WalkLatticeLowerValue
import Sandpile.External.Stopping.CompactRewardTranslation

/-!
# Lower lattice stopping-value limit

The compactly supported reward is insensitive to the vanishing translation
between the rescaled lattice starts and their limit. This removes the alignment
shift from the lower value inequality.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal

namespace Sandpile.External.Stopping

/-- The lower value inequality holds for unshifted lattice rewards when the
rescaled starting sites converge to the starting point of the limit. -/
theorem eventually_lattice_value_ge_limit_of_start_tendsto
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
        G ((T : ℝ) - (k : ℝ) / R n ^ 2) (Lclt.scaledSite (R n) (X k))) + ε := by
  have hlower := eventually_lattice_value_ge_limit_of_compact_support P R q hRpos hR
    W Y hWm hYm hWlaw hconv T a G hGc K hK hsupp M hG (ε / 2) (by positivity)
  obtain ⟨δ, hδ, hmod⟩ := exists_uniform_spatial_translation_of_compact_support
    K hK (T : ℝ) G hGc hsupp (show 0 < ε / 2 by positivity)
  have hshift : Tendsto (fun n => a - Lclt.scaledSite (R n) (q n)) atTop (𝓝 0) := by
    simpa only [sub_self] using (tendsto_const_nhds (x := a)).sub hstart
  have hsmall : ∀ᶠ n in atTop, ‖a - Lclt.scaledSite (R n) (q n)‖ < δ := by
    have h := hshift.eventually (Metric.ball_mem_nhds (0 : Continuum.Space d) hδ)
    simpa only [Metric.mem_ball, dist_zero_right] using h
  filter_upwards [hlower, hsmall] with n hn hsmalln
  let N := ⌊R n ^ 2 * (T : ℝ)⌋₊
  let J : ℝ → Continuum.Space d → ℝ := fun s z =>
    G s (z + (a - Lclt.scaledSite (R n) (q n)))
  let F : ℕ → (ℕ → Site d) → ℝ := fun k X =>
    J ((T : ℝ) - (k : ℝ) / R n ^ 2) (Lclt.scaledSite (R n) (X k))
  let H : ℕ → (ℕ → Site d) → ℝ := fun k X =>
    G ((T : ℝ) - (k : ℝ) / R n ^ 2) (Lclt.scaledSite (R n) (X k))
  have hbound := abs_killedStoppingSup_sub_le_of_reward
    (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)) Set.univ N (q n) F H (ε / 2)
    (bddAbove_killedSet_shiftedReward (R n) Set.univ (q n) N T M J (fun s z => hG _ _))
    (bddAbove_killedSet_shiftedReward (R n) Set.univ (q n) N T M G hG)
    (fun τ hτ hτN => integrable_stopped_shiftedReward (R n) (q n) N T M J
      (fun s z => hG _ _) hτ hτN)
    (fun τ hτ hτN => integrable_stopped_shiftedReward (R n) (q n) N T M G hG hτ hτN) (by
      intro k hk X
      have hpos : 0 < R n ^ 2 := sq_pos_of_pos (hRpos n)
      have hkT : (k : ℝ) / R n ^ 2 ≤ T := by
        apply (div_le_iff₀ hpos).2
        have hkN : (k : ℝ) ≤ N := by exact_mod_cast hk
        have hf : (N : ℝ) ≤ R n ^ 2 * T := Nat.floor_le (mul_nonneg hpos.le T.property)
        nlinarith
      have hk0 : 0 ≤ (k : ℝ) / R n ^ 2 := div_nonneg (Nat.cast_nonneg _) hpos.le
      exact hmod _ ⟨by linarith, by linarith⟩ _ _ hsmalln)
  rw [killedStoppingSup_univ, killedStoppingSup_univ] at hbound
  have hupper := (abs_le.mp hbound).2
  change sSup (naturalStoppingPayoffs P (fun t ω => Y ω t) T _) ≤ stoppingSup N (q n) F + ε / 2 at hn
  change sSup (naturalStoppingPayoffs P (fun t ω => Y ω t) T _) ≤ stoppingSup N (q n) H + ε
  linarith

end Sandpile.External.Stopping
