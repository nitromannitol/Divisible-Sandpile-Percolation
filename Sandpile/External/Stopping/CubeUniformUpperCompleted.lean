import Sandpile.External.Stopping.KilledWalkBrownianUpper
import Sandpile.External.Stopping.CubeUniformLower

/-!
# Uniform killed-walk upper bounds

Compactness upgrades the sequential upper bound to a uniform comparison with
the Brownian cube value defined using completed stopping events.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Killed grid values are uniformly bounded above by the completed-event
Brownian cube value, up to an arbitrarily small error. -/
theorem exists_uniform_killed_grid_value_le_completed_cube
    {d : ℕ} [NeZero d] {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Continuum.Space d → ℝ≥0 → Ω → Continuum.Space d)
    (hB : ∀ x, Continuum.IsBrownian d x (B x) P)
    (T₀ T₁ : ℝ≥0) (K : Set (Continuum.Space d)) (hK : IsCompact K)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (G' : ℝ → ℝ → Continuum.Space d → ℝ) (M : ℝ)
    (hG : ∀ s z, |G s z| ≤ M) (hG' : ∀ R s z, |G' R s z| ≤ M)
    (happrox : ∀ ε > 0, ∃ R₁ > 0, ∀ R ≥ R₁,
      ∀ s ∈ Icc (0 : ℝ) (T₁ : ℝ), ∀ z, |G' R s z - G s z| ≤ ε) :
    ∀ ε > 0, ∃ R₀ > 0, ∀ R ≥ R₀, ∀ T ∈ Icc T₀ T₁, ∀ x ∈ K,
      killedStoppingSup (supBox (fun i => ⌊R * x i⌋) R) ⌊R ^ 2 * (T : ℝ)⌋₊
        (fun i => ⌊R * x i⌋) (fun k X =>
          G' R (((⌊R ^ 2 * (T : ℝ)⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
            (Lclt.scaledSite R (X k))) ≤
      sSup (aeClockPayoffs (B x) P T G
        (fun ω => (min (LatticeProb.openExitTime (B x) (openUnitCube x) ω)
          (T : ℝ≥0∞)).toNNReal)) + ε := by
  let D : Continuum.Space d → ℝ≥0 → ℝ := fun x T =>
    sSup (aeClockPayoffs (B x) P T G
      (fun ω => (min (LatticeProb.openExitTime (B x) (openUnitCube x) ω)
        (T : ℝ≥0∞)).toNNReal))
  let J : Set (ℝ≥0 × Continuum.Space d) := Icc T₀ T₁ ×ˢ K
  have hJ : IsCompact J := isCompact_Icc.prod hK
  let E : ℝ → (ℝ≥0 × Continuum.Space d) → ℝ := fun R p =>
    max 0 (killedStoppingSup (supBox (fun i => ⌊R * p.2 i⌋) R)
      ⌊R ^ 2 * (p.1 : ℝ)⌋₊ (fun i => ⌊R * p.2 i⌋) (fun k X =>
        G' R (((⌊R ^ 2 * (p.1 : ℝ)⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
          (Lclt.scaledSite R (X k))) - D p.2 p.1)
  have hseq : ∀ (R : ℕ → ℝ) (p : ℕ → ℝ≥0 × Continuum.Space d)
      (b : ℝ≥0 × Continuum.Space d),
      Tendsto R atTop atTop → (∀ n, p n ∈ J) → Tendsto p atTop (𝓝 b) →
      Tendsto (fun n => E (R n) (p n)) atTop (𝓝 0) := by
    intro R p b hR hp hpconv
    let R' : ℕ → ℝ := fun n => max (R n) 1
    have hR' : Tendsto R' atTop atTop :=
      tendsto_atTop_mono' atTop (Filter.Eventually.of_forall fun n => le_max_left _ _) hR
    have hRpos : ∀ n, 0 < R' n := fun n => lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hRsame : ∀ᶠ n in atTop, R' n = R n := by
      filter_upwards [hR.eventually_ge_atTop 1] with n hn
      exact max_eq_left hn
    have hpc : Tendsto (fun n => (p n).1) atTop (𝓝 b.1) :=
      continuous_fst.continuousAt.tendsto.comp hpconv
    have hxc : Tendsto (fun n => (p n).2) atTop (𝓝 b.2) :=
      continuous_snd.continuousAt.tendsto.comp hpconv
    have hstart := tendsto_scaled_floor_start R' hR' (fun n => (p n).2) b.2 hxc
    have hH : ∀ η > 0, ∀ᶠ n in atTop, ∀ s ∈ Icc (0 : ℝ) ((p n).1 : ℝ),
        ∀ z, |G s z - G' (R' n) s z| ≤ η := by
      intro η hη
      obtain ⟨r, _, hr⟩ := happrox η hη
      filter_upwards [hR'.eventually_ge_atTop r] with n hn s hs z
      have hTn : ((p n).1 : ℝ) ≤ T₁ := by exact_mod_cast (hp n).1.2
      simpa only [abs_sub_comm] using hr (R' n) hn s ⟨hs.1, hs.2.trans hTn⟩ z
    have hbr := tendsto_sSup_aeCubeClockPayoffs_of_tendsto_start_horizon P B hB b.2
      (fun n => (p n).2) hxc b.1 (fun n => (p n).1) hpc G hGc M hG
    change Tendsto (fun n => D (p n).2 (p n).1) atTop (𝓝 (D b.2 b.1)) at hbr
    obtain ⟨C, hCm, hCc, _, hC, hCv⟩ := exists_continuous_version_cube_value (hB b.2)
    have hvalue : D b.2 b.1 = Continuum.brownianDiscountCube C P (fun s z => -G s z) b.1 1 b.2 :=
      (hCv b.1 G hGc M hG).1
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hupper := eventually_approx_killed_grid_value_le_continuous_brownian_cube
      R' (fun n i => ⌊R' n * (p n).2 i⌋) hRpos hR' b.2 hstart P C hC hCm hCc
      b.1 (fun n => (p n).1) hpc G hGc (fun n => G' (R' n)) M hG
      (fun n s z => hG' (R' n) s z) hH (ε / 3) (by positivity)
    rw [← hvalue] at hupper
    have hbclose := hbr.eventually (Ioi_mem_nhds (show D b.2 b.1 - ε / 3 < D b.2 b.1 by linarith))
    filter_upwards [hupper, hbclose, hRsame] with n hn hb he
    rw [he] at hn
    change |E (R n) (p n) - 0| < ε
    rw [sub_zero, abs_of_nonneg (le_max_left _ _)]
    dsimp only [E]
    apply max_lt hε
    linarith
  intro ε hε
  obtain ⟨R₀, hR₀, h⟩ := exists_large_scale_uniform_of_compact_sequences J hJ E hseq ε hε
  refine ⟨R₀, hR₀, ?_⟩
  intro R hR T hTK x hxK
  have he := h R hR (T, x) ⟨hTK, hxK⟩
  dsimp [E] at he
  have hle : killedStoppingSup (supBox (fun i => ⌊R * x i⌋) R) ⌊R ^ 2 * (T : ℝ)⌋₊
      (fun i => ⌊R * x i⌋) (fun k X =>
        G' R (((⌊R ^ 2 * (T : ℝ)⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
          (Lclt.scaledSite R (X k))) - D x T ≤ ε :=
    (le_max_right 0 _).trans ((le_abs_self _).trans he)
  change _ ≤ D x T + ε
  linarith

end Sandpile.External.Stopping
