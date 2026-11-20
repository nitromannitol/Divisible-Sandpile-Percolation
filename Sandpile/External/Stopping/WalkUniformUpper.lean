import Sandpile.External.Stopping.WalkBrownianUpper
import Sandpile.External.Stopping.WalkUniformLower

/-!
# Uniform Brownian upper bounds

Uniform reward approximation and compactness upgrade the sequential lattice
upper bound to a uniform bound over compact starting sets and horizons.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal

namespace Sandpile.External.Stopping

/-- Uniformly approximating rewards have the same sequential upper bound. -/
theorem eventually_approx_grid_value_le_brownian_of_tendsto_horizon
    {d : ℕ} [NeZero d] (R : ℕ → ℝ) (q : ℕ → Site d)
    (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop)
    (a : Continuum.Space d)
    (hstart : Tendsto (fun n => Lclt.scaledSite (R n) (q n)) atTop (𝓝 a))
    {ΩB : Type*} [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → ΩB → Continuum.Space d) (hB : Continuum.IsBrownian d a B PB)
    (T : ℝ≥0) (Tn : ℕ → ℝ≥0) (hTn : Tendsto Tn atTop (𝓝 T))
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (H : ℕ → ℝ → Continuum.Space d → ℝ) (M : ℝ)
    (hG : ∀ s z, |G s z| ≤ M) (hH : ∀ n s z, |H n s z| ≤ M)
    (happrox : ∀ ε > 0, ∀ᶠ n in atTop, ∀ s ∈ Icc (0 : ℝ) (Tn n : ℝ),
      ∀ z, |G s z - H n s z| ≤ ε)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, stoppingSup ⌊R n ^ 2 * (Tn n : ℝ)⌋₊ (q n) (fun k X =>
        H n (((⌊R n ^ 2 * (Tn n : ℝ)⌋₊ : ℕ) - (k : ℝ)) / R n ^ 2)
          (Lclt.scaledSite (R n) (X k))) ≤
      Continuum.brownianDiscount B PB (fun s z => -G s z) T + ε := by
  have hupper := eventually_grid_value_le_brownian_of_tendsto_horizon
    R q hRpos hR a hstart PB B hB T Tn hTn G hGc M hG (ε / 2) (by positivity)
  filter_upwards [hupper, happrox (ε / 2) (by positivity)] with n hn ha
  have hc := abs_killedGridReward_sub_le_of_uniform (hRpos n) Set.univ (q n)
    (Tn n : ℝ) M (ε / 2) (Tn n).property G (H n) hG (hH n)
    (fun s hs z => ha s hs z)
  rw [killedStoppingSup_univ, killedStoppingSup_univ] at hc
  linarith [(abs_le.mp hc).1]

/-- The lattice value is uniformly bounded above by the Brownian value plus
an arbitrarily small error over compact starting sets and horizon intervals. -/
theorem exists_uniform_grid_value_le_brownian
    {d : ℕ} [NeZero d] {ΩB : Type*} [MeasurableSpace ΩB]
    (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : Continuum.Space d → ℝ≥0 → ΩB → Continuum.Space d)
    (hB : ∀ x, Continuum.IsBrownian d x (B x) PB)
    (T₀ T₁ : ℝ≥0) (K : Set (Continuum.Space d)) (hK : IsCompact K)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (G' : ℝ → ℝ → Continuum.Space d → ℝ) (M : ℝ)
    (hG : ∀ s z, |G s z| ≤ M) (hG' : ∀ R s z, |G' R s z| ≤ M)
    (happrox : ∀ ε > 0, ∃ R₁ > 0, ∀ R ≥ R₁,
      ∀ s ∈ Icc (0 : ℝ) (T₁ : ℝ), ∀ z, |G' R s z - G s z| ≤ ε) :
    ∀ ε > 0, ∃ R₀ > 0, ∀ R ≥ R₀, ∀ T ∈ Icc T₀ T₁, ∀ x ∈ K,
      stoppingSup ⌊R ^ 2 * (T : ℝ)⌋₊ (fun i => ⌊R * x i⌋) (fun k X =>
        G' R (((⌊R ^ 2 * (T : ℝ)⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
          (Lclt.scaledSite R (X k))) ≤
      Continuum.brownianDiscount (B x) PB (fun s z => -G s z) T + ε := by
  let J : Set (ℝ≥0 × Continuum.Space d) := Icc T₀ T₁ ×ˢ K
  have hJ : IsCompact J := isCompact_Icc.prod hK
  let E : ℝ → (ℝ≥0 × Continuum.Space d) → ℝ := fun R p =>
    max 0 (stoppingSup ⌊R ^ 2 * (p.1 : ℝ)⌋₊ (fun i => ⌊R * p.2 i⌋) (fun k X =>
      G' R (((⌊R ^ 2 * (p.1 : ℝ)⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
        (Lclt.scaledSite R (X k))) -
      Continuum.brownianDiscount (B p.2) PB (fun s z => -G s z) p.1)
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
    have hbr := tendsto_brownianDiscount_of_tendsto_start_horizon PB B hB b.2
      (fun n => (p n).2) hxc b.1 (fun n => (p n).1) hpc G hGc M hG
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hupper := eventually_approx_grid_value_le_brownian_of_tendsto_horizon
      R' (fun n i => ⌊R' n * (p n).2 i⌋) hRpos hR' b.2 hstart PB (B b.2) (hB b.2)
      b.1 (fun n => (p n).1) hpc G hGc (fun n => G' (R' n)) M hG
      (fun n s z => hG' (R' n) s z) hH (ε / 3) (by positivity)
    have hbclose := hbr.eventually (Ioi_mem_nhds (show
      Continuum.brownianDiscount (B b.2) PB (fun s z => -G s z) b.1 - ε / 3 <
        Continuum.brownianDiscount (B b.2) PB (fun s z => -G s z) b.1 by linarith))
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
  have hle : stoppingSup ⌊R ^ 2 * (T : ℝ)⌋₊ (fun i => ⌊R * x i⌋) (fun k X =>
      G' R (((⌊R ^ 2 * (T : ℝ)⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
        (Lclt.scaledSite R (X k))) -
      Continuum.brownianDiscount (B x) PB (fun s z => -G s z) T ≤ ε :=
    (le_max_right 0 _).trans ((le_abs_self _).trans he)
  linarith

/-- The uniform upper bound with real horizon parameters. -/
theorem exists_uniform_grid_value_le_brownian_real
    {d : ℕ} [NeZero d] {ΩB : Type*} [MeasurableSpace ΩB]
    (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : Continuum.Space d → ℝ≥0 → ΩB → Continuum.Space d)
    (hB : ∀ x, Continuum.IsBrownian d x (B x) PB)
    (T₀ T₁ : ℝ) (hT₀ : 0 < T₀) (hT : T₀ ≤ T₁)
    (K : Set (Continuum.Space d)) (hK : IsCompact K)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (G' : ℝ → ℝ → Continuum.Space d → ℝ) (M : ℝ)
    (hG : ∀ s z, |G s z| ≤ M) (hG' : ∀ R s z, |G' R s z| ≤ M)
    (happrox : ∀ ε > 0, ∃ R₁ > 0, ∀ R ≥ R₁,
      ∀ s ∈ Icc (0 : ℝ) T₁, ∀ z, |G' R s z - G s z| ≤ ε) :
    ∀ ε > 0, ∃ R₀ > 0, ∀ R ≥ R₀, ∀ T ∈ Icc T₀ T₁, ∀ x ∈ K,
      stoppingSup ⌊R ^ 2 * T⌋₊ (fun i => ⌊R * x i⌋) (fun k X =>
        G' R (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
          (Lclt.scaledSite R (X k))) ≤
      Continuum.brownianDiscount (B x) PB (fun s z => -G s z) T + ε := by
  have hT₁ : 0 ≤ T₁ := hT₀.le.trans hT
  have h := exists_uniform_grid_value_le_brownian PB B hB
    (Real.toNNReal T₀) (Real.toNNReal T₁) K hK G hGc G' M hG hG'
    (by simpa only [Real.coe_toNNReal _ hT₁] using happrox)
  intro ε hε
  obtain ⟨R₀, hR₀, hr⟩ := h ε hε
  refine ⟨R₀, hR₀, ?_⟩
  intro R hR T hTm x hx
  have hTpos : 0 ≤ T := hT₀.le.trans hTm.1
  have hTm' : Real.toNNReal T ∈ Icc (Real.toNNReal T₀) (Real.toNNReal T₁) := by
    exact ⟨Real.toNNReal_le_toNNReal hTm.1, Real.toNNReal_le_toNNReal hTm.2⟩
  simpa only [Real.coe_toNNReal _ hTpos] using hr R hR (Real.toNNReal T) hTm' x hx

end Sandpile.External.Stopping
