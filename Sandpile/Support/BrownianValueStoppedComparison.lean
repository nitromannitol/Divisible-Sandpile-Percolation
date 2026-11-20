import Sandpile.Support.BrownianStoppedValueBound
import Sandpile.Support.BrownianSuperharmonicRestart

/-!
# Stopped comparisons for the Brownian value process

The superharmonic Brownian stopping value decreases in expectation between
bounded stopping times, on events known at the earlier time.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- The Brownian value process satisfies the stopped-time supermartingale
inequality on every event measurable at the earlier stopping time. -/
theorem Sandpile.Support.setIntegral_brownian_value_stopped_le
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Sandpile.Continuum.Space d → ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (hB : ∀ y, Sandpile.Continuum.IsBrownian d y (B y) P)
    (hBc : ∀ y ω, Continuous fun t => B y t ω)
    (hBm : ∀ y t, StronglyMeasurable (B y t))
    (x : Sandpile.Continuum.Space d) (T : ℝ≥0)
    (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hG : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (T : ℝ) ×ˢ Set.univ))
    (hgrow : ∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (T : ℝ),
      ∀ y, |G t y| ≤ C * (1 + ‖y‖) ^ k)
    (M : ℝ≥0 → Ω → ℝ)
    (hMval : ∀ s ≤ T, ∀ ω, M s ω =
      Sandpile.External.Snell.snellValue (B (B x s ω)) P G ((T : ℝ) - s))
    (σ τ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (LatticeProb.natFiltration (B x) (hBm x))
      (fun ω => (σ ω : ℝ≥0∞)))
    (hτ : IsStoppingTime (LatticeProb.natFiltration (B x) (hBm x))
      (fun ω => (τ ω : ℝ≥0∞)))
    (hτT : ∀ ω, τ ω ≤ T)
    (E : Set Ω) (hE : MeasurableSet[hσ.measurableSpace] E)
    (hστ : ∀ ω ∈ E, σ ω ≤ τ ω) :
    (∫ ω in E, (M (τ ω) ω - M (σ ω) ω) ∂P) ≤ 0 := by
  let V : ℝ → Sandpile.Continuum.Space d → ℝ := fun s y =>
    Sandpile.External.Snell.snellValue (B y) P G s
  have hVc : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => V p.1 p.2)
      (Set.Icc 0 (T : ℝ) ×ˢ Set.univ) := by
    have h := Sandpile.Support.continuousOn_brownian_snellValue P B hB hBm hBc T G hG hgrow
    let φ : ℝ × Sandpile.Continuum.Space d → ℝ≥0 × Sandpile.Continuum.Space d :=
      fun p => (((T : ℝ) - p.1).toNNReal, p.2)
    have hφ : Continuous φ :=
      (continuous_real_toNNReal.comp (continuous_const.sub continuous_fst)).prodMk continuous_snd
    have hmaps : Set.MapsTo φ (Set.Icc (0 : ℝ) (T : ℝ) ×ˢ Set.univ)
        (Set.Icc (0 : ℝ≥0) T ×ˢ Set.univ) := by
      intro p hp
      refine ⟨⟨zero_le, ?_⟩, Set.mem_univ _⟩
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal ((T : ℝ) - p.1) (sub_nonneg.mpr hp.1.2)]
      linarith [hp.1.1]
    have hc := h.comp hφ.continuousOn hmaps
    apply hc.congr
    intro p hp
    change V p.1 p.2 = Sandpile.External.Snell.snellValue (B p.2) P G
      ((T : ℝ) - ((T : ℝ) - p.1).toNNReal)
    rw [Real.coe_toNNReal ((T : ℝ) - p.1) (sub_nonneg.mpr hp.1.2)]
    congr 1
    ring
  obtain ⟨C, hC, n, hVgrowth⟩ :=
    Sandpile.Support.exists_brownian_snellValue_growth_bound P B hB hBm hBc T G hG hgrow
  have hVgrow : ∃ C k : ℝ, ∀ r ∈ Set.Icc (0 : ℝ) (T : ℝ),
      ∀ y, |V r y| ≤ C * (1 + ‖y‖) ^ k := by
    refine ⟨C, n, ?_⟩
    intro r hr y
    have hrT : r.toNNReal ≤ T := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal r hr.1]
      exact hr.2
    have hh := hVgrowth r.toNNReal hrT y
    rw [Real.coe_toNNReal r hr.1] at hh
    simpa only [V, Real.rpow_natCast] using hh
  obtain ⟨D, hDi, hD⟩ := Sandpile.Support.exists_integrable_brownian_reward_uniform_bound
    x P (B x) (hB x) (hBm x) (hBc x) T V hVgrow
  have hsuper : ∀ y, ∀ s ∈ Set.Icc (0 : ℝ) (T : ℝ), ∀ ρ : Ω → ℝ≥0,
      Sandpile.Continuum.IsBrownianStopping (B y) ρ → (∀ ω, (ρ ω : ℝ) ≤ s) →
      Integrable (fun ω => V (s - ρ ω) (B y (ρ ω) ω)) P →
      (∫ ω, V (s - ρ ω) (B y (ρ ω) ω) ∂P) ≤ V s y := by
    intro y s hs ρ hρ hρs _
    let S : ℝ≥0 := s.toNNReal
    have hS : S ≤ T := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal s hs.1]
      exact hs.2
    have hGS : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
        (Set.Icc 0 (S : ℝ) ×ˢ Set.univ) := hG.mono (by
      intro p hp
      exact ⟨⟨hp.1.1, hp.1.2.trans (by exact_mod_cast hS)⟩, hp.2⟩)
    have hgrowS : ∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (S : ℝ),
        ∀ y, |G t y| ≤ C * (1 + ‖y‖) ^ k := by
      obtain ⟨C, k, hk⟩ := hgrow
      exact ⟨C, k, fun t ht z => hk t ⟨ht.1, ht.2.trans (by exact_mod_cast hS)⟩ z⟩
    have hρS : ∀ ω, ρ ω ≤ S := fun ω => by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal s hs.1]
      exact hρs ω
    have hh := (Sandpile.Support.brownian_snellValue_superharmonic
      P B hB hBc hBm y S G hGS hgrowS ρ hρ hρS).2
    simpa only [V, S, Real.coe_toNNReal s hs.1] using hh
  have hh := Sandpile.Support.setIntegral_superharmonic_restart_le P B hB hBm hBc
    (T : ℝ) T.coe_nonneg V hVc hsuper x D hDi hD σ τ hσ hτ
    (fun ω => by exact_mod_cast hτT ω) E hE hστ
  have hEm : MeasurableSet E := hσ.measurableSpace_le _ hE
  have heq : (∫ ω in E, (M (τ ω) ω - M (σ ω) ω) ∂P) =
      ∫ ω in E, (V ((T : ℝ) - τ ω) (B x (τ ω) ω) -
        V ((T : ℝ) - σ ω) (B x (σ ω) ω)) ∂P := by
    apply setIntegral_congr_fun hEm
    intro ω hω
    change M (τ ω) ω - M (σ ω) ω = V ((T : ℝ) - τ ω) (B x (τ ω) ω) -
      V ((T : ℝ) - σ ω) (B x (σ ω) ω)
    rw [hMval (τ ω) (hτT ω) ω, hMval (σ ω) ((hστ ω hω).trans (hτT ω)) ω]
  rw [heq]
  exact hh
