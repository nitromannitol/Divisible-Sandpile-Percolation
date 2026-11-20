import Sandpile.External.ContinuumOptimalStopping
import Sandpile.Support.AugmentedStoppingPayoff
import Sandpile.Support.StopMeasurable

/-!
# Brownian stopping values under augmentation

A continuous reward with an integrable path bound has the same value in the raw
natural filtration and in its usual augmentation.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Continuous finite-horizon rewards have continuous paths and measurable
stopped payoffs for a process with continuous paths and measurable slices. -/
theorem Sandpile.Support.brownian_stopping_reward_regular
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (hBc : ∀ ω, Continuous fun t => B t ω)
    (hBm : ∀ t, StronglyMeasurable (B t))
    (T : ℝ≥0) (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hG : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (T : ℝ) ×ˢ Set.univ)) :
    (∀ ω, ContinuousOn (fun t : ℝ≥0 => G ((T : ℝ) - t) (B t ω)) (Set.Icc 0 T)) ∧
    (∀ σ : Ω → ℝ≥0, IsStoppingTime (LatticeProb.natFiltration B hBm)
      (fun ω => (σ ω : ℝ≥0∞)) → (∀ ω, σ ω ≤ T) →
      AEStronglyMeasurable (fun ω => G ((T : ℝ) - σ ω) (B (σ ω) ω)) P) := by
  let 𝓕 := LatticeProb.natFiltration B hBm
  let R : ℝ≥0 → Ω → ℝ := fun t ω => G ((T : ℝ) - t) (B t ω)
  have hRcont : ∀ ω, ContinuousOn (fun t => R t ω) (Set.Icc 0 T) := by
    intro ω
    change ContinuousOn ((fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2) ∘
      fun t : ℝ≥0 => ((T : ℝ) - (t : ℝ), B t ω)) (Set.Icc 0 T)
    apply hG.comp
    · exact ((continuous_const.sub continuous_subtype_val).prodMk (hBc ω)).continuousOn
    · intro t ht
      refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
      · exact sub_nonneg.mpr (by exact_mod_cast ht.2)
      · exact sub_le_self _ t.coe_nonneg
  let Gext : ℝ × Sandpile.Continuum.Space d → ℝ :=
    fun p => G (max 0 (min (T : ℝ) p.1)) p.2
  have hGext : Continuous Gext := by
    change Continuous ((fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2) ∘
      fun p : ℝ × Sandpile.Continuum.Space d => (max 0 (min (T : ℝ) p.1), p.2))
    apply hG.comp_continuous
    · exact ((continuous_const.max (continuous_const.min continuous_fst)).prodMk continuous_snd)
    · intro p
      refine ⟨⟨le_max_left _ _, ?_⟩, Set.mem_univ _⟩
      exact max_le T.coe_nonneg (min_le_left _ _)
  have hmeas : ∀ σ : Ω → ℝ≥0,
      IsStoppingTime 𝓕 (fun ω => (σ ω : ℝ≥0∞)) → (∀ ω, σ ω ≤ T) →
      AEStronglyMeasurable (fun ω => R (σ ω) ω) P := by
    intro σ hσ hσT
    have hσ' : Sandpile.Continuum.IsBrownianStopping B σ :=
      (Sandpile.Continuum.isBrownianStopping_iff_natFiltration B hBm σ).mpr hσ
    have hσm : Measurable σ := hσ'.measurable hBm
    have hposm : Measurable (fun ω => B (σ ω) ω) :=
      Sandpile.Continuum.measurable_stopped_position (fun t => (hBm t).measurable) hBc hσm
    have hm : Measurable (fun ω => Gext ((T : ℝ) - (σ ω : ℝ), B (σ ω) ω)) :=
      hGext.measurable.comp ((measurable_const.sub (measurable_coe_nnreal_real.comp hσm)).prodMk hposm)
    have heq : (fun ω => Gext ((T : ℝ) - (σ ω : ℝ), B (σ ω) ω)) =
        fun ω => R (σ ω) ω := by
      funext ω
      dsimp [Gext, R]
      have h0 : (0 : ℝ) ≤ (T : ℝ) - (σ ω : ℝ) := sub_nonneg.mpr (by exact_mod_cast hσT ω)
      have hT : (T : ℝ) - (σ ω : ℝ) ≤ (T : ℝ) := sub_le_self _ (σ ω).coe_nonneg
      rw [min_eq_right hT, max_eq_right h0]
    rw [← heq]
    exact hm.stronglyMeasurable.aestronglyMeasurable
  exact ⟨hRcont, hmeas⟩

/-- The natural-filtration Brownian stopping value agrees with its augmented
filtration value when the reward has an integrable path bound. -/
theorem Sandpile.Support.snellValue_eq_sSup_usualAugmentation_of_integrable_bound
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (hBc : ∀ ω, Continuous fun t => B t ω)
    (hBm : ∀ t, StronglyMeasurable (B t))
    (T : ℝ≥0) (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hG : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (T : ℝ) ×ˢ Set.univ))
    (bound : Ω → ℝ) (hint : Integrable bound P)
    (hbound : ∀ᵐ ω ∂P, ∀ t ≤ T, ‖G ((T : ℝ) - t) (B t ω)‖ ≤ bound ω) :
    Sandpile.External.Snell.snellValue B P G T =
    sSup {a : ℝ | ∃ σ : Ω → ℝ≥0,
      IsStoppingTime (Sandpile.Support.aeCompletedFiltration P
        (LatticeProb.natFiltration B hBm)).rightCont (fun ω => (σ ω : ℝ≥0∞)) ∧
      (∀ ω, σ ω ≤ T) ∧ a = ∫ ω, G ((T : ℝ) - σ ω) (B (σ ω) ω) ∂P} := by
  let 𝓕 := LatticeProb.natFiltration B hBm
  let R : ℝ≥0 → Ω → ℝ := fun t ω => G ((T : ℝ) - t) (B t ω)
  obtain ⟨hRcont, hmeas⟩ :=
    Sandpile.Support.brownian_stopping_reward_regular P B hBc hBm T G hG
  have hh := Sandpile.Support.sSup_stopping_payoffs_eq_usualAugmentation
    P 𝓕 T R bound (ae_of_all _ hRcont) hint hbound hmeas
  change sSup {a : ℝ | ∃ σ : Ω → ℝ≥0,
      Sandpile.Continuum.IsBrownianStopping B σ ∧ (∀ ω, (σ ω : ℝ) ≤ (T : ℝ)) ∧
      a = ∫ ω, G ((T : ℝ) - σ ω) (B (σ ω) ω) ∂P} = _
  convert hh using 1
  congr 1
