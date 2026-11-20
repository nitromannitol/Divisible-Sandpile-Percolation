import Sandpile.Support.BrownianValueStoppedComparison
import Sandpile.Support.VanishingGapEvents
import Sandpile.Support.StoppedMinSmallEvent

/-!
# Approximate Brownian contact optimality

Near-optimal stopping times have vanishing value-reward gaps. They therefore
rarely precede a fixed approximate contact time, which preserves the expected
value by the stopped supermartingale comparison.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- A bounded first ε-contact preserves the expectation of the Brownian value
process for every positive ε. -/
theorem Sandpile.Support.brownian_value_integral_eq_at_approx_contact
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
    (M : ℝ≥0 → Ω → ℝ) (hMm : ∀ s, Measurable (M s))
    (hMc : ∀ ω, Continuous fun s => M s ω)
    (hMval : ∀ s ≤ T, ∀ ω, M s ω =
      Sandpile.External.Snell.snellValue (B (B x s ω)) P G ((T : ℝ) - s))
    (hMdom : ∀ s ≤ T, ∀ ω, G ((T : ℝ) - s) (B x s ω) ≤ M s ω)
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (LatticeProb.natFiltration (B x) (hBm x))
      (fun ω => (σ ω : ℝ≥0∞)))
    (ε : ℝ) (hε : 0 < ε)
    (hσfirst : ∀ ω, IsLeast {s : ℝ≥0 | s ≤ T ∧
      M s ω - G ((T : ℝ) - s) (B x s ω) ≤ ε} (σ ω)) :
    (∫ ω, M (σ ω) ω ∂P) = Sandpile.External.Snell.snellValue (B x) P G T := by
  let 𝓕 := LatticeProb.natFiltration (B x) (hBm x)
  let R : ℝ≥0 → Ω → ℝ := fun s ω => G ((T : ℝ) - s) (B x s ω)
  let v : ℝ := Sandpile.External.Snell.snellValue (B x) P G T
  have hσT : ∀ ω, σ ω ≤ T := fun ω => (hσfirst ω).1.1
  have hσm : Measurable σ := LatticeProb.measurable_of_isStoppingTime hσ
  obtain ⟨D, hDi, hD, hMint⟩ := Sandpile.Support.exists_integrable_brownian_value_process_bound
    P B hB hBc hBm x T G hG hgrow M hMm hMc hMval
  obtain ⟨hRint, hbd⟩ := Sandpile.Support.brownian_stopping_payoffs_integrable_and_bddAbove
    x P (B x) (hB x) (hBm x) (hBc x) T G hG hgrow
  have hne : (Sandpile.External.Snell.attainable (B x) P G T).Nonempty := by
    refine ⟨∫ ω, G T (B x 0 ω) ∂P, (fun _ => 0),
      Sandpile.Continuum.isBrownianStopping_const (B x) 0, ?_, ?_⟩
    · intro ω
      exact T.coe_nonneg
    · simp only [NNReal.coe_zero, sub_zero]
  let δ : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hδpos : ∀ n, 0 < δ n := fun n => by dsimp [δ]; positivity
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    dsimp [δ]
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hex : ∀ n, ∃ τ : Ω → ℝ≥0,
      Sandpile.Continuum.IsBrownianStopping (B x) τ ∧ (∀ ω, τ ω ≤ T) ∧
      v - δ n < ∫ ω, R (τ ω) ω ∂P := by
    intro n
    have hlt : v - δ n < sSup (Sandpile.External.Snell.attainable (B x) P G T) := by
      change v - δ n < v
      linarith [hδpos n]
    obtain ⟨a, ⟨τ, hτ, hτT, rfl⟩, ha⟩ := (lt_csSup_iff hbd hne).mp hlt
    exact ⟨τ, hτ, (fun ω => by exact_mod_cast hτT ω), ha⟩
  choose τ hτ hτT hnear using hex
  have hτm : ∀ n, Measurable (τ n) := fun n => (hτ n).measurable (hBm x)
  have hMi : ∀ n, Integrable (fun ω => M (τ n ω) ω) P := fun n => hMint (τ n) (hτm n) (hτT n)
  have hRi : ∀ n, Integrable (fun ω => R (τ n ω) ω) P := fun n => hRint (τ n) (hτ n) (hτT n)
  have hpayle : ∀ n, (∫ ω, R (τ n ω) ω ∂P) ≤ v := fun n =>
    le_csSup hbd ⟨τ n, hτ n, (fun ω => by exact_mod_cast hτT n ω), rfl⟩
  have hpaylim : Tendsto (fun n => ∫ ω, R (τ n ω) ω ∂P) atTop (𝓝 v) := by
    have hleft : Tendsto (fun n => v - δ n) atTop (𝓝 v) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub hδlim
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hleft tendsto_const_nhds
      (fun n => (hnear n).le) hpayle
  let gap : ℕ → Ω → ℝ := fun n ω => M (τ n ω) ω - R (τ n ω) ω
  have hgi : ∀ n, Integrable (gap n) P := fun n => (hMi n).sub (hRi n)
  have hgn : ∀ n ω, 0 ≤ gap n ω := fun n ω => sub_nonneg.mpr (hMdom (τ n ω) (hτT n ω) ω)
  have hgup : ∀ n, (∫ ω, gap n ω ∂P) ≤ v - ∫ ω, R (τ n ω) ω ∂P := by
    intro n
    rw [show gap n = (fun ω => M (τ n ω) ω - R (τ n ω) ω) from rfl,
      integral_sub (hMi n) (hRi n)]
    have hu := (Sandpile.Support.brownian_stopped_value_expectation_bound
      P B hB hBc hBm x T G hG hgrow M hMm hMc hMval (τ n) (hτ n) (hτT n)).2
    linarith
  have hglim : Tendsto (fun n => ∫ ω, gap n ω ∂P) atTop (𝓝 0) := by
    have hright : Tendsto (fun n => v - ∫ ω, R (τ n ω) ω ∂P) atTop (𝓝 0) := by
      simpa only [sub_self] using (tendsto_const_nhds (x := v)).sub hpaylim
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hright
      (fun n => integral_nonneg (hgn n)) hgup
  have hsmall : Tendsto (fun n => P {ω | τ n ω < σ ω}) atTop (𝓝 0) := by
    apply Sandpile.Support.tendsto_measure_of_gap_lower_bound P gap hgi hgn hglim
      (fun n => {ω | τ n ω < σ ω}) ε hε
    intro n ω hlt
    have hn : ¬gap n ω ≤ ε := by
      intro hh
      have hl := (hσfirst ω).2 ⟨hτT n ω, hh⟩
      exact not_le_of_gt hlt hl
    exact (le_of_lt (lt_of_not_ge hn))
  have hminlim := Sandpile.Support.tendsto_integral_stopped_min_of_small_events
    P M (fun s => (hMm s).stronglyMeasurable) hMc T D hDi hD σ hσm hσT τ hτm hsmall
  have hcompare : ∀ n, (∫ ω, R (τ n ω) ω ∂P) ≤
      ∫ ω, M (min (σ ω) (τ n ω)) ω ∂P := by
    intro n
    let ρ : Ω → ℝ≥0 := fun ω => min (σ ω) (τ n ω)
    have hρ : IsStoppingTime 𝓕 (fun ω => ((ρ ω : ℝ≥0) : WithTop ℝ≥0)) := by
      have hσ' : IsStoppingTime 𝓕 (fun ω => ((σ ω : ℝ≥0) : WithTop ℝ≥0)) := hσ
      have hτ' : IsStoppingTime 𝓕 (fun ω => ((τ n ω : ℝ≥0) : WithTop ℝ≥0)) := hτ n
      have hh := hσ'.min hτ'
      rw [show (fun ω => min ((σ ω : ℝ≥0) : WithTop ℝ≥0) ((τ n ω : ℝ≥0) : WithTop ℝ≥0)) =
        (fun ω => ((ρ ω : ℝ≥0) : WithTop ℝ≥0)) from funext fun ω => (WithTop.coe_min _ _).symm] at hh
      exact hh
    have hτstop : IsStoppingTime 𝓕 (fun ω => (τ n ω : ℝ≥0∞)) := hτ n
    have hh := Sandpile.Support.setIntegral_brownian_value_stopped_le
      P B hB hBc hBm x T G hG hgrow M hMval ρ (τ n) hρ hτstop (hτT n)
      Set.univ (@MeasurableSet.univ Ω hρ.measurableSpace) (fun ω _ => min_le_right _ _)
    have hρi : Integrable (fun ω => M (ρ ω) ω) P :=
      hMint ρ (hσm.min (hτm n)) (fun ω => (min_le_left _ _).trans (hσT ω))
    simp only [Measure.restrict_univ] at hh
    rw [integral_sub (hMi n) hρi] at hh
    have hg : (∫ ω, R (τ n ω) ω ∂P) ≤ ∫ ω, M (τ n ω) ω ∂P :=
      integral_mono (hRi n) (hMi n) (fun ω => hMdom (τ n ω) (hτT n ω) ω)
    linarith
  have hlower : v ≤ ∫ ω, M (σ ω) ω ∂P :=
    le_of_tendsto_of_tendsto hpaylim hminlim (Eventually.of_forall hcompare)
  have hupper := (Sandpile.Support.brownian_stopped_value_expectation_bound
    P B hB hBc hBm x T G hG hgrow M hMm hMc hMval σ hσ hσT).2
  exact le_antisymm hupper hlower
