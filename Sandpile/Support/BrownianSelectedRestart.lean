import Sandpile.Support.BrownianContinuationRestart

/-!
# Restarting a selected Brownian continuation

A countable family of bounded path rules can be selected using information at
a stopping time and integrated against a fresh centred Brownian path.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- Strong Markov integration for a continuation selected by a countable label
known at the stopping time. -/
theorem Sandpile.Support.setIntegral_brownian_selected_continuation
    {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {d : ℕ}
    [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    (x : Sandpile.Continuum.Space d)
    (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (W : ℝ≥0 → Ω' → Sandpile.Continuum.Space d)
    (hB : Sandpile.Continuum.IsBrownian d x B P)
    (hW : Sandpile.Continuum.IsBrownian d 0 W P')
    (hBm : ∀ t, StronglyMeasurable (B t)) (hWm : ∀ t, StronglyMeasurable (W t))
    (hBc : ∀ ω, Continuous fun t => B t ω) (hWc : ∀ ω, Continuous fun t => W t ω)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (LatticeProb.natFiltration B hBm) (fun ω => (τ ω : ℝ≥0∞)))
    (E : Set Ω) (hE : MeasurableSet[hτ.measurableSpace] E)
    (j : Ω → ι) (hj : Measurable[hτ.measurableSpace] j)
    (L : ℝ≥0) (H : ι → ℝ≥0) (hHL : ∀ i, H i ≤ L)
    (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hG : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (L : ℝ) ×ˢ Set.univ))
    (z : ι → Sandpile.Continuum.Space d)
    (θ : ι → (ℝ≥0 → Sandpile.Continuum.Space d) → ℝ≥0)
    (hθ : ∀ i, IsStoppingTime (LatticeProb.natFiltration
      (fun t (p : ℝ≥0 → Sandpile.Continuum.Space d) => p t)
      (fun t => (measurable_pi_apply t).stronglyMeasurable))
      (fun p => (θ i p : ℝ≥0∞))) (hθH : ∀ i p, θ i p ≤ H i)
    (hint : Integrable (fun ω =>
      G ((H (j ω) : ℝ) - θ (j ω) (fun t => z (j ω) + (B (τ ω + t) ω - B (τ ω) ω)))
        (B (τ ω) ω + (B (τ ω + θ (j ω)
          (fun t => z (j ω) + (B (τ ω + t) ω - B (τ ω) ω))) ω - B (τ ω) ω)))
      (P.restrict E)) :
    (∫ ω in E,
      G ((H (j ω) : ℝ) - θ (j ω) (fun t => z (j ω) + (B (τ ω + t) ω - B (τ ω) ω)))
        (B (τ ω) ω + (B (τ ω + θ (j ω)
          (fun t => z (j ω) + (B (τ ω + t) ω - B (τ ω) ω))) ω - B (τ ω) ω)) ∂P) =
    ∫ ω in E, (∫ ω', G ((H (j ω) : ℝ) - θ (j ω) (fun t => z (j ω) + W t ω'))
      (B (τ ω) ω + W (θ (j ω) (fun t => z (j ω) + W t ω')) ω') ∂P') ∂P := by
  let A := Sandpile.Continuum.Space d
  let Path := LatticeProb.BrownianPath d
  let F : (A × ι) × Path → ℝ := fun q =>
    G ((H q.1.2 : ℝ) - θ q.1.2 (fun t => z q.1.2 + q.2 t))
      (q.1.1 + q.2 (θ q.1.2 (fun t => z q.1.2 + q.2 t)))
  have hGi : ∀ i, ContinuousOn (fun p : ℝ × A => G p.1 p.2)
      (Set.Icc 0 (H i : ℝ) ×ˢ Set.univ) := fun i => hG.mono (by
    intro p hp
    exact ⟨⟨hp.1.1, hp.1.2.trans (by exact_mod_cast hHL i)⟩, hp.2⟩)
  have hF0 : Measurable (fun q : (A × Path) × ι =>
      G ((H q.2 : ℝ) - θ q.2 (fun t => z q.2 + q.1.2 t))
        (q.1.1 + q.1.2 (θ q.2 (fun t => z q.2 + q.1.2 t)))) :=
    measurable_from_prod_countable_left fun i =>
      Sandpile.Support.measurable_continuation_payoff (H i) G (hGi i) (z i) (θ i) (hθ i) (hθH i)
  have hF : Measurable F := hF0.comp
    (((measurable_fst.fst).prodMk measurable_snd).prodMk measurable_fst.snd)
  let Y : Ω → A × ι := fun ω => (B (τ ω) ω, j ω)
  have hY : Measurable[hτ.measurableSpace] Y :=
    (Sandpile.Support.measurable_brownian_stopped_position B hBm hBc τ hτ).prodMk hj
  have hFi : Integrable (fun ω => F (Y ω, LatticeProb.restartPath B hBc τ ω)) (P.restrict E) := hint
  change (∫ ω in E, F (Y ω, LatticeProb.restartPath B hBc τ ω) ∂P) =
    ∫ ω in E, (∫ ω', F (Y ω, (⟨fun t => W t ω', hWc ω'⟩ : Path)) ∂P') ∂P
  rw [hB.toIsBrownianSpace.setIntegral_restart_canonical P x B hBm hBc τ hτ Y hY E hE F hF hFi]
  have hlaw := Sandpile.Support.brownian_centered_path_law_eq_zero_start P P' x B W hB hW hBc hWc
  have hpath : Measurable (fun ω => (⟨fun t => W t ω, hWc ω⟩ : Path)) :=
    ContinuousMap.measurable_iff_eval.mpr fun t => (hWm t).measurable
  congr 1
  funext ω
  rw [hlaw]
  have hF' : Measurable (fun w : Path => F (Y ω, w)) :=
    hF.comp (measurable_const.prodMk measurable_id)
  exact integral_map hpath.aemeasurable hF'.aestronglyMeasurable

/-- A countable family of bounded continuation payoffs is jointly measurable
in the starting position, rule label and future path. -/
theorem Sandpile.Support.measurable_selected_continuation_payoff
    {ι : Type*} {d : ℕ} [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (L : ℝ≥0) (H : ι → ℝ≥0) (hHL : ∀ i, H i ≤ L)
    (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hG : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (L : ℝ) ×ˢ Set.univ))
    (z : ι → Sandpile.Continuum.Space d)
    (θ : ι → (ℝ≥0 → Sandpile.Continuum.Space d) → ℝ≥0)
    (hθ : ∀ i, IsStoppingTime (LatticeProb.natFiltration
      (fun t (p : ℝ≥0 → Sandpile.Continuum.Space d) => p t)
      (fun t => (measurable_pi_apply t).stronglyMeasurable))
      (fun p => (θ i p : ℝ≥0∞))) (hθH : ∀ i p, θ i p ≤ H i) :
    Measurable (fun q : (Sandpile.Continuum.Space d × ι) × LatticeProb.BrownianPath d =>
      G ((H q.1.2 : ℝ) - θ q.1.2 (fun t => z q.1.2 + q.2 t))
        (q.1.1 + q.2 (θ q.1.2 (fun t => z q.1.2 + q.2 t)))) := by
  let A := Sandpile.Continuum.Space d
  let Path := LatticeProb.BrownianPath d
  have hGi : ∀ i, ContinuousOn (fun p : ℝ × A => G p.1 p.2)
      (Set.Icc 0 (H i : ℝ) ×ˢ Set.univ) := fun i => hG.mono (by
    intro p hp
    exact ⟨⟨hp.1.1, hp.1.2.trans (by exact_mod_cast hHL i)⟩, hp.2⟩)
  have hF : Measurable (fun q : (A × Path) × ι =>
      G ((H q.2 : ℝ) - θ q.2 (fun t => z q.2 + q.1.2 t))
        (q.1.1 + q.1.2 (θ q.2 (fun t => z q.2 + q.1.2 t)))) :=
    measurable_from_prod_countable_left fun i =>
      Sandpile.Support.measurable_continuation_payoff (H i) G (hGi i) (z i) (θ i) (hθ i) (hθH i)
  exact hF.comp (((measurable_fst.fst).prodMk measurable_snd).prodMk measurable_fst.snd)
