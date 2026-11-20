import Sandpile.Support.BrownianContinuationPayoff
import Sandpile.Support.BrownianContinuationAtStopping
import Sandpile.Support.BrownianRestart
import LatticeProb.Prob.BrownianRestartLaw

/-!
# Expected payoff of a restarted Brownian rule

The strong Markov property integrates a bounded continuation rule over the
law of a fresh centred Brownian path.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- A measurable bounded path rule after a Brownian stopping time can be
integrated against the centred path law independently of the stopped position. -/
theorem Sandpile.Support.setIntegral_brownian_continuation_restart
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (x : Sandpile.Continuum.Space d)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (hB : Sandpile.Continuum.IsBrownian d x B P)
    (hBm : ∀ t, StronglyMeasurable (B t)) (hBc : ∀ ω, Continuous fun t => B t ω)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (LatticeProb.natFiltration B hBm) (fun ω => (τ ω : ℝ≥0∞)))
    (E : Set Ω) (hE : MeasurableSet[hτ.measurableSpace] E)
    (H : ℝ≥0) (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hG : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (H : ℝ) ×ˢ Set.univ))
    (z : Sandpile.Continuum.Space d)
    (θ : (ℝ≥0 → Sandpile.Continuum.Space d) → ℝ≥0)
    (hθ : IsStoppingTime (LatticeProb.natFiltration
      (fun t (p : ℝ≥0 → Sandpile.Continuum.Space d) => p t)
      (fun t => (measurable_pi_apply t).stronglyMeasurable))
      (fun p => (θ p : ℝ≥0∞))) (hθH : ∀ p, θ p ≤ H)
    (hint : Integrable (fun ω => G ((H : ℝ) - θ (fun t => z + (B (τ ω + t) ω - B (τ ω) ω)))
      (B (τ ω) ω + (B (τ ω + θ (fun t => z + (B (τ ω + t) ω - B (τ ω) ω))) ω - B (τ ω) ω)))
      (P.restrict E)) :
    (∫ ω in E, G ((H : ℝ) - θ (fun t => z + (B (τ ω + t) ω - B (τ ω) ω)))
      (B (τ ω) ω + (B (τ ω + θ (fun t => z + (B (τ ω + t) ω - B (τ ω) ω))) ω - B (τ ω) ω)) ∂P) =
    ∫ ω in E, (∫ w : LatticeProb.BrownianPath d,
      G ((H : ℝ) - θ (fun t => z + w t)) (B (τ ω) ω + w (θ (fun t => z + w t)))
        ∂(P.map (LatticeProb.restartPath B hBc fun _ => 0))) ∂P := by
  let F : Sandpile.Continuum.Space d × LatticeProb.BrownianPath d → ℝ := fun q =>
    G ((H : ℝ) - θ (fun t => z + q.2 t)) (q.1 + q.2 (θ (fun t => z + q.2 t)))
  have hF : Measurable F := Sandpile.Support.measurable_continuation_payoff H G hG z θ hθ hθH
  have hpos := Sandpile.Support.measurable_brownian_stopped_position B hBm hBc τ hτ
  exact hB.toIsBrownianSpace.setIntegral_restart_canonical P x B hBm hBc τ hτ
    (fun ω => B (τ ω) ω) hpos E hE F hF hint

/-- The centred continuous-path law of a Brownian motion is the path law of
any Brownian motion started at zero. -/
theorem Sandpile.Support.brownian_centered_path_law_eq_zero_start
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    (x : Sandpile.Continuum.Space d)
    (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (W : ℝ≥0 → Ω' → Sandpile.Continuum.Space d)
    (hB : Sandpile.Continuum.IsBrownian d x B P)
    (hW : Sandpile.Continuum.IsBrownian d 0 W P')
    (hBc : ∀ ω, Continuous fun t => B t ω) (hWc : ∀ ω, Continuous fun t => W t ω) :
    P.map (LatticeProb.restartPath B hBc fun _ => 0) =
      P'.map (fun ω => (⟨fun t => W t ω, hWc ω⟩ : LatticeProb.BrownianPath d)) := by
  rw [hB.toIsBrownianSpace.map_restartPath_zero_eq hW.toIsBrownianSpace hBc hWc]
  apply Measure.map_congr
  filter_upwards [hW.start] with ω hω
  ext t : 1
  change W (0 + t) ω - W 0 ω = W t ω
  simp only [zero_add, hω, sub_zero]

/-- Integration of a continuation payoff against the centred path law agrees
with integration along a zero-start Brownian motion. -/
theorem Sandpile.Support.integral_continuation_centered_path_eq_zero_start
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    (x : Sandpile.Continuum.Space d)
    (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (W : ℝ≥0 → Ω' → Sandpile.Continuum.Space d)
    (hB : Sandpile.Continuum.IsBrownian d x B P)
    (hW : Sandpile.Continuum.IsBrownian d 0 W P')
    (hBc : ∀ ω, Continuous fun t => B t ω) (hWc : ∀ ω, Continuous fun t => W t ω)
    (hWm : ∀ t, StronglyMeasurable (W t))
    (H : ℝ≥0) (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hG : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (H : ℝ) ×ˢ Set.univ))
    (y z : Sandpile.Continuum.Space d)
    (θ : (ℝ≥0 → Sandpile.Continuum.Space d) → ℝ≥0)
    (hθ : IsStoppingTime (LatticeProb.natFiltration
      (fun t (p : ℝ≥0 → Sandpile.Continuum.Space d) => p t)
      (fun t => (measurable_pi_apply t).stronglyMeasurable))
      (fun p => (θ p : ℝ≥0∞))) (hθH : ∀ p, θ p ≤ H) :
    (∫ w : LatticeProb.BrownianPath d,
      G ((H : ℝ) - θ (fun t => z + w t)) (y + w (θ (fun t => z + w t)))
        ∂(P.map (LatticeProb.restartPath B hBc fun _ => 0))) =
    ∫ ω, G ((H : ℝ) - θ (fun t => z + W t ω))
      (y + W (θ (fun t => z + W t ω)) ω) ∂P' := by
  rw [Sandpile.Support.brownian_centered_path_law_eq_zero_start P P' x B W hB hW hBc hWc]
  have hpath : Measurable (fun ω => (⟨fun t => W t ω, hWc ω⟩ : LatticeProb.BrownianPath d)) :=
    ContinuousMap.measurable_iff_eval.mpr fun t => (hWm t).measurable
  have hF := Sandpile.Support.measurable_continuation_payoff H G hG z θ hθ hθH
  have hF' : Measurable (fun w : LatticeProb.BrownianPath d =>
      G ((H : ℝ) - θ (fun t => z + w t)) (y + w (θ (fun t => z + w t)))) :=
    hF.comp (measurable_const.prodMk measurable_id)
  exact integral_map hpath.aemeasurable hF'.aestronglyMeasurable
