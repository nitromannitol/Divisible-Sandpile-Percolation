import Sandpile.Support.BrownianContinuationRestart

/-!
# Integrability after Brownian restart

An integrable functional of the stopped past and restarted path remains
integrable after the restarted path is averaged out.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- Averaging an integrable restarted functional against a zero-start Brownian
path gives an integrable function of the stopped past. -/
theorem Sandpile.Support.integrable_brownian_restart_average
    {Ω Ω' α : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace α] {d : ℕ}
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
    (Y : Ω → α) (hY : Measurable[hτ.measurableSpace] Y)
    (F : α × LatticeProb.BrownianPath d → ℝ) (hF : Measurable F)
    (hFi : Integrable (fun ω => F (Y ω, LatticeProb.restartPath B hBc τ ω)) (P.restrict E)) :
    Integrable (fun ω => ∫ ω', F (Y ω, (⟨fun t => W t ω', hWc ω'⟩ : LatticeProb.BrownianPath d)) ∂P')
      (P.restrict E) := by
  have hτm : Measurable τ := LatticeProb.measurable_of_isStoppingTime hτ
  have hRm := LatticeProb.measurable_restartPath hBm hBc hτm
  have hYm : Measurable Y := hY.mono hτ.measurableSpace_le le_rfl
  have hpair : Measurable fun ω => (Y ω, LatticeProb.restartPath B hBc τ ω) := hYm.prodMk hRm
  have hlaw := hB.toIsBrownianSpace.map_prod_restartPath hBm hBc hτ hY hE
  have hint : Integrable F
      (((P.restrict E).map Y).prod (P.map (LatticeProb.restartPath B hBc fun _ => 0))) := by
    rw [← hlaw]
    exact (integrable_map_measure hF.aestronglyMeasurable hpair.aemeasurable).2 hFi
  have hG := hint.integral_prod_left
  have hGm : AEStronglyMeasurable
      (fun y : α => ∫ w, F (y, w) ∂(P.map (LatticeProb.restartPath B hBc fun _ => 0)))
      ((P.restrict E).map Y) := hG.aestronglyMeasurable
  have hGi := (integrable_map_measure hGm hYm.aemeasurable).1 hG
  have hpath : Measurable (fun ω => (⟨fun t => W t ω, hWc ω⟩ : LatticeProb.BrownianPath d)) :=
    ContinuousMap.measurable_iff_eval.mpr fun t => (hWm t).measurable
  have hlaw0 := Sandpile.Support.brownian_centered_path_law_eq_zero_start P P' x B W hB hW hBc hWc
  have heq : (fun ω => ∫ w, F (Y ω, w) ∂(P.map (LatticeProb.restartPath B hBc fun _ => 0))) =
      fun ω => ∫ ω', F (Y ω, (⟨fun t => W t ω', hWc ω'⟩ : LatticeProb.BrownianPath d)) ∂P' := by
    funext ω
    rw [hlaw0]
    exact integral_map hpath.aemeasurable (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  change Integrable (fun ω => ∫ w, F (Y ω, w) ∂(P.map (LatticeProb.restartPath B hBc fun _ => 0)))
    (P.restrict E) at hGi
  rwa [heq] at hGi
