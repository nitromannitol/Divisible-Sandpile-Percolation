/-
The joint law of a Brownian stopping time, its stopped position, and the
restarted path. This supplies the product measure used in occupation integrals.
-/
import Sandpile.Continuum.Stopping
import LatticeProb.Prob.BrownianRestartIntegral

open MeasureTheory ProbabilityTheory Filter Topology LatticeProb
open scoped ENNReal NNReal
open Sandpile.Continuum

namespace Sandpile.Support

/-- The stopped time and position are measurable in the natural stopping-time
sigma-algebra. -/
theorem measurable_brownian_stopped_state {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (B : ℝ≥0 → Ω → Space d) (hm : ∀ t, StronglyMeasurable (B t))
    (hc : ∀ ω, Continuous fun t => B t ω) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (natFiltration B hm) fun ω => (τ ω : ℝ≥0∞)) :
    Measurable[hτ.measurableSpace] (fun ω => (τ ω, B (τ ω) ω)) := by
  have ht : Measurable[hτ.measurableSpace] τ := by
    simpa using hτ.measurable.ennreal_toNNReal
  have hx : Measurable[hτ.measurableSpace] (fun ω => B (τ ω) ω) := by
    have h := measurable_stoppedValue
      ((stronglyAdapted_natFiltration B hm).isStronglyProgressive_of_continuous hc) hτ
    convert h using 1
    funext ω
    rfl
  exact ht.prodMk hx

/-- At any Brownian stopping time, the stopped state and the future increments
have the product of the stopped-state law and the centred Brownian path law. -/
theorem map_brownian_stopped_state_restart {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P] {x : Space d}
    {B : ℝ≥0 → Ω → Space d} (hB : IsBrownian d x B P)
    (hm : ∀ t, StronglyMeasurable (B t)) (hc : ∀ ω, Continuous fun t => B t ω)
    (τ : Ω → ℝ≥0) (hτ : IsBrownianStopping B τ) :
    P.map (fun ω => ((τ ω, B (τ ω) ω), fun t => B (τ ω + t) ω - B (τ ω) ω)) =
      (P.map (fun ω => (τ ω, B (τ ω) ω))).prod
        (P.map (fun ω (t : ℝ≥0) => B t ω - B 0 ω)) := by
  have ht := (isBrownianStopping_iff_natFiltration B hm τ).1 hτ
  have hspace : LatticeProb.IsBrownianSpace d x B P := ⟨hB.start, hB.coord, hB.indep⟩
  have hrestart := hspace.hasStrongMarkovRestart hm hc
  have hs := measurable_shift_apply hm hc (measurable_of_isStoppingTime ht)
  have hs0 : Measurable fun ω (t : ℝ≥0) => B t ω - B 0 ω :=
    measurable_pi_lambda _ fun t => (hm t).measurable.sub (hm 0).measurable
  simpa only [Measure.restrict_univ] using hrestart.map_prod ht hs hs0
    (measurable_brownian_stopped_state B hm hc τ ht) MeasurableSet.univ

/-- The expected bounded reward a fixed time after stopping is obtained by
integrating a fresh Brownian increment against the stopped state. -/
theorem integral_brownian_after_stopping {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P] {x : Space d}
    {B : ℝ≥0 → Ω → Space d} (hB : IsBrownian d x B P)
    (hm : ∀ t, StronglyMeasurable (B t)) (hc : ∀ ω, Continuous fun t => B t ω)
    (τ : Ω → ℝ≥0) (hτ : IsBrownianStopping B τ) (r : ℝ≥0)
    (F : (ℝ≥0 × Space d) × Space d → ℝ) (hF : Measurable F)
    (C : ℝ) (hbound : ∀ p, ‖F p‖ ≤ C) :
    (∫ ω, F ((τ ω, B (τ ω) ω), B (τ ω + r) ω) ∂P) =
      ∫ ω, (∫ η, F ((τ ω, B (τ ω) ω), B (τ ω) ω + (B r η - B 0 η)) ∂P) ∂P := by
  have ht := (isBrownianStopping_iff_natFiltration B hm τ).1 hτ
  have hspace : LatticeProb.IsBrownianSpace d x B P := ⟨hB.start, hB.coord, hB.indep⟩
  have hrestart := hspace.hasStrongMarkovRestart hm hc
  have hs := measurable_shift_apply hm hc (measurable_of_isStoppingTime ht)
  have hs0 : Measurable fun ω (t : ℝ≥0) => B t ω - B 0 ω :=
    measurable_pi_lambda _ fun t => (hm t).measurable.sub (hm 0).measurable
  let G : (ℝ≥0 × Space d) × (ℝ≥0 → Space d) → ℝ :=
    fun p => F (p.1, p.1.2 + p.2 r)
  have hG : Measurable G := hF.comp (measurable_fst.prodMk
    ((measurable_snd.comp measurable_fst).add ((measurable_pi_apply r).comp measurable_snd)))
  have he := hrestart.setIntegral_restart ht hs hs0
    (measurable_brownian_stopped_state B hm hc τ ht) MeasurableSet.univ
    hG (fun p => hbound _)
  have hmap (y : ℝ≥0 × Space d) :
      (∫ z, G (y, z) ∂(P.map fun ω (t : ℝ≥0) => B t ω - B 0 ω)) =
        ∫ η, F (y, y.2 + (B r η - B 0 η)) ∂P :=
    integral_map hs0.aemeasurable
      ((hG.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  simpa only [Measure.restrict_univ, hmap, G, add_sub_cancel] using he

end Sandpile.Support
