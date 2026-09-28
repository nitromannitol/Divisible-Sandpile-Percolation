import Mathlib
import Sandpile.Support.LimBallBounds

/-!
# Integrability of a continuous reward at a ball-stopped time

Measurable stopping times evaluate continuous paths measurably. A continuous
reward on the closed time and ball cylinder is integrable at any measurable
stopping time satisfying the horizon and ball constraints almost surely.
-/

open TopologicalSpace
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

/-- Evaluating a jointly continuous-in-time, pointwise-measurable path family at a
measurable stopping time gives a measurable function of the sample point: the
uncurried evaluation map is measurable by joint continuity/measurability, and the
stopping time composes into its first argument. -/
theorem Sandpile.Support.measurable_stopped_evaluation {Ω E : Type*}
    [MeasurableSpace Ω] [TopologicalSpace E] [PseudoMetrizableSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (B : ℝ≥0 → Ω → E) (hcont : ∀ ω, Continuous fun t => B t ω)
    (hm : ∀ t, Measurable (B t)) (τ : Ω → ℝ≥0) (hτ : Measurable τ) :
    Measurable (fun ω => B (τ ω) ω) := by
  exact (measurable_uncurry_of_continuous_of_measurable hcont hm).comp
    (hτ.prodMk measurable_id)

open Sandpile.Continuum

/-- **A continuous reward evaluated at time-to-horizon and the stopped position is
integrable**, given that the stopping time is a.s. bounded by the horizon `T` and the
path stays within distance `A` of its start before stopping: the reward restricted to
the compact cylinder `Icc 0 T ×ˢ closedBall u A` is bounded (`hc` is continuous on a
compact set), the stopped evaluation `(ω ↦ (T - τ ω, B (τ ω) ω))` almost surely lands
in that cylinder, and a bounded measurable function is integrable
(`Integrable.of_bound`). -/
theorem Sandpile.Support.integrable_continuous_ball_reward {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
    (B : ℝ≥0 → Ω → Space d) (hcont : ∀ ω, Continuous fun t => B t ω)
    (hm : ∀ t, Measurable (B t)) (u : Space d) (hstart : ∀ᵐ ω ∂P, B 0 ω = u)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ) {T A : ℝ} (hA : 0 ≤ A)
    (hτT : ∀ᵐ ω ∂P, (τ ω : ℝ) ≤ T)
    (hball : ∀ᵐ ω ∂P, ∀ t < τ ω, ‖B t ω - u‖ ≤ A)
    (h : ℝ → Space d → ℝ)
    (hc : ContinuousOn (fun p : ℝ × Space d => h p.1 p.2)
      (Set.Icc 0 T ×ˢ Metric.closedBall u A)) :
    Integrable (fun ω => h (T - τ ω) (B (τ ω) ω)) P  := by
  classical
  let K : Set (ℝ × Space d) := Set.Icc 0 T ×ˢ Metric.closedBall u A
  let f : ℝ × Space d → ℝ := fun p => h p.1 p.2
  let q : Ω → ℝ × Space d := fun ω => (T - τ ω, B (τ ω) ω)
  have hK : MeasurableSet K := measurableSet_Icc.prod Metric.isClosed_closedBall.measurableSet
  have hqm : Measurable q :=
    (measurable_const.sub (NNReal.continuous_coe.measurable.comp hτ)).prodMk
      (Sandpile.Support.measurable_stopped_evaluation B hcont hm τ hτ)
  have hqK : ∀ᵐ ω ∂P, q ω ∈ K := by
    filter_upwards [hstart, hτT, hball] with ω hω0 hωT hωball
    refine ⟨⟨sub_nonneg.mpr hωT, sub_le_self _ (NNReal.coe_nonneg _)⟩, ?_⟩
    have hp := Sandpile.Support.stopped_position_mem_closedBall (hcont ω) u A (τ ω)
      (by simpa only [hω0, sub_self, norm_zero] using hA) hωball
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hp
  have hfm : Measurable (K.piecewise f (fun _ => 0)) :=
    hc.measurable_piecewise continuous_const.continuousOn hK
  have hme : AEStronglyMeasurable (fun ω => h (T - τ ω) (B (τ ω) ω)) P := by
    apply (hfm.comp hqm).stronglyMeasurable.aestronglyMeasurable.congr
    filter_upwards [hqK] with ω hω
    exact Set.piecewise_eq_of_mem K f (fun _ => 0) hω
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod (isCompact_closedBall u A)).bddAbove_image hc.norm
  apply Integrable.of_bound hme M
  filter_upwards [hqK] with ω hω
  exact hM ⟨q ω, hω, rfl⟩

