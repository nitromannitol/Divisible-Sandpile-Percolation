import Sandpile.External.Stopping.BoundedObservationConvergence
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Conditional predictors from converging observations

For almost surely converging observations in a second-countable metric space,
conditional predictions of any event measurable in the limit observation
converge in probability to that event's indicator.
-/

open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace Sandpile.External.Stopping

/-- Converging observations give asymptotically accurate conditional
predictions for every Borel event of the limit observation. -/
theorem tendstoInMeasure_condExp_indicator_of_ae_observations
    {Ω E : Type*} [m : MeasurableSpace Ω] [MetricSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : ℕ → MeasurableSpace Ω) (hF : ∀ n, F n ≤ m)
    (Y : Ω → E) (Yn : ℕ → Ω → E) (hY : Measurable Y)
    (hYn : ∀ n, @Measurable Ω E (F n) inferInstance (Yn n))
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => Yn n ω) atTop (𝓝 (Y ω)))
    (S : Set E) (hS : MeasurableSet S) :
    TendstoInMeasure P (fun n => P[((Y ⁻¹' S).indicator (fun _ => (1 : ℝ))) | F n]) atTop
      ((Y ⁻¹' S).indicator (fun _ => (1 : ℝ))) := by
  let A := Y ⁻¹' S
  let f : Ω → ℝ := A.indicator (fun _ => 1)
  have hA : MeasurableSet A := hY hS
  have hf : Integrable f P := (integrable_const (1 : ℝ)).indicator hA
  apply tendstoInMeasure_condExp_of_eventual_l1_density P F hF f hf
  intro ε hε
  have hhalf : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  let Q : Measure E := P.map Y
  let : IsProbabilityMeasure Q := (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).2 inferInstance
  have hi : Integrable (S.indicator (fun _ => (1 : ℝ))) Q := (integrable_const (1 : ℝ)).indicator hS
  obtain ⟨φ, hφ, _⟩ := (memLp_one_iff_integrable.2 hi).exists_boundedContinuous_eLpNorm_sub_le
    ENNReal.one_ne_top hhalf.ne'
  let g : ℕ → Ω → ℝ := fun n ω => φ (Yn n ω)
  have hgm : ∀ n, StronglyMeasurable[F n] (g n) := by
    intro n
    exact (φ.continuous.measurable.comp (hYn n)).stronglyMeasurable
  have hg : ∀ n, Integrable (g n) P := by
    intro n
    have hm : Measurable (g n) := (hgm n).measurable.mono (hF n) le_rfl
    exact (integrable_const ‖φ‖).mono' hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by simpa using φ.norm_coe_le_norm (Yn n ω))
  have hy : eLpNorm (f - (fun ω => φ (Y ω))) 1 P ≤ ε / 2 := by
    have hm : AEStronglyMeasurable ((S.indicator (fun _ => (1 : ℝ))) - (φ : E → ℝ)) Q :=
      (hi.sub (by
        exact (integrable_const ‖φ‖).mono' φ.continuous.measurable.aestronglyMeasurable
          (Filter.Eventually.of_forall fun z => by simpa using φ.norm_coe_le_norm z))).aestronglyMeasurable
    have heq := eLpNorm_map_measure (p := 1) hm hY.aemeasurable
    have hfun : ((S.indicator (fun _ => (1 : ℝ))) - (φ : E → ℝ)) ∘ Y =
        f - (fun ω => φ (Y ω)) := by
      funext ω
      by_cases hω : Y ω ∈ S <;> simp [f, A, hω]
    rw [hfun] at heq
    rw [← heq]
    exact hφ
  have hcomp := tendsto_eLpNorm_boundedContinuous_comp_of_ae P Y Yn hY
    (fun n => (hYn n).mono (hF n) le_rfl) hconv φ
  have hcomp' : ∀ᶠ n in atTop,
      eLpNorm ((fun ω => φ (Yn n ω)) - (fun ω => φ (Y ω))) 1 P ≤ ε / 2 :=
    ENNReal.tendsto_nhds_zero.1 hcomp _ hhalf
  refine ⟨g, hg, hgm, ?_⟩
  filter_upwards [hcomp'] with n hn
  have hsplit : f - g n = (f - (fun ω => φ (Y ω))) +
      ((fun ω => φ (Y ω)) - g n) := by
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  calc
    eLpNorm (f - g n) 1 P = eLpNorm ((f - (fun ω => φ (Y ω))) +
        ((fun ω => φ (Y ω)) - g n)) 1 P := congrArg (fun h => eLpNorm h 1 P) hsplit
    _ ≤ eLpNorm (f - (fun ω => φ (Y ω))) 1 P +
        eLpNorm ((fun ω => φ (Y ω)) - g n) 1 P := eLpNorm_add_le (p := 1) le_rfl
    _ ≤ ε / 2 + ε / 2 := by
      apply add_le_add hy
      rw [eLpNorm_sub_comm]
      exact hn
    _ = ε := ENNReal.add_halves ε

end Sandpile.External.Stopping
