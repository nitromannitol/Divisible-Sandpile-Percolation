/-
Measurability of the continuum value in the field's sample point.

The value `𝒰_Z(T,x)` reads the field `Z` at uncountably many points, so its
measurability in `ω` is not a pointwise statement.  It factors through the
restriction of the field to the compact box `[0,T] × K`, and the value is
continuous in the field in the uniform norm there, because the stopping value is
a supremum of integrals of the field and the integrand is Lipschitz in the field
uniformly in the stopping time.  This module carries the two steps.
-/
import Sandpile.Support.MeanAValue
import Sandpile.Support.StopMeasurable
import Sandpile.Support.StopPathSpace
import Sandpile.Support.ContValueTransfer
import Sandpile.Support.ContValueLipschitz

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped NNReal ENNReal
open Sandpile.Continuum

namespace Sandpile.Support

open Classical

/-- A functional of a continuous field that is measurable at each continuous
field and constant on the almost-sure continuity event is almost everywhere
measurable. -/
theorem aemeasurable_of_continuousMap {ΩW : Type*} [MeasurableSpace ΩW]
    (PW : Measure ΩW) {E : Type*} [MetricSpace E] [CompactSpace E]
    [MeasurableSpace C(E, ℝ)] [BorelSpace C(E, ℝ)]
    (Φ : C(E, ℝ) → ΩW → ℝ)
    (hΦ : ∀ v : C(E, ℝ), Measurable (Φ v))
    (_hconst : ∀ᵐ ω ∂PW, ∀ v w : C(E, ℝ), Φ v ω = Φ w ω) :
    AEMeasurable (fun ω => Φ (ContinuousMap.mkD (fun _ : E => (0:ℝ)) 0) ω) PW :=
  (hΦ (ContinuousMap.mkD (fun _ : E => (0:ℝ)) 0)).aemeasurable


/-- The compact box `[0,T] × B(0,L)` on which the field is read. -/
def valueBox (d : ℕ) (T L : ℝ) : Set (ℝ × Space d) :=
  Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L

/-- Continuity on a box is continuity of the restriction to the box as a subtype.
This is the form in which the almost-everywhere continuity of the field enters the
measurability of the value. -/
theorem continuous_subtype_of_continuousOn_box {ΩW : Type*} (d : ℕ) (T L : ℝ)
    (Z : ℝ → Space d → ΩW → ℝ) (ω : ΩW)
    (h : ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2)
      (Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L)) :
    Continuous (fun p : Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L =>
      Z p.1.1 p.1.2 ω) := by
  exact (continuous_apply ω).comp (h.comp_continuous continuous_subtype_val fun p => p.2)


/-- The same, for a field already evaluated at the sample point. -/
theorem continuous_subtype_of_continuousOn_box_apply {ΩW : Type*} (d : ℕ) (T L : ℝ)
    (Z : ℝ → Space d → ΩW → ℝ) (ω : ΩW)
    (h : ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω)
      (Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L)) :
    Continuous (fun p : Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L =>
      Z p.1.1 p.1.2 ω) :=
  h.comp_continuous continuous_subtype_val fun p => p.2

/-- The field restricted to a compact box is almost everywhere measurable as a map into
the continuous functions on the box.  This is the step that turns the almost-everywhere
continuity of the modification into measurability of the value. -/
theorem aemeasurable_field_box {ΩW : Type*} [MeasurableSpace ΩW]
    (PW : Measure ΩW) (d : ℕ) (T L : ℝ)
    [MeasurableSpace C(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L, ℝ)]
    [BorelSpace C(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L, ℝ)]
    (Z : ℝ → Space d → ΩW → ℝ)
    (hf : ∀ p : Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L,
      AEMeasurable (fun ω => Z p.1.1 p.1.2 ω) PW)
    (hc : ∀ᵐ ω ∂PW, Continuous (fun p : Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L =>
      Z p.1.1 p.1.2 ω)) :
    AEMeasurable (fun ω => ContinuousMap.mkD (fun p : Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L =>
      Z p.1.1 p.1.2 ω) 0) PW := by
  haveI : CompactSpace ↥(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L) :=
    isCompact_iff_compactSpace.mp (isCompact_Icc.prod (isCompact_closedBall 0 L))
  exact Sandpile.Continuum.aemeasurable_continuousMap_mkD
    (E := ↥(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L))
    PW (fun ω (p : ↥(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L)) =>
      Z p.1.1 p.1.2 ω) hf hc



/-- The value, read through the continuous function on a compact box, is measurable in
the continuous function.  The box is a closed ball, so that the space of continuous
functions on it carries the sup metric. -/
theorem measurable_value_functional_ball {ΩB : Type*} [MeasurableSpace ΩB]
    (d : ℕ) (B : ℝ≥0 → ΩB → Space d) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (T L : ℝ) (hT : 0 < T) (hL : 0 ≤ L) (x : Space d)
    (hbdd : ∀ h : ℝ → Space d → ℝ, BddAbove (stoppingPayoffs B PB h T))
    (hint : ∀ (h : ℝ → Space d → ℝ), (∀ s ∈ Set.Icc (0:ℝ) T, ∀ _y : Space d,
        ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
          Integrable (fun ω => -h (T - τ ω) (B (τ ω) ω)) PB))
    [MeasurableSpace C(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L, ℝ)]
    [BorelSpace C(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L, ℝ)] :
    Measurable (fun v : C(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L, ℝ) =>
      brownianValue B PB
        (fun t z => if h : (t, z) ∈ Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L
          then v ⟨(t, z), h⟩ else 0) T x) := by
  haveI : CompactSpace ↥(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L) :=
    isCompact_iff_compactSpace.mp (isCompact_Icc.prod (isCompact_closedBall 0 L))
  haveI : Nonempty ↥(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L) :=
    ⟨⟨((0:ℝ), (0:Space d)), Set.mem_prod.mpr
      ⟨Set.mem_Icc.mpr ⟨le_refl 0, hT.le⟩, Metric.mem_closedBall_self hL⟩⟩⟩
  have hlip : LipschitzWith 2
      (fun v : C(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L, ℝ) =>
        brownianValue B PB
          (fun t z => if h : (t, z) ∈ Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L
            then v ⟨(t, z), h⟩ else 0) T x) := by
    refine LipschitzWith.of_dist_le_mul fun v w => ?_
    have hgap : ∀ s ∈ Set.Icc (0:ℝ) T, ∀ y : Space d,
        |(fun t z => if h : (t, z) ∈ Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L
            then v ⟨(t, z), h⟩ else 0) s y
          - (fun t z => if h : (t, z) ∈ Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L
            then w ⟨(t, z), h⟩ else 0) s y| ≤ dist v w := by
      intro s hs y
      by_cases h : (s, y) ∈ Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L
      · simp only [dif_pos h]
        rw [← Real.dist_eq]
        exact ContinuousMap.dist_le_iff_of_nonempty.mp le_rfl
          (⟨(s, y), h⟩ : ↥(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L))
      · simp only [dif_neg h, sub_zero, abs_zero]
        exact dist_nonneg
    have h := Sandpile.Support.abs_brownianValue_sub_le_of_field d B PB _ _ T (dist v w)
      (le_of_lt hT) x (hbdd _) (hbdd _)
      (fun τ hτ hb => hint _ 0 ⟨le_refl 0, le_of_lt hT⟩ x τ hτ hb)
      (fun τ hτ hb => hint _ 0 ⟨le_refl 0, le_of_lt hT⟩ x τ hτ hb) hgap
    rw [Real.dist_eq]
    exact h
  exact hlip.continuous.measurable

end Sandpile.Support
