import Sandpile.External.Stopping.RightFiltrationApproximation

/-!
# Approximating stopping times before an exit

A right-continuation stopping time can be delayed and clipped at an original
filtration stopping time. This preserves a killing constraint while recovering
the original stopping time as the delay tends to zero.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace Sandpile.External.Stopping

/-- Delaying a right-continuation stop and clipping at an original-filtration
stop gives an original-filtration stop. -/
theorem isStoppingTime_min_add_stop_of_rightCont {Ω : Type*} {m : MeasurableSpace Ω}
    (F : Filtration ℝ≥0 m) (τ κ : Ω → ℝ≥0)
    (hτ : IsStoppingTime F.rightCont (fun ω => (τ ω : ℝ≥0∞)))
    (hκ : IsStoppingTime F (fun ω => (κ ω : ℝ≥0∞)))
    {δ : ℝ≥0} (hδ : 0 < δ) :
    IsStoppingTime F (fun ω => ((min (τ ω + δ) (κ ω) : ℝ≥0) : ℝ≥0∞)) := by
  intro t
  change MeasurableSet[F t] {ω | ((min (τ ω + δ) (κ ω) : ℝ≥0) : ℝ≥0∞) ≤ t}
  simp only [ENNReal.coe_le_coe, min_le_iff, Set.ofPred_or]
  apply MeasurableSet.union
  · have h := isStoppingTime_add_of_rightCont F τ hτ hδ t
    change MeasurableSet[F t] {ω | ((τ ω + δ : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞)} at h
    simpa only [ENNReal.coe_le_coe] using h
  · have h := hκ t
    change MeasurableSet[F t] {ω | (κ ω : ℝ≥0∞) ≤ (t : ℝ≥0∞)} at h
    simpa only [ENNReal.coe_le_coe] using h

/-- Clipping delayed times at a later time converges to the original time. -/
theorem tendsto_min_add_of_le {ι : Type*} {l : Filter ι} (τ κ : ℝ≥0)
    (hτκ : τ ≤ κ) (δ : ι → ℝ≥0) (hδ : Tendsto δ l (𝓝 0)) :
    Tendsto (fun n => min (τ + δ n) κ) l (𝓝 τ) := by
  have h := ((tendsto_const_nhds (x := τ)).add hδ).min (tendsto_const_nhds (x := κ))
  simpa only [add_zero, min_eq_left hτκ] using h

end Sandpile.External.Stopping
