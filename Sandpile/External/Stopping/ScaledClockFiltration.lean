import Sandpile.External.Stopping.ParameterizedClockIndependence

/-!
# Deterministic scaling of stopping filtrations

Scaling the time parameter of a filtration preserves its right-continuation
stopping times when the clock is scaled back to physical time.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- A filtration observed at a constant multiple of its time parameter. -/
def scaledFiltration {Ω : Type*} {m : MeasurableSpace Ω}
    (F : Filtration ℝ≥0 m) (c : ℝ≥0) : Filtration ℝ≥0 m where
  seq t := F (c * t)
  mono' := fun _ _ h => F.mono (mul_le_mul_of_nonneg_left h zero_le)
  le' t := F.le (c * t)

/-- Right-continuation commutes with positive deterministic time scaling. -/
theorem scaledFiltration_rightCont_le {Ω : Type*} {m : MeasurableSpace Ω}
    (F : Filtration ℝ≥0 m) (c : ℝ≥0) (hc : 0 < c) (t : ℝ≥0) :
    (scaledFiltration F c).rightCont (t / c) ≤ F.rightCont t := by
  rw [Filtration.rightCont_eq, Filtration.rightCont_eq]
  apply le_iInf
  intro s
  apply le_iInf
  intro hts
  have hdiv : t / c < s / c := (div_lt_div_iff_of_pos_right hc).2 hts
  change (⨅ (r : ℝ≥0) (_ : t / c < r), F (c * r)) ≤ F s
  have h : (⨅ (r : ℝ≥0) (_ : t / c < r), F (c * r)) ≤ F (c * (s / c)) :=
    iInf₂_le (s / c) hdiv
  simpa only [mul_div_cancel₀ _ hc.ne'] using h

/-- A stopping time for the rescaled right-continuation filtration becomes a
stopping time in physical time after multiplying by the scale. -/
theorem isStoppingTime_mul_scaledFiltration_rightCont {Ω : Type*} {m : MeasurableSpace Ω}
    (F : Filtration ℝ≥0 m) (c : ℝ≥0) (hc : 0 < c) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (scaledFiltration F c).rightCont (fun ω => (τ ω : ℝ≥0∞))) :
    IsStoppingTime F.rightCont (fun ω => ((c * τ ω : ℝ≥0) : ℝ≥0∞)) := by
  intro t
  have hset : {ω | ((c * τ ω : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞)} =
      {ω | ((τ ω : ℝ≥0) : ℝ≥0∞) ≤ ((t / c : ℝ≥0) : ℝ≥0∞)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, ENNReal.coe_le_coe]
    exact (le_div_iff₀' hc).symm
  change MeasurableSet[F.rightCont t]
    {ω | ((c * τ ω : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞)}
  rw [hset]
  exact scaledFiltration_rightCont_le F c hc t _ (hτ (t / c))

/-- Adding the independent parameter commutes with time scaling. -/
theorem parameterFiltration_scaledFiltration {Ω A : Type*} {m : MeasurableSpace Ω}
    [MeasurableSpace A] (F : Filtration ℝ≥0 m) (c : ℝ≥0) :
    parameterFiltration (A := A) (scaledFiltration F c) =
      scaledFiltration (parameterFiltration (A := A) F) c := by
  rfl

end Sandpile.External.Stopping
