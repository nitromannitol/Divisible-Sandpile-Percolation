import Sandpile.Continuum.Stopping

/-!
# Approximating right-filtration stopping times

A bounded stopping time for the right-continuation of a filtration can be
approximated from above by bounded stopping times of the original filtration.
The approximation delays the stopping time by a positive amount and clips it
at the horizon.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- A positive delay turns a finite stopping time of the right-continuation
into a stopping time of the original filtration. -/
theorem isStoppingTime_add_of_rightCont {Ω : Type*} {m : MeasurableSpace Ω}
    (F : Filtration ℝ≥0 m) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime F.rightCont (fun ω => (τ ω : ℝ≥0∞)))
    {δ : ℝ≥0} (hδ : 0 < δ) :
    IsStoppingTime F (fun ω => ((τ ω + δ : ℝ≥0) : ℝ≥0∞)) := by
  intro t
  change MeasurableSet[F t] {ω | ((τ ω + δ : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞)}
  by_cases hdt : δ ≤ t
  · have hlt : t - δ < t := tsub_lt_self (hδ.trans_le hdt) hδ
    have hle : F.rightCont (t - δ) ≤ F t := by
      rw [Filtration.rightCont_eq]
      exact iInf₂_le t hlt
    have hset : {ω | ((τ ω + δ : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞)} =
        {ω | (τ ω : ℝ≥0∞) ≤ ((t - δ : ℝ≥0) : ℝ≥0∞)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, ENNReal.coe_le_coe]
      exact (le_tsub_iff_right hdt).symm
    rw [hset]
    exact hle _ (hτ (t - δ))
  · have hset : {ω | ((τ ω + δ : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞)} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, ENNReal.coe_le_coe]
      exact not_le_of_gt ((lt_of_not_ge hdt).trans_le (le_add_self : δ ≤ τ ω + δ))
    rw [hset]
    exact @MeasurableSet.empty Ω (F t)

/-- Delay and horizon clipping preserve admissibility and approximate the
original bounded stopping time to within the delay. -/
theorem isStoppingTime_min_add_of_rightCont {Ω : Type*} {m : MeasurableSpace Ω}
    (F : Filtration ℝ≥0 m) (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hτ : IsStoppingTime F.rightCont (fun ω => (τ ω : ℝ≥0∞)))
    (hbound : ∀ ω, τ ω ≤ T) {δ : ℝ≥0} (hδ : 0 < δ) :
    IsStoppingTime F (fun ω => ((min (τ ω + δ) T : ℝ≥0) : ℝ≥0∞)) ∧
      ∀ ω, τ ω ≤ min (τ ω + δ) T ∧ min (τ ω + δ) T ≤ τ ω + δ ∧
        min (τ ω + δ) T ≤ T := by
  constructor
  · intro t
    change MeasurableSet[F t] {ω | ((min (τ ω + δ) T : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞)}
    simp only [ENNReal.coe_le_coe, min_le_iff, Set.ofPred_or]
    apply MeasurableSet.union
    · have hh := (isStoppingTime_add_of_rightCont F τ hτ hδ) t
      change MeasurableSet[F t] {ω | ((τ ω + δ : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞)} at hh
      simpa only [ENNReal.coe_le_coe] using hh
    · exact @MeasurableSet.const Ω (F t) (T ≤ t)
  · intro ω
    exact ⟨le_min (le_self_add) (hbound ω), min_le_left _ _, min_le_right _ _⟩

end Sandpile.External.Stopping
