import Sandpile.External.Stopping.AECubeClockStopping

/-!
# Representatives of almost-sure stopping times

A bounded time whose stopping events have measurable representatives admits an
indistinguishable stopping-time representative in the right-continuation of
the filtration.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- A bounded time with stopping events measurable up to null sets has an
indistinguishable bounded stopping-time representative in the right-continuation
of the filtration. -/
theorem exists_rightCont_stoppingTime_ae_eq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m : MeasurableSpace Ω} (F : Filtration ℝ≥0 m)
    (τ : Ω → ℝ≥0) (T : ℝ≥0) (hτT : ∀ᵐ ω ∂P, τ ω ≤ T)
    (hτ : ∀ t, ∃ A : Set Ω, MeasurableSet[F t] A ∧ {ω | τ ω ≤ t} =ᵐ[P] A) :
    ∃ σ : Ω → ℝ≥0,
      IsStoppingTime F.rightCont (fun ω => (σ ω : ℝ≥0∞)) ∧
      (∀ ω, σ ω ≤ T) ∧ σ =ᵐ[P] τ := by
  classical
  let qtime : ℚ → ℝ≥0 := fun q => Real.toNNReal (q : ℝ)
  choose A hAm hAeq using fun q : ℚ => hτ (qtime q)
  let ρ : ℚ → Ω → ℝ≥0∞ := fun q ω => if ω ∈ A q then (qtime q : ℝ≥0∞) else ⊤
  have hρ (q : ℚ) : IsStoppingTime F.rightCont (ρ q) := by
    intro t
    change MeasurableSet[F.rightCont t] {ω | ρ q ω ≤ (t : ℝ≥0∞)}
    by_cases hqt : qtime q ≤ t
    · have hset : {ω | ρ q ω ≤ (t : ℝ≥0∞)} = A q := by
        ext ω
        simp only [Set.mem_ofPred_eq, ρ]
        by_cases h : ω ∈ A q <;> simp [h, hqt]
      rw [hset]
      exact F.le_rightCont t _ (F.mono hqt _ (hAm q))
    · have hset : {ω | ρ q ω ≤ (t : ℝ≥0∞)} = ∅ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, ρ]
        by_cases h : ω ∈ A q <;> simp [h, hqt]
      rw [hset]
      exact @MeasurableSet.empty Ω (F.rightCont t)
  let ρinf : Ω → ℝ≥0∞ := fun ω => min (T : ℝ≥0∞) (⨅ q : ℚ, ρ q ω)
  have hstop : IsStoppingTime F.rightCont ρinf :=
    (isStoppingTime_const F.rightCont T).min (IsStoppingTime.iInf hρ)
  have hfinite (ω : Ω) : ρinf ω ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
  let σ : Ω → ℝ≥0 := fun ω => (ρinf ω).toNNReal
  refine ⟨σ, ?_, ?_, ?_⟩
  · have heq : (fun ω => (σ ω : ℝ≥0∞)) = ρinf := by
      funext ω
      exact ENNReal.coe_toNNReal (hfinite ω)
    rw [heq]
    exact hstop
  · intro ω
    apply ENNReal.coe_le_coe.mp
    rw [ENNReal.coe_toNNReal (hfinite ω)]
    exact min_le_left _ _
  · filter_upwards [hτT, ae_all_iff.mpr hAeq] with ω hω hAω
    apply ENNReal.coe_injective
    rw [ENNReal.coe_toNNReal (hfinite ω)]
    apply le_antisymm
    · apply le_of_forall_gt_imp_ge_of_dense
      intro z hz
      obtain ⟨q, _, hqlo, hqhi⟩ := ENNReal.lt_iff_exists_rat_btwn.mp hz
      have hmem : ω ∈ A q := by
        have hq : τ ω ≤ qtime q := ENNReal.coe_le_coe.mp hqlo.le
        exact (iff_of_eq (hAω q)).mp hq
      exact (min_le_right _ _).trans ((iInf_le _ q).trans (by simp [ρ, hmem, qtime, hqhi.le]))
    · apply le_min
      · exact ENNReal.coe_le_coe.mpr hω
      · apply le_iInf
        intro q
        by_cases hmem : ω ∈ A q
        · have hq : τ ω ≤ qtime q := (iff_of_eq (hAω q)).mpr hmem
          simpa only [ρ, ite_eq_left hmem] using ENNReal.coe_le_coe.mpr hq
        · simp only [ρ, ite_eq_right hmem, le_top]

/-- The truncated open-cube exit has a bounded representative which is a
stopping time in the right-continuation of the Brownian natural filtration. -/
theorem exists_rightCont_cubeExit_stoppingTime
    {d : ℕ} [NeZero d] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {x : Continuum.Space d} {B : ℝ≥0 → Ω → Continuum.Space d}
    (hB : Continuum.IsBrownian d x B P) (T : ℝ≥0) :
    ∃ σ : Ω → ℝ≥0,
      IsStoppingTime (Continuum.brownianFiltration B).rightCont
        (fun ω => (σ ω : ℝ≥0∞)) ∧
      (∀ ω, σ ω ≤ T) ∧
      σ =ᵐ[P] fun ω => (min (LatticeProb.openExitTime B (openUnitCube x) ω)
        (T : ℝ≥0∞)).toNNReal := by
  apply exists_rightCont_stoppingTime_ae_eq (Continuum.brownianFiltration B) _ T
  · filter_upwards with ω
    apply ENNReal.coe_le_coe.mp
    rw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))]
    exact min_le_right _ _
  · exact ae_stopping_events_openUnitCubeExitTrunc hB T

end Sandpile.External.Stopping
