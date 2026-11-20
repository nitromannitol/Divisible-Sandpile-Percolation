import Sandpile.External.Stopping.FiniteDecisionConvergence

/-!
# Stopping times from convergent event predictors

The finite stopping approximation in Coquet and Toldo, Section 2.2, selects
the first decision time at which an adapted predictor of the corresponding
stopping event exceeds one half.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal symmDiff

namespace Sandpile.External.Stopping

/-- Thresholding real predictors at one half recovers an indicator event in
measure when the predictors converge in measure to its indicator. -/
theorem tendsto_measure_threshold_symmDiff
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (p : ℕ → Ω → ℝ)
    (hp : TendstoInMeasure P p atTop (A.indicator (fun _ => (1 : ℝ)))) :
    Tendsto (fun n => P ({ω | 1 / 2 < p n ω} ∆ A)) atTop (𝓝 0) := by
  have h := (tendstoInMeasure_iff_dist.mp hp) (1 / 2) (by norm_num)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun _ => zero_le) ?_
  intro n
  apply measure_mono
  intro ω hω
  simp only [Set.mem_symmDiff, Set.mem_ofPred_eq] at hω
  change (1 / 2 : ℝ) ≤ dist (p n ω) (A.indicator (fun _ => (1 : ℝ)) ω)
  rcases hω with ⟨hpω, hAω⟩ | ⟨hAω, hpω⟩
  · rw [Set.indicator_of_notMem hAω, Real.dist_eq, sub_zero]
    exact (le_of_lt hpω).trans (le_abs_self _)
  · rw [Set.indicator_of_mem hAω, Real.dist_eq]
    have hle : p n ω ≤ 1 / 2 := le_of_not_gt hpω
    have habs := neg_le_abs (p n ω - 1)
    linarith

/-- Adapted predictors of finite stopping events produce bounded stopping
times converging in probability to the original finite-valued time. -/
theorem exists_finite_stopping_approx_of_predictors
    {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → Filtration ℝ≥0 m) (T : ℝ≥0) (V : Finset ℝ≥0)
    (hVT : ∀ t ∈ V, t ≤ T) (τ : Ω → ℝ≥0) (hτV : ∀ ω, τ ω ∈ V)
    (p : ℕ → ℝ≥0 → Ω → ℝ)
    (hpm : ∀ n, ∀ t ∈ V, @Measurable Ω ℝ (F n t) inferInstance (p n t))
    (hp : ∀ t ∈ V, TendstoInMeasure P (fun n => p n t) atTop
      (({ω | τ ω = t} : Set Ω).indicator (fun _ => (1 : ℝ)))) :
    ∃ τn : ℕ → Ω → ℝ≥0,
      (∀ n, IsStoppingTime (F n) (fun ω => (τn n ω : ℝ≥0∞))) ∧
      (∀ n ω, τn n ω ≤ T) ∧ TendstoInMeasure P τn atTop τ := by
  let A : ℕ → ℝ≥0 → Set Ω := fun n t => {ω | 1 / 2 < p n t ω}
  let C : ℝ≥0 → Set Ω := fun t => {ω | τ ω = t}
  let τn : ℕ → Ω → ℝ≥0 := fun n => finiteEventStop T V (A n)
  have hA : ∀ t ∈ V, Tendsto (fun n => P ((A n t) ∆ C t)) atTop (𝓝 0) := by
    intro t ht
    exact tendsto_measure_threshold_symmDiff P (C t) (fun n => p n t) (hp t ht)
  refine ⟨τn, ?_, (fun n ω => finiteEventStop_le T V (A n) hVT ω), ?_⟩
  · intro n
    exact isStoppingTime_finiteEventStop (F n) T V (A n) hVT (fun t ht =>
      measurableSet_lt measurable_const (hpm n t ht))
  · have hlim := tendstoInMeasure_finiteEventStop P T V A C hA
    have heq : finiteEventStop T V C = τ := by
      funext ω
      exact finiteEventStop_eq_of_mem_range T V τ hτV ω
    rw [heq] at hlim
    exact hlim

end Sandpile.External.Stopping
