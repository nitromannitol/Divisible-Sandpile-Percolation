import Sandpile.External.Stopping.RightFiltrationValue

/-!
# Killed stopping values for right-continuation filtrations

Clipping delayed times at an original-filtration killing clock preserves the
value of a bounded continuous reward under right-continuation.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace Sandpile.External.Stopping

/-- Expected rewards of bounded stops which occur almost surely no later than
a finite killing clock. -/
def clockPayoffs {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (B : ℝ≥0 → Ω → Continuum.Space d) (P : Measure Ω) (T : ℝ≥0)
    (G : ℝ → Continuum.Space d → ℝ) (κ : Ω → ℝ≥0)
    (F : Filtration ℝ≥0 (MeasurableSpace.comap (fun ω => fun t => B t ω) inferInstance)) :
    Set ℝ :=
  {a | ∃ τ : Ω → ℝ≥0, IsStoppingTime F (fun ω => (τ ω : ℝ≥0∞)) ∧
    (∀ ω, τ ω ≤ T) ∧ (∀ᵐ ω ∂P, τ ω ≤ κ ω) ∧
    a = ∫ ω, G ((T : ℝ) - τ ω) (B (τ ω) ω) ∂P}

/-- Right-continuation does not change a bounded continuous stopping value
when the finite killing clock is a raw stopping time. -/
theorem sSup_clockPayoffs_rightCont_eq {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → Continuum.Space d)
    (hBm : ∀ t, AEMeasurable (B t) P)
    (hBc : ∀ᵐ ω ∂P, Continuous fun t => B t ω)
    (T : ℝ≥0) (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M)
    (κ : Ω → ℝ≥0) (hκ : Continuum.IsBrownianStopping B κ)
    (hκT : ∀ ω, κ ω ≤ T) :
    sSup (clockPayoffs B P T G κ (Continuum.brownianFiltration B).rightCont) =
      sSup (clockPayoffs B P T G κ (Continuum.brownianFiltration B)) := by
  let F := Continuum.brownianFiltration B
  have hne : ∀ F : Filtration ℝ≥0
      (MeasurableSpace.comap (fun ω => fun t => B t ω) inferInstance),
      (clockPayoffs B P T G κ F).Nonempty := by
    intro F
    exact ⟨_, fun _ => 0, isStoppingTime_const F 0, (fun _ => bot_le),
      Filter.Eventually.of_forall (fun _ => bot_le), rfl⟩
  have hbdd : ∀ F : Filtration ℝ≥0
      (MeasurableSpace.comap (fun ω => fun t => B t ω) inferInstance),
      BddAbove (clockPayoffs B P T G κ F) := by
    intro F
    refine ⟨M, ?_⟩
    rintro a ⟨τ, _, _, _, rfl⟩
    have h := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun ω => G ((T : ℝ) - τ ω) (B (τ ω) ω)) (C := M)
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hG _ _)
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using h)
  change sSup (clockPayoffs B P T G κ F.rightCont) = sSup (clockPayoffs B P T G κ F)
  apply le_antisymm
  · refine csSup_le (hne F.rightCont) ?_
    rintro a ⟨τ, hτ, hτT, hτκ, rfl⟩
    let δ : ℕ → ℝ≥0 := fun n => 1 / 2 ^ n
    let σ : ℕ → Ω → ℝ≥0 := fun n ω => min (τ ω + δ n) (κ ω)
    have hτm := aemeasurable_of_rightCont_brownianStopping P B hBm τ hτ
    have hκm := Continuum.IsBrownianStopping.aemeasurable hκ P hBm
    have hlim := tendsto_integral_reward_min_add P B hBm hBc τ κ hτm hκm hτκ δ
      tendsto_one_div_pow_two_nnreal T M G hGc hG
    apply le_of_tendsto hlim
    filter_upwards with n
    apply le_csSup (hbdd F)
    refine ⟨σ n, ?_, (fun ω => (min_le_right _ _).trans (hκT ω)),
      Filter.Eventually.of_forall (fun ω => min_le_right _ _), rfl⟩
    exact isStoppingTime_min_add_stop_of_rightCont F τ κ hτ hκ (by dsimp [δ]; positivity)
  · refine csSup_le (hne F) ?_
    rintro a ⟨τ, hτ, hτT, hτκ, rfl⟩
    apply le_csSup (hbdd F.rightCont)
    refine ⟨τ, ?_, hτT, hτκ, rfl⟩
    intro t
    exact F.le_rightCont t _ (hτ t)

end Sandpile.External.Stopping
