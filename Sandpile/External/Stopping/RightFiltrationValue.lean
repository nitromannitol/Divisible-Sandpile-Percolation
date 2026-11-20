import Sandpile.External.Stopping.RightFiltrationReward

/-!
# Stopping values for right-continuation filtrations

For bounded continuous rewards and almost surely continuous paths, right
continuation of the natural filtration does not alter the finite-horizon value.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace Sandpile.External.Stopping

/-- A stopping time of the right-continuation of a natural filtration is
almost everywhere measurable when the process observations are. -/
theorem aemeasurable_of_rightCont_brownianStopping {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (B : ℝ≥0 → Ω → Continuum.Space d)
    (hm : ∀ t, AEMeasurable (B t) P) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Continuum.brownianFiltration B).rightCont
      (fun ω => (τ ω : ℝ≥0∞))) : AEMeasurable τ P := by
  have ht : @Measurable Ω ℝ≥0 (MeasurableSpace.comap (fun ω => fun t => B t ω) inferInstance)
      inferInstance τ := measurable_coe_nnreal_ennreal_iff.1
    (MeasureTheory.IsStoppingTime.measurable hτ |>.mono
      (MeasureTheory.IsStoppingTime.measurableSpace_le hτ) le_rfl)
  have hp : @Measurable (NullMeasurableSpace Ω P) (ℝ≥0 → Continuum.Space d)
      inferInstance inferInstance (fun ω => fun t => B t ω) :=
    Measurable.of_eval fun t => (hm t).nullMeasurable
  exact (show NullMeasurable τ P from ht.mono hp.comap_le le_rfl).aemeasurable

/-- A strictly positive geometric mesh tends to zero. -/
theorem tendsto_one_div_pow_two_nnreal :
    Tendsto (fun n : ℕ => (1 : ℝ≥0) / 2 ^ n) atTop (𝓝 0) := by
  rw [← NNReal.tendsto_coe]
  push_cast
  have h : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  refine h.congr fun n => ?_
  rw [div_pow, one_pow]

/-- Expected rewards of bounded stopping times of the right-continuation of
the natural filtration. -/
def rightContPayoffs {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (B : ℝ≥0 → Ω → Continuum.Space d) (P : Measure Ω) (T : ℝ≥0)
    (G : ℝ → Continuum.Space d → ℝ) : Set ℝ :=
  {a | ∃ τ : Ω → ℝ≥0,
    IsStoppingTime (Continuum.brownianFiltration B).rightCont (fun ω => (τ ω : ℝ≥0∞)) ∧
    (∀ ω, τ ω ≤ T) ∧
    a = ∫ ω, G ((T : ℝ) - τ ω) (B (τ ω) ω) ∂P}

/-- Right-continuation preserves the finite-horizon value of a bounded
continuous reward for an almost surely continuous process. -/
theorem sSup_rightContPayoffs_eq_brownianDiscount {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → Continuum.Space d)
    (hBm : ∀ t, AEMeasurable (B t) P)
    (hBc : ∀ᵐ ω ∂P, Continuous fun t => B t ω)
    (T : ℝ≥0) (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) :
    sSup (rightContPayoffs B P T G) =
      Continuum.brownianDiscount B P (fun s z => -G s z) T := by
  let S : Set ℝ := {a | ∃ τ : Ω → ℝ≥0, Continuum.IsBrownianStopping B τ ∧
    (∀ ω, τ ω ≤ T) ∧ a = ∫ ω, G ((T : ℝ) - τ ω) (B (τ ω) ω) ∂P}
  have hright : (rightContPayoffs B P T G).Nonempty := by
    refine ⟨_, fun _ => 0, ?_, (fun _ => bot_le), rfl⟩
    exact isStoppingTime_const _ 0
  have hS : S.Nonempty := by
    exact ⟨_, fun _ => 0, Continuum.isBrownianStopping_const B 0, (fun _ => bot_le), rfl⟩
  have hbound : ∀ f : Ω → ℝ, (∀ ω, |f ω| ≤ M) → (∫ ω, f ω ∂P) ≤ M := by
    intro f hf
    have h := norm_integral_le_of_norm_le_const (μ := P) (f := f) (C := M)
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hf ω)
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using h)
  have hSb : BddAbove S := by
    refine ⟨M, ?_⟩
    rintro a ⟨τ, _, _, rfl⟩
    exact hbound _ (fun ω => hG _ _)
  have hRb : BddAbove (rightContPayoffs B P T G) := by
    refine ⟨M, ?_⟩
    rintro a ⟨τ, _, _, rfl⟩
    exact hbound _ (fun ω => hG _ _)
  have heq : Continuum.brownianDiscount B P (fun s z => -G s z) T = sSup S := by
    unfold Continuum.brownianDiscount
    apply congrArg sSup
    ext a
    simp only [S, Set.mem_ofPred_eq, neg_neg, NNReal.coe_le_coe]
  rw [heq]
  apply le_antisymm
  · refine csSup_le hright ?_
    rintro a ⟨τ, hτ, hτT, rfl⟩
    let δ : ℕ → ℝ≥0 := fun n => 1 / 2 ^ n
    let σ : ℕ → Ω → ℝ≥0 := fun n ω => min (τ ω + δ n) T
    have hτm := aemeasurable_of_rightCont_brownianStopping P B hBm τ hτ
    have hlim := tendsto_integral_reward_min_add P B hBm hBc τ (fun _ => T)
      hτm aemeasurable_const (Filter.Eventually.of_forall hτT) δ
      tendsto_one_div_pow_two_nnreal T M G hGc hG
    apply le_of_tendsto hlim
    filter_upwards with n
    apply le_csSup hSb
    refine ⟨σ n, ?_, (fun ω => min_le_right _ _), rfl⟩
    exact (isStoppingTime_min_add_of_rightCont (Continuum.brownianFiltration B) τ T hτ hτT
      (by dsimp [δ]; positivity)).1
  · refine csSup_le hS ?_
    rintro a ⟨τ, hτ, hτT, rfl⟩
    apply le_csSup hRb
    refine ⟨τ, ?_, hτT, rfl⟩
    intro t
    exact (Continuum.brownianFiltration B).le_rightCont t _ (hτ t)

end Sandpile.External.Stopping
