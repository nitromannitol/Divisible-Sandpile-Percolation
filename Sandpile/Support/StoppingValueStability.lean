import Sandpile.Support.AugmentedStoppingPayoff

/-!
# Stability of stopping values

An integrable pathwise bound on a reward difference controls the difference
of the corresponding bounded-horizon stopping values.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

/-- An integrable uniform bound on the difference of two stopped rewards
controls the difference of their stopping values. -/
theorem Sandpile.Support.abs_sSup_stopping_payoffs_sub_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (T : ℝ≥0)
    (R₁ R₂ : ℝ≥0 → Ω → ℝ) (D : Ω → ℝ) (hD : Integrable D P)
    (hclose : ∀ᵐ ω ∂P, ∀ s ≤ T, |R₁ s ω - R₂ s ω| ≤ D ω)
    (hint : ∀ (R : ℝ≥0 → Ω → ℝ), (R = R₁ ∨ R = R₂) →
      ∀ σ : Ω → ℝ≥0, IsStoppingTime 𝓕 (fun ω => (σ ω : ℝ≥0∞)) →
      (∀ ω, σ ω ≤ T) → Integrable (fun ω => R (σ ω) ω) P)
    (hbdd₁ : BddAbove {a : ℝ | ∃ σ : Ω → ℝ≥0,
      IsStoppingTime 𝓕 (fun ω => (σ ω : ℝ≥0∞)) ∧ (∀ ω, σ ω ≤ T) ∧
      a = ∫ ω, R₁ (σ ω) ω ∂P})
    (hbdd₂ : BddAbove {a : ℝ | ∃ σ : Ω → ℝ≥0,
      IsStoppingTime 𝓕 (fun ω => (σ ω : ℝ≥0∞)) ∧ (∀ ω, σ ω ≤ T) ∧
      a = ∫ ω, R₂ (σ ω) ω ∂P}) :
    |sSup {a : ℝ | ∃ σ : Ω → ℝ≥0,
      IsStoppingTime 𝓕 (fun ω => (σ ω : ℝ≥0∞)) ∧ (∀ ω, σ ω ≤ T) ∧
      a = ∫ ω, R₁ (σ ω) ω ∂P} -
    sSup {a : ℝ | ∃ σ : Ω → ℝ≥0,
      IsStoppingTime 𝓕 (fun ω => (σ ω : ℝ≥0∞)) ∧ (∀ ω, σ ω ≤ T) ∧
      a = ∫ ω, R₂ (σ ω) ω ∂P}| ≤ ∫ ω, D ω ∂P := by
  let S : (ℝ≥0 → Ω → ℝ) → Set ℝ := fun R => {a | ∃ σ : Ω → ℝ≥0,
      IsStoppingTime 𝓕 (fun ω => (σ ω : ℝ≥0∞)) ∧ (∀ ω, σ ω ≤ T) ∧
      a = ∫ ω, R (σ ω) ω ∂P}
  have hne : ∀ R, (S R).Nonempty := by
    intro R
    exact ⟨∫ ω, R 0 ω ∂P, fun _ => 0, isStoppingTime_const 𝓕 0, fun _ => zero_le, rfl⟩
  have hbound : ∀ R R' : ℝ≥0 → Ω → ℝ,
      (R = R₁ ∧ R' = R₂ ∨ R = R₂ ∧ R' = R₁) →
      BddAbove (S R') → sSup (S R) ≤ sSup (S R') + ∫ ω, D ω ∂P := by
    intro R R' hpair hR'bb
    apply csSup_le (hne R)
    rintro a ⟨σ, hσ, hσT, rfl⟩
    have hi : Integrable (fun ω => R (σ ω) ω) P := hint R (by tauto) σ hσ hσT
    have hi' : Integrable (fun ω => R' (σ ω) ω) P := hint R' (by tauto) σ hσ hσT
    have he : (∫ ω, R (σ ω) ω ∂P) ≤ ∫ ω, (R' (σ ω) ω + D ω) ∂P := by
      apply integral_mono_ae hi (hi'.add hD)
      filter_upwards [hclose] with ω hω
      change R (σ ω) ω ≤ R' (σ ω) ω + D ω
      have h := hω (σ ω) (hσT ω)
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · linarith [(abs_le.1 h).2]
      · linarith [(abs_le.1 h).1]
    rw [integral_add hi' hD] at he
    have hle := le_csSup hR'bb ⟨σ, hσ, hσT, rfl⟩
    linarith
  apply abs_le.mpr
  constructor
  · have := hbound R₂ R₁ (Or.inr ⟨rfl, rfl⟩) hbdd₁
    linarith
  · have := hbound R₁ R₂ (Or.inl ⟨rfl, rfl⟩) hbdd₂
    linarith
