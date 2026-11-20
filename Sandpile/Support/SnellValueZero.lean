import Sandpile.External.ContinuumOptimalStopping

/-!
# Stopping value at zero horizon

The only stopping time bounded by zero is zero, so the value equals the gain at
the starting point.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

/-- At zero horizon, the stopping value is the gain at the starting point. -/
theorem Sandpile.External.Snell.snellValue_zero
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d) (x : Sandpile.Continuum.Space d)
    (hstart : ∀ᵐ ω ∂P, B 0 ω = x) (G : ℝ → Sandpile.Continuum.Space d → ℝ) :
    snellValue B P G 0 = G 0 x := by
  have hpay : ∀ (τ : Ω → ℝ≥0), (∀ ω, (τ ω : ℝ) ≤ 0) →
      (∫ ω, G (0 - (τ ω : ℝ)) (B (τ ω) ω) ∂P) = G 0 x := by
    intro τ hτ
    have hτzero : ∀ ω, τ ω = 0 := by
      intro ω
      apply le_antisymm ?_ zero_le
      exact_mod_cast hτ ω
    calc
      (∫ ω, G (0 - (τ ω : ℝ)) (B (τ ω) ω) ∂P) = ∫ _ω, G 0 x ∂P := by
        apply integral_congr_ae
        filter_upwards [hstart] with ω hω
        simp only [hτzero ω, NNReal.coe_zero, sub_zero, hω]
      _ = G 0 x := by simp
  have hset : attainable B P G 0 = {G 0 x} := by
    ext a
    constructor
    · rintro ⟨τ, _, hτ, rfl⟩
      simpa only [Set.mem_singleton_iff] using hpay τ hτ
    · intro ha
      have ha' : a = G 0 x := by simpa only [Set.mem_singleton_iff] using ha
      refine ⟨fun _ => 0, Sandpile.Continuum.isBrownianStopping_const B 0, ?_, ?_⟩
      · intro ω
        simp only [NNReal.coe_zero, le_refl]
      · rw [ha', hpay (fun _ => 0) (fun _ => le_rfl)]
  change sSup (attainable B P G 0) = G 0 x
  rw [hset, csSup_singleton]
