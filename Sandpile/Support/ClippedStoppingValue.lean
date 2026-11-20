import Sandpile.Continuum.Stopping
import Sandpile.External.ContinuumOptimalStopping

/-!
# Clipped stopping times

Finite-horizon stopping values can be compared on one stopping class by clipping
the times at the desired horizon.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Capping a natural-filtration stopping time at a deterministic horizon
preserves the stopping-time property. -/
theorem Sandpile.Support.isBrownianStopping_min_const
    {Ω : Type*} {d : ℕ} (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (τ : Ω → ℝ≥0) (hτ : Sandpile.Continuum.IsBrownianStopping B τ) (T : ℝ≥0) :
    Sandpile.Continuum.IsBrownianStopping B (fun ω => min (τ ω) T) := by
  intro t
  change MeasurableSet[Sandpile.Continuum.brownianFiltration B t]
    {ω : Ω | ((min (τ ω) T : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞)}
  by_cases ht : T ≤ t
  · have he : {ω : Ω | ((min (τ ω) T : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞)} = Set.univ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, ENNReal.coe_le_coe]
      exact le_trans (min_le_right _ _) ht
    rw [he]
    exact @MeasurableSet.univ Ω (Sandpile.Continuum.brownianFiltration B t)
  · have he : {ω : Ω | ((min (τ ω) T : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞)} =
        {ω : Ω | (τ ω : ℝ≥0∞) ≤ (t : ℝ≥0∞)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, ENNReal.coe_le_coe, min_le_iff, ht, or_false]
    rw [he]
    exact hτ.measurableSet_le t

/-- A stopping value at a shorter horizon can be expressed using stopping times
bounded by a fixed longer horizon, capped at the shorter one. -/
theorem Sandpile.Support.snellValue_eq_sSup_clipped
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (G : ℝ → Sandpile.Continuum.Space d → ℝ) (t T : ℝ≥0) (htT : t ≤ T)
    :
    Sandpile.External.Snell.snellValue B P G t =
      sSup {a : ℝ | ∃ σ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping B σ ∧
        (∀ ω, σ ω ≤ T) ∧ a = ∫ ω,
          G ((t : ℝ) - min (σ ω) t) (B (min (σ ω) t) ω) ∂P} := by
  change sSup {a : ℝ | ∃ τ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping B τ ∧
    (∀ ω, (τ ω : ℝ) ≤ (t : ℝ)) ∧ a = ∫ ω, G ((t : ℝ) - τ ω) (B (τ ω) ω) ∂P} = _
  congr 1
  ext a
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨τ, hτ, hτt, rfl⟩
    have hτt' : ∀ ω, τ ω ≤ t := fun ω => by exact_mod_cast hτt ω
    refine ⟨τ, hτ, (fun ω => (hτt' ω).trans htT), ?_⟩
    congr 1
    funext ω
    rw [min_eq_left (hτt' ω)]
  · rintro ⟨σ, hσ, _, rfl⟩
    refine ⟨fun ω => min (σ ω) t, Sandpile.Support.isBrownianStopping_min_const B σ hσ t, ?_, rfl⟩
    intro ω
    exact_mod_cast (min_le_right (σ ω) t)
