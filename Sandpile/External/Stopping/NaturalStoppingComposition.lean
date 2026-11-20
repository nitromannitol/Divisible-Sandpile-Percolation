import Sandpile.Continuum.Stopping

/-!
# Natural stopping times under composition

Reading a process through any map preserves its natural stopping times.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- A natural stopping time remains one after reading the process through a
map of sample spaces. -/
theorem isBrownianStopping_comp
    {Ω Ξ : Type*} {d : ℕ} (Z : ℝ≥0 → Ξ → Continuum.Space d)
    (f : Ω → Ξ) (τ : Ξ → ℝ≥0) (hτ : Continuum.IsBrownianStopping Z τ) :
    Continuum.IsBrownianStopping (fun t ω => Z t (f ω)) (fun ω => τ (f ω)) := by
  intro t
  have h := hτ t
  rw [Continuum.brownianFiltration, Filtration.natural_eq_comap] at h ⊢
  obtain ⟨A, hA, hAeq⟩ := h
  refine ⟨A, hA, ?_⟩
  change (fun ω (s : Set.Iic t) => Z s (f ω)) ⁻¹' A =
    {ω | (τ (f ω) : ℝ≥0∞) ≤ t}
  ext ω
  exact Set.ext_iff.mp hAeq (f ω)

end Sandpile.External.Stopping
