import Sandpile.External.Stopping.FiniteStoppingComapFactor
import Sandpile.Continuum.Stopping

/-!
# Finite natural stopping times under path maps

Natural filtrations commute with pullback along a measurable path map, so
finite-valued stopping rules on a realization factor through that map.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- The natural filtration of a composed process is the pullback of the
natural filtration of the original process. -/
theorem natFiltration_comp_eq_comap
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {d : ℕ}
    (Z : ℝ≥0 → Ξ → Continuum.Space d) (hZ : ∀ t, StronglyMeasurable (Z t))
    (f : Ω → Ξ) (hf : Measurable f)
    (hfZ : ∀ t, StronglyMeasurable (fun ω => Z t (f ω))) (t : ℝ≥0) :
    LatticeProb.natFiltration (fun s ω => Z s (f ω)) hfZ t =
      (LatticeProb.natFiltration Z hZ t).comap f := by
  rw [LatticeProb.natFiltration_eq_comap, LatticeProb.natFiltration_eq_comap,
    MeasurableSpace.comap_comp]
  rfl

/-- A finite bounded stopping time for a process read through a measurable map
factors as a finite bounded stopping time of the original process. -/
theorem exists_finite_natural_stopping_factor
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {d : ℕ}
    (Z : ℝ≥0 → Ξ → Continuum.Space d) (hZ : ∀ t, StronglyMeasurable (Z t))
    (f : Ω → Ξ) (hf : Measurable f)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : Continuum.IsBrownianStopping (fun s ω => Z s (f ω)) τ)
    (hτT : ∀ ω, τ ω ≤ T) (hτfin : (Set.range τ).Finite) :
    ∃ σ : Ξ → ℝ≥0, Continuum.IsBrownianStopping Z σ ∧
      (∀ ξ, σ ξ ≤ T) ∧ (Set.range σ).Finite ∧ ∀ ω, τ ω = σ (f ω) := by
  have hfZ : ∀ t, StronglyMeasurable (fun ω => Z t (f ω)) :=
    fun t => ((hZ t).measurable.comp hf).stronglyMeasurable
  have hs := (Continuum.isBrownianStopping_iff_natFiltration _ hfZ τ).mp hτ
  obtain ⟨σ, hσ, hσT, hσfin, hστ⟩ := exists_finite_stopping_factor_of_comap
    (LatticeProb.natFiltration (fun s ω => Z s (f ω)) hfZ) (LatticeProb.natFiltration Z hZ) f
    (natFiltration_comp_eq_comap Z hZ f hf hfZ) T τ hs hτT hτfin
  exact ⟨σ, (Continuum.isBrownianStopping_iff_natFiltration Z hZ σ).mpr hσ, hσT, hσfin, hστ⟩

end Sandpile.External.Stopping
