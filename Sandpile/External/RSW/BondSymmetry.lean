import Sandpile.External.RSW.FieldBondLaw

/-!
# Symmetries of the induced bond law

The translation, coordinate-swap, and reflection symmetries of a planar field law pass to the
bond law induced by its superlevel sites.
-/

open MeasureTheory

namespace Sandpile.External.RSW

/-- The bond law induced by a symmetric planar field is invariant under translations,
coordinate interchange, and reflection. -/
theorem fieldBondLaw_symmetric (μ : Measure (Site 2 → ℝ)) (hμ : IsSymmetricPlanarLaw μ)
    (level : ℝ) :
    (∀ v : Site 2, MeasurePreserving
      (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map (fun z => z + v))
      (fieldBondLaw μ level) (fieldBondLaw μ level)) ∧
    MeasurePreserving
      (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map (fun z => ![z 1, z 0]))
      (fieldBondLaw μ level) (fieldBondLaw μ level) ∧
    MeasurePreserving
      (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map (fun z => ![-z 0, z 1]))
      (fieldBondLaw μ level) (fieldBondLaw μ level) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v
    exact measurePreserving_fieldBondLaw_reindex μ level (fun z => z + v) (hμ.1 v)
  · exact measurePreserving_fieldBondLaw_reindex μ level (fun z => ![z 1, z 0]) hμ.2.1
  · exact measurePreserving_fieldBondLaw_reindex μ level (fun z => ![-z 0, z 1]) hμ.2.2

end Sandpile.External.RSW
