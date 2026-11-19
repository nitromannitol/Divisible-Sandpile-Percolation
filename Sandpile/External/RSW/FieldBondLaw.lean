import Sandpile.External.RSW.BondCrossingMeasurable

/-!
# The bond law induced by a field

Thresholding a field and opening bonds whose endpoints are open produces an associated bond
law with the same reindexing symmetries and the same positive-width crossing probabilities.
-/

open MeasureTheory Set

noncomputable section

namespace Sandpile.External.RSW

/-- The bond law induced by a field at a given superlevel. -/
def fieldBondLaw (μ : Measure (Site 2 → ℝ)) (level : ℝ) :
    Measure (Sym2 (Site 2) → Bool) :=
  (μ.map (thresholdConfig level)).map siteBondConfig

/-- A probability field law induces a probability bond law. -/
theorem isProbabilityMeasure_fieldBondLaw (μ : Measure (Site 2 → ℝ)) [IsProbabilityMeasure μ]
    (level : ℝ) : IsProbabilityMeasure (fieldBondLaw μ level) := by
  letI : IsProbabilityMeasure (μ.map (thresholdConfig level)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_thresholdConfig level).aemeasurable).2
      inferInstance
  exact (Measure.isProbabilityMeasure_map_iff measurable_siteBondConfig.aemeasurable).2 inferInstance

/-- An associated field law induces an associated bond law. -/
theorem fieldBondLaw_associated (μ : Measure (Site 2 → ℝ)) (hμ : IsAssociatedPlanarLaw μ)
    (level : ℝ) {A B : Set (Sym2 (Site 2) → Bool)} (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (fieldBondLaw μ level).real A * (fieldBondLaw μ level).real B ≤
      (fieldBondLaw μ level).real (A ∩ B) := by
  exact siteBond_associated (μ.map (thresholdConfig level))
    (fun _ _ ha hb ham hbm => threshold_associated μ hμ level ha hb ham hbm) hA hB hAm hBm

/-- A field symmetry given by reindexing induces the corresponding bond symmetry. -/
theorem measurePreserving_fieldBondLaw_reindex (μ : Measure (Site 2 → ℝ)) (level : ℝ)
    (g : Site 2 → Site 2)
    (hμ : MeasurePreserving (fun F : Site 2 → ℝ => F ∘ g) μ μ) :
    MeasurePreserving (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map g)
      (fieldBondLaw μ level) (fieldBondLaw μ level) :=
  measurePreserving_siteBond_reindex (μ.map (thresholdConfig level)) g
    (measurePreserving_threshold_reindex μ level g hμ)

/-- The induced bond law has the same crossing probability as the original field law on every
positive-width rectangle. -/
theorem fieldBondLaw_crossing (μ : Measure (Site 2 → ℝ)) (level : ℝ)
    (w h : ℕ) (hw : 0 < w) :
    (fieldBondLaw μ level).real (bondCrossingEvent w h) =
      μ.real (planarCrossingEvent w h level) := by
  simp only [fieldBondLaw, Measure.real,
    Measure.map_apply measurable_siteBondConfig (measurableSet_bondCrossingEvent w h),
    Measure.map_apply (measurable_thresholdConfig level)
      ((measurableSet_bondCrossingEvent w h).preimage measurable_siteBondConfig)]
  rw [planarCrossingEvent_eq_preimage_bondCrossingEvent w h hw level]
  rfl

end Sandpile.External.RSW
