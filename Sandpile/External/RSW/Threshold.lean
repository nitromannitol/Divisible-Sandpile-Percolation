import Sandpile.Support.PlanarLaw

/-!
# Thresholding planar fields

The superlevel configuration of a real field is a measurable, monotone map to site
configurations. Its pushforward preserves positive association and every reindexing symmetry.
-/

open MeasureTheory Set

noncomputable section

namespace Sandpile.External.RSW

/-- The site configuration obtained by declaring a site open when its value is at least `level`. -/
def thresholdConfig (level : ℝ) (F : Site 2 → ℝ) (z : Site 2) : Bool :=
  if level ≤ F z then true else false

/-- The threshold configuration is measurable as a function of the field. -/
theorem measurable_thresholdConfig (level : ℝ) : Measurable (thresholdConfig level) := by
  apply Measurable.of_eval
  intro z
  exact Measurable.ite (measurableSet_le measurable_const (measurable_pi_apply z))
    measurable_const measurable_const

/-- Raising field values can only open more sites. -/
theorem monotone_thresholdConfig (level : ℝ) : Monotone (thresholdConfig level) := by
  intro F G hFG z
  by_cases hF : level ≤ F z
  · have hG : level ≤ G z := hF.trans (hFG z)
    simp [thresholdConfig, hF, hG]
  · simp [thresholdConfig, hF]

/-- Thresholding commutes with a reindexing of sites. -/
theorem thresholdConfig_reindex (level : ℝ) (F : Site 2 → ℝ) (g : Site 2 → Site 2) :
    thresholdConfig level (F ∘ g) = thresholdConfig level F ∘ g := rfl

/-- The thresholded site law is positively associated on measurable increasing events. -/
theorem threshold_associated (μ : Measure (Site 2 → ℝ)) (hμ : IsAssociatedPlanarLaw μ)
    (level : ℝ) {A B : Set (Site 2 → Bool)} (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (μ.map (thresholdConfig level)).real A * (μ.map (thresholdConfig level)).real B ≤
      (μ.map (thresholdConfig level)).real (A ∩ B) := by
  have ht := measurable_thresholdConfig level
  have ha : IsUpperSet (thresholdConfig level ⁻¹' A) :=
    fun _ _ hFG hF => hA (monotone_thresholdConfig level hFG) hF
  have hb : IsUpperSet (thresholdConfig level ⁻¹' B) :=
    fun _ _ hFG hF => hB (monotone_thresholdConfig level hFG) hF
  have hh := hμ (thresholdConfig level ⁻¹' A) (thresholdConfig level ⁻¹' B) ha hb
    (hAm.preimage ht) (hBm.preimage ht)
  simpa only [Measure.real, Measure.map_apply ht hAm, Measure.map_apply ht hBm,
    Measure.map_apply ht (hAm.inter hBm), preimage_inter] using hh

/-- Every site reindexing preserving a field law also preserves its thresholded site law. -/
theorem measurePreserving_threshold_reindex (μ : Measure (Site 2 → ℝ))
    (level : ℝ) (g : Site 2 → Site 2)
    (hμ : MeasurePreserving (fun F : Site 2 → ℝ => F ∘ g) μ μ) :
    MeasurePreserving (fun σ : Site 2 → Bool => σ ∘ g)
      (μ.map (thresholdConfig level)) (μ.map (thresholdConfig level)) := by
  have ht := measurable_thresholdConfig level
  have hg : Measurable (fun σ : Site 2 → Bool => σ ∘ g) :=
    Measurable.of_eval (fun z => measurable_pi_apply (g z))
  refine ⟨hg, ?_⟩
  rw [Measure.map_map hg ht]
  change Measure.map (thresholdConfig level ∘ (fun F : Site 2 → ℝ => F ∘ g)) μ = _
  rw [← Measure.map_map ht hμ.measurable, hμ.map_eq]

end Sandpile.External.RSW
