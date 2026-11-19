import Sandpile.External.RSW.AspectGluing

/-!
# Duality across integer aspect ratios

The discrete dual crossing of a tall rectangle is a horizontal crossing with a one-unit
boundary correction. Repeated dual gluing compares the complements of tall crossings.
-/

open LatticeProb MeasureTheory Set Percolation.Literature

namespace Sandpile.External.RSW

/-- Gluing dual crossings compares the complements of the tall aspect-two crossing and an
arbitrary tall integer-aspect crossing. -/
theorem fieldCrossing_complement_pow_le (μ : Measure (Site 2 → ℝ))
    [IsProbabilityMeasure μ] (hμ : IsSymmetricPlanarLaw μ) (ha : IsAssociatedPlanarLaw μ)
    (level : ℝ) {n : ℕ} (hn : 0 < n) (ρ : ℕ) :
    (1 - μ.real (planarCrossingEvent (2 * n) (4 * n) level)) ^ (4 * ρ + 1) ≤
      1 - μ.real (planarCrossingEvent (2 * n) (2 * ρ * n) level) := by
  let ν := fieldBondLaw μ level
  let : IsProbabilityMeasure ν := isProbabilityMeasure_fieldBondLaw μ level
  let νd := ν.map dualBondConfig
  let : IsProbabilityMeasure νd :=
    (Measure.isProbabilityMeasure_map_iff measurable_dualBondConfig.aemeasurable).2 inferInstance
  have hass : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → ν.real A * ν.real B ≤ ν.real (A ∩ B) :=
    fun _ _ hA hB hAm hBm => fieldBondLaw_associated μ ha level hA hB hAm hBm
  have hassd : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → νd.real A * νd.real B ≤ νd.real (A ∩ B) :=
    fun _ _ hA hB hAm hBm => dualBondConfig_associated ν hass hA hB hAm hBm
  have hs := fieldBondLaw_symmetric μ hμ level
  have htd : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) νd νd :=
    fun v => measurePreserving_dualBondConfig_translate ν v (hs.1 v)
  have hsd : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) νd νd :=
    measurePreserving_dualBondConfig_swap ν hs.2.1
  let m := 2 * n - 1
  have hm : m + 1 = 2 * n := by dsimp [m]; omega
  have hmn : n ≤ m := by dsimp [m]; omega
  have hdual (h : ℕ) : μ.real (planarCrossingEvent (2 * n) h level) +
      νd.real (bondCrossingEvent (h + 1) m) = 1 := by
    have hh := field_crossing_add_dual_rotated μ hμ level m h
    have he : (dualFieldPlaneEdgeLaw μ level).real (planeEdgeCrossingEvent (h + 1) m) =
        νd.real (bondCrossingEvent (h + 1) m) := by
      change (ν.map (restrictToPlaneEdges ∘ dualBondConfig)).real _ = _
      rw [← Measure.map_map measurable_restrictToPlaneEdges measurable_dualBondConfig,
        restrictToPlaneEdges_crossing]
    rw [hm, he] at hh
    exact hh
  have hwidth : 2 * ρ * n + 1 ≤ (2 * ρ + 2) * m := by
    have hh := Nat.mul_le_mul_left (2 * ρ + 2) hmn
    have he : (2 * ρ + 2) * n = 2 * ρ * n + 2 * n := by ring
    omega
  have hsmall : νd.real (bondCrossingEvent (4 * n + 1) m) ≤
      νd.real (bondCrossingEvent (2 * m) m) :=
    measureReal_mono (bondCrossingEvent_width_height_mono (by dsimp [m]; omega) (by omega))
      (measure_ne_top νd _)
  have hlarge : νd.real (bondCrossingEvent ((2 * ρ + 2) * m) m) ≤
      νd.real (bondCrossingEvent (2 * ρ * n + 1) m) :=
    measureReal_mono (bondCrossingEvent_width_height_mono hwidth (by omega))
      (measure_ne_top νd _)
  have hglue := bondCrossing_two_pow_le νd hassd htd hsd m (2 * ρ)
  have hpow : νd.real (bondCrossingEvent (4 * n + 1) m) ^ (4 * ρ + 1) ≤
      νd.real (bondCrossingEvent (2 * m) m) ^ (4 * ρ + 1) :=
    pow_le_pow_left₀ measureReal_nonneg hsmall _
  have he : 2 * (2 * ρ) + 1 = 4 * ρ + 1 := by omega
  rw [he] at hglue
  have hresult := hpow.trans (hglue.trans hlarge)
  have htwo := hdual (4 * n)
  have hρ := hdual (2 * ρ * n)
  have he1 : νd.real (bondCrossingEvent (4 * n + 1) m) =
      1 - μ.real (planarCrossingEvent (2 * n) (4 * n) level) := by linarith
  have he2 : νd.real (bondCrossingEvent (2 * ρ * n + 1) m) =
      1 - μ.real (planarCrossingEvent (2 * n) (2 * ρ * n) level) := by linarith
  rwa [he1, he2] at hresult

end Sandpile.External.RSW
