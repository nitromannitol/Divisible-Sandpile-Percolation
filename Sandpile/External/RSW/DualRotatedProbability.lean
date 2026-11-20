import Sandpile.External.RSW.DualRotatedCrossing
import Sandpile.External.RSW.DualFieldLaw

/-!
# Rotated dual crossing probabilities

The boundary shift and interchange of axes preserve crossing probabilities for a symmetric
bond law. The identity applies to the dual of the bond law induced by a planar field.
-/

open LatticeProb MeasureTheory Set Percolation.Literature

namespace Sandpile.External.RSW

/-- Rotation and translation preserve a bond law invariant under coordinate interchange and
translations. -/
theorem measurePreserving_dualCrossingIso (μ : Measure (Sym2 (Site 2) → Bool))
    (ht : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + dualShift)) μ μ)
    (hs : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) μ μ) :
    MeasurePreserving (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map dualCrossingIso) μ μ := by
  have hh := hs.comp ht
  have he : (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map dualCrossingIso) =
      (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map swapPlaneSite) ∘
        (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map (fun z => z + dualShift)) := by
    funext ω e
    induction e using Sym2.ind with
    | _ x y =>
      have hx : dualCrossingIso x = swapPlaneSite x + dualShift := by
        ext i
        fin_cases i <;> simp [dualCrossingIso, swapPlaneSite]
      have hy : dualCrossingIso y = swapPlaneSite y + dualShift := by
        ext i
        fin_cases i <;> simp [dualCrossingIso, swapPlaneSite]
      simp only [Function.comp_apply, Sym2.map_mk, hx, hy]
  rw [he]
  exact hh

/-- The shifted dual crossing has the probability of an ordinary rotated crossing under the
symmetric dual law. -/
theorem measureReal_shiftedDualCrossing_eq_rotated
    (μ : Measure (Sym2 (Site 2) → Bool)) (m n : ℕ)
    (hμ : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map dualCrossingIso) (μ.map dualBondConfig) (μ.map dualBondConfig)) :
    μ.real (shiftedDualCrossingEvent (m + 1) n) =
      (μ.map dualBondConfig).real (bondCrossingEvent (n + 1) m) := by
  have he : shiftedDualCrossingEvent (m + 1) n =
      (fun ω : Sym2 (Site 2) → Bool => (dualBondConfig ω ∘ Sym2.map dualCrossingIso)) ⁻¹'
        bondCrossingEvent (n + 1) m := by
    ext ω
    exact mem_shiftedDualCrossingEvent_iff_rotated m n ω
  rw [he]
  change μ.real (dualBondConfig ⁻¹' ((fun ω : Sym2 (Site 2) → Bool =>
    ω ∘ Sym2.map dualCrossingIso) ⁻¹' bondCrossingEvent (n + 1) m)) = _
  simpa only [Measure.real, Measure.map_apply measurable_dualBondConfig
    ((measurableSet_bondCrossingEvent (n + 1) m).preimage hμ.measurable)] using
    hμ.measureReal_preimage (measurableSet_bondCrossingEvent (n + 1) m).nullMeasurableSet

/-- A field crossing and the rotated crossing of its dual edge law have complementary
probabilities, with the exact discrete boundary correction. -/
theorem field_crossing_add_dual_rotated (μ : Measure (Site 2 → ℝ))
    [IsProbabilityMeasure μ] (hμ : IsSymmetricPlanarLaw μ) (level : ℝ) (m n : ℕ) :
    μ.real (planarCrossingEvent (m + 1) n level) +
      (dualFieldPlaneEdgeLaw μ level).real (planeEdgeCrossingEvent (n + 1) m) = 1 := by
  let ν := fieldBondLaw μ level
  let : IsProbabilityMeasure ν := isProbabilityMeasure_fieldBondLaw μ level
  have hs := fieldBondLaw_symmetric μ hμ level
  have hi : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map dualCrossingIso) (ν.map dualBondConfig) (ν.map dualBondConfig) :=
    measurePreserving_dualCrossingIso _
      (measurePreserving_dualBondConfig_translate ν dualShift (hs.1 dualShift))
      (measurePreserving_dualBondConfig_swap ν hs.2.1)
  have hh := measureReal_bondCrossing_add_shiftedDual ν (m + 1) n
  rw [measureReal_shiftedDualCrossing_eq_rotated ν m n hi] at hh
  have hcross : ν.real (bondCrossingEvent (m + 1) n) =
      μ.real (planarCrossingEvent (m + 1) n level) :=
    fieldBondLaw_crossing μ level (m + 1) n (by omega)
  have hdual : (dualFieldPlaneEdgeLaw μ level).real (planeEdgeCrossingEvent (n + 1) m) =
      (ν.map dualBondConfig).real (bondCrossingEvent (n + 1) m) := by
    change (ν.map (restrictToPlaneEdges ∘ dualBondConfig)).real
      (planeEdgeCrossingEvent (n + 1) m) = _
    rw [← Measure.map_map measurable_restrictToPlaneEdges measurable_dualBondConfig,
      restrictToPlaneEdges_crossing]
  rw [← hcross, hdual]
  exact hh

end Sandpile.External.RSW
