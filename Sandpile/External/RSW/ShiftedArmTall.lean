import Sandpile.External.RSW.AlphaDualBridgeLong
import Sandpile.External.RSW.ArmTallDuality

/-!
# Narrow bridges and shifted tall crossings

The discrete dual of a long crossing gives an arm comparison at a tall rectangle
whose boundary dimensions account for the one-unit lattice shift.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- A shifted tall crossing and the unshifted long dual crossing have complementary
probabilities. -/
theorem measureReal_shiftedTallCrossing_add_dual_long
    (μ : Measure (Sym2 (Site 2) → Bool)) [IsProbabilityMeasure μ]
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ)
    (hs : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) μ μ) (m : ℕ) (hm : 0 < m) :
    μ.real (bondCrossingEvent (2 * m + 1) (16 * m - 1)) +
      (μ.map dualBondConfig).real (bondCrossingEvent (16 * m) (2 * m)) = 1 := by
  let ν := μ.map dualBondConfig
  have htν : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) ν ν :=
    fun v => measurePreserving_dualBondConfig_translate μ v (ht v)
  have hsν : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) ν ν := measurePreserving_dualBondConfig_swap μ hs
  have hiso := measurePreserving_dualCrossingIso ν (htν _) hsν
  have h := measureReal_bondCrossing_add_shiftedDual μ (2 * m + 1) (16 * m - 1)
  rw [measureReal_shiftedDualCrossing_eq_rotated μ (2 * m) (16 * m - 1) hiso] at h
  have hwidth : 16 * m - 1 + 1 = 16 * m := by omega
  rw [hwidth] at h
  exact h

/-- The scale-one comparison of the shifted tall crossing is bounded by the complement
of the narrow dual bridge. -/
theorem kstScaleIso_shiftedTall_le_one_sub_dualBridge
    (μ : Measure (Sym2 (Site 2) → Bool)) [IsProbabilityMeasure μ]
    (ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ)
    (hs : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) μ μ)
    (hr : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map reflectPlaneSite) μ μ) (m : ℕ) (hm : 64 ≤ m) (hdiv : 64 ∣ m) :
    (kstScaleIso 1 (probabilityInUnitInterval μ
      (bondCrossingEvent (2 * m + 1) (16 * m - 1))) : ℝ) ≤
      1 - (μ.map dualBondConfig).real (centeredBridgeEvent m (m / 64)) := by
  let ν := μ.map dualBondConfig
  let x := probabilityInUnitInterval ν (centeredBridgeEvent m (m / 64))
  let y := probabilityInUnitInterval μ (bondCrossingEvent (2 * m + 1) (16 * m - 1))
  have hlong := kstAlphaBridge_long_dual_crossing μ ha ht hs hr m hm hdiv
  have hdual := measureReal_shiftedTallCrossing_add_dual_long μ ht hs m (by omega)
  have hcomp : kstScaleIso 1 x ≤ unitIntervalComplement y := by
    change (kstScaleIso 1 x : ℝ) ≤ 1 - (y : ℝ)
    change (kstScaleIso 1 x : ℝ) ≤ ν.real (bondCrossingEvent (16 * m) (2 * m)) at hlong
    change (y : ℝ) + ν.real (bondCrossingEvent (16 * m) (2 * m)) = 1 at hdual
    linarith
  have hcompl (z : Icc (0 : ℝ) 1) :
      unitIntervalComplement (unitIntervalComplement z) = z := by
    apply Subtype.ext
    change 1 - (1 - (z : ℝ)) = (z : ℝ)
    ring
  have h := (kstScaleIso_duality 1 (unitIntervalComplement y) (unitIntervalComplement x)).1
    (by rw [hcompl]; exact hcomp)
  rw [hcompl] at h
  exact h

/-- A dual bridge obstruction implies the arm estimate at the shifted tall rectangle. -/
theorem kstArm_ge_of_shifted_dualBridge_obstruction
    (μ : Measure (Sym2 (Site 2) → Bool)) [IsProbabilityMeasure μ]
    (ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ)
    (hs : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) μ μ)
    (hr : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map reflectPlaneSite) μ μ) (m : ℕ) (hm : 64 ≤ m) (hdiv : 64 ∣ m)
    (hobs : 1 - (μ.map dualBondConfig).real (centeredBridgeEvent m (m / 64)) ≤
      μ.real (kstArmEvent m)) :
    (kstScaleIso 1 (probabilityInUnitInterval μ
      (bondCrossingEvent (2 * m + 1) (16 * m - 1))) : ℝ) ≤ μ.real (kstArmEvent m) :=
  (kstScaleIso_shiftedTall_le_one_sub_dualBridge μ ha ht hs hr m hm hdiv).trans hobs

end Sandpile.External.RSW
