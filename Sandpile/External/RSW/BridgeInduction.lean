import Sandpile.External.RSW.ScaleInduction
import Sandpile.External.RSW.GoodBaseScale
import Sandpile.External.RSW.CorridorCascade
import Sandpile.External.RSW.BridgePathIntersection
import Sandpile.External.RSW.BaseScaleArithmetic
import Sandpile.External.RSW.NearScaleBound

/-!
# Bridge induction from geometric estimates

The base-scale bridge comparison follows from long-crossing, adjacent-scale
quasi-crossing, and corridor estimates for the primal and dual bond laws.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- Long-crossing and quasi-crossing estimates imply the bridge comparison along the
integer geometric scales. -/
theorem kstBridge_base_comparison_of_geometry
    (μ : Measure (Sym2 (Site 2) → Bool)) [IsProbabilityMeasure μ]
    (ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ)
    (hs : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) μ μ)
    (hlong : ∀ j,
      (kstScaleIso 1 (probabilityInUnitInterval μ (kstBridgeEvent (kstBaseScale j))) : ℝ) ≤
        μ.real (bondCrossingEvent (16 * kstBaseScale j) (2 * kstBaseScale j)))
    (hlongDual : ∀ j,
      (kstScaleIso 1 (probabilityInUnitInterval (μ.map dualBondConfig)
        (kstBridgeEvent (kstBaseScale j))) : ℝ) ≤
        (μ.map dualBondConfig).real
          (bondCrossingEvent (16 * kstBaseScale j) (2 * kstBaseScale j)))
    (hnear : ∀ j,
      (kstScaleIso 2 (unitIntervalComplement
        (probabilityInUnitInterval (μ.map dualBondConfig)
          (kstBridgeEvent (kstBaseScale (j + 1))))) : ℝ) ≤
        μ.real (kstQuasiCrossingEvent (kstBaseScale (j + 1)) (kstBaseScale j)))
    (hnearDual : ∀ j,
      (kstScaleIso 2 (unitIntervalComplement
        (probabilityInUnitInterval μ (kstBridgeEvent (kstBaseScale (j + 1))))) : ℝ) ≤
        (μ.map dualBondConfig).real
          (kstQuasiCrossingEvent (kstBaseScale (j + 1)) (kstBaseScale j)))
    (hcover : ∀ i j, j < i → KSTCorridorBridgeCover
      (kstBaseScale (i + 1)) (kstBaseScale i) (kstBaseScale j))
    (K : ℕ) :
    kstScaleIso 20 (unitIntervalComplement (probabilityInUnitInterval (μ.map dualBondConfig)
      (kstBridgeEvent (kstBaseScale K)))) ≤
        probabilityInUnitInterval μ (kstBridgeEvent (kstBaseScale K)) := by
  let ν := μ.map dualBondConfig
  let : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff measurable_dualBondConfig.aemeasurable).2 inferInstance
  have haν : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → ν.real A * ν.real B ≤ ν.real (A ∩ B) :=
    fun _ _ hA hB hAm hBm => dualBondConfig_associated μ ha hA hB hAm hBm
  have htν : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) ν ν :=
    fun v => measurePreserving_dualBondConfig_translate μ v (ht v)
  let b := fun j => probabilityInUnitInterval μ (kstBridgeEvent (kstBaseScale j))
  let d := fun j => probabilityInUnitInterval ν (kstBridgeEvent (kstBaseScale j))
  let q := fun i j => probabilityInUnitInterval μ
    (kstQuasiCrossingEvent (kstBaseScale i) (kstBaseScale j))
  let r := fun i j => probabilityInUnitInterval ν
    (kstQuasiCrossingEvent (kstBaseScale i) (kstBaseScale j))
  have hnearStrong (j : ℕ) :
      1 - (1 - (kstScaleIso 4 (unitIntervalComplement (d (j + 1))) : ℝ)) ^ 2 ≤
        (q (j + 1) j : ℝ) :=
    (kstScaleIso_adjacent_bound (unitIntervalComplement (d (j + 1)))).trans (hnear j)
  have hnearDualStrong (j : ℕ) :
      1 - (1 - (kstScaleIso 4 (unitIntervalComplement (b (j + 1))) : ℝ)) ^ 2 ≤
        (r (j + 1) j : ℝ) :=
    (kstScaleIso_adjacent_bound (unitIntervalComplement (b (j + 1)))).trans (hnearDual j)
  have hpos (i : ℕ) : 0 < kstBaseScale i := by
    exact Nat.mul_pos (by norm_num) (pow_pos (by norm_num) i)
  have hmono {i j : ℕ} (hij : i ≤ j) : kstBaseScale i ≤ kstBaseScale j := by
    dsimp only [kstBaseScale]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hij)
  have hstep : ∀ j, kstScaleIso 1 (b j) ≤ b (j + 1) := by
    intro j
    simpa only [b, ← kstBaseScale_succ] using
      kstBridge_four_scale_comparison μ ht (kstScaleIso 1) (kstBaseScale j) (hlong j)
  have hstepDual : ∀ j, kstScaleIso 1 (d j) ≤ d (j + 1) := by
    intro j
    simpa only [d, ← kstBaseScale_succ] using
      kstBridge_four_scale_comparison ν htν (kstScaleIso 1) (kstBaseScale j) (hlongDual j)
  have hadj : ∀ j, kstScaleIso 4 (unitIntervalComplement (d (j + 1))) ≤ q (j + 1) j := by
    intro j
    have hx := (kstScaleIso 4 (unitIntervalComplement (d (j + 1)))).property
    have hn := hnearStrong j
    change 1 - (1 - (kstScaleIso 4 (unitIntervalComplement (d (j + 1))) : ℝ)) ^ 2 ≤
      (q (j + 1) j : ℝ) at hn
    change (kstScaleIso 4 (unitIntervalComplement (d (j + 1))) : ℝ) ≤ (q (j + 1) j : ℝ)
    have hmul := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
    nlinarith
  have hadjDual : ∀ j, kstScaleIso 4 (unitIntervalComplement (b (j + 1))) ≤ r (j + 1) j := by
    intro j
    have hx := (kstScaleIso 4 (unitIntervalComplement (b (j + 1)))).property
    have hn := hnearDualStrong j
    change 1 - (1 - (kstScaleIso 4 (unitIntervalComplement (b (j + 1))) : ℝ)) ^ 2 ≤
      (r (j + 1) j : ℝ) at hn
    change (kstScaleIso 4 (unitIntervalComplement (b (j + 1))) : ℝ) ≤ (r (j + 1) j : ℝ)
    have hmul := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
    nlinarith
  apply kstBridge_comparison_of_scale_estimates b d q r
  · simpa only [b, d, kstBaseScale, pow_zero, mul_one] using
      kstBridge_good_base_1536 μ ha ht hs
  · exact hstep
  · exact hstepDual
  · exact hadj
  · exact hadjDual
  · intro i j hij hsmall
    exact kstCorridor_cascade_probability μ ha ht _ _ _ (hcover i j hij)
      (kstScaleIso 4 (unitIntervalComplement (d (i + 1)))).property.2 hsmall (hnearStrong i)
  · intro i j hij hsmall
    exact kstCorridor_cascade_probability ν haν htν _ _ _ (hcover i j hij)
      (kstScaleIso 4 (unitIntervalComplement (b (i + 1)))).property.2 hsmall (hnearDualStrong i)
  · intro i j hij
    exact measureReal_kstQuasiCrossing_mul_bridge_le μ ha _ _ (hpos j) (hmono hij)
  · intro i j hij
    exact measureReal_kstQuasiCrossing_mul_bridge_le ν haν _ _ (hpos j) (hmono hij)

end Sandpile.External.RSW
