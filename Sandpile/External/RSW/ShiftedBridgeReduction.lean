import Sandpile.External.RSW.BridgeLongComparison
import Sandpile.External.RSW.DualRotatedProbability

/-!
# Bridge comparison and shifted dual crossings

Longer crossings absorb the one-unit boundary corrections in discrete planar duality.
The resulting comparison function is independent of the law and scale.
-/

open LatticeProb MeasureTheory Set

noncomputable section

namespace Sandpile.External.RSW

/-- The bridge comparison function after the fixed long-crossing power loss. -/
def kstLongBridgeIso : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1 :=
  (kstScaleIso 1).trans (unitIntervalRpow 77 (by norm_num))

/-- The aspect-eight comparison obtained from the primal and dual bridge comparisons. -/
def kstShiftedAspectIso : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1 :=
  (((unitIntervalReflect.trans kstLongBridgeIso.symm.dual).trans unitIntervalReflect.symm).trans
    (kstScaleIso 20)).trans kstLongBridgeIso

/-- A bridge comparison at scale `r` and bridge-to-crossing estimates for both the primal
and dual laws imply an aspect-eight comparison at scale `4r`. -/
theorem kstShiftedAspectIso_le_crossing (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ)
    (hs : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) μ μ)
    (r : ℕ) (hr : 0 < r)
    (hbridge : kstScaleIso 20 (unitIntervalComplement
      (probabilityInUnitInterval (μ.map dualBondConfig) (kstBridgeEvent r))) ≤
        probabilityInUnitInterval μ (kstBridgeEvent r))
    (hprimal : (kstScaleIso 1 (probabilityInUnitInterval μ (kstBridgeEvent r)) : ℝ) ≤
      μ.real (bondCrossingEvent (16 * r) (2 * r)))
    (hdual : (kstScaleIso 1 (probabilityInUnitInterval (μ.map dualBondConfig)
      (kstBridgeEvent r)) : ℝ) ≤
        (μ.map dualBondConfig).real (bondCrossingEvent (16 * r) (2 * r))) :
    (kstShiftedAspectIso (probabilityInUnitInterval μ
      (bondCrossingEvent (8 * r) (64 * r))) : ℝ) ≤
      μ.real (bondCrossingEvent (64 * r) (8 * r)) := by
  let ν := μ.map dualBondConfig
  let : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff measurable_dualBondConfig.aemeasurable).2 inferInstance
  have haν : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → ν.real A * ν.real B ≤ ν.real (A ∩ B) :=
    fun _ _ hA hB hAm hBm => dualBondConfig_associated μ ha hA hB hAm hBm
  have htν : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) ν ν :=
    fun v => measurePreserving_dualBondConfig_translate μ v (ht v)
  have hsν : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) ν ν := measurePreserving_dualBondConfig_swap μ hs
  let t := probabilityInUnitInterval μ (bondCrossingEvent (8 * r) (64 * r))
  let u := probabilityInUnitInterval μ (kstBridgeEvent r)
  let v := probabilityInUnitInterval ν (kstBridgeEvent r)
  have hwide₀ := kstBridge_to_long_crossing μ ha ht hs r hprimal
  have hdual₀ := kstBridge_to_long_crossing ν haν htν hsν r hdual
  have hwideSub : bondCrossingEvent (80 * r) (2 * r) ⊆ bondCrossingEvent (64 * r) (8 * r) :=
    bondCrossingEvent_width_height_mono (by omega) (by omega)
  have hdualSub : bondCrossingEvent (80 * r) (2 * r) ⊆
      bondCrossingEvent (64 * r + 1) (8 * r - 1) :=
    bondCrossingEvent_width_height_mono (by omega) (by omega)
  have hwide : (kstLongBridgeIso u : ℝ) ≤ μ.real (bondCrossingEvent (64 * r) (8 * r)) := by
    change (kstScaleIso 1 u : ℝ) ^ (77 : ℝ) ≤ _
    calc
      (kstScaleIso 1 u : ℝ) ^ (77 : ℝ) = (kstScaleIso 1 u : ℝ) ^ (77 : ℕ) :=
        Real.rpow_natCast _ 77
      _ ≤ _ := hwide₀.trans (measureReal_mono hwideSub (measure_ne_top μ _))
  have hdualLong : (kstLongBridgeIso v : ℝ) ≤ ν.real (bondCrossingEvent (64 * r + 1) (8 * r - 1)) := by
    change (kstScaleIso 1 v : ℝ) ^ (77 : ℝ) ≤ _
    calc
      (kstScaleIso 1 v : ℝ) ^ (77 : ℝ) = (kstScaleIso 1 v : ℝ) ^ (77 : ℕ) :=
        Real.rpow_natCast _ 77
      _ ≤ _ := hdual₀.trans (measureReal_mono hdualSub (measure_ne_top ν _))
  let s := 8 * r - 1
  have hswidth : s + 1 = 8 * r := by dsimp [s]; omega
  have hiso : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map dualCrossingIso) ν ν :=
    measurePreserving_dualCrossingIso ν (htν _) hsν
  have hcomplement := measureReal_bondCrossing_add_shiftedDual μ (s + 1) (64 * r)
  rw [measureReal_shiftedDualCrossing_eq_rotated μ s (64 * r) hiso, hswidth] at hcomplement
  have hv : kstLongBridgeIso v ≤ unitIntervalComplement t := by
    change (kstLongBridgeIso v : ℝ) ≤ 1 - (t : ℝ)
    change μ.real (bondCrossingEvent (8 * r) (64 * r)) +
      ν.real (bondCrossingEvent (64 * r + 1) s) = 1 at hcomplement
    dsimp only [s] at hcomplement
    change (kstLongBridgeIso v : ℝ) ≤
      1 - μ.real (bondCrossingEvent (8 * r) (64 * r))
    linarith
  let χ := (unitIntervalReflect.trans kstLongBridgeIso.symm.dual).trans unitIntervalReflect.symm
  have hχ : χ t ≤ unitIntervalComplement v := by
    have hh := (kstLongBridgeIso.le_symm_apply).2 hv
    change 1 - (kstLongBridgeIso.symm (unitIntervalComplement t) : ℝ) ≤ 1 - (v : ℝ)
    have hh' : (v : ℝ) ≤ (kstLongBridgeIso.symm (unitIntervalComplement t) : ℝ) := hh
    linarith
  have hchain : kstLongBridgeIso (kstScaleIso 20 (χ t)) ≤ kstLongBridgeIso u :=
    kstLongBridgeIso.monotone (((kstScaleIso 20).monotone hχ).trans hbridge)
  exact (show (kstLongBridgeIso (kstScaleIso 20 (χ t)) : ℝ) ≤
    (kstLongBridgeIso u : ℝ) from hchain).trans hwide

end Sandpile.External.RSW
