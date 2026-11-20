import Sandpile.External.RSW.AdjacentQuasiReduction
import Sandpile.External.RSW.DualBridgeTall
import Sandpile.External.RSW.DoubleDual

/-!
# Adjacent quasi-crossings from arm estimates

The exact shifted dual crossing identity transfers the tall-crossing-to-arm comparison
to the three arm scales used in the adjacent quasi-crossing construction.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- The two intermediate arm scales lie between consecutive geometric scales. -/
theorem kstBaseScale_intermediate_bounds (j : ℕ) :
    kstBaseScale j ≤ 5 * kstBaseScale j / 2 ∧
      5 * kstBaseScale j / 2 ≤ 4 * kstBaseScale j ∧
      kstBaseScale j ≤ 31 * kstBaseScale j / 8 ∧
      31 * kstBaseScale j / 8 ≤ 4 * kstBaseScale j := by
  have hmid := (kstBaseScale_intermediate j).1
  have hfar := (kstBaseScale_intermediate j).2.2
  dsimp only [kstBaseScale] at hmid hfar ⊢
  constructor <;> [skip; constructor <;> [skip; constructor]] <;> omega

/-- An arm bound in terms of a tall crossing also bounds it in terms of a dual bridge. -/
theorem measureReal_kstArm_ge_of_dualBridge
    (μ : Measure (Sym2 (Site 2) → Bool)) [IsProbabilityMeasure μ]
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ)
    (hs : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) μ μ)
    (m s : ℕ) (hm : 0 < m) (hms : m ≤ s) (hsm : s ≤ 4 * m)
    (harm : (kstScaleIso 1 (probabilityInUnitInterval μ (bondCrossingEvent (2 * s) (16 * s))) : ℝ) ≤
      μ.real (kstArmEvent s)) :
    (kstScaleIso 1 (unitIntervalComplement (probabilityInUnitInterval (μ.map dualBondConfig)
      (kstBridgeEvent (4 * m)))) : ℝ) ≤ μ.real (kstArmEvent s) := by
  have hcross := one_sub_dualBridge_le_intermediate_crossing μ ht hs m s hm hms hsm
  have hx : unitIntervalComplement (probabilityInUnitInterval (μ.map dualBondConfig)
      (kstBridgeEvent (4 * m))) ≤ probabilityInUnitInterval μ (bondCrossingEvent (2 * s) (16 * s)) := hcross
  have hmon : (kstScaleIso 1 (unitIntervalComplement (probabilityInUnitInterval (μ.map dualBondConfig)
      (kstBridgeEvent (4 * m)))) : ℝ) ≤
      kstScaleIso 1 (probabilityInUnitInterval μ (bondCrossingEvent (2 * s) (16 * s))) :=
    (kstScaleIso 1).monotone hx
  exact hmon.trans harm

/-- The adjacent quasi-crossing estimate follows from the six-event inclusion and
arm estimates for intermediate tall crossings. -/
theorem measureReal_adjacentQuasi_ge_of_arm_tall
    (μ : Measure (Sym2 (Site 2) → Bool)) [IsProbabilityMeasure μ]
    (ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ)
    (hs : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) μ μ) (j : ℕ)
    (hgeom : kstAdjacentSixEvent (kstBaseScale j) ⊆
      kstQuasiCrossingEvent (4 * kstBaseScale j) (kstBaseScale j))
    (harm : ∀ s, kstBaseScale j ≤ s → s ≤ 4 * kstBaseScale j → 192 ∣ s →
      (kstScaleIso 1 (probabilityInUnitInterval μ (bondCrossingEvent (2 * s) (16 * s))) : ℝ) ≤
        μ.real (kstArmEvent s)) :
    (kstScaleIso 2 (unitIntervalComplement (probabilityInUnitInterval (μ.map dualBondConfig)
      (kstBridgeEvent (kstBaseScale (j + 1))))) : ℝ) ≤
        μ.real (kstQuasiCrossingEvent (kstBaseScale (j + 1)) (kstBaseScale j)) := by
  let m := kstBaseScale j
  let x := unitIntervalComplement (probabilityInUnitInterval (μ.map dualBondConfig)
    (kstBridgeEvent (4 * m)))
  have hm : 0 < m := Nat.mul_pos (by norm_num) (pow_pos (by norm_num) j)
  obtain ⟨hmid₀, hmid₁, hfar₀, hfar₁⟩ := kstBaseScale_intermediate_bounds j
  obtain ⟨hd₀, hd₁, hd₂⟩ := kstBaseScale_arm_scales_dvd j
  have hzero : (kstScaleIso 1 x : ℝ) ≤ μ.real (kstArmEvent m) :=
    measureReal_kstArm_ge_of_dualBridge μ ht hs m m hm le_rfl (by omega)
      (harm m le_rfl (by omega) hd₀)
  have hmid : (kstScaleIso 1 x : ℝ) ≤ μ.real (kstArmEvent (5 * m / 2)) :=
    measureReal_kstArm_ge_of_dualBridge μ ht hs m _ hm hmid₀ hmid₁ (harm _ hmid₀ hmid₁ hd₁)
  have hfar : (kstScaleIso 1 x : ℝ) ≤ μ.real (kstArmEvent (31 * m / 8)) :=
    measureReal_kstArm_ge_of_dualBridge μ ht hs m _ hm hfar₀ hfar₁ (harm _ hfar₀ hfar₁ hd₂)
  have hh := measureReal_adjacentQuasi_ge_of_six_events μ ha ht hs j x hgeom hzero hmid hfar
  change (kstScaleIso 2 (unitIntervalComplement (probabilityInUnitInterval (μ.map dualBondConfig)
      (kstBridgeEvent (4 * kstBaseScale j)))) : ℝ) ≤
    μ.real (kstQuasiCrossingEvent (4 * kstBaseScale j) (kstBaseScale j)) at hh
  rw [← kstBaseScale_succ] at hh
  exact hh

/-- The same reduction for the dual law uses double duality to recover the primal
bridge probability. -/
theorem measureReal_adjacentDualQuasi_ge_of_arm_tall
    (μ : Measure (Sym2 (Site 2) → Bool)) [IsProbabilityMeasure μ]
    (ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ)
    (hs : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) μ μ) (j : ℕ)
    (hgeom : kstAdjacentSixEvent (kstBaseScale j) ⊆
      kstQuasiCrossingEvent (4 * kstBaseScale j) (kstBaseScale j))
    (harm : ∀ s, kstBaseScale j ≤ s → s ≤ 4 * kstBaseScale j → 192 ∣ s →
      (kstScaleIso 1 (probabilityInUnitInterval (μ.map dualBondConfig)
        (bondCrossingEvent (2 * s) (16 * s))) : ℝ) ≤
          (μ.map dualBondConfig).real (kstArmEvent s)) :
    (kstScaleIso 2 (unitIntervalComplement
      (probabilityInUnitInterval μ (kstBridgeEvent (kstBaseScale (j + 1))))) : ℝ) ≤
        (μ.map dualBondConfig).real
          (kstQuasiCrossingEvent (kstBaseScale (j + 1)) (kstBaseScale j)) := by
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
  have he : probabilityInUnitInterval (ν.map dualBondConfig) (kstBridgeEvent (kstBaseScale (j + 1))) =
      probabilityInUnitInterval μ (kstBridgeEvent (kstBaseScale (j + 1))) := by
    apply Subtype.ext
    exact measureReal_doubleDual_kstBridge μ (ht 1) _
  have hh := measureReal_adjacentQuasi_ge_of_arm_tall ν haν htν hsν j hgeom harm
  rwa [he] at hh

end Sandpile.External.RSW
