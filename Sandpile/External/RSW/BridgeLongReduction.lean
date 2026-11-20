import Sandpile.External.RSW.SmallOverlapGluing
import Sandpile.External.RSW.CornerBridge
import Sandpile.External.RSW.Homeomorphisms

/-!
# Reducing long crossings to bottom-bridge gluing

The five-way bridge decomposition and both geometric cases reduce the long-crossing
estimate to a bound for gluing translated bottom bridges.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- The first scale comparison is bounded by the 192nd power of the five-way
square-root threshold. -/
theorem kstScaleIso_one_le_five_root_pow (x : Icc (0 : ℝ) 1) :
    (kstScaleIso 1 x : ℝ) ≤ (1 - (1 - (x : ℝ)) ^ (1 / (5 : ℝ))) ^ 192 := by
  have hx0 : 0 ≤ 1 - (x : ℝ) := by linarith [x.property.2]
  have hx1 : 1 - (x : ℝ) ≤ 1 := by linarith [x.property.1]
  have hroot : (1 - (x : ℝ)) ^ (1 / (5 : ℝ)) ≤ (1 - (x : ℝ)) ^ ((2000 : ℝ)⁻¹) :=
    Real.rpow_le_rpow_of_exponent_ge' hx0 hx1 (by norm_num) (by norm_num)
  have hsmall0 : 0 ≤ 1 - (1 - (x : ℝ)) ^ ((2000 : ℝ)⁻¹) := by
    exact sub_nonneg.mpr (Real.rpow_le_one hx0 hx1 (by positivity))
  have hlarge0 : 0 ≤ 1 - (1 - (x : ℝ)) ^ (1 / (5 : ℝ)) := by
    exact sub_nonneg.mpr (Real.rpow_le_one hx0 hx1 (by norm_num))
  have hlarge1 : 1 - (1 - (x : ℝ)) ^ (1 / (5 : ℝ)) ≤ 1 := by
    linarith [Real.rpow_nonneg hx0 (1 / (5 : ℝ))]
  have hbase : 1 - (1 - (x : ℝ)) ^ ((2000 : ℝ)⁻¹) ≤
      1 - (1 - (x : ℝ)) ^ (1 / (5 : ℝ)) := by linarith
  have hpow : (1 - (1 - (x : ℝ)) ^ ((2000 : ℝ)⁻¹)) ^ (2000 : ℝ) ≤
      (1 - (1 - (x : ℝ)) ^ (1 / (5 : ℝ))) ^ 192 := by
    calc
      _ ≤ (1 - (1 - (x : ℝ)) ^ (1 / (5 : ℝ))) ^ (2000 : ℝ) :=
        Real.rpow_le_rpow hsmall0 hbase (by norm_num)
      _ ≤ (1 - (1 - (x : ℝ)) ^ (1 / (5 : ℝ))) ^ (192 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge' hlarge0 hlarge1 (by norm_num) (by norm_num)
      _ = _ := Real.rpow_natCast _ 192
  have he : (kstScaleIso 1 x : ℝ) =
      (1 - (1 - (x : ℝ)) ^ ((2000 : ℝ)⁻¹)) ^ (2000 : ℝ) := by
    rw [kstScaleIso, crossingComparisonIso_apply]
    norm_num [one_div]
  exact he ▸ hpow

/-- The bridge-to-long-crossing estimate follows from gluing 96 translated bottom bridges. -/
theorem kstBridge_long_of_bottom_gluing (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ)
    (hs : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) μ μ)
    (hr : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map reflectPlaneSite) μ μ) (m : ℕ) (hm : 12 ≤ m) (hdiv : 12 ∣ m)
    (hbottom : μ.real (kstBottomBridgeEvent m) ^ 96 ≤
      μ.real (bondCrossingEvent (16 * m) (2 * m))) :
    (kstScaleIso 1 (probabilityInUnitInterval μ (kstBridgeEvent m)) : ℝ) ≤
      μ.real (bondCrossingEvent (16 * m) (2 * m)) := by
  let r := 1 - (1 - μ.real (kstBridgeEvent m)) ^ (1 / (5 : ℝ))
  have hr0 : 0 ≤ r := by
    dsimp only [r]
    have hx0 : 0 ≤ 1 - μ.real (kstBridgeEvent m) := sub_nonneg.mpr measureReal_le_one
    have hx1 : 1 - μ.real (kstBridgeEvent m) ≤ 1 := by
      linarith [show 0 ≤ μ.real (kstBridgeEvent m) from measureReal_nonneg]
    exact sub_nonneg.mpr (Real.rpow_le_one hx0 hx1 (by norm_num))
  have hcmp := kstScaleIso_one_le_five_root_pow (probabilityInUnitInterval μ (kstBridgeEvent m))
  have hmax := measureReal_kstBridgePiece_max_ge μ ha hs hr m
  change r ≤ max (μ.real (kstBridgePieceEvent m 0)) (μ.real (kstBridgePieceEvent m 1)) at hmax
  rcases le_max_iff.mp hmax with hside | hcorner
  · have hpow := pow_le_pow_left₀ hr0 hside 192
    have hshrink : μ.real (kstBridgePieceEvent m 0) ^ 192 ≤
        μ.real (kstBridgePieceEvent m 0) ^ 167 :=
      pow_le_pow_of_le_one measureReal_nonneg measureReal_le_one (by omega)
    exact hcmp.trans (hpow.trans (hshrink.trans (kstBridgePiece_zero_pow_le_long μ ha ht hs m hdiv)))
  · have hpow := pow_le_pow_left₀ hr0 hcorner 192
    have hsq := measureReal_kstBridgePiece_one_sq_le_bottom μ ha hs hr m hm
    have hpow' : (μ.real (kstBridgePieceEvent m 1) ^ 2) ^ 96 ≤
        μ.real (kstBottomBridgeEvent m) ^ 96 :=
      pow_le_pow_left₀ (sq_nonneg _) hsq 96
    have he : μ.real (kstBridgePieceEvent m 1) ^ 192 =
        (μ.real (kstBridgePieceEvent m 1) ^ 2) ^ 96 := by rw [← pow_mul]
    exact hcmp.trans (hpow.trans (he.le.trans (hpow'.trans hbottom)))

end Sandpile.External.RSW
